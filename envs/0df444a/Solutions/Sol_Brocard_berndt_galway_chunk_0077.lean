-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:43:00.443297+00:00
-- url     : https://prove2.me/submissions/caddaa12-3eeb-413f-a07f-b4e0a5f88f9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 13669071 ≤ n < 13848927 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 13670321 1250 13669071 13669079
    0x28021f0504080a260106120b030d09030b1e010807030302010b01050f030f07030207060504030206040302060106090302090a0b0402090604030f0c06050301050d02121f050108071d071209060903050912010501 90
    0x4141664041003d0740392542d984420201410141c03004c2c0c2030380c501c041003040004620143d005e0340740707481d101c1444010f0008082800a00d0341c0c0c0c040240b03c85000403d030305070910000f440462140d4001c0dc80781c3c03141894900843c00105100420703804943c0d56803000303038100200b41c0c080c05105059882400c03d142011011344405001c1d110040001c0c4100c0041f07400101e145000b42e042d14545504410b04000e10728203440d029503a54401e94041e0b0261055100000300c00d841200c44009a950140c900b88640c6c480401c560050114040c20951040c1c0a0040c2010390719400d000c1e000860007405080c07240d150600b071200251a503904034078108501000180001c2d1550700f06003001d564150b0b075142c2034000107c007250621400f010705600c1c1c4010000c4100b9450420f402c4070741030705e00600640d601d00b50341e00031101a400c00b078402e80301c00c003188030001003070540608141024051401d202080800c074035030f944012180300d0203003200400c0c808120154142000b96000b00c40402c030b00f001300074039414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 13671571 1250 13670321 13670333
    0x40b03040f0611040605070507170a030e040b10020a031106040f0f240f0b04050601020a0b040305040803030c030a05090f060604021c06080303010518010302090c28021f0504 76
    0x100a0014210640c078080702070420025a1001919402c3e20086648403902c80c80014004e81c05583c1c281c1c2d4520506501203400004030f01c04c05201e881440041c0382d00d45660740d080e41e0442c0083d100c2540603588a03c5018540c88181200380d0107903207540608020005032401405400c0e00400c0788500b940724000b000001040814001340721134004034040c9640b00a0315007603030280810010428603420405990714121101c0c2c00000203400ca200c41400016000010b21049403001c460743e6005038450070110010640444655812078001e250991a040e00e86540d2031440d44191051301d050306001040148a103454881c99400004e6400a07292815511012030f07070f160006009140704990001d00f070b82e0766080d00300200340e050301409030074401d07203682e0085030b912074000b4801c09004401e0b003207a121001e031807290341134180c950007000c580b0302e500e03007040703a1019800425960541004e02c100481d0350079903034900403180c61031540c000d01d036401c1510151501c003c092070550300307a18109001e000015403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 13672821 1250 13671571 13671577
    0x20604020607050c0a03031d031203010e04030c080307020d0306080a020907050a0909060803120f04050a030309030c06051f060203040602070b0901030605120109030e0a0302060306120309030118021203040b 90
    0x9011100c107030b00c03040d550400a080c01c6030f600c40550320a005daa00041050340054405942a811540340400c150715a4241a06c8078000c0f030207158528000c000610003556024171042d0064020b2500d801110b6860303841c51081e0784140c6108015a01061541600b2603150203140090600e0a014082b00282c69002c21003040b0064a14410f201000c01c0501e2a14400c1007440c0003080c604805000a9980e204881d480e80d010850030301044a601d400103540d0040381000c00e0156034000300030100d03020a03480c2100100308446089040204445a440104420b4046c030b0f4014070b02210085a1340410540c0c1000c5200d45600003019500184002c0014540100b84d02007124851082640c0e80ea260b640128000d0115810050744440c01c0d035016880064158401c0401c1c1c0d100c1c1d114524030000101c20040d42122901c4020b50155041000504500300710310044031041c84141180e0070a6403c80020707080d02c01080005004464180b4090b055260161207641c00d4507a180c051454142131402d5010340344 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 13674071 1250 13672821 13672823
    0x30b090c0a031109070e1306080c010201020403120c030c020d05010e06060906010f03180210020d0306050103020906070305091206070509030c190608070207081204090c03050606030a09020604080d02030a11010c020604 95
    0x9211000017248240134000b0710390510801460510081264455000207250502402c03109206c0e240c484840d41d40148220b8050340c0d00a0040e210b0000d80200403108c10040030000c60412501919034030050326a0382d00301050901c0340380007040000c0460843c0740340c0400144000d10071040364050014903604201e2003564844540740100300eaa040d4101038206040c4071200035040258041d40d00d101d15400b00380d0503d1400503907818841259100011000d034000e02031000d07400101080b41d000007a02400003000c0a00014244030f400c126003d0382281821821203201000c07540c0080d03403103514034048c800e402020804558540c0c0c2c214141004402c0503003640034070404e000900000c1035115008000c00d0006024074001c03965203500c0c154000c02130380c005201d40714801c0c1c07d100b00c442d1014041e000c0d491040c6000703001c1d141981d46400c16400a07003d4002c061303030030010400021440740d4090060f55020300c0d940d00150358600e10b0240040c85a51242413242c10341e403405000c2d0881d030f68040380311608a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 13675321 1250 13674071 13674079
    0x40606050d09080903030705010903080702032b150311210d03090302030f0703020a0c0b0c060609060105070204020d050106090e013f0b091e070312110601030b090c0a0311 75
    0x1003019180a0f41d0b03d116403840c0d10350502c404104001002030541000750414445e55440c8043c0d00d81140981c0c0c2c0c1e010300440a4410461030004050300740004182e80b007520405130012411004038410010200e030aa0025600e618110341ca03142d45080c0722156020141d00b00340003280040c02135020a403240c141c400881c08041c3c172100d844007030620030403c1d200d0700e400100c3c20340e41d41c500341d05e4003a690744038000084a601042d8040020204243c17020b4600e03042944028082943c2da80c810401c002030000c03c100d050003824403104000da00c03a440549050034840c1d600283c0c81d4144880a083c0800c01d40c4403400c0d841200d0b00521006d410158504440850300e41809a00c840e442941c1c00c2070400030008504000e61580f0f02424440c005800601400300c100c265994078462060043c8a9180003c4019881d03104000410006810982c040d051600c00d2805030703a10480d10a2081c20b00400b82e0041e640300c10204140081e00d601801440000c1000302d40d03036001c151450750f0f000141c65982100c5841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 13676571 1250 13675321 13675331
    0x9060409020309120409020c100507020307140f0a050102120a0b030a0605040c0509070c0201170106090b03040f08040806010602010f0b09060112150b1210030b06130204050405180606040606050d 85
    0x54424204520050700219030708140d1a1600c506e1030000942000182941c079200700c0d405003607590f9140c8100c900540032039020754500703001034440c10704000100180c1c5405100d4150741da501c903541032202004091003040007513620790002e104042400001f40c91039042d60b2030304203101501c2d41c0001d10b02e040c840e0312440c0403c00b541d4604164206c1101a0300c800e4004580c20100b099850340254100c011510036240c880c103840c085000a00d245a0034028580402c190780742c1440000d8901014640c8148141c0800303d400b0340d40c0d50340c80c4443d0000e50064403982d01c41401172107420340a020712454580c0f8107604101070b110707180000b024411301400c3c007414010308190030903801c51a5000982d18801d0002104401503a843c1012502e5012038100c3c1c00c900706540214883d16580e021100450307412003855002c1d03840d0a0104175800c0b00420340d10074919401c010000d12511a401640e204241d29012090f10301020204a81040001003990b48600d2503c0340030b02c40d80781c02a00b038510801c003020001034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 13677821 1250 13676571 13676581
    0x10b090612211306030203010602160e06060702060f070c0501020d030e060c030910050705180a0b04050402090303070b04030e040c11060c0a032004050a15020d0c0c030f0b0406060b090604090203 85
    0x2c0303540b04161034255551004034000c00c0090301600158100c400c40d030b0888002d104002805080b030358540c0190300e2400d80c0c10012908500c0d1007805040203a00060101d031070700304100000100c0780c1c0001400c43e000210483c04004e25070301400b19030441c031801e0609002004ca0070343c09a0311540d0082999070413000c040302013040e165003007140b100d407140390340c80800c41402d025101074004e0f08484200b81c068bd14584a4000d2800c040d541070b03040360703054180c070f42c200b0b400d007000c120280d04210006505032006005140106d0300e0401c080e0700450103a02c0c0c50103444c2c1c001e02404181d03140e0000100a020310005002007040c400990a984001d03081e1103da2a8500c020086000d8803040f030f41c0c05407004c9004954954010390000070b02c11a4002c84120520964034650f4030501c28a0302840d4016030082075091345228003403110300c21a10f02c1507807000000c40d1641c0d92a0f00b50b4408150503594142540d040000300f0040d441128090101d2500040c207001c440b0000403620710035401420307181500440452 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 13679071 1250 13677821 13677883
    0x80906060411070501020307020709060503010204080c040513080307030e0c040506030c0d02040f0c0207090b04060b0d0e03070803040f060e16050d05010b0402030103080c060a0c050904021b010509010b090612 91
    0x903000f41d5000000b59540e0801d004001c0d41e4400a004480700c00d49011800190b91805101719012210410007900720006090f082000030000140255404001603918600145042e0000c511a4082d91000201c00ca50070404901c0c0060084056000c1c1d403900c4140040344d5400240c1012040c0121000000d01c1100d101180103865144220100503040461081e03050f038010030b149059800070f505c100503605560013003006899881c80344002d21a0308000070407000d00345030031900c0301c0400b101c11079140c03803a1030b0f8aa0b00154401c8400b0313907145000080d16401c01115025a03114010560300904900385d440010004040301441150311507501071444400b0403000b900004550240140b046440750fa4038188003125034007040400307100303000c7d14001440228891013130b03564008081c0c6d01d050400c0700080c24000254001d80c00750240c90018510485240c03424040c80d441544404008104088103d00344860240060311140c802c400c0c100256400c04c10004003c410b4908407088a0689454141a9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 13680321 1250 13679071 13679077
    0x903071e1415070f060f050114130207080405011b02060406080a0f050708010b0702010c0c031406010803040b0405060708070c17010b01020a080901030917070b040c0819060e070506190e01080906060411 88
    0x1b485090801e4000140b4051071010614983d60644402c107609600442c0e803800c900c51b100d80200b4003d000e010a11103944900340740c843c05d01807010100c591425503000078405070095030146001a51070350401c0401183d900491074050203102c818015420030500180c03c0110500690102e41804900303003066a10951030700c01402d42000d455108143c03282420210019102030580ea103201e80400001d140e40000111811240c7c010080d034201401c01c02000825442450b09984007039042c820140071070102070350800104079800d10090450785d0000180c1c29034a82e605a00d0554002d100142c011804101c03c50b074945a0928001480070382610b4150f00c100c4801c600448804408101d45003007203130440b041405035010300c170560325042d9541001551441c08455000d44405003491136000500181c028440c40c168440c15035241c162030304007189140e04400d5034400d001080310000070501e40c1125540329240300c20329100003980781c8052080c1c1da4200c007400f0a4019513070303081c4429940050b032040e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 13681571 1250 13680321 13680341
    0x20a0209101802030108010b030712020f011101020a0801030507090603110418170903011b022a040f02040e090c0a120606051003020306010201050702030c0d050903071e1415070f06 79
    0x40e02e444850b1114224000350000d002c0e06006600c1c01601602c245000901c8100300c030300512001072001407079804d000c80c1101c0c61b984541885051a4000e10348042030014084240655a42d40361130340c9142000c91401c159a808140c0541c80e004003403010441c0b140d80500300a40030303140481e10b441c095030555031240c01184094401000114800c0c01000d1907001800b005200320001e0000b9000305142211000007840000056404040d06006c1c4199211140740152184110588107014190109050b200c1810f01c0745019a070008050000f1540071541e503401c00910002440d610322142c0214545e412503008081d00341041c2d420010800020350881c3c005400003401d03031004000c0c80b28015000e0741040d541640903509110002c1c03201440002500d0142d0030480c020110106002070554031944900c1c40960540200369000c100d0000e1040b00031f83c054600050480558988006500f100d06440c540601c1007011601c18040322a00c1c030107640395140c029800c020b9204851a0100040100c414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13682821 1250 13681571 13681589
    0x20c03070803040803010303080a0b0901050d02030c041104030b15030316060209061206030c03150606070c050a062607200102090a09051608040804031403070813060306080a0201020a020910 83
    0x4100400c0003c1d4801846c100c03482074660403090340743c079000602512105402150025466001007040e490450300c1e01010b207001a094a0091035283c0120f070944040c0c4070001441500010300b0020000743c4c56134254003000c13040410600941c2000000c1c0c5a10511200040d0351071410011414403145c2c0e41200c2288200903c030756521104007042d01c2404900322074080c0300e1b018508148030309040116500280d0800040c0030070307003903454900304195500082015a20804040b402240e951114100c2c0000740c68a500c03442603800c07201103404034204400307aa034503d645c401c109104045820a80789075000d80d008002d01c1d10340d40003001460090050000c0300d41d001c4040940015501b900e41c0c0903d0007450069140018005441c00c1550001e00944000f4034a110820040010501c0111950140368142094030310748000e03600c1d00e4445400c046000036107546440c030704110194040c815000140041c4010f08500e00007600044c0d16240d8003103000e4000c03844d800028150b80e600800070030161614603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 13684071 1250 13682821 13682827
    0x180102040609051003050702070308030c09061204050705010c080d02390d020c060405060a03090f050c011d0112050a0204050303180a09090c151707021f020a020d03020c030708 77
    0x3010003460b40c0c59074400c3d24028004081c2d01000745100340280751080506400a00070b1a1a5079115072403075000424130503400c5030502c51651541e079070200414006046003018002401c06080c8681003003010340c4078034180724059006100007080d20054621000f40008010384035800c2e001164010032000340f9862103102ca100709440c112043c1040d140d03c1440d4441220b0101d880c103141681d0782c010b080210355001d5000e00007001036161640062034038188034500451401c8443d0354206200808440844075600808480800b03543c0c4518810b1a641d0a064a6604a010100082d12107c0703030015010a007615007002414600950301250300820300942166510860030722401c40c500c1d1014002c51148652503800210b2403550700904104c2c40c0c20008140d4828034027a00504c00721301c400c0c580744c00c1c003004204000b8411213030001240300303040c0f94002d015a42500070750100c68840c21803c10302e000344184100701c00154001108103484800b4240166920f61040025155000d08000240800307000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 13685321 1250 13684071 13684079
    0x3060302100f090b031302040e0709140405010c020307020904152a03060806041205070c0b19081305030d110705010603050d021002090102030f0d140c18010e030606010818010204 78
    0x11500e100c214071000d60780c403204283c907200c807030030075105c02e07070f1100b007420080c140380300c00352610b64010050310280c030041340c4544d6601d0754100162403800e00005c0100c0e00c100100b0007030100078003035007079944554404bc51500a05900103240b0810240c006042c1080c424100b2007081250f034401c8014680240c40c4400002d0940da5410902048440d010002410504c001030349210003d0898019035108888440d01c400e01201295980c0120809903004146036000061030705011300188a4089081038400700100070910141171000c0140480801021030f2540d0b10108801006075421b2841d401404a41200b919105480702c5c0140400a4030325403920a00004221000503511000c002d50740030390700c07040040104d01c4100c1c0514295240540c10410101e41c00c6a001d00c02851001c1400b40700082074602201c5108007203104072801c2c1c804110003d007291035690304e50040d1803906001d1820042000a9601290b00d4002c05001c0310b05010202f40401c122001261501c03100300c08010085403241e5607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 13686571 1250 13685321 13685327
    0x3120307020c01020a0506040f05100203010305010614060a08010b0912011d01050601080106050414010507060c0903020114091e0d05100c0e0109060807080c0408030a030515060313030806010306030210 88
    0x9032080c038054454411440200d500104041e4500350704100a401e642c1e446031641c80003941040390448050160740c02c010004015840914065030050000054141c00d000441318181107025886110704000c0c062180c9140e444280c59040d0f40f409202a61280005404038a00d4504111048015400c100380d89840031200414070544080440007030006131500300054a00220a010342c9000440400082c05900424a1a901c07a8032040c50b00c207107401d0ba80d8840d20203e5500c180c2c50310014008950410541da4824410011401c580038014680b090150000720300195018090741c0b02041480011840c0c2c1d5040603070005c964005007954600304115011100500b40600100f0121369901e50f04581540325100d882c05481454840301c0058551600c1170313035081c000922000d8050070030040452103050501c05000b0003030841e1008960f5003491070400c0d8540d00c2030030500d405844144104458250001d0f0008134441e00b5052107621a11401d00480140425810294210900801e0244001d034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 13687821 1250 13686571 13686577
    0x40204030b0a05010501170a0b03160b1201090b0a120503070c08060417070b0106030b0d02060d02090102071403030307080403030f090f02040f050609061306030c0b0901021204030c180b0312 83
    0x21040410001c1c2d0380c17140010340350495900d03404440c511030f8100040300201194071500c5d002c04010111441600152520848655150000600e080d00850700407007003036030740300c21902404041d14244112080d002c0400c0303800d0007510481602c0022032080800b0b00206008549007281c00401c5220200d03114851907031340302e00507541220b0b0b9010741048003403c1107034041a10603240e800016406240d280000c03c030050031148030707120307032001c00307020700740c00684e00c803070080c03042c0c4441e51005a1a03071002c0b8000b904203010781d8000301c2100849d03404840196408000c80c0c0d801402400d0002d1a600c90741011401418031407900a0068506403410051141d2076401000851013168140030b46120015800d0948605039140c503005210070300130032064940b100040220100c00100011404e641e902c0300b1072001080d0380116522040061428802d507814042c0b80e0221004568592074649180c1d20b1820722502c900c1800311030486411845074244194000003070200c0000c044900301d00240e03c45501c107374 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 13689071 1250 13687821 13687831
    0x5010c03050712021b0304031a0108030306010e040905010b10080106021603020a09051f030305090405070e030a060b060c010f14060604030b0705070809030a0c050918070905060a080604030503070f0302090d03030b03010209040204030b 102
    0x3011000054004bc004100c2c6d03c1781406035646442c00b00001d0a00003c1c101d91081100c55540f94004002d11fa11441000d0030300221503940c12486515081c0d011742841c600710400f01d441801340f02d0a07c0540c40b921000da00f102c0381002e0016813070381c4440204c000740142d0400039800725140c01c0000203145d404000303460801c80c11a070810054403403580503503000701c91054031601500314070103080111b1b0a41d0b00501100038007824007482c0491027212103003100d903c90f8041d01950741d1107820b441040700003a00c3c55841f4105a80c01072400e81952507602c0c00410040180c02005000a00c49003041042c40a50f40d070310401404941d000942d6240c004138003c2d040c00f6080c0586200320024112030926a07281d0f1f20750282402602c1e803182421038060181400a1a42d1b03080142e820000030a40030800c03556104034000d81e00c280c0c80c1e04155030020101024078000380304150051100c41d603180d503100a070200700ca078141000504040401c001c2800f80c000e611030740e944184041000024000340c150101e03c03603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 13690321 1250 13689071 13689113
    0x20a0306050d0320100e06010807060201021c110708040e0a0c050406120b0604030c08060108010507080105011706010c050102030c0702130e1213080a06020705010c03050712021b030403 81
    0x259441d0310a110702c403030842402400080d40740f107481000e8036608001201300200b180c25261803010300682d5005440ca0110807240d9548000d004014048081c810304010b0115407000f54601003c1e0500740080308408016119040d503600c3c00d048488078088200e9113913560081030701c0d40b265079859000080f142c00300d444000403800c0101403a0010310404c12281a01c6940d140c00035a910603440400003418101e01e04c0b500507808120110100f114008680010b243c100014111981010046821345070050612001c6c4014003006000c40e80e0000c1c1e001402c14140c0031161003596030307a80102d500900390080a41594400802c0c410b03458028002030403024001e58031041c60a01e4404020200e905e0401e243d1519005130307445204030344d000d80040c00c02000403001c4000150720f070040d4a0601041c52070844101e50b000904404008080c0030700c601982060070100014540243c0140c225441c004403e2501070780000c0026414411210301c2c078a4807030510031030751260b4491822034079a00d00b05081d0409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 13691571 1250 13690321 13690331
    0x301050915032d0706050406050d020904090503030712020c06010b03061c0309050109050a030503251202070306050105190303080c04030f0c05030106080f030a1206150e0a05010201111206010306030f0501020a03 92
    0x1880d800015a901143c03240e50701c1a01c0c01d403812340304584a81000c83e00030030386074080040f40300603500d07070189519003070248000e0f5559081c104005410504403180b8022032a0051000080813400813a45038115011a40140e03034070f0759000002840210389982561000004403804018144d2050800003502c0003a00d0302d120881c2c03584100840e2803428031008103658000c004c2d9260391421130031106813640700300e4407000d41c2c80010350310a60407070540d890000059003c0b1307004001384025400f485e03004000550b04141c000440303403140000c40600340006000d1206142c0441c0001d4145002c55006540103089210108850b140c445502e405921465109600346600420b80410202e924104200910700451a111842c00c0a440340c0351140d0413140c1555070707400c000541041299200c0350800c00c0d50b0300c0d281c1900f9600c04100010105410950444e80341540c0441c1c038551400496020706032803901100c00f0f035030302001200900440d4000a000015a03881d50040020540203401000450f84040c41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 13692821 1250 13691571 13691653
    0x10b040515090406090309030b150301230a0c0e03150103111f120f02031305010606020d2a02060406051b010908030106030903030605190503070801020a05030105091503 74
    0x1600800c2940c486a020b0203403004a0b0008103554814004288642400f100d5240d0b00c1e2910303400a0000c980d84603e5132100442201207141c00c1c03158143c20307007814a0ba034440c00400d00a10b00d6110009100c50005543c034a045121140a43d460f5048a80001d003100e168910480101c0c01c1c880b000c0c0b004561240b1003d02c1020245020403841c0c00c40b1038000c048000310008a40200c50031100d07003060070350241c0c0e42c00c3d485600d200d140c001144114882c8100304544102450300c00d084032807541c0240300715080040c0128001d070b0302c8108203009141071801d0a240c041200c0c1c0000401040c414002c1d070001c0005000965140c100d005000040c00041104c084c62800080d65402d9900a06004000311004c00c010f03c411400783d8401c61044d4000d00c0e0001e20310b44c498000c12035808180b44080740c1b100e80c1040c20441483c04200d22070103052403100070350070920705100151950106016080c0f044d8000b0000805026028401c0700501030000c04841c0301c404640c41d84504110007858040354030582c0c25981c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 13694071 1250 13692821 13692841
    0x22106011403030f0d020903010213060e0a030503030601140904090b04200d02010f0302070f08030610140406031d030f03041703090607030506151306020c0328080912010b0405 77
    0x140e5400058090340c50000300a01c0a031042e4017150b402450700d5420300003024103072001d10180c4000706014000c101800d040c514040c000d040d820b01300314890203c5c0c00f0203000092000c402d0b00c0d0880700030300340762941c5020714081e400507005104505030440e181c42154014005460805030203a809650000c004506200200c442e0b4040e0040c184d0300f01151800d81001944a01c40c103005244079450014200366803a80d95540c03210240700140d40d40c2d03d01009014591405041210099a0505101d01e00c480c0110305c50103d8000d0b40700d01e806055880f200d004000a130400d1151800c4e100384180c954401102c3e2140d283c1e03410550302902e01401c00e030501c0b4610b0303101c541140d020b900d0b144020149680d6402044003c1c21008003255040301f004d8081c0013680ac802000340100344c003841d403042166420403900074980000341e15080e06c01c0d40488030031240032203001800c50444204000300018103100c1e042883c0076124400240390046040040d60503000019446032079400c03412035041c80f5075124440b0301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 13695321 1250 13694071 13694099
    0x5011401090608070507111003060306050a020c06061212040e010603150501081906080304030809032404080703020115080a200f0d0c090203180105070c0f08030603010902210601 78
    0x1c0e82c0841c00e403002040303246008101030181c140c41604040c00a60041d0041007030104c41e00da400001c6030300d07100144200f200f240285984134140003411411300c6000c881d541d0703076440c01400c1240543c41000c040484250144540b00b12403180584065542ea0380307006c2c07504602e00900c00e0b100040d19103910703801c1c02c00b00a1120422520140e4844140b6100c591188420304541ea09089030640d6900000070717050f805101400003180185085038440340c001042c5801c244103c0c0701c200c003450000010a00c0804082001a08030742c00000154540d21385140c20307401800c4110409a603a000e2600c000b580400001d1080c42c503038801c0c1602480707200582004694070001d00f10a0741d000032410440a041d041c04e01c0540c1c0d109005002100b02542d4072810041241d10541c1c0343c5039580112a10780306520000d0080d1b6421046a1a0200107030400c0d40703480401b0380c4035440003458840d000021903180e0340c0c2500521076441c2c000301000d40e40002445903280500207011452010b0040200005403211200c00c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 13696571 1250 13695321 13695329
    0x80f010203010e0109020306010c050d020c0103061505041a0405031c031a011409011b0b011d06130f1401080102030702010c05090315040503070605090a020f0603040c0608070903060207060501140109 87
    0x100f21590030321403a40003a400c002c02141c100700410b2901c02c040b410800c043c0603100b201d42c014083d102080b500040c29120250094008041c00b010700303090341075010040b14101d80745604050344480c002c0c1c02105440c0301d940d1141e5030500c21105140c02c0354441001c0c0b07001c406c0007601c2c104030145400801e005040215a481800310301034983c420f007a5506e182c000c104101e0145000c890211054041e40b1207c0c0d41c00300140e80c0003c4d00401400380c1180c41c001056044071070b500e1030742d09240250000d4a642c0d00940e5010140d81c650b04110400d004036008800321403505025030042d582c50ba480716000790001c50b0428010342c00c2030107108020f07000701d0840b0000c0b08040c01500800075801c45c101a5031102510881362848108041d034080b0348244100c501420701c0d0005810000900d004000e560005887c1c41c3d4440c01c0c0800c14800014140120203084800ca401c0c007139083d9881941c191500b2034140d0002e80214000034400701008066801130b410381c3c8204003602c03007440004c00115842072840c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 13697821 1250 13696571 13696589
    0x109120b0a1d15071103040e07110601080a080d020706020c0f01150f05060a0207080f0c040c080705180307080a0515090a0201050711041d03030a0c0e0a0302090405010207080a09080f01020301 84
    0x10b1080304100c40103500030101d0030179050521912120901c0c1d07078841d40c480d00060307008a06102c4050b61100c17609520244040081c40954188540d0704d8561006000040c14108009003040024810390117a0ba10f642c1c00030411501e0304210a130154450014815218440d403801d0b100380102004c809a00007500c0580c0b0303188504601b8101802802d0f0300002840c000e601c20101c0c0001d821408200c0c425000d1702c4e66000d003101e012400d0601065a07030185022040c0b00340c080400044039485019601c0204a051401c45840c1c4101c010908040c00394003d48001d001340c2c0e01a20034400001076000064080c2c02e00a0716030365581320f00944400070218000d0015204211910210700c1040030394a50b20b9008100007903450001c6851042c120000d4101c040c541c0020081010300811845899602d078124104612007440700000500403100c1400002d1290340716101003010711000354162814a94805078203a901c82d0040e10203025150715218010051103001801d4038601010300a4071304882e8140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 13699071 1250 13697821 13697833
    0xf0301050c0403060506060c010608070f0b0412020402070c031e02030f0304080c13111611040e030d020d020409050a0207020a080109050a0b090a050105010308040515070f02040b0109120b0a1d 84
    0x181c1c130754002d488080e11072540410b0500000f18026420712995000708104c4008180003454031b006480c10291640c8080c900382000d000400c405600607a014218aa0450b030040c1d4491203458458640c0d02c0d580c00103489580b810369000c402c6121503184900c92802101180c03040c1761450280b942d0317031040c1d00600b003541e041551080064240144200d9008090080100e0203000010340c1c120340b5000380341c404601d21100c000b1802070012138000c10f900d180d0700b07403010300001d0010703001e06942e03124003c07883d0b00040e0700160500710554554180c0b00135104294081c0946c0c20021902000382d00681d00076441940c03803440c001507265051051000d441d17030000c058030500409854a001680c4000c0c42d0403a24007511880310001103003841114040d500c20004a82c4036400c01080c05004010182e0000c1c512004002d400d01040d940303140c0b540c2032a41107c01246a096010040715a0500e5512070441da502d4400e040c0c0401c000308070303001c2c41460175500801043d03024032010035054800c4104048160481 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 13700321 1250 13699071 13699073
    0xc0609070f0e01140f0a0806040b0a060e04020f01050a0306050a090204050103050c040e221e030206090a0302031909050a0e060906040b1008040201031503050622031409031005070e0f0301050c0403 86
    0x5c00340030303d40040300410302c00750203640381012814080215011220080c900080025005a43c4907070380c041d01684400c001c0514195000c50580703034001c440903051107404902d1108a80c441e030001c4001d1300d406844032081c282e50304d03103a001070340103400307003d000c40c0c10704002600b44035800d010b036001c442038081041c6250f22501c80585205401030358bc2102e40c0341d03240e09140030556484003580c94401a041010001c0720904009060140203045194175401400d80341011035800000e842c206221010300c081040d60421050340c0200c103507400190840d6020600041094542d0000b600c29242074810750a9950703203d08020882d10b41480d09503001c100c00b010310b020303030f84100c280940c000e00c10f040000d040c0d0120304400da107900d81c07a8411a103991224007040092000d002d00b2044c0c01070783d84c50140440045540251a0300803604541300c1c80d078004a000c0000383c0e001c012007003482c4100c0108010608005030014008202500c200d4000c40300020f4928035410140f154a10814070046164101815 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 13701571 1250 13700321 13700329
    0xe1e07081b0a06050c0106030204020a11100c02030901120b090c130906050a030f0204060308040b21040308240d0804080c010e0102060a0906020d02030109140a0203040203060c09060c0609070f0e0114 87
    0x3000f08174030304540d607500001c130041e22148010011044540c590141011000c0c080343e103021412001035081c64200362151440940000a9035000c2e40b090800796034050420107000010014420000e80c41410349082c8003100028000400d4000d41902c018170b403040d217482c443c0069a0f034a2240a42042c000709040000c900341e0a10046075030310060000c1500d65907501d580c4000d400c20340002042600014070b0851820380d03041154800c03c280c0c02a03485620301030300c000d000c206009000305641e1031012100600c20410000e0b241104038001c0144900c20078034140341000c1c0d0024014102d452081a409031410f6000303040a08019005034003e2806035519040c00005e800031070821104c8940070b20502c0003407440340c000b40d406480b4800c4005105000101d201464400190040150510420620000d6180440c8007940818515010fa41d01d0410801080a41c8598654005240981000d0207100000880c00340d084400c40080440e42da5110900c40607410001c1c86803a005580c22800c43e483c0d410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 13702821 1250 13701571 13701577
    0x203060105010f180306020408010b030c0a03060506010507120e120a05060c0a0207030f080a0305070c0c1a070602030f15061c05060103060b0703030920030d030e1e07081b0a0605 78
    0x3091600c80c138007400c1c40c0d2081c001041c1e542c004640311500450706010b982001d2041c06100c4a04074024040d000059001c1f40b44a18940030182950b03446a000a903140d024004a0b41d80c60351050134a03c5003800b01034000c1800000c030000500c6401c4103c40038050450016200d41c6403a0844040d040e66120300801c1c00c62a40021907002c158050a0f00000c041962070b2440180b107405a42c0d21591400c00c1c030002070846000510101c240200510010081400032022000391103030000070a00222031505910514042c001c8024031050000003000140c5e082d12401c00c0c01281c0706882c03485044c011004009850007482100700700002417143d4050035041903040250084418140041c2d842c1d1650003020380e59000e03160030340109494004000c10404a110700d50b000344189041c4d0b003560040e400c00a9110405440903808140e1a0381c007c8560200c144660343c808000d0244826a00030004075082c1c48000742e05c02c0c1c200788d014240c0d800e0800940303c2d1041d4107840c001030401003580e00b41441661150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 13704071 1250 13702821 13702847
    0xc080a09110a080601031203020304030f0c060f020309030a03050105040b060a0806130504080a08060102010b010903030e0103111b100b01020705060c01060f06120b031209010c11090f04031704020306010501 90
    0x81403a50581c0454440205100140480314050031456045060100100045030341040c10513104100708070109500c0102c0c04020380451034803001c015854104600600000d2601075512440081072001403000040244244911924180420781e40c0b141004115240e1450603a000042004150840303442442a1303607000000a03c00181c645807400b5000484d4421034049940d1440042e0729100150040c2c021507001409100901c4511200130001f007101a02d40f00090a0007401943c49489a01075007103079800e507a4a03000d0907115650507a91441813843c02c1d624294a00444013032641404040c001c80e1400360044c4c0050100c00d24140510085601049401c0025540c0314804107a1800e4081d001004050681da151000c81d0000500c000700c07107001100328466401201084c004140103801d44102007001d0a00940380821410078202212182c050740f50b00c40910700800c107a11945810041c0210701030f503a041c0d0b030300e180400364204000c400d4030042c1d4103900c0600100710039886140410842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 13705321 1250 13704071 13704083
    0xa0b01120e01020702030616020307080f070f03050d1103010b0301050d0f0c06020c0f010804030801050402030601110a0605040c08030403051c0905030d020604020910060813020301021213060507030c080a09 90
    0x1500c02002208444822019984503500000c40d442076240c00c102036900000c1120414808038502c00700a5aa84030300034004219000124555003100e500100f07644030705812020444034038101d031070001e040b54400701c2481c41d464544107440c014640d0f6a8103031b0b41a07828040842d0301e5642000208200c040030400f0403540c0d0205000c0e00d00000d4420304a100c024800ca400030f103406199403040081c1007503019026410071461390100404280e100402d1811a0030940d0010ba5a031641001250301d074030b80321200300c0148501c0c0c280c0d601b00f003211f900c10b9100f20b00079681c0c41219910780c640366441e4411480007401c02c1d0700840c400c0c1c00b000d20040001c20400414180000100e82d1070010a050440c0d0442110160300000d08100650800f0852682e00c03506a8160042c468248031000d011100007070071100215402900100864609504459100840041c40c1c0c1d03551400702c1c44030b82e030710b140d800e030481d4403605081c003088440340640601491403505803900b10303060f0b941c1c0110340e000300911641a03900c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 13706571 1250 13705321 13705337
    0x7110a1a0402041d03070b070c0201020c0108060f060a02060a06051504031704090c03050906060103020a020d1116080715030203010b070605040507150c031107060503010e1801021303030f02070b030a0b01 89
    0x2602c0c0444c951074020b044481e0145884202a04250000c541d005022030103000e81350404600503a4042120107900909082400701901c0d0035000c20719192088a851b500006d001404034503054002659501c100d5850300248400c9490b28240004410f809400001c0c0b29020300051002440c0c0140a4000c200c40c10001c41c109a0703285000e100761a501243c200c0483da6682c00e002581c003050000c40d501c4075083c00d040d441c003421080d0003561140c01000c03400811042040c02c0a490b50140041148083c0032007050710705c0c03500c1e8241144c50704518441d80c03504100f190350101e0840e0090003524100c5094582280c1007c4458658070041d1030014421a40b0380201d18003c544221000030900c04107905035942c0c02680d640745400780417030909940f07006507584003c8007049120b074800116415200d54407010420340c4c6441c64901141c19601c102086154008600e10440c9075094140d80301f140d02a540d10f001d204950101a61103030300c3c90003203a55902e82000003502e0a10203070040c40840006141c0800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 13707821 1250 13706571 13706591
    0x3031b090d0605040209060a030c05060c0f0601150908060114010f0c05061005011d0603010303030b0607060504050c09010608091c0c08030109091a0f0402010c0c03050307060507110a1a040204 84
    0x40c0d1411254080b20020b0352207040c00103608003405480d0b4040e5003a10b040300032a05540300e0340004403203485100d22802001454101140c02803040c4046900da204c12503400b540c45151100800700c20246440005068000015a451001690b14121a0300144110030a101e910046074044070713684292040c80410604000001c00c2002075604c102c2900d03e0700000341c2c0c101800180245004c8429911510021706030078503e90f510800c0300c1c1165410f003000a20028042c02003a00350151600c0544a2884c00080000f03104011461441c242c002700d55210446e038071200295900f1100780c4a17030842c1da102045401400c241c0d05001d030100b508c0d604061b01a40703041c1da2402d099030b100741c00c44240143c5400781c5c03070100303d0003030803120181000c1d502c4000c0301d180006905030805d00040011303040040b01800041884807205040c0051034101c0180d81d07403503d442c01d00e000588030644171040010a1034620031858074001c210109500c0e40300321111130f1050b400000750984000a072060f6400b50b070b1402210b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 13709071 1250 13707821 13707829
    0x130809101e0806090105010903020906090a150303020106091112060d020402040902041e0603020403030206070e1801030b09070e06130207140d0906110309011403130803070e0a0b04050303031b09 85
    0x101c803511580d96103080500d03102c3d06000e84000180e01c0345040c08448441800181c1e80c03c00703020b81c40391055a80c502c042e620340313910704060301e030700c2c0c0084014801060001c0145641034010000740c1d00c8003002403200e04610361030b00d2000c2c8186800a5610400702010428503e0407a21b46507409000400160816848031250350803640950b20816283c4d0444002079500056030f51800000e1405007411401c2c01e103146c034060b485580041c00c400c00c0000d402083c14440d50703540c0e2100001002e60540760001c1d038503890f1a09420105072100c1c0c241c0d01c42c0307600000d04803c030700c40c0c09845080040c24158140c014411490069000060100d5107201c581804104206040000640e000c409503201c1c4101860124058002001d074040344000e50010031a4114a90701b0502021120514035580741d62680c4569403081b800780226001000d41a000090004142e400320120a030f00c00e04803502d4441c2076031144901032a202d28800e66403d6003050001130410511a0300740e192844503403c00030300d801a800001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 13710321 1250 13709071 13709117
    0x4020d080d0903020c03030f040605030408040806130605180705040209010e0301090f14010b010503040f020d12030f0b0108090c0603130b24030d1d040f02130302030613080910 77
    0xe140c0745550351850006055042040100640090300074600d0406101c2c0c640121344213a015850601074000b02250402101c00c045a0060943c0020344500c1e04000c441d1214001a0600a0b40d0351800c0c40080b40d560740c400d5003c0c061a00c0b14200804c000c62070001808042d4102690060601506100107085501e0030301641500314402d84548000c01c03494501043d100b0042210144240e00d03000a007031550b43c1000440303030020b800c032603900a40c051070b1001450038031000f44020140b03400c0704602444076170075401110408468880600c540c0b080c0000459440d281103548116650003044696481c1c1003010046801050305c40d0010660b081c5a10b4810380883d050f070305032020101e807841322244401e0b0b09664a00c01c08045001d0003440708401c0c0e0061020032100c003d803c00c1c0d00d40a8003506203558507803014000c0701c01c80005544030320f580031004100407024401603000c1e005980c009581c540070392a151021701e91244900f8200300c510014050100303500c809a03014481584004000c0408807000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 13711571 1250 13710321 13710337
    0x15080a0b04030206101a0304080409020c010b0114070203030921030f072d02210a050703020406050303030c040b070317090319020f030a0e0301111306030b010c020d080304020d08 78
    0x125000608040c5402843c00c0c0b1300511103030038609001420700060ba8810b007564010b606003200b95850380c0359801c1000b84e510503075004e201c0d541d100090300302240b401900b140e0070000c0c09884906075280c0540302c220440c411818029415001000320b000310f0300d020920300d0203600703680070002c0054096440ba42c1c519400b1b080b88855008d00802c84100b0004403024524000c1908402e0b04031802481c01403200e81201c10100030b1044942e461440302031780400da00780c00d03010442c0007118803045060504030780740c20340f034002030380928102540412581000021a402003001681462500d071a100d241c0d012070300100e20413410010300300c95a50080450240280c020110903028559070108140f0091500803002c8808041d0340194000301d05556011007518a0440c03a401c007441000c10000020b40109070300da801c02c840600105507406000d0000c00880c00780c0c0c0d0651000c2024900c4c0c1c500644143e64400e0009600541842d44d600000b56010060343d0090310103440b09039002a290388a410310782041c24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 13712821 1250 13711571 13711583
    0x4031202060a05010f0303080105041e0c09060210052203020a020405010303030203091501140f0f0a0e010e090a020d0305090409020a0801050712020c031905040e010905100b12070315080a 82
    0x2e000c2200c0b8188200b90050981c180404030440c40e6039400b0300404414801d562150741c0c0c802500746890008081ca00b60302c00341803400c200303085040d00d01500702039131405980014840d18000364100c900d5440f0702400361414115a80520340d820340218aa4081e03031500718214040c440d444e20068a07180541c5010310321a40f0b01581320701e0400f8003075140c0502119900c00b1041081c004015900c103440d1244003813007050b1405225000e449001c01d501c49200c0311406d41043c0c400600159540710b042c1c4c0c03e030603a0f010498a021903103480181d148d807840f8984000c0e601040811150001900490040001900180002c2204421a000207841d154242d0083c4501c1e5103840410101561011040c0c80b01090342c1011800c1450307000782907560b03005040c0358080c0c1010b150707400a0410301940c1078030001d043d031000f003441c2d0f581c651300e09602600c820348030384c50a03400010003c070716071000809030350b91103d151180c1400c07076580800440207802c0c3c1d40d646001500b9504000b080a88051100d0507000340680 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 13714071 1250 13712821 13712833
    0x71502070302040b01030209100e04060305070311040b031605060d0f0905070603050130030c0b07020106030c0b03012d09020d02041505040b0a080403050d06060c11090c09040e0304031202 82
    0x8010f01007501c00e8484640e04251041201410650ba042c00f40c55201000d03140030a855541d0b0030109005218580028015201c3c5900000400035400700d00d441a03207080c1c4040c01111110014107507075501d030184021941040f5030092106041150240484640032030300805c0c4c151800440204650a120301aa51500100d0051203090b41600070540100f080480402c241e900302131401c403416030442481290250801900c03000d15201c0c0d090601645d800c0b0385000b15034201800f02900824051204a95940c060140010800100019a070488071050030003030b014181d00350b1a048003500f0900349196003c0403e03003c04d009800d40f01511402e10741c28401a03441e800c0c0024003817050720300511003042000030082408a00c03c5003043c0c030041c1040c2e051540090b01c0320315017a031f0309029420700305200c1882e0100000d60254031a16030742d900303030040450004014490b03007400f400900c00c0324022481c0c00200141c0c2c015041580c001d1001d80e408801303803030800e0703100d944500025845031107040060b8011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 13715321 1250 13714071 13714073
    0x5090907020604032003160501060e07090f0605030402092a13060e0405010305070302010c06020403290601020a020603150105041502030310081f050c070c03061b030510030b090715020703 82
    0x3090500c1c0c0400007410301003040c0c00d034031117295640f0502411001111203075664101b0000c00f500400b001c0c00358072100b1038072460300c0b95000341101090700c1484e03500c0400c1400000c0b040c0c00380080307034040e540141c41500955076070b14194500380c0f003001441144002007000c0f9146840d034800a08520410001180d40003407500074001c01c0c055401c02074501c25813900004000282001450504032a0b083c242851120103504059000340034503400500002102c1001080140b1110020f000401c0b00c0305003075207252101001280c3d90b1906503002900041c0400210384101a010010301c00e2910515020b4a45078640500000c40b403040c160741d0000d68404020304c6040d24036942500040e0803e41c00508003038108044588031401489c040001c2c10756104045108090304400300c88501e83c00c11071320502a90f0300c0c9040001051110000d8191181d02126060040c0c03081c003074540250381e4503040b100c2c240d055403601030600e1030203420402c0620604100084014105089000307081c810340150201c0c80c61 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 13716571 1250 13715321 13715327
    0x904050a020a02010c03050c030a0e1e0a030306080307020a03110301021605030c070e07090603020f0f0a02160b04030206030a0c0c02030f0606010f0f020d0e01030e010f0209041406060304060203070509090702060403 94
    0x194141d40e418941410200030000148d0070235030b41e0040251100bc1102440114a10b091807032280c030001e15a205c004007200321850015001800c0340c40395400b0000580e50300e00c040d80320302509030000d6002040000400c08544104400304c00158014001031400314100149a5942c0101c20704407520740003c900403003021028000c010007043c08100e00038040c0b818210042501916000341d0050580c00b04444e80f184810105540c204801c0440322aa540c07138080c0007a40da800014098208200250004254817002e50240c80c12250701600807410f6807141038100000c1c3c010100c84504122801c00c841c40540e8040250428400da200c0190051b81444000144072500500081c0d040c42044801c8120032a4009071140302c04c00c0601d081c0500c0c200c00c000480c094800341030100001c1d8201841e4001100c4180c0c01400ca8010880d002c10030f00c0c0000d214201030f28821142c099000005000040200d01d503a00110750100303a078940245072000303100c0050940c48040e0345030001680480104000c240d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 13717821 1250 13716571 13716581
    0xa051c170405060a050a09030804081005070e030307020618091008100b010f031508030c07050108060a030507060c0f05030406050403050c09010e1306090c0602010209030706050406090303030b060904050a020a0201 93
    0x600904041d00e402c0c14000801e0661213001d00403020007000058200d00c0c81e1044011101542d03009a0031555544c1d0340382450751703410301000031f2401503103003002094219000e02c00c0300080f003101501450408996800b000307034136000900541555a03044020502550300c0c1091140308506046d4031009a50514504034900345000c00d00f1b280307903403404ac0500c0543e130f00850000300d034405616001c2961601c040b0015030000080d0301003205803001140c0004c1c0001c000c203c070070951b0800c1e603c8606a545040400c4154640b5100c0680319421503601445154495043d10803520f02400b0000c1c2a2980b0707583c0c0b0703031541e8456480303100040e02c04a01481001030620a0ba03c41c40022540c0810301e50405020640c121009407070030381031400304c208981c00c100140d00312001d6250400381f544030695587c200a8042d6000011192290140f4240410a58018000d9030192400d658400024905590301500240b0110410941c885c40500852001e0f40d00d60040c1e6102c1c4083c006d02580343d00540c10041e09440b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 13719071 1250 13717821 13717853
    0x30303011215090201050414040e010507021c08040c090e0304030512040303030605010e030c01080910060e040c060f0806060901050405040e07030b16021903030b15030405070b0c0a020f0a051c 84
    0xa41030071540405031ba03026040e02c00361011a11489155200302c40001c00900f20501d000c4225400d10f810001d0041d008513400c1e00c074520300d80c188241880ca001e0b0449200404071001804613170b818100f48100e5006610140c001a00c04044070300d0907442c0d4550524046047c40a405a20800501403003051703858000c1d10001d080a08041e10300078900c400007910344007001c2d407507810440d00c5000903041081c2000f195240d50802402048040d4540415400807541240d068889100c40c143c00a1510711481c00c800107040d051b660000d413600d860042000300d50004010604101c0c003407202141c3e03542c8034807885001007021802411007600d5072801038030280e0010205095429524101440070f900030038070100c501e008070703d2501804110b02c0e00740c000304482d03030b800d6400c000290301480e100c1044c040198011380c0107500311881e42d03650300cae5501083c4c03084c2d0300b042516802090040006080c00c45c0040a6080c1c0286691002500c030320225007001c0825021000000b01c0116032814000c0d041e6218041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13720321 1250 13719071 13719113
    0x30c0906050a060c02040c1215050f01210b13050f07110304080304030305130305030301030807030216050a050909010603200a090203010510050c0307060203010b030f091c0c0c050303030112 83
    0x4a0b00c3c009014001d4410b11502078001c07510341f0040c814031445590100101081d000040101c60b49614000c000d0584501800303020b01c0030500340350203079805842000360311440f0b505e54203c20041034609401502c0c0f220403058000f1401140140300e1070450042603c83c1a04441060781440c2c1a08010303c00c2d6111046209603400c10070003444000404001c582c140d036050b04100d6614001001e0100c604403407940050010700011001008100c5102c008210b00d5000e0b5007291510a904c040116180303201d0700c55680d101501440400403810514011940136000900004055540340c84994100800b0844205148600700c40050246806109007010f806c581c4404c5081d0f41c100008241040001000001403180106400354100e20800440d5111a4468030540d187d580d121039189d40ea40051768080480d80c2d40a0014028020000316918000f0003203840800002d500b00058919020858090718600c201d9800072030152002c00c0218001c04103a01503004620807402c0c840398600302c1202e41c20003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13721571 1250 13720321 13720339
    0x16030b010806030d050f09030102040602010902130203010806070c03030b0d0302010b031203090709090f060207320c04050703060801090b060301050108070f180209030a0b01170a0201080408070c030804030c090605 93
    0x55034400140b41c644d40140c506000740d80f020114482d90700381c003a006040354190300000300410750a40c19088448600e100307640c204640070311108404240d00007402891900d9010030005542c041c4a0b60403051401d0080c100040c2a284010201d25894036241c07084e400350b03440785000c9010742001c2140185128400f2620340c1075040c41d540c4903840b40480e12400f0314498440c040101800008c11441004070381c005011540e41c10145405a03200448070071080000150b54094404407898048691021421030301070107042c0155400c00c0002c2c0790240041c400c05903039500100740080b0900c10384d07900900a00c446200ea1034106c04160950b00141c002410350b4200d207004010050511078100c0130380d250501316000383d807003010301347e0004d020343c0c6101c41d41437090121a2041c409441c8a07541607890004241200a80c01c0310b030b00d56a011603040081c005920140042c02090100c000341c500d1510850070700322100e035203031503050030390300b0542050300e02c1100d13901c1c20031150041e4442c60006000954600b50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13722821 1250 13721571 13721581
    0x13020a05070210090803030f0603060601090315051504021305130b010215070309061113050604061407140303010308180d031e12050709060216050913050a060516030b0108 75
    0x86009204009003ea0940e20b001034059000d61401000342c08030300308490300ca1402c000d038000d1a40064a4543c081c0c0149400710700d440d4410800d076016aa000000701d4607040381040343c80010603005040c91002201d4100c0d8045590b1180028551071910900300c0003541e0130003082012000443c680394024038070707005590045980118189254400000700803490b60b0328800294003601106000a1002e450080d0403104c20056001402c0654202d0541181454071502404164840c0340180004964100c044210b507000e10001058030b1449201d040c0f00d607031500403000345140c10a0700121007148000c20b01a5862419004146400c041199240c0d01c0315015103011b040a000002251f20403035440b030748402501e024001806803940d03a510108180d00c0c142400415411040c0552001401040381c40714500700000c10390016100e00074030426079503c52242c1d04190280076030040320315008180110011490500c10540b10303507407003050b114868024400040444da002c8081a0510018000b840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13724071 1250 13722821 13722827
    0xc070b0103021003020903010207061b02010504081819030f14030a120504260c0d031103010b090a0801021809010501030e0c120a080408030d050c0c0c0d0213020d050613020a 76
    0x9030440741c06840c400840204141c044001c0c1c8102c0e0b24841d0590300024918040010301c1d80141ea100e8139803000b00124500c9030720f0803800e940e02520003400c00c00050202c1404460940482140c0d10710040c1940005d810345503403030700b4032107159100340d80360604008801c0038011000911b0381c80c1e04031200914608020008003411000c058102042c0e6140e80740001801c000c09100b0010401e03001140c44080d024080700586055840340580080d50301501c1b0046030320901a0041940360050f038003089095a0030009000308640000c08203550041ea4170070700240c0090280700a0a0a0b800700071040345000542050026414060f4400c030304040c40c0100031500c00b84003081d147c159000894640d00000303110861580703010111003024000f00c00c0000c0004080710004010410816401d406004907918001c0d00301c030a0141080e41300e801d03044481040300d2840e104150719440f92008200645038694480190100c0e0000e41802112a5549041c084207141030054200f1211240400350302e03181e8040001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13725321 1250 13724071 13724093
    0xf0b0a0f06030902010e0607060902010e0d050c0d020117090c0307050603070c14010209030717010501060806010206040803091207031808010c05070605061f0203040303080108061314010f0c030b03060c07 89
    0x51040654601000d0f045a214159a0482c83d80040c4003e03162411820018020004060200d010038440b481e0310b100c80c100006d2000203217400002a1400d07044044c2841200140351204074104141000c4034180381800b014524002c138240d40003400c62080c82000c0c1440c1200ca900704074031840c028420041d009034026803900e0803c0c0d21246c13010401d5170380c00c0c03884e019004545405a043c021004081255403542140d1090910350300e000340440d1341c0c0e074141500c65004c150b54190041c0c0001000401142a04008542002039042141d206061072040c04080d90070240741140000c42c0000c078800302c0020590414050b0020500801194140d00d001400c648242c00005222585520010344913035903100b13540c0a007000411028000c120714050003502d80e8010700049011a0256001180c0710800007040740c0705042030280070000148a445011044401b507440514540d2100502103082119002d1300140445079100804c2c0c048d082c03810076060000007021140307054414489000410914000c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13726571 1250 13725321 13725329
    0xa030b0604090201090b0409020d060e0c120910060311180709120201090e01091d06040201120509010b1824030d0503040218010b0a08070e100e030304030c090f0b0a0f 73
    0x40d4800342c1d840180e5100003c3d0340b11a01c9007001140005140801c1d170004c107144102c10a082280d96202e00491810940c280d501d20300120302030009410380003c40707840a030801d07100411545004400c0144138251580b540080ba03222502c10020b0001c2d0402e45400d84032044ad020300e000c0589030183c1c00030240c07034044c0300301b42082203c4d2110a056900481c2550050240e140c2c05050a607158a054001341c0344030b003289000d049101d0040a0f10780000f00da040e0055605239581d0702d03528080b07082c88020700310283c04810f0031755a4000103101940c6910007020501d4002c56901494a00103000a0ac40e940d400343d04103902d076900b11b1100d4542e9020038071440d40c4c542030422540300d485900100701c2600c500941080900c081c10004214400302e03902030482c00c6140c0d691140c441d5030b203090031509000c00f03080b00c0b504209400400e0304014001c80010281c410080e08581c207059407501c030b10f2803101003540440b0845503a607990013188241c0c0d004003c58840107a50111002e40713810114210038100780b00d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13727821 1250 13726571 13726579
    0x110604110108060d05010213050114040308040e060616050c030609070605070b0702070e09010b03060604060b09040905010216080405040506010504080a110d120203182202030901020705030c0a050601050a030b06 92
    0x4000f60b0b583c3c0d2440084101e080c0c00030001c41d2103071001c0c1003091a00c0081c1c042c040c00f1601c065081e190001c030071001c840039a948601c0c058241480c1440f1031501c1100a40b04503400703a410b00005112020620f80c004020b80100c00600e008511103080c0742c1051409022010942c004490a001141d00001111000b584c041002c1020b980d6226080b410400681c005801901b01207040c0400e2030340c150000022900c0480a803030f09503c030f0108200864170705200740d6040010500409106203841d60050030003d0140001610b048003403252907a1194000c00c044441f400003140038070207401c1a12a25500803403e003442454030741099001981c50380c2c5840700402d44804a1011001616564ac20395040c591040c5800c00c8001e041300082d44a802403010310710140300e9424045002e10b80500e4a5044111032010a00028028103030b4202942c0000d006004940d0200000c1d030010b00204001c01c0702c0c2100901910314000c451404506103201030340018403d03d404001803001c919135182007500080c08807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13729071 1250 13727821 13727837
    0x606091306080601060207090608030a080103061d010c031e09050c0907140d021809010f090b010203040509130506010e06090105040b120604030503060f041e021c0504030207061106041101 82
    0x325409000d280c0c0004103140110000000c2039078000a807503080e03030401007007848400c1e12143c5695407402128802c04c00241050010808550154070040964810170304003070825121480036401d4401c1c141d241c2c00001d81d0b0300e54960302080100308805131207200c407406003c00519078950750381e07901801c58001e00c00c1d465200450741d680d01175886119400714045503141c6a450525404e0002d4204480203016417403420340800d42454485403940c183d51840c50858603242c18009000300070080c2d0440320381036100810000c50301d60744028110b48a0424034000700004d61541c5001802c000741a4002c0d0140c81c2d82609116a5030380d50802c0f00d043d2542924002400d01c064000628031a280c565500598020001030009240d44003004522400c07059415036030b11601c20052004644d9521040c02d0700c0c21000c3d03c3c0000003103181c0c005102144c250240391b00051149503411044403800c0e10101c2c00750740b00300d1027004055041690640e203454400040c0003646444d88959250b43c280b07034240ca041007001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13730321 1250 13729071 13729099
    0x201080603031b010f0c080403020607120b04020c030c19170a03060308190305090c03060114120708210c030a03050703180506060f03030406140322081e03060609 71
    0xc00644200c64914a018806026040383c080d00030401c001440381d0050504418505032805682e80358010f43e810707801010070743e070f50f0601100c040390145140c2881f2522604a0501596180080d200300c98a8601459440b4404e8080e585002c40b0103410080455410805402088038041810000c5001401c4107642d2200c101d01200146040c0d0001801c031807000ca034208215a000b82800300005032510100656181d0b410740c00c0e40c500200d0011a8142c0c010350050042028855000000c1076002e80030404000000c61124104559600041007692000f141100d01060365000f01194049114a1500e054100804161280700344907981d07040c95101d00c00305e10b03554486c0c0e000000078200103007100000303413161070003035155141607075a14072524055100021600d80841214121070403600c548141005410b50262181c02c000d14207400c1507010a400035000c00b02d800444200c0c0c0c8a45642ca03610800660341c43c0c1a102c1c803441c4100224801d20801c046c0d92a440112980d12100319205461400c034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13731571 1250 13730321 13730323
    0xb0412020a1a03061008060f0103180503030403020303070e041104060c02030a020604080106030606080303070206010303081510050307081005011413050a030302030318030c0705100c06290301060302030a0201080603 94
    0x6500c0903958511410100104000490156004070720444484404000c110f404540401042e120300d41e0040e23400223040d10a6001e9800746421000041c0d5040c0041103e48070103041d504211429409030300300004100b031181d400424400f000d00110b404101e042001446240c041c0524000c500500500c807a0f03410941d0f40800c41c111885034020300d2039036070301c0d2a10000342c0a01104e10044480c44e050240100d04140d002c420340b881000c0a81c0200a103030310311348046038010006406401c2094141c02c000050380c40d480840342680030f01e519526aa0300302890020b240810080205103035203103480e0284100d0784d101c004944007840c0d012280340c507100380d14841011850643c1c040c2c2c1c0e10501c260300000030903801001444c807407401c41210450564204081a440744624803110005411004050080e4505042d0142c0004c00e540360020140e8500e0351900d00b215428014205110b149002d0030400000003800940d0300f880c250f0003440f01c1c5203147d01007a51641840390003810b0051100001e070b800d4174 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13732821 1250 13731571 13731589
    0x40b01081b040c02010f060f0f06050304020f0607020a030b0a05010303080f040203060f060307090f0f2d020d020c030c010615050a050418090503030703050601080a05041101030b0307080a08090a08070b041202 91
    0x114401b0100074056032262500b2420b2140c1c86802c0524900c0792000038440d01440030350348543c3c0c000d0540101c0603140300070800c150703108003c01c9074448940080440420f2403106010302c40c004100b13000450b54118100076140302e9000705403445003100d40081000507100461400d0300a085201c5903041600c1e0200040d01307001450f001714258600d0514a4410b409042d013200b00c2c604180c5108028003100b0400035840c0c20a44802078400c1900314506100e0121154010000460f01c80c000500745040c8007030789800d5174030000130494669113841040c03060b041c011030001c82c8451a807c5c1070f480c0c003a481130003500c1c5014500c51002c0490700c50301c03525450641c0e42c000f1244554440180c0c2d0b92440e01c0c00001d002000182d0f070440c0000c103404d00080e1a80c0c3c0e14070545000c1c981060760103808030782c00001100038022803415640c15004003100000d107450200140c14105100d0002c0d26200d46900c1c040c00101e0303103603510542c0240e00407001003000307042000803113042d540411340b00c5010f040b603030001c118145d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13734071 1250 13732821 13732841
    0x2a10020a020a030809011b030203010f0909031e0c14010b041b0f08040f020d031713020d0206031b0d090303231f080303070507050c01080708010b0c010e01050c03040b01081b040c0201 80
    0x7c0c041c00b02c3c41a85503140c0e000f103058030801150b555040c1d81360303400751046420b00300e801000705420001e0301000c1c0d00d2306500144114040d03c0d0102c1d88604540d0748074428028660140302c1a91540400303195441c1038083c3c15155401c0089401150302004001803d11907112908428007508a003c01c007400192041d1880141e00900328808124251400525205021041c400c0c5d40d060340c00441c4e004204e030b4198000e860b80060896560303102640812015500c09400f0503c240d5189448460348407540c0c025103480002540300152a8020b414042c01355851210400840300f1187c141000701c54580800e40c0e001007110007400b4180840d42c49030544030403d900030f449903200200401c41c2456000d0002d01c2c10500c61001c1e158942d4401006445000003940c2c5180070407440c500512100b142c200280440505950001c142255224401c41c2180d100b0380301b041e0400000400c200502c41c1555019005007401c80c02411403c1740c1640e100ea0b4070215a03042880303141c59030007206205100350000d083c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13735321 1250 13734071 13734101
    0x2070305010c0807020607020304030317061f05040504060b073201020301121707030909051f03080d18050a020f01110f0a0b070905010c0f02062a10020a020a03080901 73
    0x44501c109002d440075400312013610044c8150f0000501042c03002c401d8404407507240c6c48a07a10040400341e8041640001031515400c2503c0d1500c0814100700c80c244031a02000c180c0300d403545e850030b00c0107110a0381c43c3c0e900082140740c1d08006540004105041c2208100082c8428404841034190428980c40103068801107542c004000420700b540c0090f9042c0d0168850301074201c22105404804005000e82203010703000c40d42008040150314034a0300019404a08884140143c000a1a49084c0c038441a042519100b2002c1080c0c403400c0c5851003140030340e05807043c0701e480d805111f0369003d03598884c84000a02641050039183d0059001d00440d0700c030046000c0903200d4101c1c10019940d960440c106c01072f41c4001814021404450040796118207884044e900d03440c8580e866222804d403c242e84100b02d80000b0b08001c1c6a505d07002e10340e0803400d00f0440208850003500c40005030352174108d20410395002e03a841001484000e60700001c0103003210360f05080644d40e507910700040e5801800b40703045805d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13736571 1250 13735321 13735331
    0xe010c0e09100b030f0609010e0903070b0405070b040308090a17070303030b01030b0a0801020a020c040c0e0f130509060405011112010302010e040f0203090f07080f030f030a0204121a0f06090a09030207030501 91
    0x20b54201c1e00b9451b8402d10342a0354034800d0341e80e15000512000c505580151440e00200000f9000c0f07503020f00801d0340b0038010727800c491000f40e0b90320400031a50b00c954002ea03248000411036682524011200e0001000481414046a043c921100352108201c0c48001c09050b03403a114001c5ca64000d8000d0300010000800c0c0c20a03065030f8201c4903020b5406124100f0040c0a00d003807000c8140f402d849444218640c983e1200c43d084503c1040c840c880c02c02c4955954401d40c010030f004091305c032a0240505c11500d84010340b420382032a1814900355201c0a01007081144240b0110209800203490541103c0d024a402404000c40c08045401400d410240072150b0b030000007009007428001a1000310090309008613007100c1c0c1d4841001e0744032402903c4010194008001800e880b8011501031900301010a50051800b596182502c00c0901c0a00b030444032001c00b81c400b0001d0240101c40c15502c070352240c811001d00d161840020340c2e25040101983e04480e524035844091610800040b0041c43d801002006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13737821 1250 13736571 13736581
    0x130b07060506090a0e0309010509040e06070306030b010806041106070602070210021b09060604050103021b010903021c0806010915030e011a04060b070305030604020304020111030a120e010c0e09100b03 88
    0x101401040381e4103401060780701d000c501030806501c540c50841c03170500c019508120b0514011102580f05000f0075600540b100e6044281a000b4043c0c0c6001e0351842d200000e400303156140032965a00305070b0103500c031030300100c08000114070110003902507582e04903001903543c085d03850100300034000d850010350000044181c00380a5034002401f64480d07240e440f10f01045a00440421064010489000c1c0c0c02400501c4108076650090b0090280200b5042030004100d034031035181400c654100780150300507403224021000403112080d0941a0300d8803840c0482035403401c0340018002c24001d205010588810074140040c043c07007a44001c000e0b150100c0244080c8110328807440440760b80c5000c0504c00c40c54110300048046902d4221071140340c2c15181c80e800d42d40ca83c0300b04030083d00018030680c10720101000f0b41603104c0050000300342c1020700d0b49800d000f00051401c110700300c81412010b050305a2410318000c0d00035802c4840c4d020310180464880d100c981d03c8980b100c5019026a001c0d060000010082c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13739071 1250 13737821 13737833
    0xe1e04060c0305010503011e090201030209030303040602070242190c02030c0f090109020309011409010203090606040c2003090409121b0c0b030907030219090b090403050f130b07 78
    0x60341d41c0090355028030543e43c03588109070803101071381142c2c01c14880f500310700b0380030404075040741025a005040c01402c20344d83c030012a08541c000c0351704440c031039800203580b000c628044600f4100a8008200c42421860002d50500b01003400c840040c40e103000391803868141101c102c1210181e410441003c0b505103540d07140a48050001c0204074440c0c002e600603e0b40750305218080004048000700075003426464103071210000d500183c2021125500c40c2e400e584c0c6041c0385100680075031820300005a41c1c2c5044481e60303050620242c8524071940c1440c0020003041d41c800c0c05401e00b41080003070110f07031000c02e60f280d620354404c1c0340c001b81d00b0908095036581070108090f2720381003150290319a4008101d0702c000030102d500708044000c18060044001780080b10004001d540e01c41d0f804001c440e01d581c1c81e5000120307040c465200c0281c113036034845014409002d41340242210349900766082c840340e00b450b5402070710780d00070052203d2001d24041510600364000c0b1040c50000c040300f103803003907550480c1d007410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13740321 1250 13739071 13739081
    0xf0302010212030c031305030c0303010b04061b02010e010e04090b090d260a0b0607060617010b0a14090702150406020d0605010e0a09020a03150b040501091e0e1e0406 73
    0x26400750289180301c1110324505000c0f20f104520304d010740380c6156900101002021082d000540d0240300a02019203d40800c000a50181c00d56414142e181c13440c0100040000d0603526141c207001111000110060342c12510084142e103013420108440d0072608003160041c00201005812008000c0900400e0040030403160901021941c0f400c109030328000c858030340c2c0640403407515402082880092612207081d8081d418007040285075038502040c60700c0341c00544d0043e40120307117084004008061103101c03d225543c942803090f2854140b9625180303103110031011800305035018000b041e001981152003888886007282419070701c0000303400c1c5402d140000703401421044135100e2400d071003c40e0a46c0244d608001480c1c0040000e55900d040a440320080e400a012800c280340c0c41d91006511502c440c030320703e0b01400407030007619119807424000402d251159070009240b04c458075006020400382500110a8400440f41144540c4481103100078071001d01e0782d03101000c0f0806041c0010046c40d5005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13741571 1250 13740321 13740323
    0x3020709020a2a0b090a0f020609040603060f060f061403010504020c010603050604051f0905031c0e010204080f010c0302030601090e09030d020c0102091203090325050409030f021203040206040e040f020303040f03 93
    0x43c6038180d46041703055983e512080000f40103118802e0700d00f00180781100c004c0650400180020071505e540f9901e0b4015201070b07081e00e02105860320014481021120080801070245161080f03800203600d64448507840180542809075030001007a03041910250071401c029a4020203d801038586805c1490325a680750028040c0f144220840034103968046c045c1e000d485070484040e40c902000c0404003c10005120010804c5507201c0c142000c035140b0a1001e8001842c000b00031b0300ca5244503405e100e0840350f0f4540c4613400d040c030510502041e07981c4442c0c184165406003800410310703280c814a03c1c0c0742d40104903074003c21500000c0c0b1110384040640140c4081407003035400040c600185400580c030f9011349124280c255003d0700c0b00c102c0d20b174600504005003d90302d030b5105c01000e803500089000d9582140f0b0640c080740e021480c04030b90705c3c0d0404c448039041e94110496030560070720741c0c0066958416842510207a40e14240881c090001c00e86518036a80c1d8000c0840b555070340e44e4001c1007511801440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13742821 1250 13741571 13741583
    0x160c05010905031306110d1403090106150903030207080102030c0307051305030304180b01020105010b1918080114090d0c0b061309230c06071b09060e0f0603010903020709020a2a 78
    0x103004400706c400000d81c881d4003241601d03000c5020a0410744502c843d00020401d6000b9900c581000504030301e13a6404c01b661031040d550300f0b0415030440c280130345040c07084d601c0003c2c0c1da1320400410200c003045409407908180c0501e040d65030340c1e100d0907142940c0103054101a50500000400103080781aa01c209520400035560510501003c100168200c030000d114003a00d8900802c0741f0300c1c40111080174444070b5006410038000d0950141900c4241103e10f0304400041d070f40d9819200c00303201025510a5110312150010706410035441c0d401000035209a500400048040022420595610b0140b22007002d141d0b00c108030501c4c10f401c1c61039403521802c1c59002c0c01d03000c00404455016000c030700f201503108090095481c00071582d50708910898143ea21030540c040450740801c182605008110041400c20550640c0307041c030095800030303003402810741846603141c007528000280d00446c40604a50220000507120507030800117441c81c819038640780f10b03100100309540209007030b102c075180c440d0341c0290b03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13744071 1250 13742821 13742837
    0x60108010507110c010206010915120b1e0106020706030519230a140c0a050702030a05060a060b030402010c20060a0309150608060109050406020f031e0a0203160c05010905031306 78
    0x201c0504d4503140e1032084240180c02260040c00080b0301d540003030442182c00c24005070903d98031f1502d030f000250346045c21100c0703400c4502480301d0702004480d0703e584046043d8510700301c0c0d4907040000e5038070201c1c0d1281906040d10b6200140340106400824140700e000f403402032004880740c8110400d200c0720315001101d40820800810f03d28515486160707040d0709149130f40070344c5803100d40c008401c0390071001c001e81c1048001c2010200503201404500d44062050009240ca81819548941a245950000c000c602401c0c810440540e80c490700c54090240c0111492004180003028900014504425107821010005900314511b03032680c8502e200500408006001ca030080c60f030a03040c1c800d41d119440181d401100144442d01027948510b400601c030304401883c04005000106154104440f80c101045101a11816058091010690020714070300214610b142c0481e030b0210400b101c03c01e1008204188a611080090940c061aa010740290403240c50740396107010102005603500503030000440c09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13745321 1250 13744071 13744097
    0x1503040203070f0b0409020c0a05010c0c05011116030e0d08040b0406080109020a050f0c0307061103060909010902031009050703060203010e161106040b04020f0a0308041e05030712020111060108010507 88
    0x71030240c041d0382201c1310036841c080c9002caa0802035080b01040c0e07503950166100800000b01c00f40710301c8085440d90780b10350444291740d0030460b0071682d4615a4030b0146000300094420b0b0841305c54420803ca60500b00020103080e000045078450450340c2004003050000034001c90301d500c00e400135104483d160703540d00b101c50381c840d00110164042c50b103038900030030018020401318061007006018156403410841c2d082c4182512148141c1c0c0041c5910a90740f0400400d000e07860901d48441e580c8015800024440d00304d190b40400da6904803042c0785034080d40d442d07010104000d4103000c42001950040815520313540c4503880c0c00c2007290117070b60f00d028414822a00e5101c150190307425100150481003d041180c1c4c0d03d80320307c042c0c01760040040360300c01035580451301150f844428007030155008290060b1034504125240031803201503440045829010901048071380d80005e205403e803025920070200c1ca281601c0181c46560011a02251a0003000004104040154003151241c0640da480314001100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13746571 1250 13745321 13745339
    0x803060307080127031e030209040509010b01080a020a0309081305090108061608070504030204020706050411010e0d0206090105130608070e010503151005090a06050d060503060f010e090705150304020307 89
    0x1c4d400c107651821421510320780d0309545030031540400b40c001e050900ba4010b1122051301c100d103c0d580a280440c0d40071400d104213080c580b00b09503003c203541000300070480b4240c002030102e99004002048103a000550003214510a40100c000154042413140e141d112420b1034440c1034a56002d000d0168050400001d51f00b00000307541070094412010100004c540c0c2e4a0440b13002e10004c11070350610804100c00001600c542c401040380314080e4500007014206807401030340115070440d01c0360401c04088902d0b1920b690354121820529412904560755080c03810042e80d0900031a0280d944d81083c65400044494001071018401c03001c5903640242002d0394801551a804260381d441940030b006401c4125a0900520200194821b403d01a08010480001070300b00c071301d150840030001c1da0215806458074031600641c80a001e007100503041c5482c10038041c0d00031000503c42c031903800c0c404801160146400f44001005014003030400f00e0521000311a918076a413068030120b000b403140000000f20500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13747821 1250 13746571 13746581
    0x3060a0209060f0304020a030f08070b06190b030604150e040303060506030f18070503030a0e09090f0a02060d060315061502010605010207060c0303020c030c07060f02010204030b010501032708030603070801 90
    0x900184158101848000c140c901c0b900300170801c0360071040e40030340403000c19000b604034071100e482000c1035551000b0a1620b00c0d000140546018040c03440b400b0003461454078124181d0540d01c80e4000c03c1c0d1203543d00000280039084001c0c0350102481001004900510303540200380c42103010703880510010341e40e40c0078404a8401203a030014060a02760100f0003200c00055805d8601c43c0340c00c06c03035601c0c0e612900040c0c2146c0c40385417902c01161000c0b064003000e08045800d59482500c40c0c0280002c0110002d469860700c2c00d0b0400248a4200040e0600600d1110703031000025603001a0700c51200f0344040c8658006002c14062401c80d0100d180d41d50015520500a040c1a80e030103034041c001007481e105041e2250305040c2005c80c149034007401119442002000580505c2820030014940700303240c1030340602014030b100e40900071640108014404607159107101411141c0c2032a00241410a15a0f000030301881d810103141181d4110550000384403002015600514084007901c0c081ca580c3c00959003254 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13749071 1250 13747821 13747837
    0x1308070e04080301030b0601020102071b1509030c090c020304080106081b040504020d0303020f091804021009060203040e2d0f10060c0210030209190305060109020901080a0f02090303070b0603060a02 87
    0x20410001840059406d1080c0c9400c5201030001500340a066681c640c03410401d07420052400c02c24031801c01c20440c00c0685a00081400c2c24424085425078441c4080710304a401178900c960f885401100003e442002240c00030480d08000300b11590306d0f420b17103545900910141c00483c0644102107005c92402d4801c00b80140d60051aa5504210170b0b50150041e4015194227a1341d40b80030321150055403102e94041a00304450210303ea240d103441e2040052440d007540741001084140d04007440702640020850b000c0c0c5114030310f6008540d848000c1d200001000c40901c0c45200c07410b4524019070701a021400340102d0f21101d4a0072242e460368149400c004a41c0310ba040080c41001011015060400004030f940181d450f01620340b20f165808a130b08880c00224a0700245910300d420000e20070240301e0503016080d1450194588403080c0002880302030007825103004070f513a4030015041510607a040307072076100780981030700c1d100e031800e0402c40380745003045481501030b029140014498100328403c0354007132 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13750321 1250 13749071 13749083
    0x6020f060609010501020d03090c1d0a0606030504050303070e060403170d050106020d020307030e0a0803030702060a0e1506060306040e0601090204061b0804060c140a060b010e0a05030c0103020715021308070e04 92
    0x354481c070340840c00342c111840140c500cad140030b4a003c240c400140500e01004800701d201e040c0c03182400840300c0115103e80c0e1100f400c040c944070034040021808401c03130780c1104440c07500361001120036000811601c02c2c1c2c0c0c00101100131501d0780000780c042450103040300c00c14140d000c220036030340c0b804181d842c0c146540f96240160420012540040c4c080c05035100c01140140007040c107591541107580c9194070130380b41320015a01c002c040081000060155000080400f405000140707199880b000b2002000752649100700d602000280703032601c41c0d90240d0b02e04c40704030b4119070007565100d1100000394081d006000000300501c07111b12481c001031a01034045640400001e190524100d030072507210780350304070403601c03280700c81c0d2000890030302044004142401400c000034440404e10024041000c0f00d100c55005c0c84180030200034540e0085440b40304c105080c280036943e8181450044850700213003a801e07c0c1140b0100700600080c544c0c1038400d0684060000701c45c206a02c594010a00345400c803002080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13751571 1250 13750321 13750333
    0x902040b0d020a06051303020a0303030203061003020909040f02030a0c03060e0d020a050c0402160c030606090e01090201080f071101050f01030b0106090b09040c1418090604020c03070206070c0f06020f06060901050102 95
    0x1c0920640040c917041da8160b0880b040b903a203a900180c801c9c6072580c015000070383c001c410f1000340e280280581d40100502d050840c40c02d00c2d40e00c046205280000c0029007100e20f83c29400c8159141132240c00c4415078400004085603882c0d00d400c8008048100340d150340d621070803502480d89400003e40901168000c002000b0b190507140c1044082d52162583c000e0030480c80c80307400e00281e80b19200002840c411070b0003107903c41c02d1400070b03005c8800c8010151601d070b04141d000340150740c0018119812241c0302000c80d03110b0717403042c6040d40ca101024105810341e601c0d1104004003040c0720800e0034143c0e4800c00e81d103501e9176612981296010518041c40726a40020010380b070061501c0c2d84165007129850814a01e42d007907201d031550441d00000641d09420180b81107182c6685440e10b100780e802031040b68114140815130342c0607541c034007650301c000380120400a0b064051040158411000700300c20840410001c0d01c5000094480d0004144403070240324980120f042880c200c0d2085050710010b90007085 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13752821 1250 13751571 13751579
    0x5011403070504090302030c0d05030703110702090604090602130b070605060405090d0c03170c03070e1002071202030316050d020d030b0108040206031e01090b01022103010314031c0902040b0d020a 86
    0x10042003002801c506501c02000702401d5448c09100d820480001c54503015124900008040c05031585014103181d0743c50b0401c08180181da038102419081030040c1d5000500e6960b40c170f01070000b48a4881304128401409500061100380310000707154052066030184050f8544800f44419914155000e401e640c001051400c0b040f481031403400d110314007920300107103070a112404100d80800c09807403840c1014000010090803a4010024010b400404d9a01001e980c020620007901c0f00c01034024040540700c0d800c00c000a41d60100260703a44010410b8001011610307900c2c0c02da940f00825800c413000340c0500c08000342c0d018040e104c0c060030140180c5494403156155401c0003090344c802081031101c0c14250600400001d17000c00340e00c4c0640b120b6400007a9030708201d000686040440403913940303030805907162503034265140001c2e01c0c11039a2140400d12001a5030700038609602803000000d08900600043c10030040c01038115180050003900e0400c40e203000c241c144120301c0f08400c0f02a40200003050104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13754071 1250 13752821 13752829
    0x6030c06050a0212031e10231f03051803040b090405040312050711010e0705030307030c0503070510051503010c0804080a090308030f0103050601051009050105030604020d0203040510050114030705 86
    0x4620b0041c81a106003a8100100310680d401c140c0328004c1d80c228058000c40c080b0444140142c0082940c0c803180107851801c013100d14890380510064100c9444488240120707156040340c3c0180100061400b064880b40701d80081c01810304131200741c1e840349400c02c108020b69010048070262806003203010300c0c001301c04003032001801000c0e0044080044429030300034110ac03280305090180d062580c0c0c0092100380c0c0b501290940f03540e60b011011503001618104681e541c004200c4d120250f0601748113458034018105242507020350320001d0014000c036000751081246540c002d0380319030f9050300308110000107034091500300c81018035960082441040810702144291001d0302c15408545000c6090130b4032691340c05029001a6045800d0b140b4810050003007040034410f15024180542d82c500c007848441000501050507403007081d05010000021400d80d484e42c0c0c04035401c0c038801c408150742d20700349840c0165aa200e841d6250010303c0c03601c1e00204514a01c41d48510007444010010030086042000300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13755321 1250 13754071 13754077
    0x103030503040c030602030403020705030c01090f050d02040212010f060201060b0304020306040b091608010207020901050301052211060307020a020a0801110405040f0605090c0a0906021207060e0703060f02071506030c0605 97
    0x81d200500036070f400200041c064001580f246101e075001e05030180c900310074507103096580c2d98110305011009c18181b0a0000e6224080700700c0f03400b182c030510303100a43d0000c04c0081c422251416203404091001140c80000c00b90078404440b01030380200030a503629041054140000c3c1c41c02541508250702060100d900100e216801080c100140d1302e040e00c245d180326000801580c80410142d4020078542d046d45402c28000c3d00400c4107030001e02c60b40ca0a607030380204222248240d04c9000c0c0c1217054940038480e1280d52401690006003c0c5a0760382000b5401075910540024124451944103101240c48a410b020724501410100710f071604140c109404c10025206551a02510350350b1180c0c0002d551340ca102a29014070160880150780700d401c3c0b24010000c030f0b4560072000a66104204580704140024112403803103400180c00142012285949412b022155202810340d5041401c0202c469503a0b83c0149609846002c6071201c1d8143e0990140550326a444003921540c1e0181040203428003032001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13756571 1250 13755321 13755323
    0xf06090605040f050d020a050418030305090a0203070303052d0d0e0d09060507050102090604030605010302090f0c070206160c0305010203160801050f040b060403150b100509031b03070f17070f030b010303050304 92
    0x11f03940005171210003003021034684e40340106d10714409584070424140c040c0314054214050001074408801c0030b4000ca90740d60304521004003001000251130180a04001c18810104541d41404001d05105000f00c01d040d001214425009441c195290501400c00114013464162503210f66080d5450304400340d50030341243d0400e0722995020080c0d603105580748001000518880c1100003015415801404540c84000b1b00105400b8492000c0c03004212110081d595440d6040f40e41940da01085e4006a030001a003840040c940d400c020801306c100300b4190003540c40354207020b1208140d0f5504c8442200c80000038480c842c5c0001e40902c4070f0440c1d0038035801891490360301602007071804e0b55a5683e6140c0c1100780d90041e0610b035442460b00d00c20700d02946002e404003074034130700345052504010020b5103c40c2a204c82c080c03402c01e409000312164800f407088400038154091010040c42d52240c80310540c80502810800c28000c030140480c401c1d4010300080c060760340155100c10980c0c01e65500b910247c2c0007900c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13757821 1250 13756571 13756579
    0x708070e0118171c1106040204020d0e0f06181504020405040809090c0a092c0405010605040e01090501110a0203041a040308042301050f0f030612070f06090605040f050d02 75
    0x100c0800e41c100c041c2e81c0c400440c0c1c00e0318003c040290144c8408a42d4000b1081c1d01410410f1100040d88841c4000841503000b80e0120b500503510006d00c400d15000704404030100995014245002c04081008900c0b58032580440180800c1c4081c2c003100540c840e0308040c201e50052200700c1c08203000d4241a804260310520039070000d80307849240400215030700c0044910401c1c40c200050402111544140c600300206802d007001440a001e218840b08141401200d54004a48038000102400025004080217140150082100e40903907920a80603206c180410b64566007005800c207406210b00342200c100c0c2c01654055404d217420004a6060349002c1c0d41e941c03032103110902c804404640e00c000188001c010400800009050808840403280c1031010102c0c1401012b20128515100d49001c0310700c114044640255a03640c0c0300c0000c0c461a000d01c0d0400c85034810700d100421034529002988040d01c07096111600c90a540310003c83d203c0c030803401200c0801c11901c03030420050800425100c0c00900c024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13759071 1250 13757821 13757867
    0x1090b0604110a08090a0f050307050f0c06040303030926070605160503040f0c030506070f020609010603120c17040b0912061302040b0f0907120608030c030a18090207050c090708070e01 81
    0x611280300658801f0001c0d078898000240a20400c00e0400080c407404c088003001e000400c41c1200011460b01680c4400f03024551600708440070420080415080c0c038140810700030300a80546511440d075041003004450007880c00d070100700501d400d4405101111190f5407020701e56601c1d9030302c10854410306807080707540521004000c40018002d200c80391061910342d40c1e408083c140700200a1030708201810115069140a5007480820003000f145002ca003d00e040504125489140c0f01482c64005059840301010200d400700740050b50400420801c0c400701d41da803180075640b00900d038031500103603048141d84400340484c000600f8181c216060001d0b00508842c64141c41c00302080b0462011500040060f042d400813900d40b0046100d040b01500b13250000b035050649400f182d17a500d20950740d0402c18000e040d00a41880034034451a20003400c000780c4159201c0c415468010365400d6145081841919014001a0301d64880c034025842520f40c2c1c0da68141e150902c03401503951940041160034654200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13760321 1250 13759071 13759073
    0x41415070f06050f130204020a1103030109020a020c1009091d192904081b030409050103020306131a060616140c10050a05090a0302100201090b0604110a08090a 70
    0x12001610016014101c4060580d4a5152180c12508010122122403d114060189414000b45010440b0f5070503200140e9914075440192031071800e0b0b07400c10046100000c004152181590064282d007a1580c00f2036903000140d00412088245580c2031100141484200704184d1000fa000804000c10740030703c000c0f03150030301440703582800080e99012003081000189007040203c0a40802e020304e05049180c101c00c0030b00d1440c06c252090150000c2d00c2128045200413078524a0350328017a0303160865085942d01c660354031500007d00743c03d100680c803034000c2c440041c01e03510620700c4406915501c41e60b10020082200d011050005c4040c0003a074010800748540c404215004054a0815000b018074490f900982021545024200740b245800350307080c1c4890080064116090302c000c21041d0a10607140c0011401240e41180280c0c000781d032201c401c24100c00ca240d010b51040102c54000c0d0380420396507465006100503610310b89059a04c151042008030a01b5100c1c020b40382d08880c80405032440007803e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13761571 1250 13760321 13760359
    0x3020f190512010608040b0702060601020a0303150b0304050703111e040911132007080301030b070c0f030503060108090f0606060901030204030206040602070501080f01060815120d030c09050105030c0414 89
    0x26000440452144170610050101901d00350f07511403400d10041c4001d181c0000001e4658001c00c0c0b00405054840e120081c110440c41211005400d2425a1a4480c5444e080096450f00540300a5a01e25981d10728007207681440c80e00c000f00f40341c204c001d503107141c1e42d210140700007401c000c0c2e000e4134003525016542905944410500303108400720080440c1c114403144200c1c8406c40203501c05401c1c54802c10100000a11803025241100d4000c0c00ca04210f583d030442c10780310350481000081500c0c01600c070b40b404242d0058042d6018040a80c0c80103106e03500d021032555100442003003140d940d0b105200044d4685032020050011350310600d00941055940d0780400d0107600141c10040240e00003201c01c3c03105507481907074075a20180104d5141e901e545414000350000ca005007000340c80c44901c08134001c7d0b5840f0008549918901201101c142c034040c100c0080050420342011030015481c030400180c80d621807820b0780d0080400950a9207841d1400707044007094180700c50601d4021210720310340004000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13762821 1250 13761571 13761607
    0x10050103030e040621080c030705060901020315010806031b03070315020702031513030509040b060d1b0309030813060b0310020304020411030405030d0518011e0c03020f1905 76
    0x8880d03140c8840140e000d4040000f13032181500b0200921110480c0708580c03100c2c15080d201d425400c4015280d40700041d8000f42e0451251140182082c4601400c3c0f00201c08150300940c4601800c1030b42004508c0090011528010b0550702541d06a07c60074200118541038100c096100c5c0c00101100c0c402c603a295100700a00303032900340c1d50394040c1d808a4910306608040c00140c240390812080c403200340c5040301200a204201c60300180401801007402c81c0c0f41e407200c8e8401c903240100203000a8503030b0342105020003e40150803c124915584c0806035070840d000340500001207a1640b12a103855803900c8808a500038299010b4813b9602c0c2c2202d01e4294070140b00c031b0600c03942401d0015949103007500500c0b040d50101d2900340601d03070702002048003240d80801600e50540502d00d01013080d0700d032242c034200380542900380007a1030b52030720708803007151811491080d441c0074009100703222100d030300b1505400702d00072040e0039411400d042080400000600180240c01071041c00c110b42401e0030201010300500c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13764071 1250 13762821 13762823
    0x9050a030605090f06090d050d060509040605060102010e0c03030405121002030108151e0f06010e040c030914010209010e061605011503050c0306010303121509050403030c1701032310050103 83
    0x550303075414483c441c1814031034088101d14010080840c0e00f0500c0125590b05040b96a0008008001c80d01c00b2203c01240c10410080100500b04c1100b4140703400c110008080940e9070502561070080369101c000380206031884a004010091400c2925000078494a001c151100045038041d0703c030041090103a17031010358040c010000c0204400090b030560b114665034081e1a490f44a64545a005030103500301110a601155501c03541d90551129030060314002c1085140507445402c042500620039030540c03107030740c4103405010f041c401014015085800c038810010390500003440850b0100d000d040404c010302d02203801c1861100c0301403a80d100c003802c545a9030440450a500f9000030000c1c40410800e420b40c2c0c1900710090040ca502d103650140c0791103016000c035120103485840100a11400850f2031004103003405041c0682d1600d403a0040c003d0000c5607042d00402e140c0d8200d1000305620700000f0b81a254014040704107203c150109004981c507400003040c152150b04d592540011260003454025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13765321 1250 13764071 13764083
    0xd0b01050403060c03020c0d020c03030d0e0a050109050f15010803030c0a02030c060103051507020d021c05090301060b030a0612030c0605060406150e03060702010b0901090b0a05030a0f060f1b0f09050a03 89
    0x94883e1108039420702808000e000b044ad8002050107010f42c0c0c01000f10740c1c0d05500000c0000f10b00d012851282e0409815100160565103401f1407001449404641c1a2220314a041690718105800d0400c0144000c28004d801055100740300003000306001000822400599004481c1001c1c00404503928010090f00112510b0300005001c215026070b440303005070030038128006001c6108030180002d50b140b02195603040c040480000d00d4000500841c101c3d9051075010f0020701000f612606c202c1c0b07180c1d1003510b80c4040c843c50154009214413610080114071903140d42c0310054103c030360b182c180241c800600000d034861398449000411310300041101c030b032124140c1c40d04210a10708804242c284000101034078296410b00f05c404100766681118141910700801000413001007d401041940304690445600362040c00b11903014406120001c0d10b801e0704c11031040c0480c903285940041030300c142141004920720410740382c10100d40907600f1458101a14500450059078400004103a03801c0c0380d000b178441d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13766571 1250 13765321 13765327
    0x40602100c20030903060f060d030c08041802030f070212030f0c0f030106020d0f08090c09040c03050706050310090b0a03060b040b04020307030c0318020a270603150e06010b0d0b01050403060c0302 86
    0x10b05d0806004681c1d0200850710b13840068640030740032a4400c010000010208440c0c0f420034405c1042210582e4007074200241030740924401100d05030025401600d15078204443d000001c0c034020b01c0011403030100300c10090200d045449031031003854664ac01800d2555101c0051103681c05500c100800f03980200f50f1a130003480c0ca01c649036000380500c4803491010007042100803c00001510000f20345410070030135548845150b88a042100200005400c018a20301907440c000031712550010103140180c100690220845035141c14600031945c0c5200c0e1141c000034124000c0001c42c1546d440107842e100094008a03a070040c03080010103e030f00458011005c43e94494180c01043e078036104200e0140599800114050066000240703075003402d1007440a5000606142d0011107099401643e0300a2030a03014408291a8901018286d01044d0900d0402c0d1410a0410f41c00c900000d607a03040b503590000c640e1524981c40c440034060f001e442841c6052280c02c0000000049141c800c1e00d03010042d9660040e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13767821 1250 13766571 13766587
    0xc050403020414061c050c09040501050402010f050a020d030507021606120609061415120108030307110309010e0609060705060a0b0301060b071104050403030b030a030c06050601020102040602100c2003 88
    0x111220200c90a00d540c42c088100165600c03034000111002e80340c102e00d489160483e190047c40c01c042005541d0304a510101880100a015005280540d01c00d0300e82c0b4502c100150b10482e00c6014010300301005074071075034847d090b003402903000c40c0d00300703a25106441002c42c46416800900100340d2001c000149000d544400b00c15240c0f03d018007500100d141405035514140140d540d18030f50144151107074086c5140c0485802c092001c54103100e04a0074948030700d6a4608a20340c4a4200b22130301c4000c141242038580c8ca4100200403220001016101c00601d80060030900c0100c0d04203090756608040104500404103804202c001d00c00c440c075800103c1c00c01000000e00d0700b9a5620340c020501e10700d05000e0100010a00794151400303070000d0710005515034407801c0231400760010352038040d0980103001030801030560000b181d103190f50260609000c1d03511903400482c200e201da40318080058028485d032000072070407074010b6182d2418502e46440c0c3c0c4145040a0781c2c182c20601d1101548c0e52001801e13031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13769071 1250 13767821 13767829
    0x9061305070e010e120619020c07030b060102010b0402092101020d020c07080c0402091011070504020d0902090f0c0403060914060c0706060e040305030402040b0a09050705040e13120f0309060c05040302 88
    0x400704036041e02e000d8070705c1e500c0c10410790380c0702009401c807c010720303101d55044800d000c0c680c140c0301c007010300404440026581c0d0030114555401564440c1c0154200111b581c40e0741098001c40c0d2402e00064404e004a07028008040c0c3e5504c0003c4540241d55001c01040115500c240040c007039400988000e00100b5140441c9103142204111165015500511001600769102d003a94400441345051188201041034180c0e800c1c00c440303030011540f161000c100074800403810391084001a1081e9070080a5840d402c20500ea40361f421124041c54510401c405e000040082e00003c02041c030400f40310000b0306031003e50504100b02111800c13403601010602005001c10b500620340180b2035440803001c14103098400a0131071200800283c003c42e21800034145584558611800500300f0700400c01c4642050740340100a40d22a2141c1000500d446012a80c405000003140140980c0902414940e0740b1402e41a6801410084480149503803000024003040060041007280b01055654642c0d0701c1c2144100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13770321 1250 13769071 13769087
    0x19050307090c0206060603041110030609140f06130f140603060c040503030a030222030c050f01080f06010c020a030b0901050a05070f09030b09070504060e06010f0206100509061305070e01 82
    0x90a0282d081c20a041d031000d4010070710b2070b0010310a580d981d83c0d03503a40d03040030001c0d495040801a0020728a030403d8144980c140d110b6070655154110502114031446480c00030034400352a0f2000c40000980400d1280c503290764107a00001040a0100da1400c010410710126400603048000d40c50810041080034079080c4403050340f243d034a01407942002d0418001ca0340d64018403071802e040c5980010b403006561143c8014030102c024500d001e0300100d032603180c002c01502d143c0c86414020700d541880b081c4198092031405101d000301000020301a603603180115001c241d07049027a600040324650100204840076005403140b0850f40004c196400c1221781002140c03801405103080003120070b0351204a070750100844044a402c40b8048225440340081790742020758590025034842e03d0082d0005041020321071160ac01d4800341c03160422001141002d985820048540e4985418401c10610903460180301c0e59800c55000391181c1c6141d030b24140250304442064440c20046a0350b544c0c030058075039004000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13771571 1250 13770321 13770329
    0x2030114010903110f06190c020307050f13020706020c07060c050c040c120504080c010609090c0f211502070f0605150d03050f0f040e07020705090408030601030c0e19050307 76
    0x4800c0b4020716544400404a4071108040d100300042404401c2c1c9960301e01c2036078048545414560203003000204090304020408208900070302601c0400181840c3c0640c201038024000380205000100235000c02d002136028480485425600b8489503985040411900d0041d0410380c0b00c2201104050810b0340c60556070302c43c80791181e1700f014000d00711641e1001440f0f40d181071003c2c010a842d20f0707c1c5401501401900702d0030b840c0b507117010b0000031681c0082e00a401341074003c0700c41c200d4540c1c5910101d8265003450050044217030388110000c0303a0761104544080c1e0f00c2c0c0250140c1503090885468030050340d01003a0240d44504e40c4603150030620402d44903054214120140d41900402444081401c1a06041c005000e000d401314080c24064240301c22038000342e10f4001c10769a02c548401c0c00403010002515010018443ea034030224640c1030410007103010f513800085140c210f94030000110050400e240c01c05080240c17a10500c141c0742c41c1c610040c0050725000322100c9038a41484241340c030709849540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13772821 1250 13771571 13771577
    0xb01061403061c020a1703130e0f040206071403130810090201081f050306070207031a010308160318030804140d0f030c031e05040e130308070807030e010905010203011401 75
    0x705001c80c0c0e07039034a20441d01d03100f83d54141801d1424240001541d1030310b21350001c03c6612081c0305010088502000410160400450600034241c0b07510100c80700020448514050101da0f6000c240035190040203000d5280c1b03c0c0078400c0141101a0905045d900500c08210580c82040401d0050440078040d420104211040c20015404035400081688201070300e06007151004040d1503402c04030b40c1048001500018003100c901d800d1003c0c0c02961041d103407009594010054940064010700b07120545e040b00d070810b000e1414088030301c0001800e04c41240b4120b0a02665003081501000888070041c0190b0042d40d4290320f0310f240c80684c0c0b150800c0c0b24061481100700c0020710380081c664050401c903650305440c10110700307411440c090391419000504000c6500070102a60102a8031400800a40e10015408841c039156041c0ca41d2120010000003400b0959200014220511512410b513200540340b602180c074964400c5907a0031101d80310800c0c4ca05940000c0140f0120206500700e44000740c0a00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13774071 1250 13772821 13772827
    0x80a0206060a24080a0b0406080303040501061a0403080a09050306070909050a020a0912020d08030414070f03020303180604090c03020301032009040305091f030e120c1203090f01090b010614 83
    0x8200c0741240080d10f440780c03d00c41540041002c0b04a40e500c1004524000713002003040fa40c5801caa282d81e0740040b10126110360130600e01003a143c0b40e585094440d03075013502c00300d0300306070842c0d58094994001541c00810081803d00c0058160740c00c000e001d00074080c03511042d6000341040e042c2c005880d0b00071b06000301c01d070040081291403a030102c4071f0002c80e000d900350000d0a1031070707100003811542c00c04801780522034080244420b107d900d03100e615140b0141c0040b030b9840c540e1003444140d0a44a0b10000c3e500d5081072100300032803402c1000100307045d01d0040c0224907003034480b00c0410481d280055040b00180c1d0100040c010803150704151043c004c4041c031800903076442c0f0400917020020043c13006041181c08207455600303071601e81880e4080408111400110204400020b00810103a01d501c1101e11804001000d0700310784030100c40303070a54403002034a8480c0111590340f00070b501c042c01200c0d0b188034140c1141d00002e13080c41142c400c0f074410741c00007405514100d4000c1c054032108403070031a400010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13775321 1250 13774071 13774109
    0x207060203030712090c0812130501141803010908030106030906050a0209030307030c030c0c030b060913030509010f05161a0108010b10030c05090306070203030a0c0207080a03080c07080a0206060a 86
    0x105688020805141a005c0b60b048100e1601c3c031a19002540101400c0c42900306e0070908950030006800b010b5034045050a55559401c01105c8035080c071014101c1d0000100000c0080c0c00107a500039995013400b1f00040b0311111950b030380b0750741c5078003d82c08000041d54500740071042082500400f43c10040c42c072419270030708502400080d01c80c42145030050a105080300c2d080200b41c0580c1204004030b4000b40710b041620340c2d0382040030004030300f00c642c1381c4030701586400150f5407000c14019080c0107405540e69400c1440110056854902e101d0300f0409000f02441700045d04200110801c485c3c0f403260300c410824854410000810340c0c03040e0442281c1d82d040c6405a462038880404007440051b0515012507403803078903141a2071174403a9041960309400784d8410030041680010096004440c000710400052140090403625825640940c82c2150008107070440400e101d541c84d00c3d000f001390001189450031b9035480040550003440c01c0b9015800070800c004144c5011002d00006200d00303208809900300d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13776571 1250 13775321 13775327
    0xf050c1305010f060809151501090b130b0a020a0f05010b010908030307321204030905060f04090c050c030a0206070801060302071104050a110c0109021e010203041401020a020411070302070602030307 87
    0x5400b48008010076140040d02212040006034031007147d410003202d203401d150b80036055902c0030018150204860540000306495000200d40304001e543e404040340c1414120140c117281d101c441a10214800d840c2c408002c250800c0803041414420720000880030084c1002500402c0d103035210200c507400c00c0c4100880310740c001840700c0b030061090154078001c1002d0b00c80049802d07d000c04030146c0c9100860702d583d020740e400708128050741c040e44070800c03100d50b00ca081000f5031180c040c0c0c071004039900740010014030509400c981c0c00b449490808500303250440b0201031858129101c0600103034003070300520140b503420664041c0035207142d141c01d51801001d03485042e0300b00d40c440d40c101c3c080e541e01c000003120800e1130b62200c100c4103000000199a00c4000c2040d6021b415489001c0c5d201d60030348901e4400c81c2d400c04192154080c0180c025505280c580544c039002408003004807410b5001c1c0d07101020041e643c6210b0300f00d6424000d10b0242c0c8898082c10002d10b841c0a80d082501554020414881d02e04d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13777821 1250 13776571 13776599
    0x801061202091503091b0405010609030303020f09060f0403031106040804060815040c030b190f030b1302100f0e0109081b0105040e0f0603100605011403090a0f050c130501 75
    0x203403500302580c0c501d052804503500c080d8401441542140100910500d001e0120342c007003681a1608014228038403003030030402180c400780f007004085907070306800704002402500a0701703450b035810388280e0400f4000ca02003441079000c1d18103603450000018041c01011741060003031055111040003400f49107059030703800344c07030344540d01403c01440240c00024103591401c414989000b14081c105110202001c01c016014000740d400035403007802c40e041c00805599034050240c2c201c80380c00400881042c035640b1036100788580500110714200c8102c0003000542c03503445410404400a6498290103901e20700020100300355031070084c0c104041d0906c100032003c400031390740400c1408078132080c1400381d01100503202da01c0303140d01208414102c4000c0000356458a08100e100302001d03015510840800d01842040b0342d414068103011903416002d5007100380d50540030b5503221040000300d809040c21512500c04244440a0440d25980803003800b52540c10304003005c10111090784414400c0f54148000b180081c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13779071 1250 13777821 13777847
    0x80402090a09050f010e0d030b01020307120305060607050f071517060108090a0507080a12080f01090207080405130603030915120504021f0c0506010e07020a02190503010c08040b0601080106 83
    0x40d884a440b07200303000341804200504182c030700c001c03c030350b40c0d0308400b1948135600100c4640c04a0300d00f0002c02c115500203c1120707021079000b801c15081c0d00090205400900c005424290000c00510050300042c13402c000c1004200300c208010a0111714001081c4461420030815000700140c900000800008034850f640d0424000d003444c17203c56941c0321410745002449030001e07143d88074009000420b003101180519500b401940d1724a0340d40006801a5a00e4038251800308011824000400c460360341e60b80600b80079845084d034285803950780c034006250341781c00300d1405900d5035981404200309a00704503044020700c0c0c1c80340101d00911041901034034101c0040301202c000f03510ba000103000c560341c001070440b960381c2da80c988580100284c0d100404080181004403094464103001160a1210614240c4554504d038010f0160101e01d5084c0204170360f248a1840700e820200f42e01040c103681c00c2c01100050640d40e81e030000f580c94941007804a081014010303605100a45005100c0c084d40584016564 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13780321 1250 13779071 13779091
    0x120903021309050309180105040506040504120c0302030910020c030f010b1513090903050705010c0201021303020d0201090801050903090118030305030612030405030118030f03050f061002010e030c07030209010608040209 96
    0xb41d024100355096100365640c003a03100c0c105000d039105c4d60000c2c0d68160305071502a1380402080e964181480102d98050b82c020708800881c10351750303010502c24240000d40307a200c1c0c81641d080c012401c0c00301e4004d8080260b42d00140c0c120b280070300000d003402c01801c01029110002405001c2041703010610380d2841c1c10000c0e02c1d950340014115040c0c08055196001410f8003542001015503d060003070058001107811039283d42002a1441070510500946020000c0e032101c41007160b10310340c204001f8200c0c01c04100e0601801c8080029100401e22416100d0b00d0500c0c09181d8840c041d100042041140d220b1820b81441005d2040c07010075801019698803000035245100000403001c0721134039500032640241d6240d800c10036812007000401c80c070542c07031610a4440c0070304003084007019001d031a001c88010503241c0703c8000080d81803504044d0008040c1d02400005010001c01c0a1a030459110704460703049680424000c00450500f11201801040700d4545a84681081e5000401821010b0000d000c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13781571 1250 13780321 13780331
    0xe1f020a020309030d0503070801060c0506010909020112050a0e0c030303150d020a03080a0c060501170a0209060a080f0d020607020706020a02040207290a0605010e010804020621070801031209030213 87
    0x1141c001c108441541d10000d08648002000d088010303c0f81d031044a285c070018040000002d1824003888458102d690b00c130000d8413182e8201840300c3e00828082c3c038168101b000500c9010040705e900d01c5400d0140ba1250004030314051305d00f03034181c0f410720b0340403c00e40254010010820441c50050440c00e411204980d403100c200c00c1400010420f00c50b0750400760194900007140400c46030800458180306208001c2401144c4e41c071107042c02c0700c02054400310090f8208404020042c5005501c50f60b12210080440400d070391141240c2e444c0c0030071080403082c00d62114140d502c90725010032070710b40c1c40340c0244000c2c1410707814250000e48075035001d20000d000350b030042505010000355042d900140480103c02100750207110082142e060030540d0000f000601e001c00100c0c02d07511900311005602010b8640c80407031780b1241d00303202141d4011685542040d000050240c0c80919603102c150085481740e0300e00500794107609025043d042d0081c020804d21207019410001a01d0303d02c805d202d40c1c5554000020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13782821 1250 13781571 13781587
    0x6050612070902040e0703020903030a200d02011a06032401050d14060a080106140603040206090a06020a03090603050f070503090c03030301060908010f09020619030204090203130302010e1f02 84
    0x800c01a00141000207026507500440c450786140d000d03008031048080030f0400703500d0710201075041344101c600d03045e010380007045039110b130a0041b06c41d82c460030104002e008104170202200c1e070500c51030072501001030351228014a0421410b0100e0001002c1c01c580c00c80c91070130490307001d401c0c080703254072071001c80080031030f010410380e00400c03d480800940803402e01c540c00d03070425040c030506406c039201c61203400c0451703010502510500c51841600ca2451260b90518078134820806e00d9007000388120781c1301304100181d1810f515084d0b050f4000304000d4005101701c210500c0c015240c203030b55400010400d4a050100030861038020302d61a045002420407550307c0c1c0365200e0075400d010b00c04202a40600c800400000c81c5d45c1d10000c12000c03034003c54020031108003c0c81c509026215840e070b002c1d500c000c3c140b10070303401c8140031030900c41e001038035060042c6080d030b031512414280c0e00100c1d14920130740340b246000014143c0a004070030f108040800600b4202c455034041c09032044100034070880311580403031000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13784071 1250 13782821 13782829
    0x30303070f1205010f0312020d050405010309020a05060a0905090a050903030612010f11090a0906150e01170703020714030306130506010314010f06090e01060e0103110409090c080f0f0307060506 85
    0x2e5403500703884005208942c0c440280c509041c0c6148801c9405000780300c076000e00c16202155100da41c110550f0303194a4a80391000440140141000580e0701c21009400042e459072148010303c003814094480c0682e031464a400c014800d04000c08480905081004019a405000c000c6903400b40040755407601c44009030340020300400c00d41c90040015032801c256600c20071401070240541d41030880c1d89210f40c0381c0361a058070550301503104000c1d443c5009206062600d02482050300c10302c07010705d04803c001000e240c1c890401c8100780c8000c4003080d8002202030a10508030744c00e50340c41d1284401141b444c10b2810208501c080307490007a04020740d46c1d00103e07205a100b50010301d0030400c0b9100c20f584a503180d0500d840600b0080c0304440106000840c00940c420011076002c0c12101213403100e200349400780c1300640140035140540700213654200030100d10441d052155140c0c507405205401641400c014240d468210380c014281441d82c0300344051074043d03c002084071802a030004011130180c440350042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13785321 1250 13784071 13784087
    0x70302070506040b0603010b010509010e120f030319140f0a0905010e0109080306091e180c120c0102010f1503020f03030904140a05060604050109030602160204020c030408011a030303070f 82
    0x30010301507a001d01c4180403000013032a01130b042c124020000865180b006441a104611b80140411004400d04416180c00d0011510082048042c0c500da4501c404c1802d05644c401ca070000b4014107408080c9898615600c07032406d0300805114045401c1c01e08061150308040000c0c4091700300d540301c0c00ca6004120003904280044503040000348841109481d101c1240c3d0002c031211409046920001005002c24203000b0806c003000c40078180e40340c1c50f040f09080401c4030001c407184562088402c11409601e480010301c920b19aa00c0181c4168101d1600080c2540c0c101400e8102550802d0380e10781015071000e42071030451b681201c6111000b401e410110781540149840076602c14600b10440c070a818500f10683c2c402c1c122180d0401c00d5564079400c000c1680154082c850011341140e40500004246900502d0707160713004144400c1c2694594000340580e440940c0c2d201c030f29080401c0c1000821030901841c2d04c82410000300c495407001c2c41c2c021030340c3c9020080005080103032540c4480e9000e4029158 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13786571 1250 13785321 13785323
    0xe06030411031c0305060a0e04080309030408070e0412030608191502040e100602030a0206070c05010902120313050901080a060506010c0f0c060e040b03060403140906030a050901060602030a0203030403030507030207 94
    0x990f9802d840c4a0b4155040d8042160401c0100303040500003101d07442c056065809a49540ca40340d10b0b41e885646a69a41e038000030000e550a202c00c210105944408100840c0140400ea001e007603107140030b140c069035001c40004507006250500c0c4080c03201900101d00c603200002d0070014542d03203d110781005010792210118003900c40c1d10006000c40c0040d0030f120b15900c01c00000070800f0780c070b50f9680c000300d0b580e00c60b441c040001600403a02181015200d0540c07a0203450199001240100ca290000b5009000300301081e0b8982e400042d4044084100d45010002030008072006142513241495640e00c031200400002d00d1641c0e40d10006546a00580340084841e800500c4c21030100e0061426040e800103a028075004251628040c642514082c0107030841080e018000e040e543d26165019601c0c09901014540da40d802031045503880d446850145204100382c101c041850b0406222160131030325250454001c5410401c507003e00c141d00041100d801075414907001a069440000480087c040d0602c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13787821 1250 13786571 13786573
    0x150d06090213060c0503091908010e0a030806010e030c0415150309020a09051e060103020c01020a030203061203030705040e0901090f05030a080c030910050604020f03040308041103010603030e0603041103 89
    0x218810000364003400c0c1403031641c0025075280f43c66030815620384425400c003c00350f900803c940c60303007803d0840d40380e500d624800940104040c0c942281609440d0903400c011039035804266a0700c141a030101c0d076190010001c0c00c1c19044007100d040401c0c1c82d010020794a03030103262154109884da240e0b02d4400e10043c40f000d21800090410000010f002c0c28080d20141d01c540d690410106007445d443c45002c1c01425100200c07180c07455900403055024a0041c00c06041c107501780107550b10340380207000070010321a07207580c01170340c85c6841420440c1c8100030700d2950344280e009004010b000d640010885080c4da9440c034100c0c03400c0d80c0d1b000e182030141c600040c00070403445940116408015000020340306111454841c0d11043d5603544100c00140011034105400381d001c29040348000c5110340c421500001d000e400903140044040640fa866403080e40d00300c000520200800044c00b101c00b900c1184610214003d00000e071440c3c400a0500a10b01583c6100e510b00201280400401280064031494003030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13789071 1250 13787821 13787831
    0x706090f051e070e060603010303030903030f02040b12090102030103051509010e0a080301080118050705010f0203090406031103120304020109060e031603060b0a05030313090207030504090501030606050f04020306090105150d 98
    0x200c1c0b4011a5440c00d404007070b00d40300d0714402082000004006130710407200540082e08680c6103407402c40141c225064140c0a1550310f461440c400510380c002400902221050b1075074900301174010413040c00340200702c007280d43d00c18001840042c80200d2480c1c03c00c3c20158103190182c8a8000c16030041140e10604d007040d201e800000700400100002850407681c4010007009000500003020b440b80036a82d40003405500100c4062007598010b00f40f030302e004040d5104681c28503202e03101240440300d02d5041603942c250400c460740c4e03151400300b088102115039040c03031600b5828103038006407880c000d60043c24103000d080010101e1903142007011141c1d04581c8200c0b40d00c41c50b582e0034504000c00f06410420302841d583e8030089002d00f800011141d6405100c07140000240c58507425400941160000701c081050400000a604549000362800786009034400540303c1d14000c1004580d000c5414824000c500601c10807680350345001c8407a044540958440c04604100d05480f409807140d401c0d840d0005241c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13790321 1250 13789071 13789093
    0xf0a09020d050403110604120f021e030702030705060403030e1003020903160905010b161e1209081501030203030a0c05250e010b07080a03090f0c080a0201030f0203010b0706090f05 79
    0x59040399000302d00075120745803112134010390030b506d034401290701030110104e03043d102056500c692030881c400c3d50140b0544021054089003980b080b980b41d46030703141c20317400840e404055107001d00c81d4a00405e003c9039214034051071a03802501803004020154422080b0003e480401402a0100c81441c940107090300c1c01c401c0c0300403c0c000c01c00d0b1039000340e101c05450300c000881c00d0381c0e00000720f0700d101e0f06415014180d41200e581e2510b00d03114a0500004000501c4140000146482003c1d0b2101b02e46481d5031510f18100507200e80341c42c9030310140044540354000100003503103020045170040d0031645800c01c454411401d10a140c410202c000400c00780b0303030007045051100094501015207060014000c0c282c5d0361116682d50034010414050a5407008104901000d170080d4809400903120700d039108001e8143d0340300d002562105602103004e54100a00420842d80d051162125212001d003013103055504284068050340241d120041c6419910344290b000d010064440541840d03222088a03510102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13791571 1250 13790321 13790347
    0x706050a050f070201020405060909150a06050d0b01090b07060506010201060e010b04030302070815062b031106100f050d0809060d020415020601031a18060a02030613060506090f0a0902 81
    0x84448880900c03203100401d201e10b1046c0211030480e000200618117001211040203000030000d0502540152544c22b240c4d07182d03c0c0c0c107001c10010301e15601d4450300c4002d00f02c100e00c16280c2c032010882c108031400c202404a0740d070000640c0d030526048800002c0554a074001070340100032a410900c4504510b200000f06020304000802c2544d2181d401c0d030703095a554081d800d40e1504280c450f10b100d8100440020410b04203041c8030b803080c8150409503448001130010901e9405101034043c0d0020b41000800c04808900b0001e041d006510300b03200144041c81c0c401c85081c04c04007401881d210704203c18042052111700801d40707440703600090050b83d46000419800c0000c0d8010301c900ea105a901e02d2040200034004941c40d4102ea412070f040b0001181c20181614031030780000c140504800d03400080325140501000501d01c501000c8500503941d0808800300905003030881d90346d894180c14024103000f1601c2e8003060b90550340303065414512003c03105d40020b40c40d901d20b411446445e0710229014105081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13792821 1250 13791571 13791581
    0x110a08090102010b010e0d0b04021c0606050915030d0302030a020403080f030103050c01050304170906190f020601050607030210020901031e0c03050109020720010e030d0207051305100b0903030706050a 88
    0x4242c000b0020000d50b4801550703018208000c003a4042d06489541010562007121140c0c4030348000c05c80240d142c18405800c0c01010340309001d071000ea03a1035a00780170509004800540100c07c0240f04001452504002980e412104004000700354000c0040b511109050701680c003d168402421601c420b0300381605940380c1c10920042c0c80034801e10040440c154001c1e4201ca002d25004208a0b0541d0202000900e265210307030760aa411101c10048800307141ca080c15038100f60030882d1f40c2c0d11184441808001d11303002040e0455403103000c00f040400c00198000a0203052104040000340e100c0c031a21b030045e070040c54451555021801c018040b1100146075500120488400340c070700b008107903240c5901360128050b20000600750081a058079a045460784c0c01038011030014503141c031070800c3d01c0010904001c1c40701c4002e070242e803140c00140000d1504030104115080c12903410003d40c5003090264480525910038100300034000103815541e07803020320031189950381184050115080009100340205 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13794071 1250 13792821 13792837
    0x210103120c030917100b01030203010617060609040501090203100501030e0706081302030307050f0105100302060708090a05040f06030605090610030807030210150617100501030f090605040302060403081315020703110a08 96
    0xe450500c00d80c01b0340d03002c5d100307990594469036203140840d025203c9000702d04001410f45070b0301c840d061080340030541d507502035207001e810315120160312418242c20601001d80c4980100b814181001001c9440b041c002a102c0100c034480d1800303908941741c480d900c900264080001a41502001403040180400000c0444004000038020416a91a010310003039025040c000254070035010000e130300208012102402004000400c11440300c1c0c0c5c0d40b8001012140d0f20780c141c2071055120041001031046038842d20f036024240f800500b01ca40390500d40740c22030009034000100002004107192003410303c200700441d1260001c0904100040c00c030b01d07041043c581644a1000041d100c2000e4620070360310008103034040d41b40e2600140042c0e0910005402410305684110001c030350b0768103075101154050180c03501550207500544a14141402e00520b182001041001c2c08041280310200103800e00702c49a406001900c00140c81e031040e440c003110000011102e03c0ca440c4100c8408a05101d08107000301008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13795321 1250 13794071 13794103
    0x50109120810030303020f0c0706030e160302030303070819090c05130c09060e01030e03030c0a09050d080403020103020a1704050718060f1202031203070302210103120c030917 77
    0x240400c040340c103540100da20049040c0302840400020340250003030720382c5685801150341401ea00400301480c120290307200303000282c4c5660070403034480c0c1c05200111800d04249680000d4500b580c02091b6284001b40030300041188208c0004c009071002079100035881c0d5010390900c82100c19050120007419640070f1248296522120341403030160600c582040725145454040e02c20b032411000f5a014141c03d440da5050503261a40c02d00aa4010300c01036100c0d80020320916201d01640f08020043c15091700100d0059034801021804039410a0035242100c0c0d0910340966640360100c0c00711003090b02440c0c03980842c100101484100000421030600340c80203501d81c4905c102245001c8016148075219904c50701602a000b448036540d15807650039042d0028003190020203204c181c5403a0b6601c201d4440000076404110f03c0351208041b040301c91440d40802c0d0504195045403902001c1625445860b41402017240078001050b0090322441c0c020580003451089003003010703a2136038440003803603600701d11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13796571 1250 13795321 13795343
    0x10b0d0803060f010824060d02041e0503010b01050706020306011707030b030606030c010c020d05070f0b19020d120203100b04060f0201230402010507030210090602090103051b18060412050109 84
    0x52940700b9680385104098407400c045001c00d02d0b180ea896411094603c00303801c147c0411140100444034001480181295141d80c1c0300419501c03103481482c0b25076002640300b6418100c2c000c4060303901c0400d4491980d000310b8010380d280c4840300140c460340546000c0c41c400707803004800c100300c450f05540302e81643c01040d0241c407034956544003056214403601c1700c1e1601080c1082c400401504010f8034120065115408031000b00703848031210790f000c08882c1e01850aa5400042c1446401210a8a40c918000318002018450103940000d4581e003414102e00744100d90200008600001100720030f80105045548642d945450b0307813005141c1140c0b200028003643c01c10448125074102c0d0781c41c01080948180702221503885640c0119045d5103e5182501180705680c240540c00c1968450f02c01568440c500059482c5031100001d000c0c1c0794020004c41c00f000c032030b1840110a80d0890200c40881140c0000702800f1105c03080020b4440c040c8d40c11600750b10b131500640104101c8c055200301c2a680c042c100c000d071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13797821 1250 13796571 13796599
    0xa0608060415150e040f0e0a120201060b040e0703140408030a0605060304020f0118031403030105040e0606010804030f02010609050f01051507030e0415030515070f030605031e010b0d080306 83
    0x45102c50b03c1c0300300641288040352804485106494184038100011302c00f0610080ea0001c00d801c0c0c0d010389003440010717000905174800b00300f00f000c4445150004d40c0002d0203101c1c40c0441150003070007984601030b10140c407030002844042c0b09038071030504002c001c0c203002d6060a286c180040e054004441c01c205280c6000b03008a0940341c40016244195802014208910f80d0040111550030241001c04021960f551000c07002030031014103610002007201c002c540702d40c904000c03c81600c4608000b030b80607401280601c0709699000f00c145078029054240415403002c0c200c003c078014074060703000300050b510700014000001c034080c0c1224100c41040324940112404150118524450700300010302169188003117645504141d04800152000c09032024452980da8035124100300110406e0300c1c0d842c101d0000c00031815005035480441c01160b18082112500700804a9911a05041c000001ca04500b6110444035825004200c40c4c00780541b03901829904c5180002c0345420956070907105400513a000e01c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13799071 1250 13797821 13797851
    0x50d05101404020418090602090307080c01030b01111903110706020604021201050609071805060705010b030d02010b0a0e090708010204080a030f0f050f0702011707051206090f01060f0e0a06080604 86
    0x4d0640d0358559840d91003c440e4032240004001040003128026000d004102d5165824880344005100c9030b4050039034000054001400c803034200a9440c10f0201840c0845842e06001848903240300100540360241c2880341003e403064012a103840c481ca2141c0c80001c541a680420064000d5100f031710078609465800022600707030760041b40c840390088083c2000600d8144200e9034030349503000d41c1d010040c0f0300d1b0b20382020815a6003c05001d84090b91100d0200341d207030074100090000b446130340c0300801882c80d640c0e002500b0f01c1018031401100b41e0001c0003140c4411018001c800c0103020410013155201e40e5511074075105c0003040c00075408a403201c00480c540c075014400031054043c2d5a558107207000602d00b01602c0b2a0000e034400d0b41000940203102a110064400c4540102520b450325a120842c19980c1500d0040c01010346016140307240c10711907055428004241075920320b00301031400c84400c5404440c0240e41586c4170381d000600105c0003c546400c80c81d02402030105480500401084503284 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13800321 1250 13799071 13799077
    0x1b08070e010b2b0203040308010303080a050405030a030b0f032509020f1c020c060703050105040e1b040c110303010e01060306090b0a1e180f0b010206101401050d0510140402 76
    0x50150b104101d10402001c0000034038030103074002c500c2800101e180a03d081c0880e001114210049800c6030014002e068103c0903241e0700007450701c8140514a032aa6544c0d840e80034000d400000d06484e0701e246a4580c0d1000d041800d0488090100c0c0d103032800c1c000d05940c000c0c02500200c00c2903200d0020115104683d402211805403014104903d130508441103441c03480208102d01e6070b4554207101c000703c2810284416402100e0356900400d841d4140000c000880b050184080d01544c8454400e01d110003e01c41d01c604800c90131500091250095401503d2124000d0302d50b04c0c0c54040000042100665070415606030b81c0255000c105041e19409c03a40104d82d01c3c03030405580b2085050003001007184207029a044c0100c5120215111607443c41d400c007070200002000300b84030340c42c0c0c69001e694996174442c0400c40740007407008121900709250441008181401048500e154107828002c0c0307640107508890309281c11141c1084240742c51102510841d201c2c0c007a158421076040c0c3e00c40c9081c90607000f5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13801571 1250 13800321 13800329
    0x1140709060206130804082d030a02060c070204090506180714130c0318080c19020603180a0b150301110a1d04090804180c0305040c03030c030c1b08070e01 68
    0x5102c103440701641c1000352546140c1c121a5030b0410440414265000c8c003808255a1006084100c4c180140c0c0d0520385d410f10240d00b038000e5501c2403180c1d512041c1e000603c0c1360401500c5000e130303a83c0c0e299800881c0181c5582c00303002e84188503140603c02e080915101c40116220360b401510900c5440e83c01c102c0541c000440000e80c0490484096807179020158001c2a51070514180010b8110716089422100304030040161141c80002c9086020340c0b034148509030035a08440c9045c084512964001142400003600c00d0103000d4501c00b419504c000300308040561103030800a510718600d0044155024141c008542901075420440d01402c24038002096a5068101da25200030b10004601018070402d42803034129480380e00c6801d0840030440b404020406080800003407100440703029202410b4940d02071380002058608001c0001286000000409895062a00d60304c0c905031410b04035008185c0314009810f0400c010001d10361200d0020303404040340c140505982c4007954401a00c0e0f11050240300e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13802821 1250 13801571 13801573
    0x303011508070e120a020405010b03010b0a050a0c0f0f1101080103080f0c0a12020a03020d090308090f04091403030108011805060601080601051b0303061f0c0809060f0309011407090602 81
    0x21a805814012001d041e4004410300c1c0c804114a014000204200c2d03458071001125000400d4650550405009942c05802e0070700840c0c0c83d65141c0403040342c092248006510401001040c08107010344550303ca40012600405900768990b458144a40e20300d401c44c0003200c010080015001d980d500400047c3d0480f50030200c00c0703040028200c0130f000c15502010009240c1e01815501c00c001030061002d40d2181e440e1507000340030196107458068a0300c2508980c85040c441d07080410000103038981c044038141c00d000e030f580300c41034040000460301a103022a4010010803803c0300072210504000042d41c12074031038034000c0c440380303a0021328503024444145c0d02804541021000030003d500403841980c001c24185040c40ca81098800c00740e2420501c000d0300c20281d000081400041d203080c11440100d244e044540000031045010090001645102c00030708880c400700f688a61649c4000c241c074041101030b5416507503441c10000c83c90080064581070080c251101c008624001c3c0304100d0301080e40c0c0f03e50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13804071 1250 13802821 13802849
    0x80105040c0504020906040e0f04060506010c050303060409030e031903020d050f0301030b070e03030f180f01080f090723041a0d0618020d0308100503031c0b04020d05010b0403060e030301 82
    0x1000340006544800721446d0400d204000018803082c0c99582d49210355881c02c1c004000707081900d0705c0c40a4031005400503040103107001c44080410404812250840002c580004220140f4542030361451010f0441c0da1b4140a01d039581400f1003241005440300510035820781d060a038565800341c0381d5020360180741c02e1456061005100103004283c110350850701506180c491000e0440019286a03c03104d602c45c5581c0e0040385010050000c0030849442c0c90088480d146131501c000b00091408000600d04034035989407002280c14503109000107805030041c071101c8450b544004000301044828003e1041c000c900c1c20038071954021101c1100400c1e280c0060010007801c029844403400b03072428030b48684928210a00c00001a0755a802c220320b03003840394503062034600c3c01080031010958540d02560203600f08000c5e40712011a40b40a40c042048007080000c0d458014a010800030700585031103110041c03604002041c0c40759054082c104881c4569801e024031001b10810070344030700080c481c80c02e100580b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13805321 1250 13804071 13804079
    0xf0f010b0a0302070501020f0a09090b0901060e010806010e0303031008100e0307020603040c0e0f06010e01020a02031009080d0608030c070603020408060601030504060b0405010f14010c02030d050c030c0601090c09080105040c 98
    0xf600202141c5000f1070000d402c068010000014a078015040c0502083d6a8141040544038078003400c2201c050840382001c280d8036099000d0040d010b40f402040c100020300e000240b9903802101a0400c6840c003400312a01c9181c100b015840c0c56a003805020000c0c0b00d1800000500704841c000c640c5050305c0c920155042480382e900b4010140c10281046480081d00180400d1840000002c10702c1000d03990240e010b02c0c1400c40024043c4884580e00504540180c3c1030303280540c80c0054812074002c9080c9000588540700d04040f8414010030b4024000c43d818654005107207031001010786a1814203070140d40352180e40c1c981c160100d100c3d40c172407000c00e40c004000282489d0301a07840140d01501409000c1484007029001604440f03090700503c2c080e01e00010280500f20350580607080d40e030400c0c204000004a01e800080c1e0b65204142200c00700000050390301c0c0c1c2c3d04c1c028800d45004600c0c20303007103a00c60750311121120081d0920074248400603110a070001540f0205005e1140256008044c040d111824 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13806571 1250 13805321 13805327
    0xb0a0e120f030c04120302010207030305090c0a0e0903070212010605010801050928020706090302010c0e1203041203020a020d0501050402090604020a05090103051b040303030506121f02030702010f0e03030f0f010b0a 94
    0x1000070440040c10f04c40083d9038940340032607a140b540300f5400165502c00030b1901800700c860243c02800594022452403042c0e40f102c10041e0b0541d1400c010303a03940d55072002c59280c0381d4440c0220094000244142c0c500740040705401410036901c090302e40082c580c0e00c075024050401c1003140c424800713011140e8540f0b21464040342c0510f1141c0a800050710300000784d180c69054a05032401200140c0d540d184620b45942d0201c6440c0c3c408408807010034014004110550b90307406140078aa14824018801d10209402000380000843d40507101d02401b40160400b1402014212400c0c1e00400c0769200250040c5800d00c202d0b1800100c81c0ca900f03003441a03510044000703290060240e50b68424442c00c00c2c0890702040003500056119543c04074092070700c44240407007013110003558130313080d4000030842349072094198003180880354280005884e42c0d5800001c901405200ea24031900c1c43c035021901c803030341c68040700451041d040c4003114201a103e5441024140e8000d209403011042d0510050b000544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13807821 1250 13806571 13806577
    0x607030203040318080a0c090b010509190f081b0409150902010903061e0b030c0901150302070605100509091614030109050607090609060201090f02010e03010e07030b0a0e120f 77
    0x4042e152401c0e0452003011382c0d6820382c0305078201000c42d61100030080f0401c05008001c134044c04003201c060083d0340c1c0743e00c0042c2041c0190120030f4031030300c0b010483e030868032501400da600030003481d180000e500350f0395072650f0b4036000200144800082c4c580c42800c0d8034101030040c480c0b000c0c1d10803007003081e805503004200004d00c5449402c90420507000c1000000c1591401101a541c82c5540f800d00480c2c40d0350798110440b02c2c1d10703100b503000c0e4202c602c101d8000ea4880c0c15460445034420a15200454003000803002840b0346440203040030b00d84030900090390100300390041500c034207030b6041c0318603154031402d1a40c6021140d01040382d0342c0290000d001d059102c1f1241001d503100a4004102511315503603483c20100700715510b50000d800308504102440d8000300d903400611740b90000700025000e40c1c0750820700d1404108040e0521542c08200e82d05524258011a0340740c100b207055a080507200d00e400c83c00200c0580b40c815581d41002c560000700a40460355078280f10500c5030541c50211040d00ca0307055a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13809071 1250 13807821 13807823
    0x90f08010209010c1401090b0901150e0c030103080913090b040b06091005040c030e0a0515010b0406020606010507021815010320030f1509010b071a0f24040c08011401020a0203060703020304 83
    0x2540b00c210480001c8c28031021680038a407090004030390b2045e1044140d41c0f030400c583c0512032400700801440201407800c1c4c100c0f810340c0d40249007180e8075400c50020510501c0c61100c030f01c01286c076010711002804105001c00b8092482007200103203540303681c0b04200700f090341a00d03c6049000e5580c0204030038546540a1031005141c5d080c041000c0d07044200950801388261010340d0907030031000c40d0242c0e00c000010f005014040c400c0d9000d0405040200081d5070324030041020341480303400506401550b0350381481d0320b0050101c2c80100143d240c0b074611192010300e42056940803d040150030540146c1031941e0120032021440158115550326444e6440d015001c0d2428140280c040b80c0c0e0012070300c540e009140608078a41185507518801e161540c3c10000c0c000410080b44044020f005000103801d070740b103401c02000c0180c0c4180e8098100300d205922150120941c1c0a460050500b60540e00005500d04903601205200502c04003103005903181d00b0107900096050704200009201d0328000e6010395001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13810321 1250 13809071 13809073
    0xf02010609060e010503060a05070c120e0402030115031b0e06091201050c030906060406030c140111030a02010e010b030706020a080f04090501030605041202070e0a09050319090f08010209010c14 85
    0x256a01d200d42070440d000c50b00121500e642d600c0061282d82400c0000702d801c444030000c100110300e05140000c0c441080c0d484000c1440c2000e0300c403a214144502c45140301410024021035403541e640380180c070042c0401082901103030919000c00e001c44002c82c0001541001621040074004050f4200300c05903024082d49544031362418290300002000748903051290b86003100050303030b0307082c02e003c950b00c0c0101c000c00f8107100324280401480055180c0020404841c1603419104000050030f005840880c01500f102585205c0070400000c6e540e41500000440c125041c020410380541205041c1c8038010f902681e80035900c60405000040d0245000309440004030050505090b19200d00d80d00b51442a07000361103590b01c600900003442240d008007140d124490000700802481c00c0901411094002c00200200e035940e010001444014822140320340211300e0b047c20111040c0358040e010781134a0081060071408a4804101c0c940140b01320351071030170141c40c3c08600d40440d603a01001904898180300c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13811571 1250 13810321 13810331
    0x709020c03070c080706090f14060a0e04050a0c0e0301090809010c0302070e090d11010b030c09090c030613030f0503090309040b040e01050a060302131e020307030603050a03020a030305070309120f0201 88
    0x70a0f0310390030381000307041c0020181c0740c4c80f442c122006003400801e40014014005864082103403864011003e00f0700c803415290382d40c44002c0325030156000e1244414464205040000701f00c81c10402c0d82c4041c0904043d61142018007501d002814200c42a014008107000e208110545040d0300036401501c0042c8a80f04580e58075450b081074080f4020240e50031807003640401280f48200e504401e0111254407400001c011528601000a948044682005000308094008200e561303000b03204880d0016000f5007213850f03904264107229900e5141030001d03800110860990204a4860780440c9c0c010789551000318100b281c42020007004081490a20703901c669917008005000300700380503175445203000e04070018840f07183d0b00511411004d10444280d440e0b16108001c030111006004480424498440068503640d4000d01900144000d8102030554490401d90b0400c00d40c1c000f4a100050303110750b40600003a214010207809560801d00010080e0030b0105482000328070401e40d1381c006140600c00410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13812821 1250 13811571 13811573
    0x616050a0c06020d0e0607030c0b1b0c0619050f070807091d060f040506010c0f020604050301020705031c06030803010b070303110c0f070812090d080405031209030d090303020709020c0307 82
    0x24001d529984458090b80001035000300460304041c2d0140114400d4444d00d2502d507080da0002c02201a03050000c00e140c0d551804103d8080860f400c3d50340000114140c240d5903a11444520742d10142101e96100088510905032045d500d103010741401090384410400a40d16109070a48071a42d0080a1504006481000140c603044178441c0160120b21842d07244030904000b014080000c110005041c0698105810701c40315036400078541c031642e60803800040007481188001209442158080741d8158001300310801800000f0008090b40c0c028003030b5160392440091440b03001d50301144000b501425085c00104050140e000080c03020510a00e000151554680210800c2360401a0039100c1c581c0b0500d503461075480100b00f08806040c0038001003070006814000e1500038030800000070b010703015a816440c208420002910003912005050754941035090b5400c2e101c0c0d401c4911150b00c284541d226441000c2d01448207181500d401d5406003034068140140b06002e940700c8102181c0d030b4842001200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13814071 1250 13812821 13812833
    0x1504030201020f130302010f030e0607050c01090510060e01080606010c060b180103031e0503160f0507060609020315061603051e07050102030a0608030a020d08150d0b0103031d0616050a 81
    0x8101c1d400c61101c04c0d40801d0a50000404010840c06a5024545403640034450504000750250744090145403443c1d6178100070011074058a5042c8000b0b10380e114035600e440120019821403c00c1d95459500c4100300e0f0380e0766501d141e0720382044d1451404170b414101d81c04041035180c2c101598190002c0d008150400400e804a00805403d81c0260001078030320b203404041e011104003c8000301c02d036140031802c500300884001030120049030340000f480b0300c0d948040021406001611800c0d608003108100690741c1e100705201960040b10689402142c565805d55030f4505502130700c10039202e01911801c040301c00c0d601503c4640c0503946c40105040c22410300c41c4480c01c400018a207841c40b03100050b0b02d90420501002c20b0f50116000b03102d858000f4081411415400160340b0517094451a006120713172502c00c4552a10000f545a650308210106400d01c2440700c060700d064101d078440c0c2e5580c150044107103c0585a0208602c58640c0001c04020802c0c2c07075029089500c03100e41c020019180d5400b06641c5070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13815321 1250 13814071 13814077
    0x608060703050610020a020a1203030623010906050a08060d020301060909050307060f06060c0303091104020d0213050405070c14070b0c06010305010b0d02090a050901090c08070806181504030201020f 87
    0x3080000307031600104005420000c2071a903950406000030318500f021540081c01c0c400907030144407591207548050700f081c5442504203d0050480003100c0055402c1080d81e407505450b03204400b4081940c141001900c40d04c603004558102c0383c16920581c4d00e4a4070400c02441014501059038103640358140461528400d2090b1800d440c40340000715980e49084c50039200b5103035220114440240f0340301d400c00481c0d0300010903503c0d490f8103140000f81200e883ca0304908003800d510595400c984003240c4040c2d0744c0c100350300500c8201c0d121a42a032103640c1d034404110944008445240000342514601d00010302d11810654070300503000c0a6908094803072010607d29000800c110240c1c3e40010010014070101380300e452170125059404011078005a00440c40100e0040c041c0040702c1d56032400150a0788081d4405032429502c4030814002569a1070390781eaa49507a80201d01c0d41b4040e60021440a0529000b070701313809907095002d0031a0f00300341c080350b81c031048006005030203654003000802c0701030300d0780001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13816571 1250 13815321 13815331
    0x30a020702030f10060e0a0203040f0f0503040306050c0a021b010906030c020a0f29010e070507260c07060503160315030b010e0f0901020306030a020f0a0909050d081006081306060806 80
    0x10015071740e0310741005000da03404042c0004820501c104140000300301c41c0d02403503440c20340003181c0c8801c0e8409807034410324520a561002e0443c44c034000c180401c017058100241000c6110764200c40c1100c2403000d00d40b200c080c5041c1072034007203900c2c03800400c140d42c041c0e0000880e6212074016500d4118954135580500d110a08040303030004d4070981061441c9201c89200950001428a02c490b02d40c1070505080000b8005410641070101c0402c00804001195101040602d145450240842441d44001a96030880d2450500da07002c6c001000c61428031440690303100e082d06542c1e00f5011a04540198020b00220500d031a82d0700ba10f840110101c0c3d01c0c074100c240205040d9401420030310701041403403d0710a015240c0703011360b4010014041d4580d03002030080344254040360905041201c0c00c0014604481030b902000415040080c40341c10300c84007084910104001e512005d00c9541c41d0700c440210100c0c1030140b6400b00c0c2002021800401034000901c0805124490010300191070700720b030750300d05601120 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13817821 1250 13816571 13816603
    0xf03040b0426030f091f0f020c0415051504080303100e07080601120c03061203050310080c0102060a0b01020c0d050303040201030b04050c09040207050307120c030206100605030a020702030f 83
    0x1c0400c0800036406440d141c103207003802144629881c03401c0c0507481c1e102d141340314004420041002015030741c1d003051040042556500602d040001c468000e4281d64482040d540036001e080d5200c90282864020051011101c010440f102070030501089840180e108615640b0b003024440841c02c194208025405200544038090140f0300d8612000324241008040300300b00000070040c0100750760006001e203104040048080340048035035004a0080a0a904c902e454034640c81c049000e158000c4c1c011070007065005109206c5580b603602c06a6034850034011039006a0064001505141c690340c45090300b0344c8144140c40390025050005a42d0710b0b1641e4007502c941d08000280030442da010b20492284902c00c0c1d5041c002e526012400c14454060001c4450140350001149002c001e410700072624110307130001803490b400341c0451008101180314181200540b2400012030400540d50a07107034100c0e0402d6603034034a107a95007801c5c00065082502c01300c1c0c15103c1d001d20141d07204030500040584460b003a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13819071 1250 13817821 13817827
    0x503130605071806020d090b1b030a0903050c04050c09090a150b03070806010e0609040906060308030103080306130207050c0409050c120d020c01030b03060402010e1309050a030f1b0210020f03040b 86
    0x59070780d5641e03c00d59120009551200307948014554115240c101105c907800c040c02c0d158004924922245034040c0c018401500000a2072000e80782c014164109880c0200b00321520403a4235002c0c0021034078240c8902d01c800708244081c42c507524010800c6a401548401d000c00c0a411000c1c00040c40d0406070008000c0240100c204003c440e440b5602aa00c14000d20b0544640b81f12407011030300314818040e106004030f07100c44400c01400304541102c1c0c01541c5c4000041d640c3d41c0c1d02e04028104e40c20030742c0c0c224801c000010f200c2c0a0340c199802a5240c158005014104e418a90010080104140c0d20116128058103069038610307a600d0b0304290071000082e0203400f40c0f01090300001d0030b003081d403820181414a480a042d007284c6000406540c4954203081c400b0f2200310900c0040c019426540701c004800381401d080200300140402c10b0820240700c0e440c5d003c80e039101d549055a1100240c1410040803210030307440e41c05442d040c0c203a030b000c00d802d50041d10f1310034019001c098156440358102d48001e40c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 13820321 1250 13819071 13819097
    0x90c0403050129031c18050306130302010e1203191103040507080105060d0302030d050a0e0f01020c06010e010302030309010e01050d0905070e0c070314030a06090906050604050108060705040501050313060507 91
    0x40000350741c0220040b000703801c034109a40c44c2c5d8415100d41c1c0114100300901600104c14801d541031000e0081c0c407004048a54601e005a40c011685810440440c010750900c0c0341c0c4880a54001181400410141206415a5101b45480150782c0c03505080c0713030070142c035280c0201e4000c107000300841c0201e0040f8098081c071402c010025082d64005406140070b092144942004258080160b946143c1c018202092644480c90840b018202886145401c0d005071009115554015030050486201d4070013030b0340043c2c2e0386520003120900c00340b0010750550000c201440c1598403070043c0340c0400f10141003a034106641400b0310001c6070320103d0b0442da66406802c062003800101c40225900c080c0c003c520380d20304140d41d41c008101c000200d2810f0380c01240800420446c60068100c98080d03c5101c4080204607110306101019000030744203030b4007441c82c1030000310b1020300201d503040c45203035192189403600349804011030700b0b0351009020402c100c45440390071b030008070039004041c01070348940e6070118a0005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 13821571 1250 13820321 13820381
    0x180301050f01080a0b0405070b0a0c03020f070b04030f0501090803010f0501031415090403020c060d0b011b03050f070c09110a020f0d08130203010905010e01050a0b0307030b010302090c04030501 85
    0x10180540c6202107a140042003401c000262016803030342d104000818507240d9260035843d080054204400811021900000c070a43c41402c0c0070310140282c2c21203001032424003c0d5a2524014001c0103443c00c2c0800040c00402d5905a0101d200c3e84220000200c403407aa45890250350403c0c1c0042d0b141c1c8804400400056074507000e0200c1c240140c40181c51981040e041c0f80f103002d40d2881e0241d0003080c3d404005801c2c18000d0000b40c004c00c102804903a950301241e01c10324001e01d406a103039408288003080d28002c40c156100003201140d0306448081c038050280e4400c047e0f0350422102181c008049440100e04024280507460f1004400d8046546503460380308040d0608a080c0d003140220351060940380c40c0c01d40c0c00444103400c01c6840001f803052101500100f409400f04040c060080c4d801d02c07c0c41d82543c0740c150312003481114903030020807107400464105600d6500c54407001c0c0816601030010700151030410a46500b00d00c3c54400076140990325582c06081d07561803440311f0154200307040c80c80034003a2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 13822821 1250 13821571 13821581
    0x50f0d1506090603051e09120307020309010306060c150f0b0307030804030c170c060f19020a031e0518031f0c1206030b150103060807080610170d0f030204030206180301 74
    0x403d07800c06010902d4103a85401103201742d000d4240c401001000072410ba80810702024155031450300e8010f5691070300e448042d44c1ca034440c410741400203107490000038500d0b10544841c4056940900c07800074007136038080504080c111009076808256a2612040503ea50400c81840154410f420352501c2e28a94108184005d0b91a03024002102d2600e803000c120701004160302d440d802c001c880c202e440311184c000c0d02c40c40f801040d03d940e4500d0030340844850850b40019030b00e1a828881c4e66007951440c00d0700d5003d810704070300140700c1021030300910001140850401c804103401e9405412168151540d0a4401d05404a02e6440390066640d000b019001035006000e201c808484540c20f0007240e1840c0c0d96444500c20003854443c00e00500452081207a1084d00884003c02c1c944003150b400c40d896141369515101c05640000c05541c03035220016078800300c20340c2000c60a01502c0580b92011940b001a41c505131103424480030954200000710040ea50113028008024850329125400c070400e1081c5400c6034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 13824071 1250 13822821 13822829
    0x30b07081518010e010f050d030f0e04020d0f06080d050403060b060c010603032d05030a051005040e03090102010f06060f05030a02070c0e061305060616060605030304060503040209010905040201080106050f0d150609 94
    0x80003e01c0c0c10b000303079123405100c002c0d09a45840c2c80f0640b10480d50044441d40c180003d030650150001602281c80c4007d038216003104003805034100021a0303034010081d9118019400d60001c210144010004601035a0045200c90000380c00c0d075150140781d0a5080c00c4450903001100480c041c146000d0a42c00c4240e004107c180498040079030301c011310140a0030502004204a110b10f4503440060105040c00c032a0b02c00410020f001402081200050140c83c4c0d008940b9050056207040301c0700403210020b0203030360100c40c0d541d100c400a4005401084032140d00c020011443d141c2c0030060880024000100b1030300130601e80503440b0b4541490340402251410607402071407420300f8807050002c281d54203402c44a902c102c1012141c440ca43e04e1420001500240d4411a8075000100c4e000958503041802140301b58802c0781d003079486070b0f01c1d00c0b005822100e0079100640000c5461006110543c040d40003004010040c00900c3d04000d621603031304007075034803003003480700f070114150401c0001c107400c295414054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 13825321 1250 13824071 13824089
    0xf180c07051f020a081602060103060507020f0a080a0e09060f010804030215040609030f03051e100b0313020a0506070507030b070507051b090c04080a1101030b0303040306020702090c04030b07081518010e01 90
    0x6e00d080400a54400041c0000703850690340b01c000c118030500030882d800c80c0250312016114002103a04040c030042d0000021180402d94610901e8141d1800c6004140318450041910030410711950046450040c0240101e095119040d032015034074440320480ca00c101d10944010462100300d103001804c002c40051004145400d0805000d004401465081d1100c092800c40c162140d0320032080d4400141c040e0b00c030442c490000000d0096482c00d4030404180c0380d009450b4031056581d150144042881480c2014145810102e410b00c0060100c6407400c0d0049403a1900c2810030203280c80d00341c2400c0e41200c00202c4100d400c0e0b00d079280c908082c0070140d40200401942402d191508000c41d850700e036044c0008000350851440042542e000750301030352960001804494072076403a89041c800a50003240143d121302201030009480704014000c4506a03944086007440c587c5491600b503880d400d01610700140702034803060f020f8050700e414001d0043d0204504100e1130755403400d4034a8a8408040c0c0160540c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 13826571 1250 13825321 13825351
    0x5040b0d0503090d0c15170702070f0e040312020301080604030e0405010614030a1401080307050f030a0e120a0b070203120109050c0703050307090b04030f020f180c07051f020a08 78
    0x818404000d0320302ca080c01361078101c420500342c0751030341c50008244c00004000c0d0950b01041082c96000c07000e5880d0300d411844000c050f40380d8100c21b9950781a188142c100ea0301c800784091006010300080590400e2181c10104134110940440302c060f0381098000740303180d902c250704010505a0256614001c0441aa401c010650501100074000d40f80700c0300d03200d19200d0000202d018075505600442c038500c1e0080d6406031070350f1a044401e450354018907054400740319844450501e00380100c00c40d23180c1d051980b610060b801c0d44e1018010280c2a2122a0301a130080000030000724001c0801c0920607845603010316543e40d0204c68000d45540180c00c0464101e107054104000f080b000d804503901d840c1c25040c01600e942c6ea6850440c2c480c0407039000742103000e0000c10000304000484c000b0003100b600c00c541c1d030403400d01980c4c140314a45044c440c0203079504010001003000701c82a803005101582c0550152054289241003091241c02c0000000c641c1650010301511a02d51000f02260400791030355030581 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 13827821 1250 13826571 13826573
    0xb03010f2711060906070605010305070812040609051012060801020913110a050f0c010e03070308070503070c02060904060504110306030f03070506060603060424030b070c0305270607050705040b0d 86
    0x54a45002d2014501880c40001e4400e404da49040c142c86220b54084800c0c080f540c0c4030300c7c1150721019a03214441e0341d80315601e0084014207040d0281c03400c0d51007540c0c0d0643c00d1894041080b110b4040100c0120a018401444d51040181e0303014100162050344000341c0c1d107408036400d00000c00780255101c50300e145445007900200780c0420442d40001803a18002e134032445d11000c550064420b4003583c14040d843c2814a002102d804000761551901076220089255140c41081c3c4451008407200000160511075840c014a40380d0045c2c21012000380000507620744501c0032504590b40310401c08170742d203400305c01c00003c0d00d0204035800c00c1c4a6a070b005141030070940c1e0780d05a95800054000d51155001100050b2300b41c40350390010942e0030281d0380d480491409070b0041c1020b21031742c1c0025a10968035800203a60f060251201d0481a0fa2540d58585445409408605201d151040850b40105000d40740d00c80307030307880a020303181803400340014100c003070b00e030100b0072040310014619680a11164085030f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 13829071 1250 13827821 13827833
    0x50a050103060e0402041d030c01060602060c030106020d08040305040b1b1002070b0a18020406170d0e180a060e01170c0405040312020903070803130801060b07021f030b03010f27 78
    0x136041035040d600803901c0075006003010603040c00b80241550a12001c20003200d44201504000110386003902504e480b80c4034814030024610090190101503840075410390f40e41403280340016441406442c100c0d061507140c004000903980032907422040500ca5512081c000f500c180b00410240b21003000440c940032090790390303201e404002040b00c0f9000da91040c80c001c0a942c6803080c8a0742d01d6004104100d81130300c5900780380841d1100c9078441041e22822030000c5159004204504141d58000c01c410080000c03610800c00c40080181000d000036100c43e80042c03c41000a61075010f422a00c03074440c0d8000043c1c1c60b040c50808003000c880d1241c0d007440e0510002c41e4015074140c20b1000c148602590315075030180400d1501c500c5a00c2140180b1001501c0c800e0b0203c0851281c003030f100c03400c00138044a650740710010a01d000350803010358404880d0340d000403c03503449030003101d41014a0030081100344084000a0031203038052801e822181c2c071904000800d6903140404084292801c04005550116480303174 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 13830321 1250 13829071 13829099
    0x120506061201020403020301060605030103110a0b030a150302150307140f090f010c0b18100e120a09080a060606030e0d0e04020315060403050a03030e0607020d03050402060403140106050a05010306 86
    0x1500500c541c1c003961404250030f4044030013840e00a0001d1100e1941c600008005a00900c42130b111480c1c1140c4510f0b0620300040c49004840d54900c4c41403d680351901c071200100034030484480005401d03400040107841c0d015850140018543c00640c50b032502980213084c0300142041031202ca80d040184d01070048041059410140e0147c94008102070103400507241c070018000c000e0040003460381000700240000b103004040c0c0c40ea060035134404600a0341083c0684942e8410342c50070380c10415001c1803011040c0701901390780416213004164140e94170015824001340910644106403920020f00950340c1601030b00c0c40715800e01c00188501c1110840c0182400c60303010300644513540000100750308440c050b84001171008002d0005540350796030300d0416591240054101d010a00f040c1c0ca204401d103020480710b208865a40141c401118910000c9006150040089034410742c14030000c40030801000762103490b8140200000f840e83c1c2030404100204080f9400f142c10142407100034801e0344c1600d5a2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 13831571 1250 13830321 13830331
    0x2070612020c061005030d05040602100504020418030c02012a02130e0d0903110604030f0f1509060902090c030603031b0102090612010303030605040209090402010f0309080a03090c120506 82
    0x4080c41000c80340000007034480c805a00e09944074240512000e80d1071a10041c044907002c4048030f416100141c41554a40142d21842c07000d81c00c040801240c8000c0b03500000d80c820f10090001480c0b01c0000d03468802074555201c290000b55414078480110358001840d0104c0c1541d0b9a0062080c001040d803000150b1040e48000b40649501501c101c0149115003089401d16440380954024043c404401045000184020b4400c940c407040900c245083c03a07030898041e0b07078001c1da0190790003550742c9511001850111b41200d02d80052890030942081038400c0020b45441158041810181401040000003020340360282c2c03034000b04180030386690000115024001d43c030b0f10401d50001071010341c60090050710141604141c00217a00301e440501008402c0c140d034400d0300c04000e1740380c0725001d22040f4090307001e005030484402e5021801642c003403000204030344003070320780401e03484465943c22046411102c2e1880c082a250000e00d420000850000c0028241e1851140074201c5a51911039a804000d04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 13832821 1250 13831571 13831577
    0xc02071d0402130b01020f010501080309091e1b0405100801090e1b0d0201170705040e010602060402060417030d09110103060e0f0117031308060604050703020703141303020409080405011103030106020706 89
    0x500c0c4d14243d0007441607540342c4409200070850744d139443c13000588981c44031800900c90680200014820511010304607a40000214000150b90301c1c0f02c0d040f0342ca80420b031240c5400c403e0900c000141640d4038103007800c0700070559885480951400242109640450a0380200c54001c87c1061413901050340300d09c0e035503c000700c0d010403950410b0b0005072000f08021070300c1c4211031119400c002a00e5004001003080b500c584150034503607039079580e040b0707100c403010f0758020f50280c0108004c1241308008000442002e02400c16a4076000c044003100003100c4940c0012606100c0100f400d00076076030180319110080c55480351800c01d510b001604107a03541d0050042c07080582c40a104131102c081c0030410745080c1e1440520503c50130b510740c9075640e550b1404880f0f06203d181002c0009122511034001c1d1208554951660780703071401c04100e4500d03031b500400c59401b1001c000110000160350740e4000d030140c16001d5803681e07607120305000004041c0000c42000c0c3d542c40c1d2042004001a0b6800030718038013183c038585 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 13834071 1250 13832821 13832831
    0x9030c080f040f090203060f030f0d05030711010207030309060501120f0219030506040629010f0e010201150b1e0705060109021c02041403070f060e011107090c02071d040213 76
    0x1080792405030160341c2040d1804030050902180e0002c80d81d00440c0504003c40c3e4034035a08108504242d80ca030401e0341000e0345508005514800c1a0003400515005503031801d0076005401a544541e0883c0c01a10060f40082d4a40019030103100e59072080d24050320591324001071080258690080720a2100d00003400346020822079007840e40903036242c0001c0c5a1110513541182000e09000c406410444105c000306608144843c00240710303110746076100c6206840d1007011501d0f020041d01c0ca4031401d001141955200d00340d088210481035010707000f500310a942e50f81c40d00f0345c0c88041c100c400010311243e024041d00300042c40204400080f6a4119170080c14050b0b03946030405081010407046010540c02d075030010402043d40d02d9055008200c0500c16022622826980c2c0c600c56140901c42c880c40000c01e44143d0301243c254861018024000c024201b254103260341e9000c0c02d02190b8682c540e21005030004041800120b080510314545007005e803107002902d0605400103004205107940d241a000d41d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 13835321 1250 13834071 13834087
    0xb01020309060d060e0705030a0e01020a0c020103022206030204060215010317031902040f0303020c100f11120d0203011701090309150e0306010b04080115080d0c1a070903060b0409030c08 82
    0x41c1c1000005c0d156107245020705040c1001c006e080782e00161a000c082c541440008042c3c88414420f82e10321a01a07070f590208010290010760007540f00080c00004000c082c8040a010420780e924800100b5250f80c0040c2e40d9807500b20b00a0620560090303194955030398400400101d02c0c3c11614070106040d0315800b80e42d07900d90f984581c2c4508908000c0302e850340c4c000304d00001c01080c072902000c207c80c0241c0a0781c1c00b1503141c000b0003d4103242001e481c00071800800c0c0c240501807142e6400c5040741c06450442d0101d8280400d40460303a0040c2c0c001042c015000801440020b00501040101e151810000d00c2000030303035074000d040c0030003902903062928007410b100d001a511840c042502c02030090192241942c40750f0110303240d5403080c003410100e5800c0000c9519039890140902c42260b2451024241d2241d55a100b15100e0001107015a201109d800d61908000d520100c00d6003e03803441e841d034010146c40d500c0c11030141c61010154900c91840c0c4105080421381100c5603c9400e940300510560720b00070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 13836571 1250 13835321 13835347
    0x5041104050c13060e100507020d060203060a03051219080903180d1203090611090609120f030307080106020c041b030b01090801021602040e06010513090f020d0506100602010b0102030906 82
    0x251003940d83da101400c07080000c3d60f5070482079a05800005807240c41498a42c032105940c80d01c101c22000b074021925451903000704840da405550030400040642c5c800c03581d00c0d1035840c43c0940348030300d051012000181c0c580c2c0715843e05a03200c5200c241400c00c1031482c50010407203070302e1b0b0003218540100c0003602403d80c010341d42c1e0703460300704900d0b640564100301200c0002c1c40240141403a0404a031550b00d01640b48020102c1c0e0301c2510340e51180208000c0ca40340740d5405015404030310400c15582441003092800c0110300c2440514480c58269407501102d6140030002031804014a02c000d0041d880d04a64011004982000d058202110704020412650140049038103044581c402c10341c9520104110a80b64540030051403251300071942804025a03588845031503000a101b80f0350320170542121f0b03082c1e003066078000b0050140102c105040c55060358010a8411014242c211130f9504600304002d0352403541143d80000c3c04161000b0020f601340d10002030342d28030881a0040c07060002040200700010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 13837821 1250 13836571 13836577
    0x1020105040506042a0905040c0f050d080903100207050d020d0f08010303030902010908030d061e0503070e0c07080706050106031505031b130c0c050d1d04020319050c0901020f0105041104050c 84
    0x170105400045003030b607030401d00d00200401e42c1c040720342400c0f2000c000703041544203040406035580203000c411041c14a94a6946640c491a0266010301400b40e01400e400c0551025040080c060000781003802a1100000e0800310038410700410f02106071303451030155070b2005149042d00d5050400050700411400180c0760f81500380d000308190b100c00620050340e01101e4101c0c4084a00f050004100c0441c054512503c0142900030385070158025401000445001810a600f000c1103010143c540196610f9010322a4030684051352000d441d20010070189a046c440c11066000c2c040d11138884c9803c0000103a154a00b1314640c0c03501191807080c454481ea0707249500004001020401c0060051005001d000440c6200045d203e41c0502c6000c02551405410f00e15800368100e415030001808901c2008001d4201401c0010800400c5611510600f070900c60580203000001980da114800700000918255a62201d040680d0600c024030000480c032a480c0b8101000c11100801e07541d8441c580601c10340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 13839071 1250 13837821 13837883
    0x3080906071202011b0c02030303040615030609030309030813050a1212050a060302090108060405070905040f02060c300405040209010c1209050405100b0313151406040b0102010504050604 82
    0x2049820b55007070b00d00d405611001416041d03981c000c29641d002c4030192000c580485001e901500104006800601c0e1070340401c402d080c840050381c0c0f031180c50741c444904460455400300d003c2580d400711001032681214800f940300350300f4001d0700d8030a078a613504e55442c0d201e040b0005103601000c500c480c81047c0207840c90054048020300030003081c0350007a10741c8003921051106a0080070305400114055102081d164483c6801500902401c0d01d0320700c00000900b0000c000396855400c108403100103917116070050100c60b12090090001110555401ca8552041070701a001850034000110304441140183c404540049170010b8554030360000588000c501100d008140c04003c0e010446200d801c0f80c4110103076401038030204455900c45048201c84002c074015108108014000508400c0b400040b031001a4881c0a10603a0f4840700c00c000010398131032010740007102085408100319810030b0700c03500510f07034402d10007403105042503104c45031070300300190000d42408c060001c449000100c080c100f0b0a1320b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 13840321 1250 13839071 13839083
    0x406020405061c0b060a08010e0702030d050c03060102010e0f0a0609061805060114040b011e09080303070c050f03040b040611010b030a060b0102010c0c0203070612140a02091302040f0308090607 85
    0x43ca03902c010300c0d00059031071110100818500308055829003028025100c0c10502a02c0b8400300c0d0342090302c0b2034480c28004101710114030007042400003542035030144600551307403003a00070f460303003442000682940e54030300d01c0140716400a0030b040c00400b0002a14014276070041c00c0040c070761409090460103003000100c944800c0302110840c104026000416034102c43d2080361550703076003405004101c191004c01000e00d0001d102c144e803091854461100400c1008480e0909522880e6075110490654204403448004940c0c00540d0ba000c0c031800740302c910404c001d41005549441d00313011041056024a02540040100f1508403080011096101ba090030b04000c04841c100c40d0380f443e0120150526644c418015428183d40b549281c0c021000401380d81e07030043c05042d45c02d00f0300c1012501000e05400a00a09460f80007a07184044d40400d01030003403c6a00c009a034641c15602404400e00c0007240442d0100d10400013001001c42d010020001d80707500402c0241d071200343d072000403c2401895005400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 13841571 1250 13840321 13840327
    0x10020906090d050c010f080105060f030604090f031805060403051b0a03140303040201090915090506030712050703021005030702070b0d061e0810090b0408030403020106120305030702100204080c09040602040506 92
    0x30302400013000440380304242d03076041c20070001160032294000203203d002e030001000e0007800740d21035064020f0343c1e000c0c0c030140c0009019070362034454201800d5502070550119020084040c08280c503d0400009018252030140c83c2624642e681a070301c003201d2560030000d0f600d0802284107640c0b114402402150400c603a841d8500700441c0c5e41d0b403254802e60301280801e0710200d00241d129054064010144843d403c1d501b8900c1c81c00d81410050240206615130500443c0c00c0842d0005210100c800c2040c0103000412a407811032050081e5900321909100038400184104607020703a002460105841408034420b0f00c51003111090006440343d500880d02600f0f0400410380e0000f01d0104000840e0029411180c01103948040c0100f1983c904e00040c140481100015000ca402d0100854005100384000120507980e0188656100054402100000c0000050102e4990b042041d144000c070070f008114545842d1a0004c1e69410300106060b029140b004009030a1160f6039042d24001c190281c1788a527 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 13842821 1250 13841571 13841573
    0x5030405030d05040e010906050105070609030e0303040905060f01020c0901060c0305070c06050d06050906030307020415050306071806080f040204050405100c0201021201090203010e010302191526070210020906090d 94
    0xf16070030a0041842c0d80c1c41c840c000241c0000b0130b010300000c60788180c441e81d140940584613103000d054007180940a001d0b58139000c03c0759881c204018001895002800552414808101310700640d1401010f0304661209007009002c1c0d440c1c1c14a103045404034108080303884100d260a541c3e9000e0004041c010548400e800031781c0680100c010400c404488800b0006071703868100700800c1c51016901a0b4256000703005000050800c0ea02c1402c07240040f010540d94181e9650000b454202d046030030500040301c0e032203019001403c82c8044005041107042642c03042c54501070760307014140010000307442a510350012a044c400c0500020001400c00d050a20404200c030502a000c2e510501c804660b011041c0000980755030b445c402c0e01d042e1072000303081d030003641d29503001c00c0200c100420320360b19021280c0340300082e070442183c4000714032402500c2c0c1810900328298200703014000c0034a0350041c80f104c04204184a0360106d4809000103003414016118042d1402181080c002c1100c030b180c0140b0b03e010220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 13844071 1250 13842821 13842827
    0x606030b03060604090302190c050306070c1401050c030a1107050a03020d110609030315060d020d09060c0c15180b0901050405121303020d02060f0d05040302060601020f0604020d05030405030d 84
    0x20311041000e400b210100e854400901c0212100600007a00680000b00f912110354a05012201c140380594407000000351100f00103801d18906980b00303004070705007030740701002c00030240581c2e0310703280c0b0795402000310b4030744900110340034400204114085079403680e1480307441310f41c80d054429484d0000e04990302c6400c0da190196035070100c85a007801180f44041225000d19002a100344a005204003031411a12480002e0b0010309141e91650f5100b4170a1101c030031282d905102900131290281c5022405941604086049842d180307074035002c0058020f80f180114401d903002c01a80d60030540009566004100d15500980c9940401020412050288510305605420131070003540114255400e500302510314411307901c152501d413100c082c0d140e1010000f500d4411005a007a80c0050a69031500704e0f03500c004140783d8004034926203002e0383c400500080c5941081100d80c055402e00060114016003000150740c2c01008200a204410000817841003040900075903000f481d026045403100442e1010103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 13845321 1250 13844071 13844081
    0x4050705040b0a0c030809030703090b0307020f0f01051e06010c0209101a030a0b01090e0c1309060303050c0c01090b0702060c010f110d0b060304020a0608060102010b190806010b030603070605070f020301060603 92
    0xd07030001b801c038408207010329008002c64017841d0781a140c4803039240ca0403c128401d504000c0610301503000d100d10000341040e040c008400c3c180c181d60300010707461404030600080321040042c085404039681c010019281d8203d5207402e0001d4045410700f0030781d518a8030078140c61032030b90818412880c50120b00d6022211044c0994001c2204030b10500280008000440d05802d445c440c00e021100240e010070303800c69010340201949002080380d40f00705501d500311071040d00d0980e8401c5000580c00030707141812140a10800c0500c98003480c11706211460100409d803540510040a48a04070010b42c104241c07209512135070141144180c10701442c4000c04119010b5044a40c00c64034450406440c8101450300c6070840e4480c1e9801007066824de4100401141d950030020203030790556503204c000c2e01c6a9610440c41050340e40b5150103280e0300703a0400b6101400e040041c1d0240007203580c1030060061503a0302240d02c0741038441900e4040d8170f602d084d0510892828403418003941652078200082010b9500d5048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 13846571 1250 13845321 13845323
    0x7030201031109030a030516050a140d0201050f0c16020306010e060901061b030807170a0507030b01030603050a03140d06080102070209090c0d0215120f0105030f03070c030204050705040b0a0c 84
    0x10071070305000d00502d03421032040032002d5616411012440380064002c502034a00c804c1c2c1c21815000710171041e5201ca19000215800381d5203100d01003a84114480e041051a1541a140c4000e01990800b03078403030011a280540f52001c000000700d401d0503140405070542e61001e400504651595a441c0b0001404c80e1040d03903410302800300c08001145c814001e000c3c0c01044008914400d400032a1038404491814016045500300302e022031505500483c880355050007849859000900c0b410414400740845014145403070600d42042000c001240c8040703506000650035007040da0000f8090b082d00d09941c403544811041e681c0c07400a0119400c0e00550103070100610a4500d5041c2d40c0318040d0b9140d80766000c0c0d06195102d4100301c240c03401814141c0c03600d10581c500a0500e81805009000908181c40480700e004c90b00c240500104502d01d410040c3d48071110448019500c0c0400503162840304c000b007800040c0c0210344503008101c09a200e541118000d0503007030311040c1c8945020340000c0c80e2880b00c0300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 13847821 1250 13846571 13846577
    0x12020d020915070c060c060e100f05090c0904080d060b0403060218011403060d0c05030d0e03070501050405010f050f040906080a0309050405100302040e030d060807030519110d0203010b04020a0207030201 89
    0x8000d940048203070111003000c0d41264075041300c20725200c0c0468001d10203d000300c62490311140c0b40c603d001003c010070328002040030004940085525500d00131910010003002950b40141c850f80c06070b469517900c581c2c00c5500981066524074100203c800689441d0b03001807610400007d0001c14001c40398050503a009042219012240f00f00f4011503065126501b0480d82c00020808034809190401c03c40c8411841042000d4001d030780c560001c0d00344440e86101e440400c3c081c051410b024a02070152038007401c82420010b003080c4c288000204503054154174042440800509003856003418000c0e603005001a444c240840b9860351200394541d2031541045021801d017142c04645c030700d010b00405100e0010401d0500e0818599000c000c081c0100c540d00e0011408200446040d040e000d01561000d010703814010092945507240c22840d1603038040c441504817907c4500180040d00c941001300d0810401c640741c050115590002a00400c404078403150300510010700d400310b054010954100301d070f000362 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 13848927 1106 13847821 13847839
    0x1804020a0e030d030b030601051008040b040c03050601031202010f0c121107060e06100602031204020f01020f0703030801060905030c06040b0304030c0b0a0b0906060c0a02010e0112020d0209 83
    0x11500000782c0c44a45e09285400c082056030700500050700c900360070303030007644000b03001c004c0140c0010310900c058804075091202500c8480095030b08001030f1603403560740f8600444480c2070581040c000d542091003c40904ca100d00c14070700c03032001c640c90340901c65080e5101c000081116840901495905020703140201d50f4512030503d924109400038146c030b0505d1070302550000c41c50760082c0c04641c4100226085a248855011b40040e4140c1e01000c0b81121a40140d0a1109142c5800b103e48221240013041c9540080060304817410ba441740300390a40c90b01c0902d91071f40400300b03005401210070002040020043c81c01154064064079105075856210340d40c14288500035150b100d011620382c1d40c3d1141e145011140c0e1034010713200300c0e0a60701c1c080810b60515200e10701604043d041c801d182a4024030b0b64020300c2d00d100c8805d07208c0821035139a80114000d000a4108071040d60041640c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 13669071 13848927 := by
  have h0 := BRFrame.cov_init 13669071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13669071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 13669071 ≤ n) (h2 : n < 13848927) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
