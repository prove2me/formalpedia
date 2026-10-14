-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2994
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:21:19.586974+00:00
-- url     : https://prove2.me/submissions/1c644a86-c5f9-4ea2-8790-3e4a8dd0372b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 538309352 ≤ n < 538489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 538310602 1250 538309352 538309363
    0x902090a0221102907030e1c0c0e130506090616020f0318060417010c021902130b030f16080613120c14070306020d1b0203040b0c150c0904050108 64
    0x548100e4120070034020070300080403202240103001303152161900072807220746040d082020701314081442071080c2d1009190404c201801c02c600e85a1254401003503444500b07072844644100d82d00c0014a40201c0c251001d4048071103203058124040311200e05001c441e6990300e640c11650052500342c503c0d00503010901c042028900c1c441c1c29001141040d899030764000f0805c42c81519154400003c000010f041ea822012084610307030401c00000e003200c2c0c001006410031101041e0002c01c48800e241280040c3e84500d011070441842d402e0001e600c80340c07070001c41e1800306c100741d01c6519481a07032100e550364a40c5607018400d03604a01c0c156000c603150342682e82d600300003c910003000c02040398003a001c0d07244205420795609024284002142c50f032903c01c9800c0080d9a002901c030300b50001511010101d00e13000f46c4056203400c0700408200004103600075200d00803800b4000c00c125001840c000015801c004801d54840441380a8150341000c001810a550080002d00c0c06541080700014002c0e40105a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 538311852 1250 538310602 538310611
    0xa1206120209071214070c05060601030b03030a030906142404180f030c480510050702030102030708160201062403020f1617070f03120902090a0221 65
    0x7085055112150f003940d08200228402191544c4d600d1700d03100801e041405035000e12101c0d00c401c0c1000a150414904000b80181418189420403000d46016100001105c1c0702501e1460002507850321441c1c0800501406008258044a0f40c4140300441c080340c2d03240e06000d10300c000000c00c0320030f12105002c10340755202c102c40700c035524800d07800000c108141024480c403172192410b10f0450a859441e800c1d64044030b10503141e08002071800c1841000d814030100300011421150020500d5552280443c43c0014011180907100100c60821801e0181040e40e04036070380140255100d19101c50001d04060341125009c242c28403c150308003070f40f40184214410744000504103107403000403810090080c0003107441281059800c0209081144c58400134010148507045003820011480c289686503540f400e85072482c0d11010420240011400d421004100c0ea050504400c10004120301c1001000710400194014840804200d211501c0c2e41c01885200c2c0005103041750351000e1000d0340c1001d01e0468 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 538313102 1250 538311852 538311859
    0x9091e010e07020a17030711070b1b0f0109030807030f1a150903010501030b0610020303010803041e0902030907031b0e0f0a0207021c12110309010c080c030a12061202 73
    0xa00500000904078011a0301c15494011030707400d000705036180038401302c0c0141c8440d10400d000c0240024164444000088544544000d0000b10300340180071250b03105080816440c00030140c0b40075110b0a09010301c43d80c166400000304421070044c1409800030804a41000000340b41c1143c3c842101e1031803081807003000707412403202070300304050052000c5031060951214100006210784545540e0034050765018600c2041007a1042c10302d802480702180705080e076201950420f2005024802c000800d6800b2031701d540c01109460030602c41c545111010795001100e42d580000100720040200040d8102100c0c402c01801410401002d0011402c040c60300901002031902d0f000b090080314600b0b900d540192034840c00500d000344580c005800c00901c0070741c001520f02148812000d021082c3c0030003c0b0046641003425a82e003441202c29128803800c1c0d071281c14041941881c00030303c0520402da0388995840d200300d07036807007900e04405440180c401c0e0116100900b060008a04070007a504110030391a0b016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 538314352 1250 538313102 538313161
    0x10b0901150305040204020f30071d010903020a0806072015040c050d1415010e07052a03040906051917030d02040306050601021c0e040207110909030909 67
    0x19003040b005000007a00507a8016028040c0141102060000b0440403803264155031008406c83d00c46800e503c0c1d00090b011481c0d6000701004003c54201c48811660303003c0700d588102c200c4104005a0392070015801c0a50042c0a08002180703850300080c881e4002c0d00c454441c0d00f01e140b40913450010700101e041000000380c00680f458a686403070118003d800601c11049525003a49450202e9001460f00c1c2090359401c0981c411442907031014001c0710800c00d2025a80d10140d81401901e10000720b0181030b480400c072000403240d0702001000f0104014480300b141c44030204008920055590b0070500031202254901040080d607072800540e03240e82e00d0480c400103c0c000d1316224803000c00303c29210440a0740d002c100301c1d4000991480c03000f00051071140d4000a040d08240b000286494125801c44030321300542c1504100c007640005c14410b0501c2c080300d0250fa030b00414030704443c1c00001c0c942455000400b08092020707a04021018002100c000e40340c0364060ba0350031403080000b486580c0158050310700e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 538315602 1250 538314352 538314389
    0x9061503201e0102011b21050c031302011707110c090114100c1e11030d021c030b03060907030308070203030708070c0611070f110a0803120403141209010b0901 70
    0x40c80305408038075805000001e0402041c4d00b03125040d0300c0c581b101000055226841e00302c1242c00c039540300301000300307a10100110714000b0305001c44d03440043c00c2000032070100f00350300046a10407503035189000f0400101a185080c101009410f945845103424101d0140c080c2c0c0807181d05207885114100d40c0c20ba5021141c64080320180203140e03119138185e5040000248a01c0b01244c06941861000c0211146c0d001455075241405052011000000c0c1d22030b80001501004050340040e12545415108203044000070920760194000e0041001c515014001d1300c0412103001c0c8003140740c078210f038000c1d01d41201079903401c402240ca0748022591a0081014207011640c014072408008580e644582400107802d00300048013030b5550059041110b00580580c03100d010003034803021440c0e04081c1039035105401410131800c0c503203901031074942d460341c100344034001070601d072080d00c2e66131502685203225650780401e8019a082280125400c003455800d14440e20b00505002020760704841f481e65000d50041c0c01d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 538316852 1250 538315602 538315639
    0x50732040509190308060405060f010512070504050a03060209180f010326041503060f120620030103050d030c09030b0105061b160303080105090411060d0906150320 72
    0x10b00348060310311850121840f018450f0444001440c084d84890100f0328140c0e0400080d03820090030300d4021a80c1034008a0280d03080b40c2a038070b43c1c40310144081c1050307540c1c54007100c450117658410f550180d0341c918000103001041c0d000f46024a000d40b0f000c0f110255204129092100944030003081411500041010520501641c1180001c2c0203484151201c1009510281e030865040081c500b10402005000c1c1d58051140c000244802450103203114505030070f803010311041c0ea00250940b529035011030050111840844448012409540d8503940c480c14003035643e02d500240440424075100384440c00b41c1c020081d40702180e5004064220a0b802c1409122454201421b50809405106200d2508880a0016800c00c503d0344000b0000a450343c10000c012a05c10f03070015010355603a10134800442c1022403e826140b10551341259134240041c09140140400d0344080c10151070001a48805071202c1c9040d02102e02440d07014003030402c5e4440c5000780144502d0030715030103842001e81e801e000a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 538318102 1250 538316852 538316861
    0x324230f03071815090e060f01150e0103021303030903151103010311011206141836070e0a0c1e081b070501020c0706020a05030d15090905073204 64
    0x14041e03c010074200140721182142c0c201c1504504615500e42d40311074010042042060391203a4500000011940752a02c07402d04980034a401c13400300b048800b0741e800a40d00139011241e88050301c2e281150803503920306000f0b2403007050f4001100e80480c091140380000e244c5000749418404008003e616503442e69071000341c0702080d140c1090510101150304040c0014610566000300281e001e400b00301d05c00c220400895860042980f00503060b130754244a000c1c0b04401074413400c4070001d0700000e44200c09a00d5201078061036803031058944664031020504030801442c49008001a5106000346002d1345015689415080340030600003c0040007000d01c1d030712440002da0401441c111040e0b050f20f03d660840495031040bc400d559903900002c4641000500300100c0c0000d181c0c91000d0f040c203480c96034a007901c91241e010881290303904ca40d9812084101e1119060041541c054100543c207854580030351075078064030130f60351b090b00019100c0b211054016814a01b4046d420854566480584200030041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 538319352 1250 538318102 538318139
    0x120f0d0641040509012007200619230711220e150f010e0106080403020705040615030b010f09090510051c050c100c030324230f0307 58
    0x45001c400603885464500c1014000c0204000200c0c03980902c085080c011980044203071440d820400c82c040c0031883c00301864401d89800401c5500c144110000116280100360507440b10040030315418000ca504408403009a11b084148000302000c1c0100544031070042d924003070322240024400201c03a181c29003040e6406603442d80004000d145643c41142180c036401899400d680c0031080260400400c40c1d6055842303290700010010560508281e02e245030018800c4030180000701d03000c501094024070041010b050054820085641d80d0940f490b0300003051242e11000c24038140030315045500c1000c01070304d4001162210909240b62041c40402004014440069a2100c03100412150748840003072190003221291a03040e0021401c10504084001410501c5141845410603a035500714a0444906802d0b0074001900c0b04405581c41700340350342c4030219500310300c42c98020440c0d00c00b0164981c1c0c2484503030508029800030f8400d2106000c032041340568150300403081080481381c91030402616 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 538320602 1250 538319352 538319459
    0x180b0a030c14030928050703150612080405100f05090f0414072607020a03050a20030c0f16030602070f0b09010501061704150509120f0d06 61
    0x1010780c880011185800913540d44500381c203d40d070010038003810f01d002c415000300c2c050b00c44d00f254105e580d00c1d0b590354002031100800d00fa24078400c40c0207039030095025100500f02e800c2a040303000664034200841d9070050050f10b02c55080e0051141d055445a680c00030400126112240340c4480a001c002440606181c19580149c403880d082140003640500e0324003681a54035901000c0340484801c003000400d42e00f41c030440241d66010800740035070009800324065010f007005507480307409a40c11034003c0081b40c2c4030508205000c45a03021084000300525041030703942c054410000010059075168580243d000d00ca92440312000d10100c1c07100c0c0d0040101030b101c1c1b006a4110700d1959a0f040400004451007006a59907200421425070040c992440459601c01d5002c040d2a09a5500c21704001c00700d00d00e002241c1d20030001c1c100140030880c0c8903a240c0742c0c002c0e45132180b034403020001282c0d114420414880c0c0c200140060401c07104d03410760240c501291400d00e1245980d038644101c0d84098144901e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 538321852 1250 538320602 538320617
    0x102060708090a170301091103130f02121f0608162c0901090b060907080f04080d0e010e0715020a03030c0504030611030603010b0a08211216180b0a030c 67
    0x1d2240d5420b01611140b40030f50070703186e42c90180064215110b5610080c03c4120030020003080d50070250344200d6003540311100452082090022031404c1a1607691070617940b0800742c1241440f444901c40b1000c01c00d07410740c140305030341d00c4004154555a401484000c40080a0406d00111a070341001c5046261000440d40b6061400030080c8e007207181c2581d02d2005659100161414003001003800c035842401650341c0141410140030003003207840005d0005016180040200c0c08100d103104c03c0315003030503889906201c07030724041c406a8020103040852010340c1c482c1400000b440f0108003420201c03690290080d00050407592002e90282c6107102000e0304100d401c020100002e1481e104e02000100d0a12945440c2c0c42c01009041c02c403200f0404092081000603400c000d11140000c0c4580d0301840840c03a030252500d900702d0841140107480144100740e003078004104a5210030804a140210b159a84500d201e440c604241d00940007030007a40c00c880810072984000f240242c000110f540c0c602c0c41c4c07500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 538323102 1250 538321852 538321873
    0x506030916030b070215010e060609010311030a060e06030d020319030e2d060c1b0712060b030d080f13032003090a060203090303040306090c08030403030905011d010206070809 77
    0x708400466002110650445400c3c0041603604020b82c41e0f581d40300100c070318442d5051030904404200000c02d114407038500080d0410259120390000c20303141c200c0c2414503881e401e2200700c200c0500818001c6804030501e0b100080c00d245000215031040c4886a0061441d06202460042c00c2504203070040e42816181c0b4106803107100c0c01c0103060b04ac40d0000c000710001c9418005080d00742c4455503000052a030009041c400034070500030464101201c41001c04000cac50008241d2030920740b89a0011000e440d02c080d05409221480e0064003400740101c094608100342042e0648000005469003c40301180781c000860314642c080318040c1c42d80c000c0c10080001032000c09000817510706c1c1d1000024541001c210704149041800c0b40350081c2ca11030029608200f110380c00300c0d81da4020351001810300c603158400d003024071842180200290549005507a07407103450303060203458801346109582c0000d001e250b000001020b00407141142c0d8205901410030f903164005d048410b050f018014040300c2c00303000c540703c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 538324352 1250 538323102 538323133
    0x90206031f1a070201260721020c010903090e010b0412170309010905010c0e03030d0b0604150504050108010e04050604021012020a0c150509120d06050d03021b030f030405060309 78
    0x5298260418041c2c5544041a20006207803000305084070050202613225038100d13100c040d60465109082e460021a01d880510307000401240e1082d0300d0310003030b100050901c810201900607002aa0180d11008012035458214508807102403180c1c821003003060001707002e01c042d0041490501c6000396190a00c02110300700800c6039a00136110724080e0703903440c0388140400c1028064901900082d04001c6030441400d00442c3e1240715650b942d0450303d40c0d5460907507055a4240c10340340682140c142d41d24082d0f0f001c000c0540654007501402e07002c00c24400c000280761181030107851090303078040d0150441c0c0d140d03075090100781000d0800d81400c0c00103040c0050f07010010351000d80203820031a6160b0461902e6805e0005203000e80c451011082d6007000100190000001501e04001e89183c0c40d5035502c40c20000500001c1119410081d40300c034a401d8060181a40040d0002c990082c0e02034410300d203010b5004140d40c0e2192074441700440c0d00705210801c4240b404001540d407009101d0291160442030a011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 538325602 1250 538324352 538324379
    0x30311090a090509010506030d05340b040b01122a0e1003020a12050a140a0807060c080a1401090213090c0507150203150d0201170903030105100201090206031f 70
    0x40e1202e507407502006405a070074055a5000740040d40504a50041d042d002086403123000f1218000b280ca81032070001400d6000025180d4203000d1103101c181c580301d4500500410401d48054aa0755036140c00460304410b6a680c440840364040425181ca002040c480584851090705000d144440c0070000603a00d1040d00d51b8a2144140303100d11480a4210300c100032000c6090b421036447c0411401650001078000110811035641041e04507454101c0b040d051032800b03502c0c000082042d600030446004011194000b91169001c507118440e880e40e8004414003102e1042004100c0d81d038172200100f0804560368000e081080841080c2c854140e181c84004c4207885005504000103900041c0c0c040910140da0340f80811102030840542c550304110352042d54a103400c280240c03103081d6042008045a0044045000500f41e14210111a15100b100c40344c49800920944d03000c0c425400b02c40420901c10301c01c507400590300402e05421038880144001da0702401d8a03411310480b01071840410345180c007048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 538326852 1250 538325602 538325609
    0xb0c09040905010f0e03070b0f09210d06060203120a050601022107020103060b03090a030f050d0e0d08060a03030203030f0601030b12030310051206040609060f0c0c12020c0a03030311090a 82
    0x49404400200305208485c403581e5031074a15001480350f00d00284c0b81580454020320f1f005d03200d4100c1d486503907d0f542440340150b0310800f5802c64031503080898900a01900d511620b0382010001c9540e107a100ba6141e100d00c4611842c4c0ca5011000251840c0e180d900641d003100040c130443d880c040c452040140c0401200035200200740000c02c92104640e8107004481c040c09542c48101e0840c00c2000010b581c0790207000f03000f001d00a40d040720031072181c4200192030030000b403c40140a030401d20030645488080398420800022029000500b80713061005015003113aa1660045140d90358000087c07040c0280604414109920f80c0000c1115a49102c43c04c030080b8506800f83d0b58138100449205c12403602e0b84d0006010780718079031030049000d00c00306195512a8000ea400700b440a01481c042c002008081c40210000d442c12400040055220003880005442402010303c2c0004069040c5d82d40d0002000c0168821091181400085d110303170880100800e54203200c0b0b0918600c000040e4462141c1d41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 538328102 1250 538326852 538326863
    0x90f07060519020d02030a0521010902030a0b1905090c13081f140703090309150903060f090b0c0c030f0418200a0513031203140a0e07030b0c090409 65
    0x1072000c2e10503450045241e00d61981d000070300c20400e40c0400030b034982c0035040f899001d02c18045110b09450207034801e55180c01102c1d503101800c03903840d10b00100c02174006660b00d04c001890130303c0c00d4010341801d03007101c1010000c085908142601c1c0c0340c04c0240500f40204849980d54052028104400d500300282007d80b4014019000c9001d07040700060385004040d50030341210b8102118048a00c50310042e46401c4081450042804011400c0958000d40c180e07100c91507621744070302d002191036808401101038a10880c41403003010640c4100c14243d070541c20014010034115070115040401c40300080c000341410340b0903241000c1000c8a005105e411640c054015001b00300882d6210706002d2143d48401284041c8038081c500d040d0001803124002d00c11038200744900040d01503a05c1100c0c2d8a1000250780c0444840492807031094014041c1c51602814141001401e02140e000603003070040c80c3d04a40740c90300800d00d141c5141c840c41d041c00c0b00542465441042085260120344481c018010305034040e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 538329352 1250 538328102 538328107
    0xd080c2e0902010e0d05012906030103081602120106180b0303030c0a0c050312070e120d08060604080604081308030a080712020d050f01180c0e060706020f070f0515040812090f070605 80
    0xb0f02016801d0b90000100c0705a113042d648c0c1c160954a40c0142c1e03054981144007141c0701d869540754013041c50034602d0f01039880170301c0c8001240104030541150094520744082c410304110385440e004103540e140c7c5509035041e0024000079980c1d81c07401001d031110901914010300e0303140054480034115405001003010410b40001006003a607080030000c42664410365004900d244200030043d2202e03031440c001c1d000c22810030003080c01d80e81c1e000143c9019110388003d8650500b064030303184c49030754420700d9050381c1d5018280d00010038500100c04c2d02c00a9200c0c0e00c446086030344050044038190b81c2410400c0c10030303500f0301400080c44694421240b00f28901480b842665040a204969814040141c0c03541035040c85420515107500051804540c50261507080d110342c854500030010b4014290010032158004c80c244050001034085480b43c00c1c003403426030f031341507054014040050b070007214050320281c410040d19140b081005107590f408081001500d6090780c1c2d07203450300c0c14218a03600010000e60003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 538330602 1250 538329352 538329371
    0x5120f09011707120b220f06090204030b0109020d060b030c0a020f0601140d17130918020d20030316030206010e0708240d080c2e0902010e0d0501 64
    0x10020b9102d80d40212000c1d20010301e8201c0c00144542000081000c840740c480000d6031440c4c680350840034440c411038104400c42c46480c02c10b44000c003012103842c0366080c144200090605a07910854003501d400a40c5121503078289103008000e540a000344052155944400140501403e0090340c0a0f0340c010043c5c0d9520381d240c09000307140a02810454817541c000e41c004122014040442e03500240c4155160003c02115050011100e03c941c8241c1c2e40d60100010940094961200200140d0703996a900708110315a91f8010284120303080c1d8029040340d441d244601c08601131081b500142100000040c409840200c080b90441d0012000c80325170301131407601d110406130144222809005041d00200d00351404280051050030085c1c24404100b0704a0112110780300d00100305103c02d0405400e441802413146403100c00b0754840070044446d03000b0010310350184400c1c83e10401c20112644000404001c401d940b074002440746980481c184100002504016152103c4c15144136002c0d800006e2031284 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 538331852 1250 538330602 538330607
    0x20d060e060612030405010f0c0506011d0714090105160210181d0115020304092406020c030c060903150a0905010b0a06020d08070e0612180307020303041205120f0901 73
    0x41c050502441852148603004040400200380c1c1c00300c078401d29241c00111003551007a1406564000c1c080d04602840c0008140c51804201d0320421703d144000b070001694605000f100d5210040a00d0310082c2d108018440070b9600c1900a41002100407150555040f0141c4c009002c2c2d00c6c5450041d0040f80710700b8200c504d1011141c81c402c0082c407000c0341c1740250b043d085c21040d12010050051000000ea01d9251681492080065030003074042c410082200c289107044064010018800c01d001071000c0c00d07004942144081501030b130008000d001400c0750b5000d0340810850741c2010207000e405216085100c034004032064180d030b0083c80c2d00240020003000e01c0c10603a0a64840c1c102c158000c039010b200c200403d03503000450a4050740186030821041d180c0107030848503000003402c0681d004801203605080011030413011381c0210503403148642902c414ac101652030f80207540020390f0540007031008112070541e0a16088040744100c0c00e0f2111216000700c02007030360f00304401d0140c2062010030356221030758 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 538333102 1250 538331852 538331863
    0xa05070905040e010c110f03070b1302030304090b031c0f080916091e090b0f060a0504050703020307020c01020714040e010609051816030b060f0f040e01020919030b0403110a020d060e 80
    0x210304000d8440c3c41c43d121211fa07035034401d10100401d83d80c103c000260016240c860460748a56000b416070380d40c1e650700c4180da0060a92800a03e00c2400780c2040404800d0b211041079080702510749450301d0720307490042c0640762868001c0c51a5014080c050441e07403618003000d102d40140004081c0018800c5c12088015510080780c1c4803122150300d03000e0043d011603040d801b1a40c0c000020144000c1650340c4001045000c0c0450344103d03005400d15050140031a015000f0758840d1805030f0881c0c058000f107200480e5201c3d034a1044011804115034040b0b00c9003019000322800c444000700200e080790f40c03039100c44120740c0120340f00100000210019244500c0134000c88501515504452242c039083d40c036282a40180900f40a20070352004001040c0b54682007048115032400070001c0085403081d482d081c2c041d500203200184189601a2000c440d5100b581c00c1e5020b5a42040106110f69150b80c0c003a682d1200f8003c1380c3d007031031040c801888016601c40d6506003003c0d2080c5400706081c0c00052100307240c40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 538334352 1250 538333102 538333127
    0x10121b090f1d06120106080d27180903090f060503061906020618190b01081002040317070c0b13030c090507020d050d0f18140a0503030a05070905040e010c 68
    0x101c00802c1e02c08089030034400710b03000202210003540090301000350302d0040602d94000c2d150707406001d02411300d880d0008030205120748068940d09208046070252101d01505019031086407581010050403081c2d2548280c040910a08245009644604811885410651014000500c00002c01640c0c1c1001c0d28444640300f07240c03c1c0c1c4003c0d50300782500a51202c1000303207900450140c00780d1500381008d0401203040502d00b2040840700c01c11850421113911942402481c40314413803100000c00c154120303c01c95003165080641003005803c460742a025903070140300291541001242c001c0b8050342010700500e0610548515003090a10398540a490700f14681d00240d460340c6010204130280d50049001c7e00c0e4084d41d440c00302d545290103808000100011442c4040d00e514084145890810038840c1080b514020ba21445100ca80c1c954641c0d590040306a00038820f410070b001064400003d904480e0700038240b400c1c0b1054064440c4049401c5500e03140300d8a100d40e45449000d06240c2d0081e1800900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 538335602 1250 538334352 538334369
    0x603050a1d0f160e070807032c0c010c03140f131d150d0201031e020d0605030c040606170601020307080712081f0315060915030501110910121b090f 65
    0xc2d43c601500e800341c1306401400c2034140550040010341c1180309501808031194404803ca0b0000d048200450a241c010781c0360780c042c0d01c103e840c100c4056000703048440b4000d9040d5203a6a00a003605241c1405402203d000c103035041050264010780c9180040c85070241400c0341d01c0e0100b8400800ca95040310402070040e580701c08003640a061a921a08031b24800d980d0207090100703282124280494039002d50107074200c0110301c085115804048150040001c44a0440c1110580c400410800007210094480d41010410442c100d4252225000c2e03055440b0805005032800d1060b1900c58000b03a5021131800c80d841044e880c0c6240d10160014111500070240103030070311400031a4241040d0100c11404041d1000e44251004041c08485c0c0d000300000e0302034450b01b407100c40071080000410542a00086605509041d4589903400d180030990340140c2c00184036054030700307c2c0b10050301d6a04030380611803000c54559000704110000c82126481c16903443d43d41d410340624008050301100f8103038102c2c60b174 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 538336852 1250 538335602 538335643
    0x307050f03070303050c0f18010c060e0c031011030103120311030a02040315060501050a03020706180c03030909110909191104140d023010050709060203070c0603050a1d0f 75
    0x112047d01030a07200b08490640c1301da0f480b1040200143ca8200c04070350010401800c1050a81c0f40b00b0300800e0112400d00c05070100d954100a0411400a4960340360318110030035070900040011800005c901218282981800103074014141c0c480c49082d4030840d00c280e410303500001e04004203e10003108a4030b140504004001701c0c0c0c20403000030941d220f070300c154004241c5c0215680e000d0098980c4403501241d44080001c50480d050314088030ba1074001c0c40181c002c240c182c2400203e901150260426240c0401030240c989030050007000445040501240300c8a0400d805601950744c20f8402c2d900b40d2100e1346c04a81d00c13146408000f0134001032480759980a0f5a056203e140161540b01e0f80c0e6203810986582a058510400c849140451000b00307910001d100b048a501e10814865003d136003d2100c0340d0352012010385030401641d0b40d1290b000001c0107001c00040c02c224661007580180d4219000c500d0201c1c5d40b0100c2180801000d0f01540701c400b0640101032181b100243c208905488015a009480b5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 538338102 1250 538336852 538336867
    0x1309050108031801081b0f2b06060f0f23071401060501020102040b040b091c03030911060f031f090c050d0f090209040b070c210824040b030307050f03070303050c 71
    0x16402c1402d800c040c020000709403513001180b820191100c10846c00c007120f0481815000f0301101d6014488c070500d910340b81400100340c0a100c2d02d401a101c1c5800d854982d4807205010040b00c404004120f541c0c0c50303801145103105a94202c40040102d00d0050700c1405000f200103c0c403032300711501e0342c3c8098156031042108114950b560302c2036038229008400c98035107840804012a94000038040100d401c00c0200f640b0004154165001050040c06051b8009026400406001c00c83c400d140c00c0b4007926905000054031030103400c0080a00490340200e22240654610141c0182c5001031405c1c000710b0340104480d0b07006034540c8501705891007081e00c144042142d42e0042008040d0107880a0300f0b08081c8000603510303034000c1040c035203600e07801a4501610002e10889060040c1e2881c0100000391206010a440104a105402042068a030302c403204144400c1000024080200800c0e058003061105201080e000d104000030f4443c042c01031551240540350003801c6a0b80200200d100ca01d040c000300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 538339352 1250 538338102 538338121
    0x307022b080d0b1c0b060301020403080d020a21060602100507270e0c0a02010e060c1803070b0c030405031c08010302043305010f1112130905010803180108 68
    0x84000c107030001030480d580d11031074910b500580102c03444207070002c009222500402d2074502c0980050340c041c0607099404c0e01e80344109802c0c1d10407407001402c0400d0070b00c07810600400c60303801003200c141d2504001c0300081861326102205c00c0c01410b120b00319036031078800300309440d0140045894501950740821192070300840c050a40445c9000d2040d2200c075070090035000448520504000c0d029a1160260a240411001d1a103a1245206030015401e0411495031005d0028010340146090b0052a0808076500e00302c0d840714034000002549486141d0b03000a2040795480103200f103d145c0000385680761309010616240020a14024240d546a8292101300c03903408201103054950480700030079400c665041d50754070135810910210100c0f948000000038000c0e4000500201d400a803500d213172001c10746005584828030040010300b25002811628500840e100003801030320244200c0d280040c1d101c0a50f58111082608a01602c1d800000c21121801c00784091000044e424a080c43c25850513030f0780b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 538340602 1250 538339352 538339429
    0x1b080105042a170d0906080f04060e03040302120a0b07050f18010c12120b150301090e01090c030303091a2502120a050304060605040501150807120608030702 69
    0x441c1d181081d24103601d030005445520a00060102c0780400d8904200403101d1a100c0441c4c5045130041040340c8400079100b40100c0f4018429400310402c010140d4860b168203000d002003809400150204003c00310051355104c41c003c4480307a903500100f02e1096507192160240d50041e200800b070000c24030841c1480c4d494903003200c11010b110111b41080100c03000041e607100f8100c203c001d180000510520740407a0340180e40c0c10b03103000c00100034040c51420f030040c441c22145580800a03291782c2040148800c25098021141c844224000020410740c07513100c1c2c1103040001e4000b10f0003e605c07140d4100038086034080e42881817500c1c40400d4514104025180301505000719440165101d151000b180d203030007441a0350800c0d005068550751550405002402c1758012182119074614152010881e400c02e407003800d060341c10402660000c1c0c42c00f00415a5103c800805440401040b00485155050b0314081c0c00002c01d4950000d549505080c0304001c3c6001c075041c40c40d01e8444201402107a2180403500c13 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 538341852 1250 538340602 538340633
    0xa050301081b03060415090c030f0605070e010f030e0a02042d050c03070f09080f0d1407051f0609110301030201020d0e1c050312011202013513050a1b08010504 70
    0x1400030036000c129103400090b143c0d415014103410780c404400401d215412b1945a0039510071901004255115030701601c0b150203141c5c0950016210841054145000340d110500642c10302c001c0b990642d401e03600140565203000715101608040d4410701d0039010b40707903400c17854116140400b03100b240f07040d510130348503800001e2582d0200002c0e20009420a402045414041c10502068511015120410a035290008441e840020f103011850b400c1c9554800242c40340301d42e000c7c0c0079050101443c00b60100240c0020014800155182000039140700d00d8459017840c01c0358080b0300c54507507142d80006070401c015000f1903418481007520740c1d001d42d0780f592200d11282d070713041e82d045410103140d050052660040038900d000ca5441e0b0740011981c1c2e503100081021680c400d17600c1001418034440c81e0750403a90000003a541c20002d0100c9900401e0107104110f600007580065201400915110b4610300740d91580243c07400140c1e024005800390b480702c181d02c040c0500400a000f6410982e8803200071528440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 538343102 1250 538341852 538341863
    0xc070f0305070f1a09120604050105061e10141303030903060501051e0616020a260706080f04110405040b01060305060a050f040e032a0709140a0f020f0a050301081b030604 75
    0x401704504c3c2e0301d40305a000050819800c81c0c0040c9058030300780d4020441500c0440c401c1d80d90720080c1d201281464040c84480e0b0000d0040c4511441c0c8150035200341046003000c02c0341788020f210391107050a0380c044c3c00e00114000d5858800192460038280200c40301030704094010f01611514a9607265402c0d81d640c9100700179503446658100d030700710ba60b03000301c10b00b00020b500c54440c41c400680346200000b110144900d2003105885503826540807903680c070303180c403e81c0d003c5051600000d80000200d000c7d6a446800f41c2491603030880c288001070700319442250125031900f0002d005103c0303141e00d8419036501201c2a5407420409042a001411608645c50703c0e511560f00d61011802c600018016146801c154011101c001c2d2104481804d00e004c908003506003031700c202c0c0000110b003003460041050008140503201540d40311030014001401030340c075a140180e9002c102102e440305800000349094070311360391031549a50401d55103d00781003007040c029188000160013805690b0b00030518541295001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 538344352 1250 538343102 538343107
    0x190f26040c090906150b090907140d02040e0a06050f060909040602120405100c0e090f04020114160201030f050108151e070807080604090c1a0c070f0305070f1a 70
    0x914010316107880680081c202d640c24007001104112640e0007002e10802d69552509920303031981c42400c41d5020791f00302c1d543d100d03400e0404994218080d5140f203810044130035285d0300c0c103002d1803004420b90307001380e04c116440b045000030488080820b1150790003410080b00d200c081d0400e01c4001640c5400f03a400c80c035208442c00300c0031904006c11907044803006681c0820000c620306d480d09149466a50340500c6001840c1050049516140b05030941400d01200600162840e01e03070307807000a10f61200400032070520103c8070f6024000402e4401400d2524400551401c0c800800c0c0b000409a400d03011125543c0d03400c190061002080200d0010400b016440090f500e40e5559208040c0b40100f0030b203134408500000c000d11a400380d0041035288280c290361684101070300d0300310a2000300d13030a90001400c04807a04200740321481100300c1c110404208002e1007402c01854240ea82c2c01c08142c1d030301c041c09520380c002003082040f03001e03c06403009014109920b2032051a1a1081c0660748103016001a0b0341d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 538345602 1250 538344352 538344361
    0x71e0e03070902161506050a14100c0201020c0301140105030c01050c03030c0a050f0705030306120d09060e030a05070806270303130825061b0512100506190f26 70
    0x44c044d07918140c030380200c0040c41c10382946440c10001c200b0340c05440e0090b282414042020641154070754800607021b4034110003941d10600407545040305a000728114051644003040a590034010185c00c0d01d064000590b403945001c080514010326480300e10b05002083c81440e940500100c244da074040c0e01d05140c25642e18424008491911914171243c11443c00801c9003418000d00001842c400c55054948118030904460b125035195256101c00002400518050114601c1031605002140c0c3c00340458442d20056a1031608040b441d401c01c4105600c0841003042c0c0381d125110400e40e034288001100b0f102403004072001d4403444000c021402c5180c00b13034080c500700310400088455800c82c0701c820010720030b030312081d01903e007024803004d0301e4280c1401041c01d148198904640707000c1071181c03075aa10380440300c3c00c5440b032824018200072803070309128000034180d201c0744002c04110064600c5180080c0100b040600380107020740c064400c0101400039401401070800c00a542d5002400c071a6145948 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 538346852 1250 538345602 538345627
    0x20118060b031501090f0501210611130b0d1a0a03030e0d1a10092702030712050607030c081320040f020c01181707060204030209071e0e03070902 64
    0x42402003c0c800c82a5180005200380d40d950040c01440708039101404984d99610f52942040300040c8151440124000510000b403c6039101540c07c500d40c0309098109024032540c4400c00560b50302c5061880300014840c0205841c0344110b00e00c1d0110100030600101041003c00d0100400d800020240214099409040d955000810b1440e0340d20820121142100c000d00300e292a0040c0d42000a040b1f2102020030252100d01801c82c1003402003958614200a546850108600001081c2c0c0c2500900b100402d450080b0351112114034081c0c001001c40b070070000c030700070200d5494007542010030400f00f042c0004d6100b100250483e0740c1e007000c0c1491403e109820207070002d00e02c0581c2140d01078507084c0e5040c1c000f004d40e000f0b4810001c0c000001c007c541040c042c0d403131440c02280d1004045015014103100804c003401c0103010b01074080c420060600303460303501040f4070500544000c0c3c0810314803200514481498529415101050b290940798086e00a020aa40340554054140855000b0030380400000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 538348102 1250 538346852 538346863
    0x30415020309030a1a10030b07180305070305030703080f01080601170f0619060f050607031110050a0203010f290901020a0b13170406020304060806150c0106060f020118060b03 77
    0x10001c055400c2007031903117010300c1c40e80106045c90040e840d6132000034404840303221880c42160380240c01c8011550b10020704484403105600800e0744480b6000002c00460700c100550400383d40724200566545820b030501815000c0000c04a4548104400060000200216000c0e0449100800d05c103c0d83c3d040c1c03d406424401802c2032540d0600c201010407845440b204090640956441810000181c9070b502a0350342000301c1c0a6140c101c0c0080205600282c41120382c03c22200f076190a99010241704c484020070343c0d0003901c84203034a58000c401481001010001d00d00140400400c0c400d10620f5141c00341040c5440e5000d1200e00c0c080821210181d074000e000e500c003226400009140103140c8210300500100c09000152400d0f0010010102621010000c03035092f1a5a0703002507050502d0040c003216146030080450790808440015501c24a039804042c0c4500840500003007040303800c09900405040702c401480303045a0410740c01030b140c0780303544d81240985074104030013184502c08503000c64a803a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 538349352 1250 538348102 538348117
    0x1b020a0204020d0f290f0a0506030601030908040b0316080601021b030102210a0b01110601090f200a0f08220f1a0906010509040201120b04060b0d090203070909050304150203 76
    0x840c1801011611000030240c1724031403d0b0700041d0700507003c01c440c060001e500290300388076811192004081c0143c0c0381c0078002d10342c015414034010910284940c0c84a080350802d91080c4031500e0003106124900306042c02151594860346402230702440c20b400002e6031289080210419490f8481052145031029011241c0ca5240e003c41038070703403000040d0b0b504145107040300c4100a00746842c41d0003502d9845000f01204040c4400d00a000ca642450490002012000038044040340d488141c4610700d510415000b81c02ca001d400140c3d2186142100a4401121030740e2060400004008000c030b8194034071021040c900c9070030001140890346150004848100500143c034191400c000165000c40c5201080c9c4600e281d0810b60b500e990341c6034107000741c000d01910000c6c040359082c612500660003960020100c100c00a1001c20000d80d02c4007a0a1a94000b08410b03002a89401e11002503040811843c0e00409142c1805c01c101e14040d25465228001d40c0680380240925403004c1e44030a108200740c0e03011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 538350602 1250 538349352 538349381
    0xf0d02031f121403031308030a0906090f02010f03150603090303060905010b04051c0317041112010f0605060430061104050901082a010507051506041b020a0204020d 72
    0x407070307195440c030021021009402c0380c00a03149080e2296510010080e0b034041c201414a50140003416607500e007181e0402070040080c00d40d66015400032806034010f5490240c022000d24510140a000040c03071011250714600502d42002c1c025001c1480c030039810021130380c0601c0d0001d201c48103441e040b070180040d541f2030340740541048004150641d4400c000d0044480c02c5448010030003501c80600d844c844501d00180203d9103a18001c0410308007409041ea210f40b02d4918440e40e00c416100144600030046d107440c496030365441c5c0b0f800b42d45c00c0070320408018290488070b06060603e410020320346410100c9501d01c0b081d1020308003070662800850a5504164041e10030f000041c3c4100d80d40185800c1403090b68403845482000244682c000700d10490070800004203803181c80a001d800804540c6080007060400808000007000706005000e80b0713001401841c0002e0700c45c1130100421042d10300000d012240b00002c6010000d28a800150721032070300d40d043c0c13805078813151284040b400600100b00d5800070b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 538351852 1250 538350602 538350661
    0x180f02150418020406030e0f030f03150301180c0503151801060e04050313060f0c12090504020a0309210210050a020714010c021516110f0d1d060f0d0203 67
    0xc2c1c0541d981c01400c142ca94942d01000101001c10046035258982d05920076260401c0000c01c403030104c2c0c41d00a5a0100101c1c1701000644070a00c0801d013140e502703003c4012032948400798803040001c1c080360040140f4081740100442d040c00072170100f0b4000040c05044032800d20704082015210b080d00030300010440104070345e0252919003003090b220b03400010440c880203500100403800030301800044503210701540d203280d50706c1c015540310100d562035111485d06000c091078000801d0b03900c1d40001d110900e02650049444899442c00c10a24070701d1100340070112603000720700090980d001900451760040d001c80800c0780e84880481400034400c484020303140103038101005040003c150054088585a542203900791044441c100410300c0c0b003619490405a86d603540340f0413032403040320445041035081060380c00c001e036080c0507507240034216054ac501254144c03429a28890070581070803200241a03d116250070b40420001d0224801e08084414260380400444c01c2c40d181c2d0090110301c6560f0040c000b5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 538353102 1250 538351852 538351889
    0x1d0a05031b060118180204050a0608120a1425080a0e03070b0406050a050f04080c1f020601091e050103060605030714030601150c050109060b04180f021504 68
    0x546a520040d152003401d4000440ca080e02800012968101c8284003903101c1070403508560300000e0701046101c40d514032090445500969030f01d2040c40d002d44004203000a556203041c84860038030030000041d0403501d405010300341c903464001060010452444180541d140e400c407541403845010401c032030841301c0c411b1840760b0401105030010510f41d03007541c59030b6500368084402c0558900190241803070b280b02c00c0c8410000c443c02803010301500c41440c1481828285004071a0740b098225902c83e904c95401140380c000141440d032404d41a10484441c07201101d2412440a1340d1000188580b070051562654440541d044001e607003c44698124020b10003941c3d2414503070040c05140c00380c03a20078054a8400180003401044031034034250044c025205907072a010160030f0900c115104c0c0c40c2402480180c0c0d00c0004c1080c4504904544100790000d080000c074420311085481201441060090031100c410100f42c1031400304135060340c100c1c0c0007610344a00c00c64001e0140926800074000100d501d4580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 538354352 1250 538353102 538353113
    0x50306060909120f12220311030421031106040f2018010519051f090f03080307020d050301030209040b15060a170a02042d0510020d090503010c0504091d0a 68
    0xc0c0041426071220070941d465506490341b003440942c4148003104000c03221440042d0203940c502c02c10704c2008003a2818941d0f6103442d004100c50b51080c0100005203020724408043c3c118050500800c440d00081060386000e645802c800402d41102420b1305164001503000c0700001c43c41121703180406030004010b41c90040c08200902000e0241c188211a15a44c0b4001c011101c1d2414003100e42c000c01c00d8803d940c803200740300700e00c01c0b00b1b440344810020440b40106004030700f80d000100031840b541c1a41c0d9a0b01c1c240e44003c0c18480750710b0403c41004020030040003d80c0d41c0050b107a07001508003101241c0c035110440c1008640a02c4066075400c9103012a41c0b0f114070b60861a00c603408030b16000c0c0040150342c1e181c00715040788100e01942c2d041c424082e45401c454480040c0644501c0030302c0d13030403a420707580390800291026240d2282500603401000c5180c5010b40c0100148020710043d4000d100301c858100000e05203005901945464030355070b29000307180c1c4180700040c0d2800c100f801c081d07601d1b554003400d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 538355602 1250 538354352 538354357
    0x30f1513022710050d05041a07050d0635010b15070204051308071403040b030f010918030801050112021902151003031b0609050d02061503010204050306060909120f 72
    0x103001028440515651942c14151280b842202d8584d80c0e091030000402440c400030200034106840d9007140311082c94501c0b5041002500036070b04e5807030307254540c80c1c2400c505094a80540002545410444812100f5540c0000300c1598507004518a1101c80000c4c8010340107011181e4220344c41700e0b03a400751541d001c01d20300c0145840b41c000e48090015a03241003040b42c880c1825030f002040080c04000d20701c0401e50301000c400d41c0a0840f82500e00e096950101110b0641003038070070340e94041c3d40000401c1581e00034859110915101c9c4080d00000c02c25490140c98114140b0440f07040c05510310104560320141e034103e0300d441c1416060325030000306283c0001d544a0684040340041c0800c82d002c1400304a40003801c40031645c1c5070703960320302c0b5100c050403c85040c108104125141e540b81c200140000e2000d00507000d600d00c1541c0106401d1500c1c80b0218111641f019000d40680d00c10003040c08992070109615a110364180c0329200151550b04030a40f070a02c1619524540170000b1545c0301452140f00c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 538356852 1250 538355602 538355647
    0x2090403082a0a350702030705012307020a0c0e091207050a0c050a12031214040f0309151d1906020a0c090204052206150207150203030f151302 63
    0xd074801d031014800700100f5040031610301d840400da8060344c5155091241901d29500025610603241401c00c40e0759218207680c082c3c0c251143c00000000428160039440016981c04200f03840142401e801d1902c80d210401070b280207003442c81c5404400101c415000708115104185d2207010700303540f0b0b400c9040c00c41d240c4103d06011948055075510010b5245403182100d000d843c0c41041040e102d000f2560103940100302c01c0ca0400d8480e44854001160054409101d84988e00400c015251a142854000c0140c5082e802002c0c0c403040003890f496100f80d000b42c024451240a50540d200150800002058017026a101c07258885000d84049180341d230106018020b80d00c11541464820f0300c46550708141d004601810f504181680f12800150204082c0c00841541d403450000d0840c1d01c9408070000c071800036100c00c002d6423003840e042003c2c1454550352030490245d44051070075070400d06081207815034040c00341d003807151103030004595aa5400b80c0d2242100c0300d9034421551360319103801e1003964000808 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 538358102 1250 538356852 538356857
    0x16080705091e060f060c0c090a051e0402030a02060a0f03050c09011e2a03080603030705120a110102040909030e310f0203070302120a0902090403082a0a 67
    0x188001524100109001e00400c0c0c0b0300c00d54490319909441c0500c200304020059603202142421010030354030b401008042e00c2d030200c00a811144008014003500d46805404d0b008143d14100400c004081d8400f10070800b002d10001080039515180002858003503030740406940700300300140e180000d5030880c00d4a68490242c1d1070034441ea41d02e52a07840024081c030440c86012855524280d0780442d24001c0000c09141107082c0b61103444105500410001400603180703c400c0761840c0c0d8030050640003c071f425444001100210318010880e6075840e204c08400c6045604480701040e22000c0c14001c00b80780901f103804030001c43d1501d94425541d0301403c070580050340890040034840689041150000245c0c40020f48002e010940c1c2c0c04d00c000181003261080001c0039500c46a941400e003840c0001d40c00b41906581c0907880f050141c2d40342000705005002c1c20b42e081c0c500989480107031512111168095054181100c1580e600018081c13084100082001600321505804030040707003143c007078407045035140d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 538359352 1250 538358102 538358113
    0x703060f06050f07380603070b09151615091401051b130902071a0105030d08040602090a1e03060c0203090a0302060d0b2713021c020a081608 62
    0x11001920248503c0f4800002c0c41402c100c08400700e0107a16615044400142007540442040514225180c145003240380c10b2174a80814040305281c03c04c5840b010700746d044085032030020355600050101091541d000c1044101140c422050300d840c0c0c0f0805a0150400d00d400d00c8610303c80382c10030042ca0224411100144000b011030103040c8144903107489901404803000e0701d040c550202c0d60030740e0070610b4400004041c4400204400169002900c03506120345c1c0410b0034a4a10203020384243c01c141c21046c000d5008040103252180d006010700d03081074004000580c3c84059901246d0079100366007083e004083c190030104410038181c4031250403280588403c00a401091004980380c1c0310708950740f030340124080004d00c054035000f401410701650480001552130701d043d000c944164406000000030814001c84902482d0b901e034030047d40802070518505901d15187d0002d0307841d0140011039aa091080e1004804640b40e000c2c0b028003a111446c21100c1854800312014400d140b40d008809890059 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538360602 1250 538359352 538359359
    0x5040302012307081015090807090c052b0515090f010807141f02100b01050f0304030809010e070b0c071406070803250e090f06060315040207020402030703060f 70
    0xb094049092074400c0c0341503007980c440c801c040b144400003030102001c019102d007001590140d00051441d00905640b51400c58514003d130980c1001c06039481150f6450030300700c040b400351760f00c541241c100c400300100b040d60514940710485410655154145003440c5828140820b9020429440c01014002c50b404886a03039603440500d0009001e100300b200c160b208490a00094044a41d815040d08020385803007160303c0c02d4401c0600a031303d40e001180c050f07002114135030300320442402507079036403882801d11034500044107070200740500c0010700c050704001d0f01750041640341c0c8081d080620407042c10300859100c0b5864401900160740f001b04001c843d0f1041600000b9511104800322402c480010100c0741001120741301c03408a5131000340005111000e0008400c003400d000030400001d0401c5959000600c415401406000c00014000180c3d50220004110a50f03545808681e031011282c00e402000408410114010303000b1107000940c00780c000300070042d0b1968554800030441b141d171498074030007568 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538361852 1250 538360602 538360631
    0x50a0b01030b0a060f1710210c140303120108010b010905040e0d0302070c0f031a07031503080904060902030411030d080408121b1204030e33070b04060504030201 71
    0x2241204140c00c9a40403100704085405402801c404102c2e07400c004030a181e5106d8040140b10040716049000744504d40c0504c40000c502c41c48003400d0224019a0103200040e0300c420880710030074460340ba4403d52024000d030982d01d050007502d50b030310700c0c98090089a507101d46401d80a444410758860000d9105000060186003501030b8081c401e08201c05030141c10703a91482200a90b01405040e1007000310b809001445001c030f64101c0f80114018054805034158080b03009a24441c0a460744080504100c1c1c800d50840741c00140e9000c41e5032000c4440e44d142107240c0418043c04080e800143c3d407034070100400c8207000c00c161006080400c100d040e40d00c020303080c0005448603039042d0780c00b5000840a1011504003001c00c0c0ca00760300010310007241c8550100c10703410580c86500522a03003a91510301000d0008050b08104140d4902c0c03821200c1003901d0003e400c1d003020822008149030880b01c90841c0000101040000f21410b00d40c006a4102c0986494107201c0d01604040e10110015868440c1d1240c8029 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538363102 1250 538361852 538361861
    0x9070e03010c030c1d0103090b070f0f0903030f0f02100c0206100b0c030304110f091f081c0c060605030d0908060a060e04081b010e0c0910050303040b16050d03050a0b0103 75
    0x12031544805c40d6411200c90750329031070800c011045060554a9103100c0c00300350303800e003020302c034019640d07400e030348440c00d2a001015155580d200e00c0902059038001c2c00083c2e000921744010103468604540004225081240f802c2807070090f024400d85040092100c030341d03011030320720312900b04140d15824169655070103071018800d066004180f5041400030500040da900c1060381da491000344188071b00303c551000a102d4000507035031070460100f0018003415035103443e2440030080003d43c001e880035084441d2440300281105280c0301c10480c000342c04008000c555848580036080143c1116500b0106c031402500da0311082c060403002d840b410740015048621070081d501a80c070034020511140e1516a640c025940110b2200382d41080d1ba11311203c5048024894400903458510007011201500c40030302c101c0840c060200742440080540a0006450020485044500510803503584009491031842d5083d44030744010824000d48260b460398940c160841400340d1000e02041010b206440c00540885 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538364352 1250 538363102 538363121
    0x6020a11190612020c07060903260a0c0302010f0606170f27030c10020d0f060302090c070f0b010b0403060e0a031e26010f0e04030215040206070209070e03010c03 71
    0x200c807225030070b0258911850400300c0701c4002040140c102030380030644604100c100d801000c0022000103040050016050040700007028041c01150401d03900b1250280510410340c035441480201607a40341018030035030001e000b1682468080021584406006003080100190340b014122440041001303070044d40000c034055a80048281c01d9000c0c41400c4003a1940d46420180c0d55000500040350042400d1082d1140250342840c0166540601e01c500c1c0f04803501c07950740c011440d01d032440c2840140c030703108503880e0032194500c03882e03858550310300c0c0982c84250340d0f071001090b41c1c402c4000050544070240141080e86e01c1004240043c0c04c860100550754408150064005110070840d21588a03a81611a00d400064030340342c6807011000751031085021008900380b40031101c030801000360090b8007030076030f000e041002500380d003905081e2802545d50107c5091240011740403c040340455840400b26031070254050100038591070714170b5015000001085d003440c0294200322516101e503220340f1071980d05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538365602 1250 538364352 538364389
    0x10206090a1e06020d060807091a0d0602160b062b0f230c1305060108041103150a150803131e0f0315060603051603020309010b0a06020a11 61
    0x4a41540b41c681c4803900e035158144401e804080311101040a030300041c400a035070240041251458400d58a2030007480b507004040d40f03031800801d0080c4140e40441030741501c408850b5070003003a1607424000024440c0d84d10710b84403d0744117020343c4100440700350b545100744000c840d00700750070b58540c1070b00d1088000d100100500024103c0d8040028245d0000007000074003a0034005120b090f00340e5847c400b072000f08172124455000c241184141d00e01390a0380030012042400034007031810302900280002c04081c200602d008425031811295031410884104001c0400110001a0030050741d801e00030082060317801c0c5182c404107004146018000200c51081200c40200c034000c2d480c040000d10b41884000d82c102085c0b5800d4000140383d512520134102842c000c030b50070000d83c0d50100e1090202c607459030100c2d01381810b0600708000e800c61100d200485000b5414056501d5841602d02130040c040c0e0303204142e105010400c0440c44950004001d44200c1c400c0b5041e1021000c55400c0200308060902940c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538366852 1250 538365602 538365613
    0x11d0f04020f2107080a05010615050f0d02120711010c0201050705180a0806070323130605070c0b0405030a0e1203042d03080d0f02070218070c0203010207080409050601020609 77
    0x250034070000c22181c4844800c110203560811160f000d00781200342e441409158800303400391050010030321a8070b0081c00241c400c0e44130003030003840c045c120b8013464508a89158020400c100e07840300c2c0d83c04441b4030715260402094945080d90028124405480780d12566601e000988201640144181c5000f00003984407181805006240c0e4860844451100d58004201100004060108100023401030080d61804989080200030407080c0402403100ca01c4a0035500c030a110114070380d08450310324907800001c007041a41d18a041600c002003003181c003c080450312400c000a110b4080040e1100c0c41a40d941c82e10030010040401041e4600f0554108d41900104400c000c041031442e002e00d20f542d070102c03142000f656810495051180207074025900c449002513041d400d03846c0345c03084081c003c00f220030440c24182c040d00400e0010180c610704d020b14030320020119002d28054000d45c04202d600500075981c0712150302d0a00900e4210f403240701800303800c3c8004501c0d503600101d50103204100f002c00800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538368102 1250 538366852 538366879
    0xd060b07031e0e090c090d050a1e0c06050a110a060f11090913060905030c060402090601081608060102070f1d13170d09150b0a15091a12011d0f0402 65
    0x1113040a8840c3c80900010880003c01c0e844004c01502d081c0d02560242583c030b0000e0401920a0700000a10a4046030701c01400001600d034000c0d840c19074010303140c8141c56a440d00340c260303003e146900203000d142c45110303c02e0080000581051145000e805001d00c071768103c03c3d9001c0201c1c00741a0103250b0000304040064128084072130003d104034011280810755003400e0302c0b99410360f03000e510b00c00841d4010a040000750309000103501d07003006081c80c3c1a9094907003a401d04890b4142080303003c0070801ca034400300310180e10030801d241c05412082500303209070381c1d00c071240060600300241c14103e5088180029607080c08a10300c00c25029000f00d0418171500c4040000300c0181c1c089002c9071703520b981e01e81018020460a0f1250300110000100c001480d04600c010840400c2d040d40c4150811120302c035441c0d00316a801250b4600320740071904007945002d03001503048441d00485022604210024000092181080d06048402c0e802d0461101058407895403500c002e48040b9806508150740f40c101c403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538369352 1250 538368102 538368109
    0x30c020d0b040c171b27100b070f0f03170c040906080703030c1203060914012909121906020a0f02160312050910020d0e030604020f060f0d060b07031e0e 67
    0x10340ea0305000615101c812403024003090a20b8801080f101c0d5110906c43c10418850850390010340a4036000010508117942960391541306020342ca002012031000c58006400c0500801b203507210342a01c0411007002c2d01d000c0800204130b403c5072203400c03c0a82081c0e03002402d000701083e01401e498041c0e80d13902d80b860b42da485180d050107889013240f0406540f1013001590940c20300c031340e6010103075401e8070000651404e075a40c810030141640e1140964101821103030701d15004022510196002e50b54072940c0e600b02500d00c0d080552000d0f4031542401d04610103401c000983d802401021100d0312000003d44100f02d0403a92031003a600c1c2140d045003806001c1c404280d5900600001c949c4500c1c8c0540740c40002004162065194000e200c0035a00002c6038031401c6420007820126a8001d030010903041c0f07000c2e00040c40300c030050090140603040c0040c60400805101c021258a41c4403010103010f015924440511168401d007000c0e40061104603d1a8180001452520150398103945810b410184071040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538370602 1250 538369352 538369393
    0x1b041b02030a09060e0f060c070902160c05031527060c03010e010605040812132303100b0d0f11060a0f120629040f0b031e07050d0504030c020d0b040c17 67
    0x30740385100d6148000f507603e14038002011841c0b010b01e41c01c0201061441d0940c54450160046403003600801c0c1803880100c10d100540341c0c865400903000c25040400005246034030102006030507140591020401410041d00003141210030300d00d04401c650707903a07038822980e0303018902072034002d900240e0480c100c401161000e01461110441c0d8000041da6420006040b60515112080107081d10650501207150030300001c42542e6508600b40000b0039110700083c0f5284035154010302d12405042d011050080c0307204803092144e805461591350364205030010b0600e01302c1000b04000101d8490343c09401c0c4e48079000b0310f030455a070480807001e003000ca03072400240c220800703800c20144d400910000136101d052820b0140140010301400796241010304200c08180115048440303003c0094050203001540700007100d4000707102e1900099681c0380c0d0310382126400382e0040f000c1c1d4040303080c41608051241d07500325140070707601c2070104800156031088041401c600b155441845600070240002450b43c1c5401c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538371852 1250 538370602 538370617
    0x14010c0803100b0a0f0f032c10020c0307140c100e0f060f3001030803100b040311130501080714060d06080601081203091b041b02030a09060e0f06 64
    0x40d0b81d041e984903043d8000c603030014108000000c620003283c590441d000030354070701d0100641c80e062041000865904802e00c82455088420595690710013500080910074207103035003c141020340d5540031f410f58031581c039000414240d8050b00460303220070070b4050000702201400405089070700320307204400d41924604100740d41160070182907611040244c0e81c98004103240031400c0c22140e00c411118801c00808449404000741c92808018044266080b0300700c4281100d40c49450f955480d59140b100390080c00d030580c400c100c48a008200071003040301384622102104010703501640460180d64060054032000e100303003071a9410121091060038240b602030410250044d04443c60001810900c1040310000d600003038441d00008014441124148620b0205024007a1000c2c03d608001307007200d454100d101d030025152201d40071010b00070b44841d0005000050b4064203074030b092084007400303034603070780080d1f44036000800703180000c201070f8060540081e0203100640f41015120241040c80103a030300020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538373102 1250 538371852 538371871
    0x3021b0112020304030339080129040b0408010902090601180501050a02030c060112050c012d1403040c050a0504091505040c030f030906030c030b09130602300114010c0803 75
    0x2915087e90351200d100c0c0400340d20000c40c0d0300d00035540c804c58108480b01801060000c000c900c2004118030030b0718550b1035010010340800e0b24100000010f81410794491a805107a08060104000800071419403224003c1c5000b550303c0e4503c0e55a00e4011500c4c090400b0720b0300200e801b4001e040c802544180701504808d511030044900d820503242010b458640b00b43e100d0302c1c1d241f11143d50b20080000602a46001c0c20081c24008411303041d41c0c404c8a005207a040c40440d00121038039031089000c1c8240c0421001540c2611103075a00e040904010b1034020050003001d000b0300300b00e00f0001d20390806220b80c0045036040241201d1202c020000034001d1710002d0310503034040d481141c0120200d05900c0e01541b10368440d072100c0116a14009000d026645880801c60606241404d11300040d10b80c003000a5000d2042100034038060120303d0710350000d00a00000a6425a01c00d06440300500c01d00c2000503a2001341c0017503641d583c1d0306d83e42c03104c15a03140385a540c00120a10098400a10145c0c06541c005c1480d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538374352 1250 538373102 538373111
    0xc1205012607090e0a020a05010302090315061302030106020d090614090405150604061e0309020a031509061a2407140f0a0f0213052e0504050a0903021b01120203040303 74
    0xa0b0816070555503201048085034205c040c80c0310031481d2104481008185c2804c0c1903090902160000303840302040d01c1030701140100900003503d1555644141005101e548204540b6541c481d04025500d0342542405c50225aa14101041e114000c50840c0c83d00100d21441d94503003094001403002805020b010071024080f2400598400c1d43d805c40900040d241c540c0c3e40030501e903807000d0080b61440c0c0c0142c00c2e000b814641290341015071601c122540030340e5044480001c5642c0010074044c0200000200a008545464007040c01d00400c1c80e225510054102c41740d82641960341c40903102e481c18001c0382c441044007045100c0020301c085800401c0b11000009507403807240080000c40c204005807800300c43d80e42030310161600b140f0704a0240c04a40641050412040c030742074211030860040030850460401940300800701e1454140202405404c001d0301c00e20481c2810146440075000d0003070100c001d80102c207105200300c5101c5401c6140940141e5030b00c20303442482070203d002940080c005030209500d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538375602 1250 538374352 538374359
    0x30a0b01050c030406081e060303180303090d03110708010516080903161529040203090102090d0b060111030a05030c0f0f13080607050412081303020307090c1205012607 74
    0x50000c4c02c0100040d4031001000d20b040b40009164120200d108241c1039140d5040c00110340707001080e100700c40000030305004d280402d240081e145020300107200b0340c0203818007003150030544c1c843c00c0e94505064032000ca800c000c5d01d40d4545400c1e40c50894140d20b1042c18a220f0040c0c5078031452400d07800c0303625041900d1811420088241c04010704007030075580c204800b070048080c0c1075580300d407503ca21440c1480d03106074100016040c9003e80b040800030b20a0740c022002c2101a0000c1d0b044a03c0040d004042507081036640c50305400c4104100c40e13550220741d00162000c104200171045410201040e680c2c40e2840d50341c40c400c0342d0680c1180d0810010b21006110300f0b500500150001c080d0324800d0316400101c24038101c07c00c0d14012004110100704a414007080040070240400141107503801414981c880c08481c803c003070100c000c1d80c8043e5143c0704958000800c00310540c44170411001d55503810700307580321001d00d01d020388e070007803180000c3c80b0482140d908000000b11560344010408600b55422581e5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538376852 1250 538375602 538375627
    0x4020d0c1d0114060f0910120c120c020706081303030212270304060c060b0414160f1d040e0c060a090501080603060c070b10051509040c02070506030a0b0105 69
    0x1122010705551442000040c81034003980b02d0381c581c01003022100240303005a60740542e40640508081c0d14090714482c4d1016484074019032022003454050700040101c05403804000f006180110001d20060349031450080815101140c0c00060301d130070b03440b4201c542d2101c86120b074a4023290482a0201503081c88a4090399030006161130082503d0300e42004c0648504070030181148032240b402990b540304100400480e6042024145c543e9000702002905401d20f03c017207006400c80400002c07100b0360102c1040514008440815614800b51351145511503102006a411014030246c510083c1050402e001c410718040d0040e240c080b400070103903407419001e51b01142c0284c0000c10000e000ca41c441e1003c0c0082e581c044100da52100d001c030024001402c0c0084403070041d200d034880160010700100c00050421030918000303001000d001d451084c4201c031501c405102c94000c19012407040307003419040000d45200140315419a003001300301501e15101c032510300c00204009440c070f60500c4820310183d04a00c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538378102 1250 538376852 538376879
    0x3070b04050f190308060108150f0402160b07140c100b010302130b0301060f02070b1806040f030609150c0e01120e0f01021308190318180e010609020c0604020d0c 71
    0x2c0075881442500e003e5141c054100c400051203a410808040104084983e440c1d1034603800c96000d0714200800040040450040d00c02e01005042034212209120100589400c55505c200029030700c10000d95502c040d0042184514480140217a00c002c440c1c3c0340401a0354400d44401c841414010b180600e005034800c0301a0880d40b00941c180307004001000f0b45a0000361810391520244040e103e40b5040140c0b81e01c1c640110352400354040c200c0c1c40b101c200703522464110ba01520492034880a078070b5603407406000ad0107542100719100c0201ca099090241114012040c0140c06074456a140e201000e0044480000182540c0c400d6038860424038014602803010300e000c080030b54000350369016100c0b071482800206034484025a03002501303003013024250b9907845c0c44060389840c20020108150707860b40f0328000c40e5004440c0c6020000e0302d019440703641da4016000803d24030001e0100c41d40e6198030ba8120700440700d44e24203d8102c40c00180051600c03652a025061158a6a0741d1080d225150f00c20190b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538379352 1250 538378102 538378123
    0x60f0123360111071a070f1a0a0b010c050a0b1902072d0213050403090918030206010b03150607021804030206010303181208090a15090e010b040803070b04050f 70
    0x10048480c074090156440010307160b1207901800202240c41c0b034003008060552040d448441c0c0c4c1c010109102c02084141c0001e181003a030040030260a4100103540001201c8056540c0ba114903d8801c5220715540900407500d40c0036044009000c00c048075444110308604020702055180c4412900f5100c490894406440c0160003202860b05401061980c0c201c0e40c0707031a91034808000200503205005036510000c1d0440c0148180c4040350a484a2500b500c1241c5a90007000c0e10500f131041c5440300200100403840f2003030082e800c48450b6640c81d50030584070712040da10020703505420101503182c2d0900e40004c00300284003400c2e0341d44030256070300c9020303100c0c205071401c4005070402e100400a045e8811528640c07404a48507801e0040d01c0c061032610b861400b150f00070803081002c2641051a070300c001e0141c000f851600210407407144070520050a50400d4012202c04034044400407c0402805e0103440076145404000c43c075040b01502c3d1001141d80040c0100e44138804d20045813100300042c03002d002031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538380602 1250 538379352 538379437
    0x2208060a0902150304021c03050d0c1110140c132310050a08070309050c030a0804170f030f070516120303050906090a1101111203060f0123 61
    0x40d42103a01c10040d04a5280c201080005000c4c014400580d461201c11005c0151088889031126644d2a00b5a820300890b0481d0194a00c0e0219102840e50440543c0403071041c82c20a0b21078124003400c1c900c00320740302035074000f404031842c5c030000f810414003038001c0c40d5405e8481030715a6595580c80741c601c00c5000185110440f20500c040c250000d040034045150140c900c0e003841c0381803c03480b1000030110500100010105a200c03c0b8210070700c0418007181c0b00c0c51034080c01b80c440f01300a40c00c000034181e00a1180c0d49003d4100c4c078000c0700000380402d150800c0b03407400000d503161a19016049249800440094803280603800c0382d0500e42d22004d00e25401400c90301c0c1c540c1c1c640030039801d004e01240c10040c94105d86402403002c02080180101d240e50b5119849100c168000208000481e0300a4001440d0b040e00e20403103180340804000742000c2d520545c011280f0b2002820428011501824101c0c81d020005140d005a225000300300340c01782ca182140d24211660441d00455405803038407580d85280d90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538381852 1250 538380602 538380611
    0x609031a371d0111070b041e050a060e0c0a03080717090607060605040b040209061c0e030d02030402100e01020616031b03050f010b03130f0203030d0e0d020f122208060a 74
    0x140c190300703000f41c0b4044c088807290301e0304000c016140c4803a480301c01000184089088200356110702d8141501d0465240c000f4121400001c241c40c008004050952403e0400d100b4070303903103a616180051040091b294465542c504220352075440f040021b80d01165180c8545062108800940710305c0003812986028840109001d031070301e130074842100d4003003100710701860040010b5445a00d0311811603c403d013440d00e8040c00052641c042900401c0c21500c21240d0b03020008a0064a42d000c1e00954051402100e1001070b140c04480e0685181880d2a081c1303000d60400c000144203164040021090300205050108401c0509005000c1d81c0007640c09007804a5510018041d00703080c030b42205400360281c8030f00103103141410151506110207820700200000c0d441401d41003103450500549000743c01041e400d0200d10134903941140c0300c1c0d081315005401032007051006440b04600007074803441d00d20303580f6041c1e142642e0141d600342035113654802d000c1c491543d0000058a80e41c20801c09120722251280040d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538383102 1250 538381852 538381901
    0x40e06030102041e1805010b07080d0b030304061d03010b090403120b091312020c0307050d020103020f071112030315040e150702010506041a031518070609031a37 71
    0x1703d2100b00101405030742403420300184140d01036441121000ca410040c0c01c0d071030f07290050100f00500340110a01d07070980400714001400c0c0390000342d803040201c85d00640094680c0101d05150880705904580e640c0079580001085c0802d004d024110490780743d014010070754420b000d000c280b4000040d0b48401c0a11400c000b0b000a000e081903a103c0c04240c14800b4040c0a030701400001d68508072801043e108078036641d0010700b160f029070f04890002015070403070f0380c6070841402e00402854114010b90700690030300310001204407010048034444e15481c50103909100c0000148401408401c03180f540b0351041520b00c0c88074203000881c0324030806032580042034074600b20b0280000d84290401d400c01c14002040156802e541c0441e5840d158080c01081c100c5d1680c810140382c10f00024900c40074060b0142c0c10020614030703400201d9070107490060725610440100c0340c06241400d2800c56032100c10072845450460b2164050b1010f08803500d007091440211038540a201d4203c0d59008480d040100c0c490100c030f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538384352 1250 538383102 538383119
    0x90503190305070c02091801060801020c060601050720040b090f0604110c1c0e06070302030405010e06090d030e01140c010b090106020a080d020f1312030908070803040e06030102041e 80
    0x100d0a011191070140814200510081c0c00c4070040721000703210f2105200026851100d04200340c0f54008100000e10102d0307a501c408074001e6101d070341400e42c1e44c01007000040b0903501420480390215888088807000d10300301c40d10320a460f80c843c0a082e1f4042d850b1201042d680c0c1c0c0300c401c003e010b07428290141d841d9042000802080b9081c00700710000010782441070002c0c0a402080703a5501540b81c030114030305d000c80c0f504100da10060322600e86074824000310764038060550000160050327401c20303203812180d04001c20411009001e06280b0560054002e840d01000074490455050844018108040154000308583c4043e07044500307940a10380d036074601c800e404d1500c0380100380100018005492100820b44031100548a02140680540c0d000510b05208061007002c40c0c0401e032030070404104494488012108a000340318060780040d2480c90f010451401c00302c0e032082200c15550086150500d03200240685c200d0080000d64555824000000c14a195542c2000e40c242981d5031a4241420f18850 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538385602 1250 538384352 538384387
    0x7030e0414010528120318080712110f131a0402090616110d06050901240501140f0c0307021309050c060d0e01060806100506070f24090503 61
    0x1804003045880004101c2501e84d05259070b20b82c03511040c030030149084105204001c0c0400d030b0280009802500741e4009160340881501441c0409460f091b8145603900c500741e5403080380c1d0140c07000c1d000790344c13808600094000713404822854000d0000c01300c1e140d990001845801c44840d2144103262560791500c0018541016034001c03000481d011401d0842540c00700f1000c0c040d1660340c00b092881507207410f050002c80780561154603002004c10103515050b180c0140a031105590440882d0b09002c861160090307040d155464070011114441c8540b0700d0f040045820500e01d41c1d1307814010b0010401c81800344400001448005000c1c00219524002841071202c00e10305800c0c01c001481c80c003040343d80080c4002c2844500c502084401039180e2110b034219400410724100c3e0007103d9031901d540029410004603040784500007142445450565031000d202080c8900c0400400310407030b078440940000c2c000c0345140a86e07801c0c1c5030425041e65104003403108490342580241ca1030b80c0f01203450341c2d02d103480c40030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538386852 1250 538385602 538385621
    0x50c011d010e0d090e060918100204140105120a02090d0501110c0d1b03050a11030a0206040b0a021c0e07080d0e0f0402070807060908130308040503060f07140a0507060207030e04 78
    0x60016050386840072450021a0151455200c0d02d20100032608028403900c401c100b23100304d501030f1960310328086100c6009501921404000c542030095078000d80d03001d0f20075207031081c4110314000321aa41d5903000340020350203000c1440c1d0064942c50f104010560034171030031203c400702c9212280d0b522211005d45140450018031002000204540c860b20084e55044541100c0d034182406915241d03c42c01c242d940c441c1c44240001c481c48003040ca0803549a0000d0180c1c007a40c06802c5140e403607114442c1a105034421104e03a011100d01400b001e440c2d080c000d030700048210503d14141e03405541c544d00c0c600d041807060900400012020040c401803840c2600084101440c2200c0c11403030700c61141d503a00c90301d000c0c9640240000360784800d40c1b014400100c1c112852441d40035a080c00b038903100d00d0549941c0e0400d0140d140030b03100d21030010740f001d10041c2105008004584803103010300013086050089500c00d85003001080000e100c80c800040d06030000d043d040e44607456012240d0207040511040794241c81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538388102 1250 538386852 538386857
    0x210f0f0c040606020a030e03031b031e16020918121c14040f060902030d0f2021040e0f0105010e042702041103130212010b030706050c011d010e0d 64
    0x203040103c0d640005505030f4590f4075090007242c041c080c0700000c0c150700901444e043c080e902421034252665001c00141000501c46690759080c820703c2c4550b40340c1c1c0c000c2881031200c20090b61441005460070001641d070129049a031a06c032100780d810600c2c1407992000c00c180f02c010012402c085980d210b01000c81c0d60541020040080144105901e10344640180001d0308030041700001400f4001240c20525580760041c080710400e98030408003c2000c411840080001220b091342c0c14100c44404109047c0110982c3c001c00388800140503656a42d401e41c05890104102003000203400c80a410519108254444041503150303d80f10015180c4000500401d129a2071b120101d540f60036085581c49646050210f0052440400e00c04a00280f40c51040301c03024180202c02c000c3c60b8120810740010040c800c0c1ca6540910149410850982d9111441c60741e040e0400782c01032003d00d12070030103031406001010001c189030302c11130180701c03003d011074040074041d0351070300552110345070100040c4c0300e0030500d803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538389352 1250 538388102 538388111
    0x40305190309090b190803090a2405091c03022107051518010608010902150703050315131a12120d020a03060b041d0106030501050609210f0f0c04 64
    0x2a54010040002c0d0300940402c59a1140403038415292080801c000c0391500146698040e240c02c54559a40c1014161130b10440300d03c00007084031104070145244000c08003031819250111890151182e03007154000701d8000c2c4016003204601640e9000c011060f03030094001e04090400070040001211001c152030f20000000c00c0380c0c00005000040c15040409a910390035215164078280102c1003120f0075040c8101e42c20310801091201c411b510140c0704034030840d101d20150203200119500c42c0690400600071840500010750a40d101499514000100415040158007884030100460b540b5221648031552400c01811550500b41503503c00542204000d10710070b407070720030030721040d01c21403000c0843d240c2c0110b0b460f20070038001d400c81742c0600f02600400d030321ba648451025028005400000f031040c0b401c1800001c0103402841105d05030360029103001d107000b10000510151080111100400071114188110240003c0c0800e500001020000d030103001a41509546812140b89032548182e180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538390602 1250 538389352 538389403
    0x170403020604060e071a040f060f05180d12020d02161401120204150c0501060603050615090a0503030406030b130b1f180902040806091204290f040305 66
    0x260181c0c02940301c0c0022401c0444030300510308051261b4491000c0f42c10704c55030f52030740004a00c040c0003920b0424810350402540c4280c1141c2c0e16041c1c0c81d01c0310104070204891102105043c0e00140307481c0000e0030600c20041640d030740850a20707c6009040040e0410781c2403c000903814400b481000040001a41c4c1590506658101c181003580c1c01c64140a00260b140310700d48a50703015035004047c00035141c3e00d04982501d02070040440c2c00c4007140c6a5103810360105002e4040e1003a903008070406003880303401100605060480f41d00258012758060342652001503255010801000944007950700450316145043c184902c1c3e515141c0254415400c000d480c905035241d02c0c050050022a0495040c40301604020a41e402c0e2102180b0000f44190003001017001741c0c1540003041100c126100b2201c144c1e64208040b9180c41c84441c0c4d40d02c042c4020002002005400388042000c0704c5104d540600c001c0c403645518a103540620902c17140e0040210f400c0003800801e0100140a0f809990f0302c01e0b64211 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538391852 1250 538390602 538390607
    0x2e060b030705070519030905030d030501080c060306010507061b110a050a110d0c0e06211b0a12060f110c0325020d200d030219060b0607060507170403 66
    0x50001d400c00002044060034480d003017080f484050091500388030595842d050080a030300380341c0141e50181c4500c1403c59450b40c400e12500d03040b0f0f070b42000030f4000b51508004000e443d03400540164100401030094078042503103071044407042d0110350726a814490340d09101800c2108038040025098008001403000f1401c00701c0e050100700c2e0b000d450105074180c0b0b5000242d800300d0030900a0403030100d40c500440e0118088440b503006d058201c95500f48189050058030350021407803c0c1c1c543e00d41110f41c5c180c0424201c202072150821000b0a04401346844441c00c4220084115041d281c15450315004031020207280b045100e4070140c0c0d83c04030702d0300c2c00b00d110090380ca1013003540350f00c2481041c80b042140a03044030600000680c2c01080ca0801d0070703490404c40e402410b91031210034960a50032035440345240c40c4100019059260300038108200107204503060030f00d17120009440e510784540240c905942d0b200010304003075115070300015240c103080720001c0401040c0e5810700103418100040c040881d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538393102 1250 538391852 538391857
    0x105060c070b030604021201080109031d030c0907140d0f1b1b05070f120c0920030c0408120c060c0f0304060203131b090b030c062a2e060b 61
    0xb01d401004650780d88490000c03800900c124003140d040c05514000102d401c2c50f06400c04110b40d4040d030b8421040c9440481c0075540301c003581320b038560705a201403401d0005003000c080aa6100f50b040c10804081304074070060014940c45503c80c0c0e60495900d060b000300d003052034800d00d00920303a4100c002840d554908406041c030460610700c020407141c00390040c81000310402003900900410761030103142c0c0d60340b0500301030b01e8519510200c990079030700200440d000049214000c0c1200402d914030130ba09404080d4114254009840158203030020000800d912804025800d168a0f0503400705646254442e40141001c00140994007168810882251a140143d0a51b504076403c510300595945410b801840083c1840034020282820b039040d022080c0003140301401110803207401400351007802d031308054450800c00c45555000708107000311440d00807030350030704282c2c2c60901c800e4820351503804c0b14091400c0f03c0c804107424101d001e452003016240e174162003660a1006070005020140c18584c5685107070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538394352 1250 538393102 538393109
    0x230a02030306120109150c0806040e03030c220e0702060705090901090b040f0c0908120c0604081e030123040228021207060c0311070b04060b060904020a030606080105060c07 76
    0x841d603c28100400c19001e40c85180079541c0400346160054002c890300c0c002c0d2800902c003101044680000810a0803e40114048800c008000d581755940c0c80340d0940c15508155401020034090f603040e9600034202e0107901c0050405230362600e0091901d0040240381038401031801080040500991030345854140102d415200994004144d030070220010800415030b03c0c010b89038a40c10242034a4840c2e03008402c85068800e2070080c0d0703070003110f603181403402840394404070702c5c1691084001a0204000f44041d19403001082500d10341b00c01c40c4c3c004817103190401e03003040301d0441d140d00c211504e15044620075240c25006032801e43c10080291000c680601240c07074038542c6c035101340350b001d072556100388016581402d00d5003043c0d444042c0341c100040200082d1507181d000ca85451032211121010005440c1640ea03c00040b030042e94980c0d071104007400302070140941007841488850200d640341d0002d880071000c1c641e800102146400c0d801018000180c2c8106d024103002c2000521a2601066420a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538395602 1250 538394352 538394359
    0x7080c0c031c08062803030f09050d02090604180b0a0501171911030d1e1b140109120f030b01090513051801020a08010815010e0105130b04020a230a02030306 69
    0x55882c40046100c40c22050481c1c2c8a1000208804807a500385c164440141c1c0e0082d90780c910010b454040a89240886006aa602c0034020b1901c3c8018a800d5450561000014002280072516514240c03841d20b0300c044100d481405200c00c110300d4100d544101801400803200840300c012070311442e503886909018035a51407020028840c8113001c020049461080780140403144081e9180c00b00814282100ca21071050881400009668910030540c0100520020907070078030454aa556194440350318039503450310ba5480b503600c00081142c40b0b419035504001501c03940c1d0b121061440003000c4030203445006040c002201401d1051307032240d10f99810241c3c0a0003001a41d505c480c0341d0313452016449180c0e02d0b180e41c00052128450750b400601581203901a1088a0740c160718100210308200c024002c0046002c071400040050349010040800c69240b6040005080101c00001c1800c0e82e0210902c900420400c1031440000012483c1100144040d4507200b420038000380402500c078440906414031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538396852 1250 538395602 538395617
    0xa12051501050711040905060126030405011b1505010b12070c030e0607030e09091e010b061206240c0708011b0c290117032b02040b07080c0c031c 64
    0x1505c5e107510641096400601300d0b051580d440c602e54599115600d0307e117081102e02d2051600d0703800000141d60954030140c4891014000050759440c1c01070b96000c0c16605c03101e03100c55083d58903411b4841c1ea03020389030310408940c0d903480858641032900300141c5540104002c0c1d4000c1030200c0d501801c141d400031003c84000365101030343e0030101c5100c3e007811405584480c40c0010b01401100001e081c41c2298134100710070342c0144590083c40e00300d42c0b68514003500400b080200c040750780500d0020990045004042d500b0054400c1c50071104021030b01401101e072100000c00106410003081680c00a081d41c4001b80400d04075142088691285903d510050215504c0e101c2c080100c043d140f500c454031083c41e6450340d4031344007510035602c0c0700c00c0c400e00c0700a9000107404080c0b610003004031009042d082c040604100c09510f030200804548581d084c2006ea4244400b207541e443c030000401e00c1e02d000c0c45105441d0084031000c58101003a600a403446644041481c1d5030205060000442d45526801c0c50034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538398102 1250 538396852 538396883
    0x906010b03100803031e090f1507053015010c0809150f03160f08041209050d1506050901030b010311030118050a03090603051009020313080a120515010507 68
    0x504440358111031284c0c007003c001c0001903e4917421510743d030703c13070001880e805898000c8403684900c0300d00d403103000e00d030860118450210310000301184c00c480700c0d1070101d01d0101e81540016100c210503400102048281c40c0b40d0103640380c07070b4002580025006918025140d09040064490380c3c005100902018001c544841c4030307500c1140841e424420740da0041d07601d1300e460f00c601d211507004030340580025003072060400c1d1341d070b2054803034980002582c0c40d501d0964403142c652040125114214204002d00c003040456140c581c03048980d0f825108034100c202407214031301114251211500b0590041a0410042011441d8030000c43c0c112504480041306862038800845e0140000030f0092118a504003c2c200800000082c10800940203135158806581c070b40504030300b0348006a0b000782440041807002d01c14078035168000e5400c00702d100138014083c11a6030b00d114143e0410303030710003010441014001520000500038240e1001c031044c15152040e241c4000a40607000b13183c406485800180840d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538399352 1250 538398102 538398121
    0xb2e06050a14090d0b0f101512061e0e010504051006080a020405090117060a15090c020708102406050f1c06080303150f0d0807210815090906010b03 65
    0x2c03100400090f05600e43e0000038100103c02c944103440140114208030001650300041205090640e40c208c403084014041c1040d01306c42000c2c98503440f2442c1d0b41d891400040903c0039a0000508852100c00c4090311031810518030303000b800c160b01103070260342407a081001012060704030500381c03081ca0800090ba503c0d140e034100001d000c0c6802c4140c00c00b10702c0001060018621820900305400a400c442c3d0656039110000c5c1039902243e00310041c204044800e010600c3e01d03801002d1030242c584100c5a10139520741c00c142c5003034880542d00080650315401410001d090b00000c00a803901075104c451268a888402041c038030030041c2584d8070b103c0206d8503490b110794103588419540c020788810b020300c503180c102880c0c4076401540c401d0f01100510000c01101e0070901061880d800005158080300400e90b1950b044540c404034007203544895294002021080c800c107055640c612959800d038080c5450b107030f501804171100201520035040281044031200c00018442d054900b106016622611100c801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538400602 1250 538399352 538399357
    0x12080315130b030d170f1e1906080102070f11010e040908040f0b04060c0803220311011805060f0a09050601060f080105061213030219030509150408070e130b2e06050a14 74
    0x6400900240c424003015842442235003180c1d0071003903010000350b0b5807150110308074803a012004045002c01c001c80d03000b0076405404648210810305101080c45a00000107044031500541101c030b44402007414410100c14510310340250003098509440c1c03e04100000d40584000c0000411500300000003c03154070340c0e81c08143c0d04100c0007040400c1104285030142c4030480f42a242e4409601c0d103000d0449100050b100c50041c1c50704180031f00100d4585400b002074091008110640781504c0c0d040c101d002940c10440d680c024500d641d20300c0c4483c810400d0090560006074015845003a0a00c1491424402c005034907412000401c11910395260b00c0c6000c0e1f09045118046940c920801d07d00b81c021b05400900400c184881141ca51000441c0c1180b00e00c0c1c3c40c0214050654aa40407060600841100001a0b03401503044280c60310400e800d5900e07001644004c031040000c1a40390108200303044485020010070961400000107a00e0424400030710502541c079030541041001c001c0d0840c0b0392400c2c000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538401852 1250 538400602 538400641
    0x30a1203060b07080a14031e220c030c12021e15041511031801050703030b130c1e0206072102030a061d0112080315130b030d170f 57
    0x4000782c4910242c10044c2050f0403500103000401ca0f040c170701c030042070f501804891103040a0072003011211078240d140301d1884001054001c58a4183d2450141703911518040c0c4080b9100304030341d00070141980b0b00350401e0a0701da44810720081d1500c12200050790760150304074000340d074039050b0210300c1c40081c0012801501060f0101804000250104807050212100c54203400e19858072010b541460303005503030744e03c61618070460345064881d0306100c2d58801d000415465000b4540400d610441000054500c1c440310b1405a0a684d035001000609800101910240c000345400440300c00d2000300c06521340c900148440e0400030124094a4a05200074403030312801c0300420215200e203800d202200060425000e0214070481c00d1591404502462000d00e0581d44100a0400c1e10359440d03884880d10b41001c1d020700f00c0c00c494055406859102c60503903c44003080700e04041703070080c5c4007828142000b041190440801c56010020384610740120515900489010410b036504d0740d5000c00320008007107506 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538403102 1250 538401852 538401869
    0x1207030b060f010507060c110d140a35270a0201030b030102070605091b09010f090903050d0c020a150b061803071205030a021c021906150e090601080c030a120306 71
    0x71f043e001d80e950101002249258100c121185a0480b6806a0b07480d0000b07005900032840801000c071302c240c492405540061440601d401701010a16402c0d01c0a80e4220500c0c0c901c283e80c0002c201c9544503071025054408440c00c02d618003107403000d490686031420740f0000b0b07042c9a125005440369031025411100000d40010f4200401c3c00d003482c0c0c0b0358940440c502c401000d00e815041c1544180f80c20240d60741290785402103080c0191412000c0d070041d040c0c107078041c6d06114007440800300c01c00941c003400c90b6240c895405401000350500c0d000010890480f44802c0261a101e40c048041d02d850040304e00e412180744a290514400000113481d009041e000070602c0d07111a0800000c011000015060285454081d03e0803071403401e900300d0201015424050050f03000b46070000300812041da032050b15500504011499180d580c4800f54032070f07226400840d151180320104000c410301400500d01400204000d070102408440009507130307003910030000e86000022082010181c0c020f5006400614494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538404352 1250 538403102 538403111
    0x20d020310110418020901020a1b150f020d02010e0a02010c15020f032514030405010e0708280b01052814010e0d230717010b1207030b060f01050706 65
    0xd2504000c80c1c0140c13264a4034074541c2c103019032a03000c4500079182c0c1d050040c0d0040c144241603803200103185441040020001c4803507100803840c07602d03034480100d02210544602c40c02d14250f0f20000e10b8084901c40000c2103914106e42c43d50380800c0070030100ea4040d02403801e510f0f084580d0400d4101405c054074402402c070b200140c901000081d2802451052000d81004000011458004519a08442006000200e8a4141d0061440c866000d143c0007402003000140c1c445203600350525040503a0020803255101210018004206150001c9a5000f0f841c3c4050302c2005641d980c0e40d030b100d041c02014030802042041505c64040410400150104002c680b80c0c40b698030b031a074541c484c80380c402884c0091016a00359206040070200c08502d1170b40704070001d10000d100341c54111800c2c030b11a0620440d000d003850000b441c0032000841d1110030717181d0000081c04501c0004001045056004181060304280c4003040170070b80c14910b9070383c800c0c0c3c15034051036080c1408004860921449000902c0c4a140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538405602 1250 538404352 538404371
    0x7080f191e0e100603051216060e06010f0801060b0a2706090501030b04090b0403081302040e06060414070c0609080405280501020c03101a090c030702060105040203040f020d020310 79
    0x2900111603228040d800e82d1031688241016400313035013a50101600d541d020040e48452032540300300802d1140c440c505985018019960341406172011400c10741c20640c4a280180702d0040b030034950400504070b800080001c07600d0005001030900a07171019006100d038142c4640700000d5607131300c5010120804080001d44544544001c0d05800d928000c5900191606c00b11030740c1030605208050703803250040541d5019954503501100c124100a004080025522034200010f880714000e02c040d9440c1180074000d1807802c00140002c032410100380004401c050300c00c1c00105600681110010394004901240250f100e040100c5c00b4421540140d801030320240b00c01c0f12204010308d00740e49810001080c0c541c00d83c0e80f2001246c4e11030f9001803075580b5800041c040300d41888140e22800c510340b145000800c42c9980c86000a0340d1440495001003a140000304003c80c065040c061140074040480c1c045065041c9030700d0350b42c0b140f454180000d00441520a400095690030032070b8826600b01d224040c00742c0d404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538406852 1250 538405602 538405661
    0xe030706020f06060a12111306120b06061e0304061d03070302070f180e0703060c081e010311060307200a0c0e01060c0f0309150503070807080f19 64
    0x10201034a65010303c1d00481c002d45805c80d00442112080c400010071540caa40f146800740c4082e21040e0b42c400c0c0c1c0c800802864075940d005150040c2604c03003901002c0c0e9601e0400e001a45d90040c1070b80d00c51001000320f21010000000c0640803240030300300c000d4503030390717149421001000d11044c05d9541041000310440c0c620302c00801008414440d40c00e0b62441a5030301c2007461010020300a620710403040c0e04030700e0303480d0420303620000b00505003204582c40d107680c0c0d0700c0702c10403a500c0390038110005030540704020f00203070045601160303181080a250f542d5031550305c0b020607229034a02e819204000c00004181001d1040c007070046240141c000700c0c00101455039125503100d0310500100c8a03903002c903800181e1400c004050a0480741c89413581c040ca040e45964030f000c03000901108600b806040c04021410015403400aa40003072304c3d4403003e40d00e041200d00500440002041642003120400c02c1189456116112a810103513070701c83c520054080440300400390000c541000e115284004000d4801c42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538408102 1250 538406852 538406863
    0x1b030705370c090c03110307030c090803030c030106030c0e03073f02010e0a1508060f030118120905060d020409050f071704230a02090c1c0506010e03070602 69
    0x400319840700811140703188420000200e81c400341070101d8681d0108400d640d03d800429012000d4a40003035980e0048604621580042d540600026654070440d0072458106c7c0708000070b00760b0580110309514213212041f0103071105004405c10151500d04980321349019042d0408120001030a4410035a107451b45200c0900760030852034218500b0703040c000b000c06418400f02460f0744100d0004c032a1074420b03170011749420503003010f002d07001401410000f4490000901d1080c40e0001e51790b6480d401d044c9181040032050f8224442c0d0702c240d00d451121929950060900071540382e00120a80081c09480026070f28000f01c1e900031a00700c50001651400c0f403401e5070080003504c4852070108400d03110b000d03100c03060850031504070021901100c40b440c2d115580800d40d43c0d01c02e1040d50740c0d42901083c6401a05007540d0303104440c915a00ca141c1410842c500418900e42c000160b0102a04046841c0031444010341400308454070b107961880400c8090b4415046451003003070160480b5550381d82c0d12070095581 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538409352 1250 538408102 538408153
    0x20a030203100c32070203070806010b0705120315130608030c06060a060c030206011205010b0402070f0c15050906070614040b04060e0c10051602030d030603170c031b030705 76
    0x2400b03d4158000907101d1a0850340420700300346080e85401131a0302084584c0d110241c143c0c0d16110b20100003558400401c0342d640038180d04400151174001c103290082ca41001d10180d032004510a00410080000c0495002540c840072202103006d01d41c0101c42400802e020780200782d0301e006c00178240302d0407a800140307140150400e442000e04140c0d200c1049032b0340300d02a90014016000000104031204008001d2052036004000002d10200302c407000131700304da0000d10100c4004103001000803d05c44a540d20707600401c580b020300c0302402030300b10008010348501c40b450741c4100d501282040500403507030f00464421134102e400b5051403c050901c201d41e2a0211402c6420034246540f0f1b100024021580920715400a80031050031031032034074161803580000e0f5400421543c01e0b1000b00140c3d40800c6075581484044d00c1c0000c40030b06600380303d06007801e40f00004142d12001c200959400c1000400c45461080b100700b81c40c0c05400c1402d4144c11417045ca02c01500c0c3e4468be80300003122458295540248 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538410602 1250 538409352 538409357
    0xa020a080609060105160507120c1d0c04171018150212070e0414010e1504020702062b110909070e0109170f120d0501060c0b040f020a030203100c 64
    0x40d50740741010000201d90485080f800600240300302040c03814000d2142c100c04c1d2144041e5003145403a030090381d02d901b205103020b8991080c602403c000004004400c0071094207052541e803c03500d001d5030140c586215501c550682005021282e00c200301c824480c4001e03461650409102ca85032000e040704407810304a030103488100030b480c2540341c10301c003901c200c58000f9040344841440756180c40050740c030b00905481b101d40044d1a13503080c07818864603080c01c40c080d000341d036010011401c5c080f010740619086040a28013030380c410004a409681c401c426115644440700c2001208016011844600350700c3c80681001e4a080c0b82c01d08400300c03003102c0907101013070b070903140341c0c03003a584108048946018554600780072031201e8106000d01c1403042d441850f28002d0303104540c0780002000c030703491812030403000c01d10324540040b4088800d0503440c059640103000ba890285103c190503214007080c0b03007014100030031900350540701208644031884400700840d0005d00391107003150348811100c050807105545200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538411852 1250 538410602 538410617
    0x3090c180c09210c030b09010c110a02030a02040f02040e091f050112110102190b0405060f09060106080a0f09030809010b04110a0e03011107140c22090f05060a020a 72
    0x540d520032402d000880e100034000340058100b4960950301c3c000c09107400e40c1d075403440d0307000400400c0c40301406900903c046400000d450080441c024101100d00714000c040d81c10040c9107202583e000904022404e80445001580b42514404031000b4800e640c02242c08114400800120001c042100d0340010401c003061450103c0225886048034424040c003400450511100f10203c1c5081200f226215418012281c0d080c0384440815541035a0320000c031088a6144104820048103012681d0800e101c40080b0700f03142814000f03141c968a05020b600d0800c00f070300c2c001551803d02a00988909130005200b088002058107005141800031220302215600708480f081407400c00d03100e60650f41800b0481c0030306210017050225022001c0440099166496400c0c41d011004140003e140c0c0724410320002202c9003000d80c406040241c1c1d00c1003188a50544000c18004400030100781191102014002401d0311941c0380c00d90004414000140440c4296010070603840c1c6554000c1c041d8125645501d070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538413102 1250 538411852 538411871
    0x201030b0406170307051b1302160501050127050c0a122307021608070515132403090c1523092e0c0212011e0b030c0a140103090c18 58
    0x10b100007c003c0c940c0d8111540888040f052002580500400808046503462010729070302d17164291402a0403400540c2c0301c6407040c442c0c0801d6100d0b07000602c2510303c8140401d140024441d03603c0c0c081c05600d5030034000c02c4100b24445100c5580089185c25803010358400104076031440c1c4591080440b8003002600c1080d03001c03411542141c2078801210860307070081000c00d081400340400590640984c6003410400d11649e4010460000d00c18086c003050070303000802d8240004081498490a441c1c1401d0525011609001c504c2c4030607a44159140381041c02d08242c900f15048581d102c14503030310b40c03ca0b2047c800744000790400d100140b14010084842d032000107a03011400003008450b403060b000d100120140249028083d2f44810603082c0020301e0f0740040c8100602d103130b00351903100303038801c0c842c00030140a410b0b4000d0522428400040580060461602c01d101051180c4194065880160b40c0750043d620960322a8201502c1c0307617408105030024994072007090b442030306104001d1404904004004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538414352 1250 538413102 538413133
    0x70201050a0e060f04060e100e15160c0b07050d15060906090605030f1503120306041109090a0b030c06070b010f12032003040306110a080603070f030201030b040617030705 75
    0x300d004000c0d1541d507125a86450359520000e007d00300415006016141081c1c4445040b441168082c9030040041d00d400c494140b8030a0000200915442d103130080784200c15031441e1712813101240654410492101502c91704403d8500b40643d81001d01c2c4107091407221071004086290345002c6404548600303034030648502e801d03610030065001d440700185042c4009812880e030312190a8102281800c840e4015107210040307402d00250030300d000a082c4000043c428181030900c103100c540c81050800500b86110980040d40d5550054500d104082c0c44020150113503905010700606404003c2034103a45200070b2510890400c0c09208180c807050350f4a10008140d55002501c483d61035043c1d40301d4811542800d540042c00e813482c418101184800d101c080700142d814031800403500360b41003c05440c5c041d01407005042580003450b82d40650801c0504200d01304003842c2007002e40c1c2d4242804210200f620003c5801807003668844001642d90035006180c001000c0020302c0f015010f9800d0702c1c044003511020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538415602 1250 538414352 538414363
    0xc1407031103072021030d090611030106080108160b0d0c2d110604080403030c03171005040b19140105070206040e040510020304050a0b0403050c121b07140621070201050a0e 76
    0x840143c104000180781d5803510351141e1103049c454040002c00c81e15110b422030b0313160001d03080640800c0d040d000520040078100541d140350300c186c083c60031280e4280b10260b50316000d48a99003a0103601c2c0c1800c448002d00a41b10b001d284a424031071103558000c1400b01c818040b2009080b200450303806080d5992840001c0f40e080d11540d00050364a01d0140385640840c0e90040c001000d800300700f0840c0a400710070074002d60301030081c400700302100e110307a04000404c01140c840403003046c480c83d1003030b09206480c0d0f022020001150306918201ca1141c02030320058880340305050000303621410000340407500c03150102500d40194000d0003150402c281c07a07e6950101c4c84103442c007509039484540d1140005102c41c4d030041d400b922a240490400c10008086841c10310941c4444180f14804689003c4170384d003a170300144050840900501c800c914080340b402c40c61150080d40b50103020f0004031501c0c40c1465030800f080c0501002695611850600c200a00038201035400040a03030030180d8a507400c1c180040c0c2c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538416852 1250 538415602 538415659
    0xe0c150d09080910091a13090504060b040c05130b1308150a0507082203030e030304051e0304060806061305030d0906030f0507020c01270e04060c14070311030720 71
    0x9000324440c001c886ea95002d4100002100f1102a4902c0c041415651030040500440c4960350108a081c000400c12007038665408401082000500a242c40310314140c4480003100d16a002141c1d48120108550690146a810450482c0b10b2098401940308600703103010721406000c0c008004c1500d40280407504c01401391900c1c44008100000000e0040f214040d030146580300741800118615215800d602b1900126015a184c1d04504400101200020940d0446804001c040c40c80c01c0d04010020300082c0d0081d113868051640440e03030300e088014103040f4201500340281260342481242800500711410350080000003401c09500c444221420701416014080b580c020344280c0407003100450b4040001c90700c070000c0d090103442908422404034540d6001d4024044400314610341400e2201c265200d0314884010001c0e0f01c0300b118107150740e25050354035081d41881d10619841c48616020300d140107501c0b0281c01520b44129100c4030750089444804405404d440c0140342d00501243c0c3c0141441112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538418102 1250 538416852 538416869
    0x510090e0a0504080a03020a02010f06151d0d110f030a080c0f03040e06040b04091e0506130f08070804090c03020c1504050c01031e02040603050601080a0e0c150d0908091009 76
    0x103817414040c02a0003a0840c04400c0c40001054070582c020101510411750140c042c281e01c0140f040140f40d4010200c488117101d1003011402c1c0100391020034070540300513002403c01034108004c090f480e0340d9144015107a8400904490241410b030919140d5980002a00c0440d4855000d500343d820030044103682c201e9100f50304110b059540c0c441404050311a2000407a4019942c0500314006070008010324560b007209415035003034018900d062440e260019115489208003844010006004030840d0200d45074407500250f03d9000500d00792009010fa5001440081e0906104c11001a415805001b840c942042160103440131000048004c910642c1c000c0c0c000e4126021454440d4000d4221400a2b804030b1041c5403044000300340a000c98003d9044500065203d0060103000d607846078040342c02410101c0100440c0407035000b015a90850300a05031b004012001044095170000016542410606075043c070045071545001001039104016142c8103c521520100d044ec0c843d4034490300741c03403644 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538419352 1250 538418102 538418107
    0x60105030604080307020c041e27030c1b08011a012c2b0b1f06030f020d0507120c090506180d020307030c08070515030a0507090510090e0a050408 64
    0x83d2154609540000d02000030b5101c1c4044014031902ea600c100e00491a031924804103840d41c200f83c1c041502d0018208003a0807519202d000000012030745000041070741401e2039050b140c03062800350429000c400c041c001c01040204005088203064004550340007100e440b0310706020aa000540e148400e55422006200c032042c100ba001c542d100d06482c01086004007051030041880c00c405070401a200542150a0400c0c0022400c0240780290650070110705480016049490106880801e40501c2413804054550407071200e96a0980e04469038400742140510281c0f0b00b800f006042e00c0c160201182803285400191817219201e1080c12050351001000c0c00d2402107a040c41c00360308032004403803e9015910710003620050b036082100350010b5104807400d0508515104040d03080003840c0d484203000b1044444040c02003c0224122644101941000140c03501c03140b03c1281c5441c0581c00007900148107039410b032042034210b07100ca0304550300a4040241551669064400d685003a140103212103001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538420602 1250 538419352 538419361
    0x804090507142a031911100c050f03040305090901080f06060901050a17030c030307020d022a0d0f062c01090201021f0b1f0e011d041a03032a0601050306 67
    0x486800f112181100b0308503401d01c00c10401085411450303401c48400705541c0315101807204400e11000c09020002001001400c0014401411501c0360f0f11100e113000b80c0010000c1c0c00c15020301c0a0300d81808003d04228100e40c4c491008a40c2d03500482651380c8680b24500000b001844c001054a0580320040c020b81440d0307103400343e820310300c2aa004420486010030b2015561603682000914842c50250340180464208003e002c2e04015100701c0c0d082e166200c107022200181d841d5070714035810050680e000c0c00507414905040680280c1c1d070500401d0316050481311010340c4041d000da6040e001c440381c0100c00c4c29480801c0c1600321034030314200a015810100c90144ca0f0343d4a5813041d001ca0050110215001c601c0344002280e200d010780154044080c0e01200840a940c09592000d05003c2800c040d10447c1004e00003203164400040380c00c0c03055880d40c0c1410205114880c0000d4251409411607856034043c02c9480902800baa0700790401d0b80c0c5181642d00d1091700007030100c0c12160f0280181c00d550f00d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538421852 1250 538420602 538420657
    0x408041404020c0d03141003320d030c170f16020a060903020d030614010827030d020301031109070c020103180212070306051501050421080409050714 66
    0x1511041d44150b0a000141c0c6040c0c0c20700c00720002e80000d40d0002a52442d55904001d1000058020076014680d09002c3c80010185403c540602d0b000201080688242c1e440b1448a080c040761082000d000340500c003040e468054001c002e4035407103030700e0b89d00e450140c0700d413140500304048940012031060034022600b030700d01000c445000380c2d90910544881130b44944801098800e504030803801603003d41c0c46070040503854410000905404001030b52040d0303010000a201800c090f201040b50701d600042c9003c00203c003842440c003048038100303403501d40c0e50001e8003070001e4000748025600c1012580b02d58503e8503006148901c20031762621084402c003003030340044005124101500040048100c0e9501c0581c3c5c4510031214114000001072035600d081d45400419540044c000c0441a00c9901748030005a0b0400199004e5070220500001c41c03048524a42c00d54074500e00c130241c40c90b003002402003103100c01e40d00310501c2100b00c0c0c0c91b41024070000384140c5400340300d058412b114bc000790b40a12100300c1d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538423102 1250 538421852 538421879
    0x1060e22210e03120c03030118020708031509060a05100f05041809021203162402040909030306150c17040e0702100b0105030f061903080310081507021c0311040f09050f040804 77
    0x42c101c02006040401558488005520a0313b84c0006002c118280351500d15007034940741e50100c0151550408286444080317581c8280e00091402400400401070f0f8006100708290340c004c0007030081000c0c4440c00b01c05040700602d04c03454140c2c0a0300c2c03440807014107a0000030403212200c416034240f011000c07140c1c40e4030100103500e034080f010a28186c01112403030109400904041c03d03180f100000d03c140c842c6005402c40d94a68040315520840f81800100c883d0864000e5480d0f03600301c16880c1d030705164070728604282d2085820050480d62140140943ca0743d000801c090a5005e5110811040400c00011340320b60004548101e01406100001030321800c1c040d404d507224000a11802081c1c640380d54400d02c00f82c104840745506000100d40420507900c0030030034ac4800011401e41480c1078200010001d465902074103c80d802f00c1810303e404040184264001c5000140342c0d15501d0b143d50700c2e500511900032107031207540541824480421107070b0601201c0c0602035507102e50011710741403800481d1010b04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538424352 1250 538423102 538423139
    0xe0312040e1b09060d0b130b130e03070c0303020304080601080c060702040b010203120708190e0607030c0908030705070e070e0d20060c0105040501060e22210e03120c030301 76
    0x64140107200554480001404170382c81d600c4800706480c690703402844400c00178100f00403052410a103003460315031100e4560301c100c94031501d00420345891a0304124503502c510500102141c0c40d4003800801d0680c04401f4000780c1c0d50400603a0441c1e42d030f07440020350b00d000c03115580780d000034100b024100502d030650141c0b600d0081030040c0c03401c0c0b84000f4a0b001c2d00320f40442c1e81c1000300700000d040020860030203914800508c1e200c03c00304013080e0b40703620076541d40c0030042c800780a15990360f01c4424000e001d0460b0800070055201202d03901e460615003035448001c144030b103d40c2c001081c0003003040c060261849481d085000780c42030803030ba002511404521840c1410040e6030009006900700c0b503481d08030047c1009042c05002141e6410940342182c21140d03940d10031080945d40d8800d0000c0c50040903c81018841c41440c07800e0501c0f228204203040e0b0016114018810010b081d1285a494012009200c00e0314101c2c00e8568410000302d0820041c400c580e0401c101744c0003000140800c0c03c00b0600303100b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538425602 1250 538424352 538424401
    0x3060409051905010e0a0c0b070f0803040807020301061403190303060b0a0905100f170c0d050901050a0525140c070b040806070311030a1a0406060e0312040e 69
    0x54002607155641014070815001120302141e81000007804003d018440000b1080c0e00100450303400750704c90054081080c020351980703050025544061154440562141d1900485560f6a900b8580360100c22540010b508070300035401c0072400615034107060518601c0f004054082e0400180d508015140c00a0001040b0203066036072030003181c0c042d0144003a221001c2a41c450a503450b08140170850368840c0d40790301d40100100409451103485d804910003051038a4103510000c25154020802c5090003030104520084e403400c3c0c2006040c4405410160040c040103000304a5900e0300c03224a2084401250840386d40006508105882407046820100c0010030404450800b02201e0f200c2d420720704d00351b0160369803400108043c000300b4020300440d034000800d030504004a200f0a040c5450900000346404001c5c0e540340c1e240c0c1000e030351903560b0b294158130050003004541e40710300c8003401c11600d03440c4242c001d10030801d45503960301e80c0a0481d02039540610302c0920316616510080c010360304805640d0300b0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538426852 1250 538425602 538425611
    0x6150d0c051c0b010807090e03030c04051002010603021816080105031b010207030b0133090611010906150f0909080d0b0d320c090411041503120e01090f0b030604 71
    0x41807000f120345000e84400405452070518140312602560703203881484010350010800e000d01c0007032503c1168122041030f1002440032012010503401010f8640c0083e40000310741c0f00744509446103100c1c4910a01c0c1c90601407030b6640306000c085941c3c1c1003d00409803d82e20071141a2802961365101071040c1005104440792a07440b543c1d5802e40c500c3c207a01405091030001e4030f43c08130503840d4042030300c6492290034181c084048181c00078400c411b43e1240c117041c4600300e03805400c508002c2d000001d01c02d401400500060201c0c0d81c422049070440d00c00c0210880d000e010109941900b4001c002e1116005403115050400100068000780820401e4030f500001c1e0055000014184408003103d0780c50203800410f00c1809641020980070144002121039044507030820034994600c0c851039045500200400080d00c407040200d4014082d5040b540c000c1c510302c140000801c0030000081021021603984d85005480e60340c015031745502c41d800b80003000c1480c80c40912410307106034080d43d80000003c00215 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538428102 1250 538426852 538426909
    0x70906050c0c0a0b071e0c09051506130315090b06090c0403050d030213050117070e0a0815150f100c02040209060c010c111b01081003060e06150d0c05 66
    0x641c199016132240391070b46004160398043c88080c80c540c11500c90010080c84c01019180e860b4a0b4030400b030700a8409055980c400700324081682c1410700a8a00c02070078030343c0c2d203101c5a038400c024201c81d4030003103070084030059021a04030740138001d48c0441e0fa40840800030548800c400c00140c1100280b00c00c800c2001448004040b030020080320100d510309442c0140d51300c031201900d080c000c020780c02c158148024034000010a0f241d0b02d000950000aa20b8030202420140e00054085202a4460a5944101074042c43d5041401c883e860041e200c2c40c034030070460700e0a034003800840c07086100402e0307100082d01c0700840c80c1c03801524141d19040c4010001403805240c000021362580103030b40d407024169510610005034540010802c010300907c10010011100c100441a01103d60340000c00d0400841d880400c1241000b10900d401a55028500344400d40010420f20703901c1c03008950000c0320b090b40300c00100c3c00c2e0a000c1e643c664941d4002215880c07160400d02400251496401c002002c00017404410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538429352 1250 538428102 538428109
    0x80c0a0501021b010f02040b1c0b121006090c09060c03050409021201051c02030d0f12020f09030d09050f04180b07050306010e1e010c1415040218070906050c0c 70
    0x1000283d40340c0c1d04140000b0510300c00c080c2100c0140c10320304101403040009200781c11644041e58864a40c1c1e5040100145440311110301a09845001c0d81c1c0202c03100c41c0e500c0c0c20920100305aa18540244001c0102d02e0352080c003103040d01c520040640100b107081c5428001c25100d248a0700f1001e010f42051803500780e6801d02c0f40201c0e400041a00c0c016040d4034014442403070244044d107541800109225a10f008030f400280e10b42d9000c450050034450003050034000c40e4000c80003007505043c046021522a03140b84500ca4091340200c1c0303101d1003401140351002049010304804c1060700e601070300c035041d400300c107109200081401c09054840001195842d130001200000e480344980c142c0c0d40e46d21b0b102c2c10b111001420465240d42101d1060340303140c0c0c1c0c501d0f004005828000e010f80003464003076064041c6041c110045103601080314030074000c2c00f2031507804a8500400f50b015510a64071050010080e03101c0c801d120390140c50b4040000c00c001410860b4910400145c803800e034102c81607410299401c0c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538430602 1250 538429352 538429357
    0x9090423030d0e06070e131d030301060e06030705040e0a18050f07090e0307060903110313030201090e0903031501020f03040603050a050a060e13060b04050c07061512080c0a050102 79
    0x1115030700004440303010021078000c10181600500007401903040c16030010b441c0030120892180030f4403018141c1e0003802d203d6000000910007080f81e150030301072064055601c130350007401ba95002c038881d05001082c6040c9001100c4c0315010a6440310305140c1400d141c00c40905020b042903216644450b0702c441120700d03400c2d580070103501c135100905014003201801c5060404541c040f4a51344d18204844e1000303a0040210f03510241d02900020350b80009140036500c030781d40c82e2041c2030684000700d181f41d00203881c3c1012006407070007600d903ca0401c2c1d444007089002003044502c220160010f0000c0340d0f03002c1500c91503070100081401515491208100c8981c99a00184c0c442c0c00040d4885c024480c0510040c8a603680214214005000c0039040000000c544480a0008246030304111b00300000e100c03c5500421136240020310a21043c2001c2e0014002c40d0483d46007911010314100d40741c9100d56007001c45a08580b400710444082c0300e4182c44082844e0043c03140746070b00780180084480091001c0c0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538431852 1250 538430602 538430663
    0x18050a0b10030912020303090c01361d161b08030903040501031a091618030b0402030609060103051c0311030a02030118050105030a0803090319020c12070b090904 71
    0x42c0050860090f09081d100340c80c64480708800d6400402c1844000c01c2c3c081001407090b8002c0c00c004559440001e03410300300001c7e0140050080200d04100300e451400c5200c090100c80c107104040c1c4524043c200c5181c01c40905440c080c10320910807c85050581c090440300d081440c40300c07510b000e0000940c40e104030315882120342d1801500002810f004c07640c2c241c0704200d011180380410480c22003c48000c0350614030040d0058000d030207030042220307586104094041c40c0030599000402065034924041c030100905603001c0380709000d401c001507520301300064041d04030b941010040804494810200d09803101d18100201015101c1611002201c6c141c002140a4205201c006a8940c54081c4401044e1a081943c0d6001800d2400400c100c0e82c002401400940e000fa00321307a543d031540f080312451441912041c0c80071603020013999089079008101820700c1c107400d0f40c02c002d5201120900580380c0c2070501030050031441c04d104001d40345c00c040c112030b9401880f64001010000c190003010a10980919 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538433102 1250 538431852 538431857
    0x904050304081209032d122a150705090306010807050f031506010810030605040b041106071a090c1908070608010501120902060d180605010f18050a0b10 67
    0x180421580004108400e429a001c00b960303400c0514600000781c586c42ca070300d141700e85612681c1040c03a841035107000c041c6540300c0380000c40d50602c9001c41c1e00c2c041a0019101038094124240070141d040b041024180000701415000c0d00c401100300300c503060940b40c0034003030408001b030900c070b020f0031a2410490180609034540003010445d2803d010000e8508084c00300c6c3d030198101d51003801c0b001d17001c00c8641750032800c2400c1170045650b52482d080703212000c0f9840540759a0405080c402481800d44586001c0e078041c1c03440c5210801c600081c40154480c0030f030001e14243d848145c500700c5003440600350742c001d81d0304c0080e1800d440d05407001600c250f650203241e81c10451184001c0041035002c12101000703007894145280298540030003c0c00c1d5010814800c610340340c0320305c119400c65035420304440c2c4c41d0042a9041100141c01a00c075860810040310403140c4618040000c00c02c80004a20941191419034041c1050312f80300500c0700240c4805801035029a8a81c20079407000e41e038165506000c100300c0d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538434352 1250 538433102 538433107
    0xb28050709051915020c0117060f0402071a0106111b040e03030403200a020a0b0309010905030a09051504080d0c060b030327010804030f20100905060a0501060e10030b09040503 77
    0x152900031001e205901300e01554008203480801d40d800038a1441d0f400840b00c051101039880b0000b1406200180051540c80b0b44005009420459015003150f044d40c1d4281801c0d0325680c0f0340b282600c0502052074a000e16510182c0100d100c2d40d540503080c2e880860103000490303030b00e8180440c9171035900151412030210b4221040d860b400e044014086066a2518005203540300682c0c0105c2e41c030008a010341c2484402c00000565440700c01d410101d0800c1c3e1200c00c617980c40b104a070f801410010a80110b900c981e0b070a0200706c03e10300012058030305035a0800040c0020401d66030742031b83e409101d12412180310b03444408102c00782d031b002c0c000382c442410400c00c1110116100711803a041b0524603d0254140000c081c14072004c80c3d401000450002c14900303112111021403048010030711103058000341a8402c0c03e01d00404102260440182d1074854000ca800356241d00c00f4000c1998424000c440000362a404030041600e007104001507108614140050070300012008a26a9241210305442ca607100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538435602 1250 538434352 538434359
    0x1080631080c060c161707021e030c0108090c0609010c0605011409060d030f140409090809150408030904150e150306090712080c120301080106030b280507090519 71
    0x6010080c2e208034010409440c10a402c10070317510720b049079200039200c41c80900081048000c1c3d441120310b01a0002e0071410300b25000708650744030fa000d0001540c0280202c041e420f00550041c0c600714000e00406e005408000509010301507150021070426042003440301d008800b14440d88030b03040c06000240851100300d0008401c0c03000d02900501400d001e81c2e40401c1040201c0e0f48061100d04000f41403402c078030071000f0300a5025080c0202e03001040303014600382000c400c1003000802010341010a4542012002003c03507a045640158820b00950313800800c0042854506a440300e81081c900c1e0700366030000c0c0c1d111000d108006408a8005407202c1041c01c50a241d0714080280d03980c420840070091000700e0814181c06040940007400602a001c08500714407014810f03c0201c200c200000c5145440e983e403041e105020344240c1c4810344102d4003420200312901d00c40003841401090031880b0075180308045020f44002c0c078000386400700708207401741d01041c203030b8640c5204c5840c800c0000341001407506 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538436852 1250 538435602 538435627
    0x6090f06050f030f06040608010e100b0d0b1b1209011d030306010c061508030703080f01060f0801060503040611030a0915020a170c0c03070f14060108063108 69
    0x19001802800818800003150b40045400c503a4440c00c0d1101d00d2100381c4401d0b001c00c02401d00c41d04000c45030b5003800030481300c840c800210813120b184412400d1100420081c2030001d45003c900780030302000030500003d114048140000185940417401d80c85c640b9104288400c9183e1040e80c1c64815039440b280495100c0040d0654105240300c100061032079803e0290010303011105c1904020242c94840f45076a01c00080c20101074000d0030000103580d40e4400718900184000401c6a016998203c51400481c640c0c1c82000c005102c105035844d2800e03641d081c8001921280c0008004540141c2ca4480c0e0941a4a43c80c001e0b501030030f40302070007040c58001c61905a800801120882450720b00c1400710380005540003c1030965160240c4809569071918202d20301c5901c40c401500d1140d10000600341304000406028021035030260850014411210390243d884080038800c1030700ca0351004000c1440b580c540076004101284d2403a0202c84a513825004038280030003028160746065004c21042d4a030701 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538438102 1250 538436852 538436879
    0xd090203160609060c0501060b03070806012307140a0c031b17062e0e01170c10110a0b040c090e030307140f041e0311061606240609 58
    0x1940c160026000760800c04010000d0901c3e209a07020040617500030000c2c07140a600000180645080c104d5681c41c00c2c00d0007401442080d01c4090026208800d0b0701c03c8105c0340300c59110b5108908244034079018142c2c82d11400c2c4440038901072050300a60400703a0000b810011070500841c81050071400c0e00b0800440411849040d030700241014400c0350b26050342410104c0c03419440140006880d100101980c02d60740e00b4500500d01c6810301c0045140070a01c500b9102c102e5048549680030801108003840d103294a40713200d9050680c1010203010b405e8078050140b84001c000041003400c807023031384c0040e465800410710162030580e18402c036070409019603681c5000701008000e0ba40b006500c0c40c204840000e020004410190300202e102083c000a4085800102e030018910055000d102401e501c1c1500b810201a1000f101c101700407c10140340c1713080841c10748a1105900f108060000c800c0e480380005060005030083e0912030000c22805044070a03450040913064943c2d840e201c0c1030078a211004401c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538439352 1250 538438102 538438123
    0xa03090308070f1e0201021e0903010b0a06170406020903030f0d0b03161502100c030b03010c080c07112103070309060504050607030e0406030c0b2d03010b0c120d090203 74
    0x507124500c20f0b5080e80007942c0394900710303942d4102d03c000300715080101d00a000710354074580100e600147c010f0ba801c2c0b0000160454990440080110204110030416015401c4c0f050402055200b41580040320f20b881c3c0701c96005008000151802c50072000107821940108a550701e0440082411113800743c051003030007441c01c030541c01400c006c040c031380c100b034154031017849441c4890540e648800101407007404646032074803000b1810300507a9040000900a0810b606c0605d02a610f8840b80c0b4007200d00c1020349902541406003058038140954903007100c58411030410640256030241e884070f45a800700071800745c0298010107152266018a4020300a9030030350310210420606000030b009d03541c1c0c2c0408540341d06915040080d020a070b0711001c0340c0500031503032018001c4021a000019100075001c001c1456504c0c8030240103030058041242c58003080c40e40000440c3c00c20500c010b0005900c0500289070f182d084500320348525603210b60141250784400c50549003a41c40d01c3c282800c6080401403003a01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538440602 1250 538439352 538439357
    0x106030b090d090b0c1c1815080703060f0620190b091c110a0c0f090e01020301080d0c170c0706030c0305040203150c04050306040606050108060616061a04020a0309030807 75
    0x302414541102d9035620314600407000b8102840d84050306d80e001e8076004213441400003042250301e50358101440b1090718220104041890800060070080c0300e0702c02c4009581006000b0b101c42410018103c51250a0301220035010b240c3c1802c640c103800081002c8000001c041c009160100c01501c1c14014001e00513000e80c9580d400000030817810f038a900c090720107001c5280342003110b0041d4082e0300c1d480d00c200110007400c5100200c20100f400c0000450385c2050310f100900c1030006e400c11002c19801c0703200908c240181504103d10861803035210f41a03a00182d406401c00140000f107c030003110b5182d01c04038000c038850f48450000c01c00d1756050300403000c02d06102d0404001520b480d03008030352a040440d8a607911170001d0b1002800c088204425600908006800c890013483d046c82c1c450b0080c1014010b09011518441c0055118500358046464040a03000c0d9a401005241ea4070805050319000c1c802a0b86088000e1503059141d03440682480340c0d0301d590105651144e81806003841c038024104508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538441852 1250 538440602 538440607
    0x5090c010e090c0313020406030f151a030a020603070905030303010b09190b03150a080d05070b0c09010519050d020c0a060c0302181c0506040b1f03230106030b090d090b 74
    0x1c800445201340c0ea0300c00c20080031031000703552900c0050000c04041c0c0004020007100c12000c404d121074151515001c284c0d02604020f05800280503241085e01221081d078150300c2201e00400501780304020b15044031460400e100d4107901c07040000d066800980100b41503000100e408592442d16000116030f90220459444100e03083c80d81038520f52200919503600ca0003000b01035456519503460300401031019005132024140c8108005140751b00c2071000b515003000c0d110109414040c0d00040b00c0410005850f05440c05404060f040078004080110005010090110b103d0b00c0305d590005110703000078200070348442007141c94000d0031103550000040c201417041c00740721507003210038520800d50308084507002021181e640c1181c04500000d00014054006c11050004115203400c7d014018112209820608102d2241c42c410b2900103100c007506040c250f14040d41c100d0314841036011000a42070001c00c50079103940340e140303000e842594071030413644c41454118000d50f0710805940c060210030004c02d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538443102 1250 538441852 538441861
    0x3090d031803050703120c0509150306030c09070e030a120809070605090d080f070b040b130503250b09071a04050d082508180607030c080a050403050105090c010e09 72
    0x30200d100d039400041c1400400660b10701418081c420303086000311641402d000c580c86000c0000c248e900f00056030750143c2e03043e0241401d140a5201920b1041b00090014291062214100041c900014160303505010078902d01864644041c480500e1840c000c030710120540e180480000c00c204401015104190044481440200d0f03200d411908401c0084402091410031410002d41130320501084800322000041d0003410000e07190a9079124a006040300f141d44e075208110000303140c1c00c19000170a1a08100400341c119914504070341010303461100c1e00002c0e4400daa40b0940e00f03003c140d680d160940c1c03208508211002000c3c0d500d2441c0a03419011905040c43c00010032402803400500405003800030411848000c1031071554007010202020f542107404050420340c2d025030000032140c00004582030300303081130b06000742140c00301681a9030741701c20b1150544071100d071a0070014542e070410008000000100d0302c03d018250055031004054600c043c4580d0007d0301220305030302180d0003030b01050f0800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538444352 1250 538443102 538443131
    0x3043006090b16030c0c0201050a02030903010f240b0906180301020c0f1209180c0715050a06091a130b123301090207020103020f041d0f090d030b03010b09010b03090d03 74
    0x450306031f080c20580c0d20ba60b0f0740102641507004040409030590300c1c02e184a8a035220310b0b049071601c04003006903d00e180c05141c2400c20180302c3d901681c199441d04005181060034014020100440948480201e888211000a0a81c4c2c0094007080007540130710714554100000b0301c8419603001e00313048070502d030a6003000030507038229503240601d00d1004007a00041c1052048002c030350b06540e128040c0d1802c5003d070404800101016109c00d10341c1494840045010469403080c60b007040c0030800da55245a50000c20070101040a4500c129019100c0403111a29107406000c60906500c19014102c641c14500c04013800f6000f81c91400508420440c031500011145040c240c10359050190150b520070090006034003920841c84a40102000081c0008901d80000010410210841804450341d00c4010072225010b0082d00e501030150040c003031801e406070203a400100d100030041c0000c501030000b400092031003a8241d100100038500041082400b620602c150070303414559040c1007040b184242d910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538445602 1250 538444352 538444367
    0xf050702030a0e0f0d0b04121701050a0b0306011403100801180c0611031c020a030e010b01020606060901090305060103061e020307140306040905010e1c0203043006090b16030c 77
    0x141c90084148441c09041501d642c0c003c0c3c0300d171541059407107500741014900001b805903952040d1002071403d001d4002020b032002c000c036040301da006008030522414902032410a600c080c00c95070602004106040744c0035a01c5010350700c60340e404180a100c0a2600c1c0a0310b0079903106c1c003206201c3c00403010540001895007810301d030580340f241c508502076407020780d60149103100d102010900d50903880c128100a05054006006000c0b00365424024003140302e41d01c1e801d8070920f440d0b00b8056000100080c03214282132001d842c0051052410544066582d241c0c5030500e07030207130410303605d00ea04c480f070001c0c0e01024481d80d0315a05441c25001c5140d458074000003064801c10056500d111400040848d500c3e40d81d94101d0b00c44150418020800c40c1d54003540c0696032008914104140c10399492407480c1c8134001b000b5102144d4080c010b28a02e49446803400e442c039000d80a101211410000311400803400074459401c440344118141c02c094105110408047e103510101c00e41054201102c85d04140d81c070412 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538446852 1250 538445602 538445627
    0xc0c03060203071115040311030a0207030605150a09140c041802030417310b090d03032301052b020438041505061e090d060f050702030a 60
    0x801030722522000800c88013942c4084000c20700788070f0003002d0f8006603102c090150185200e925010fa41110310700e00385413240a07070038030040582c004100800110f0450f400a50380003c1e107900c240101503114000070b00810550f00709180707681c0e5459080c05001010b40701c2c550451821858181041c1c40c101c4e030000220040c114100c600c64010000ca800c100103421002090801e503800d1540307034030403e007116601244040501040400070007100142d2143d1352030307420554410780116417800610b4400c1c006082c030000d03003ca0070140e40c2c0b400a20050ba0441c88040030b0415400b942c80c01394507000c00c0010340c42051000c45c1c1e0007104225910384507480d400d444542c1940c1510046920000c1072a02a802c408240b00d203440400c01003640f030546944410a008a803000319820008903441c0d0702070000740140d5004003034001404000c0b2140c00c46003900c402260301444110781e1318050911011030448a07090710221000398550b2000a00f1031006d014140c2e020440c0d02c002c60628280b02401060382d4074885 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538448102 1250 538446852 538446863
    0x14010b03070612020702060c0c010305540304060806031b010f031d010603140708070303180b0a030507200309040236120f070b0a0e03061005030d0c0c03 67
    0x60243d60b20072950151800d06400603c001d40b550303428814075481c0e40b1a414464002481d000c0016064040c40110f001c000b4016003000080d1b0583e5004900c81c002d450baa40d1944c100340c0f0340a00b90560782e03e10310f6100101d0701009152510710306100030303098042c0074004500c02d42000ba64800a20341078400c040660209180c030030811020803000b0380040c4028010380980c0200c401840168420541000080b00c0c4110789003400380780d07081c0700703a6160f5609010345005504410303000c0000c644580e410004103080d03d81000041d542e10005054a54004030003400405d07205c6041000301504460700c40c0b1102110744c403589658440246076900ca1081181c0244030302d1313012941d5131401013030940480c10003107090511724610712261201c0120741101c41c00d440c4038080c0c1c1305c0340b801d06020100300e5000d500030a800801c00d1505061003000b581c0c000c01400001c000480005421542c0c04216050180c5400d05400540c40e0510042c9401c00641c41c91120a020002c042240011400302c40442202e4021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538449352 1250 538448102 538448117
    0x60a0e03100e150417032a2505120f1308011b03150b2208010203060a0b040f060309020d02041b0815010206010b07020103060f030308060a0f03030e0907140a03020714010b030706 78
    0x1041201c0055170382e05013007e941c0c950b40c0404401d05e03004000804c90748208102c4605680c00079100003441401c9428010f025410080055012400c85d0010348401c404031864141411515501666941a0b550241c20a60b4403012200a912002003506031414101c0c40c042c000b807900180715184490030740c81880e49401000580c4d00c0021544ca85034210030340d040245042c540d80e5aa0303058082e4100350784a80c0b15a03494400018100e60040c100c40445802c080c5148209180000a42c02004080416600304c0300000034078005a55170701c41d0029640c003c0c01c0d0009502d034006802841e6000042402e41c05003102804c0342066030f00003800383d0464291042003a6100c0407807004034060f0186901c1522205080c020100400d0b0300081020b00c100320a44500700010780c0c41c0b514000c0180c55100c040e02003810100c020901d0b050280140c1e074404114281000080c001c194001d4030382d8452008600042d502251103800c0000340c01100c512124228024031980c002200002c0c1c030358011784106003e00080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538450602 1250 538449352 538449361
    0x140f011e050f04090e0c030c0d03030519020d020c010e060105220f02270607020f0603040516120510090b010e0403021009080a0806030d0e060a0e03100e15041703 71
    0x50011140442c40d00703240d064450365100009805000c031100425018040d004c585042c0e030400080019030300a00900922046107285c0b03041e00188800381c43e01c4100139003a400c3c01e00001040c001041c0d8030075512801607440388041017083c05c540f0101200344030341d000301004000560b541d00040c2000c1000c1801c0b050304500941c2003000030700c004408000d0540c0007080b842c06000c000c2440841d03407040398501807112003c4804014103480b483c837000307520480760300c1c0342d14132418598003442d4440c0c4180c00300e441a034400c00c1000d030300c43c0061707002c8451a1b40250003034080003c00d2000203841e440800741400740c04601d07510011240814080d11100c2c910110018007070500c01c10040400b28a022003c0101718402c0c00d296166a110348100b10100700044080340c0d00b410000344001041c2080e503140380c00041300808201040c1e000220140411003507000e0491540d4052112400f41c5100d5a400241045030105042c20114522403d02c2900405800c000c00309950000c140b02e000150160150303a0f586 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538451852 1250 538450602 538450607
    0x70b18060126010903080412050f0301060302071407030c0f091a01030b010203070c08060f0f06011d031002040b030a0b0904120f170a050118060b070b150910140f011e 73
    0x244038020102030b40c02c0103801d0302030580225405000320b02400c00c035120108e141405440f24815003240c0a102d11080004200c1180f00c1d60141040c1c501c56101d03610122213022440e8a07000e450782040d80c1c03006d4890001c224200e425100c0304000c00c03028406108144034502003c8000300f0394400309052644401d440002a8420310440e801140c1c403c2003041c0142d101c203441c0d030b564581100d10404048001000c90a01c441c0c00c11424421501650b40703080d24443c3c01589034603d1448c18800c1d07018420480c01d40c2002480d80041c00c00740040c0c601050701c9240202000080d10b600c1e4031010b01501d204c9040c007001c9481e02211381100c0d00d060402101d6036201a000b103910140d951004c040186a00c401c0c0086000d254200a0488200340540540148000512000c031680c61059a03013144040140700009a08100c50310361044e221103404000808480228503209021070749103004030707064581803244862190440030745100c25200075141444460010348440c1c904207100070302070200a050320b1350a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538453102 1250 538451852 538451909
    0xd080103080f0c0a1a22151e09021e0607110a03080301090b010f0e011209080d05041a0a0603030801051c080f210f0f091c05070b180601 60
    0xc4965084408224050401e0b030a001c4401c200c054850404d880403a0807203606c541d0050920b03030645003051142c40b86030303101021685105000445952604060388849620035510000392810702d102040d000010720401c85c0000400c969808440c1041d03142541941740c072030580700551f6021074940e5007642c0020016001c0f8255901c000c1c030700800000082002c02c1a90445106540280c0703480c2440a030180c000c0d1030705183c000f01640099001c02c503518541c0d02a40200d1400d600500300b1603e450704a100c2001a10405c80302501e5040c2c5090442c110300c08404609031340004003540401500e0305554000b40381c40b4040c81518440c0142d50b081c4030003030031020042e0b039066500140050361280c268140c3e0700c55400c20514186c0c40518070700f03600051098421000e2048200d03540d403032250b581c1c1500c0380001241c0601142914402c030004503806081024130031140040750f0301c83e241c8451142c03816011045004085403503003803240c440c01030040740c00503036503054a0b529080b003414940d40341201c02960 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538454352 1250 538453102 538453117
    0x603040804060c111021060b190318050703030f1b020f03011b0908100204050f04020a02070803120a0e03130509070201020f030a092105030103030f05040803120a0e0d080103080f 78
    0x101542c5c035130a1001d5041110740c610804501c101041c2a89440c40400489005110713085125008103d6803605003900c1c40704d0221003101703081c0010001201c9928010f1031a03880c03400c5401c1d922105042c01810f0704001e50301c40070801d03894440c0c0c000309000508402c581081100900403c0c1c103403501c010568080d04010441c1404122409004150040003004000380344a200918026180f50307202c2031040e4021281580c00140c041950050110f040c0700c000c0d44182080f6017117004204010841030404c3c80144617010a84c0019101c42c282480c940c0100c900c2c032400740841354420441c2c0c10700c0c1070250766104103d84049910b440380c1da880c010142d02910a1580c1c4c144400360000030000d03c4480303a4006441e941c01000170100b4503203100d04d11510204106c0003000810400d20040000a00c00c80c400401414180340072410250b507104d10b10302c4c603000356280400745601a0100081442c46204024030311940360018045845100b5001c2c1c4030340d90601000e0000d410018203020441207282c11106030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538455602 1250 538454352 538454359
    0x20703021c050d081501050c060430030e07060c032111040f0e010501050f070b060105070b0a0f0506100c110409080412171333090f050603040804060c11 67
    0x500f42190700100304403405c030351000001044c240c15510b02d500c1a400c0d06c049241020040c071064856456000080109042c05103440802c203141c1403001c6071910008803081010703140814540ca2000405041030202d8100d441000310154240010030b51004e2010038004a44000311060b0900030b1a900140c100e03400b07940a0110000740014462030408590030440c0c0b0403000070b503e1139889000440c0c59200b01680c0c0c0390000010701c840d40201d6001482540c01100c14144949001c0b004c0d554060200d00403112600302c0f61390350301c092448054a0154941c042d50031161a4001d0705007940c0030380340099206000d00344200904074808035885079489203218a030004251030700d03030b581e415498018002c842c03011250001102d10500132122180306803070440d8440101c0400c81c9050000403107980114401c260815030391001c0c03c83d0510110742e8138201b0031a041d968000c0781c074209001030045500c00c0c0c3c42140145420401c0001156003001518140e41b07651400106590540c100300445000b043d032525032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538456852 1250 538455602 538455613
    0x12120706060546060513080105090c10090306090c2405030a0e190803071b080a0e03150405060105030c0f0303160203030c1b04061502070608190e032107020703021c05 73
    0x4ca10744c0243c042c0031480100864030704d4150301c0c0d40b50142614025206c2400a074007150180314203207044404044c0c8072842e40f4003441183c0c2d0300d17242d60b0700790b0341c0320102070320709513501e01301072180112003441c4030424161040584040700310074100a00d1032200a100070b1039582d035030041c1500001c1c144441021903880082d000d880e50010b04040070141e2085e20440b000c0740341442d0607402140401401e1081980104526007409100c071020fa552401515035203500d80113400313000c4114030315880c2141c011402840101170035810b0a044c14603080742900136034843e5002d403605000e55a800412a5001c0f0103601002d400400c2c0c0c2e201003031641c080d06100c2146400307401511442180c0c840f030b1550700c208003142c0620800341d072800c0703113848000c0d074240c0480160840340c4240301240c090a02030ba0011392042e0007000900f0185040022264806503106003900001012032040e80d0400581125030a1407141800d1030a044001075910880342c40000d00401c1501340e040b50315541d400c003068465410000391807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538458102 1250 538456852 538456859
    0x4020910030b09030d060e040809010c030525030305090309130c03061d0703112a07081203041a0124170a05090616021b12120706060546 60
    0x2900d0760003040c0720114083c0707807502c002801295000408d0241e90490522440c10040f100115038262807040182c045c00001c011140348035440c100d000c5802103101a00b40011080e43c600201500c802400043c0740d030b48280030540d0140d82c2c550348140d0440c007105c800079881c3c0c01d65105802400080c3d00038030000c0e00000ea8080159a240081482402281d50401a0b40d81d40a0f9581060180b0030003400b207282c410102100c2c101c0000461000c90340b007070044074540c958500c182c50ac0e10340140300c5156580004001d01c02003120038030950701c0c5243c0a496180003503041c1000d00c0c40d295590722907040c140848201098905002d0204051800d01c40c0e005001c6a203880485903018201c15071702c150152044500082d0003282c64506211044841d030301030b00fa2072401c45070080d80300c501c50000941c414511440a01412810071001c0c0f046900c003811151a1074036400c0080c05c0755035a45c0140d006941002107d003141c2c00d8a5207021501c0850481c09115030300c0b010040d200c0d0243c045000c1d40d80c5000c42c0300031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538459352 1250 538458102 538458121
    0xa062316061d0609010515010c0309150302070303050a05010303021908071b14010201110a0f0e060315030d0c03050d02160b010b0301090b0d11060a110303010b0a030b01080f04020910030b 82
    0x1d010b0080301c0d0442d05103485140410342203c100301c5042011b54020032004000b0f62164001b955003e0007841c203807111949075a500602000840d1034180883d0f030000b0304038105034143c0501a8800d0343c00d0030400c0303590701d0354070301079104c80b198040760541080201641e010440d001055071030b203a4020f0541a803082403c00400c500300c40074041c10040481542a200103584140512411107003500f503220f00300f00035140242c515904110b144030a00a0303000c80c1020503200ca4000d50b204090450f82090a444a0303424141004009103800c01000194107000000c030350007204441c0403052551300103a039025a82e018400440da1204010b1158203600f000142183c2d100d0044e505070b0308a0182080b81100e60410011080d0310070758014404d50184102103054581603000c0c01c5584803505000000d0481551120b00b56030098012451030762001c00c580840552610491283c04d1007820f00c202142026810201002c000401c000e01c6811340c0030009404000c4050480000c41e444510b03d03c0340e0070001c1c602d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 538460602 1250 538459352 538459391
    0x2120708180721140303010b091f0e060904020403021507030323011e180902010813020906061608070c0608010504061d0901150f0e09070608070804050703021e0a06231606 75
    0x1d442070ac0c01c0c0000448240d200b1440343c50251081d00c2e68905413000e0024006170b90020301030140c5c4158240300000150301e4402d0001c03851000601d0a980e80c81383c43c80d000c0c04568840070075542e44d0156865010b04040d1100c4d100c0c1c1952421541d1200d00301d40f07402107184540c0250000812245020b510365841c803410b030400d101c624400d8a641500395115079806034807440d880030103540103000740c0c00709416060020050103c141c403070b84d0248030070042d500c600d103180e4070560341100c034185080020006603038858110381c0940802c032800e010682c03401c4428621f90305a040030181c030503141c00c0441d280c07040c00d40c054400d0011405007200d10340d6503126846140c3c1541d1003810141d4400360002401000082007500540e451074950232210780341c002040341c408038014000c076010b1143c06404405a900e000390701d41450030320380d03454500f130043c642400810038941c1d0260f0184856008901e100d100900400c01203941c004000507210400885004082c0e0003407e00506603900c0e01d24040088400300c0705 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 538461852 1250 538460602 538460617
    0x100e27070f05031003020f04110f0c0105060324060f1011010b03070e1b0705030301090b12060601091215051003140d2102120708180721140303010b 65
    0x2140401d40d1620607054645200449281c02c110320102400e000600d0b1905810f5880d950241001980c48100f106a56581c0d2010140a4680401050401114070240906a070043c001d4000e0b0404880454801c2113181c4d03061841c158640c64180011060b84440c002c1105c50580100404490884850301030b144035814001c180195080007105541802c0006807102102c812600c00105556061032905011070303011034901000700104581d1010a0042000d18043c0c4842e550014200d803282c0b0401143c103003262480c4030160802002c00c111680c018070a50102c865505100c64014698944210460030825192011a00d404c0c1030051000d4055400c41c2581d10480e26422110031200070265210802216400051503172100d58003605c60030100c80034950007040016080500754415682d12440480e410b50000d200c4100708903036210305070400f660b8584100d0190032a1414548040210714180c00810762008002caa80b02c00c000c02c1103400b0b80880d81d4001543c0c0c032542c43d4070300c000941d440b00c1c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 538463102 1250 538461852 538461857
    0x6060f050a030f0b0720011506030b030d1b021206040201020f0a20010302040801021903151809050f07080a05010c03021218010e01020d05011d0105100e2707 69
    0x49022406040400d503000641e9002044000d00c041c40340e44020761410024220010040303240b00380c1000402101030503130007407654030000c1080302e81907040c038840c0369880e4096401c0600f030100b850b0301a01c002c5494480749545103003031140007400e18032400c42810895402500400c0210101c0c0e1003680c08a00320740160b00c00d90079035000005030710505a885800c60f00203000c2c07803a00a502c600c8141100400301241d081814058105a2386001890032038000c4040d81038058000d61811503c994103108078280c4a1201250070103480c1403030000c80280c0135200000701c0c81580c840b0b4500c180201000f8049501d2489001ca407907854481003155222455120211407640c20030380061000d60090080d240f2844210380c492160b0340ea203600b181d03402040605010300c95542c510300c5034940c0390f0038001070039041d40042e00841c15502d028500c151039900200200282c02c140c900600c599501e030b01160841c0310301448c0078000300001000003160154980e000102900d07000c010b100460101c03804642c4a49801e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 538464352 1250 538463102 538463129
    0x1309020316020607080f1f06030507020c060406090b03040212010e0304061412070e010c05010c020d1b0201090b210f090d11030f1b010e0106030b16120203071b0606 72
    0x110300c10b0380e40d03000980d4840e02203980c040024040380d902908555115002194880071440c0c0f801c2501d03034030030341a00644002621a8100729030b0036010400d404070307403a0a45045107050f251120040170b050040c080d5a075640800070105081d035817421050580466102c008100d08800c0c40c0c1950b60f00d074464452100070411101d010419420210305981d0125442103403252156146041140c10740c00102d4031a040c030260074400408980248100016904507030024404880c8821000e030040581d00c8a14135006e1042c0150360050340d20000800440754941456611100d270250a0080e40c8800c2c0d21000c81d880240382041a06002403a400380151002029603003c5090000d0403030302100d80150010b25907004000841c6021516002801040f0903240800c0001540c0c044090940d0201500050b65a4540a040c818072118040c1680c2203035900002014440d2425400b801514421680b00030241c0c2c0800060f10890203280950302500441c1e040c0d0078880f6051500e180101b205000d01c54080c18107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 538465602 1250 538464352 538464391
    0xb0c01021c09020d02040207030c33060305100509030705010216030801051e130212040c0609060503160c110603070903260d0e010608100603050115050609041113090203 74
    0x24850388102c02d40182041d42c50f03007103035028032010754000d9004804200e40e46494801181624142203807001074021a4844400100d41d01805030b407450004401c03051a111081000030000182500328480f50719001c5071586c0c5038140386056002d80400600b95500014085007000301c101c00c8455180c3c82500e418000342d0300d074010300129103804060a0110765403c2c81d05221071905c80d959200500d0041d10140c038001030503801040400c0d0507581241c032850352142c2401049e41055100c80a420980b800904510b040040042d07584200c18403d0140450300c201d500034814400c81541d40c0c0c04001e080640d0f2402d0503000100100010311007074441c40104802150750604007200454007940c091805400c00411140c004001c0440b520036460b40d41d6075102c00245000e0900443c00c0d5902d03600d4002403c0c52550918a003903540150304a01c8002081c00103010136900c03182a10458081900c00203005490741c1c000109920031103240d008034041200001070700711000d030002e61140c80c0c05401882110351 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 538466852 1250 538465602 538465657
    0xb13380c070906030f060f021b0c0f040b03061504020f03070206071d01090b0306030c10020d0f020601270f0e0313090203010521030706020f180a0e0c0906040b0c0102 73
    0x10f6900004003007210062440e0085421600040c00c11441000b00514000c04104403481d401c0c81c28268800c15046007030b451000780b030091700004c41610242d030140100d40c07100b0001b0384c56182c010021400764820380c0c00045180c80e035a041d038001c1a40b1001c000e640f8201424007030341d1079100700d8034003000901900c0403c6083e00f40410424038a107040e1551040a0305001000307900c0d030002011140c07d84200d01c0303112403a940d0700c3c1c60403d410203d50050a18aa0b003c40d005099420200c4c0c201c0c103550000004000c185102d44c0040940808691602c1c6410010f00e5050050020403080d40c29090800c555100c3c1c08201200400d5480301000c20700d80b00b40c0e03480241c6026030200348241c40d8019072080001e1120b140802c42c00054410080c01c0d2440c20000b5668441240c0003840948100d407000720b000e10038140d271110081c151120840303a20761039620b418000c503420b40300208031681105010403012095100c450996000c0c0604241e0315482d84114802e00e4003e4112110440b00340c0e200754212030b200e68 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 538468102 1250 538466852 538466861
    0x3050d020a0302031c0b030102040b040501140301140409030c0b10092d0c050705150f090f0a030318050f0d08070815041e050a0f060b13380c0709 64
    0x2980350b0099410494000759505c12039141c03a18440300030381c9078201c0c02c3e080e5500384000c1c40a0b02d41c2c1c9544c90344860074100010984641e01c980210414404c000510100007a0018000c50315400c5a011510302c1c1d60749011182c0050515000345400307030590a015030207006003140030030b585122104006403501031b400310040c00070165052220000d81d820654500e80c00b030300100da4002040c1031081c50242560f42d510b20300038000007240890f48084081c000c6458604000c9a04401e405004055038607400941940340d2011840c010b00303050fa1480400c41e01126031b41c00c2000e907a040800d07207240d0f01c0503214242c0c40d040350850f070f039001800035400101200d00540100d80520b603d4222407140c503103050305020040885403030300d0003003424041050348005001c1c002d6500c0317081e00701c10108003420140024804d454103030700300e4603100c038040c4007005002046615050480e4280380e40f1070009034540d6240b410510b090401c85500c404010100c20f80081600d00408410103030307034200e031000b40da600398030b40489 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 538469352 1250 538468102 538468123
    0x80610030f0803060d0c08060105010314010302010806040b30010605010201090305030403120b060c0a0203150c090609240705061b0a05090301060f18061a0304120c021903050d02 78
    0x1200c0c550300c0e1020441034009107034051000b626a0401145984806c401c07030196512a00455100d0b800500c0103590601a5000310040300c011182c1071b50540e0300207816200001d0034a40195515004000e6959448100f194a200c283c5601c80303103c0030305c0403040070f440001c140290f82c5600384030b0300240d43d5205101e000840c0340c15944480c255116654100c40064a850f041c52585843e03036120125075403841e004108900000d401002240c060744103040c249885103644440b034000c02410400550300d0341c81100c0c80f4180c111052070f03523100c4071341c000703992219a8050405824007105060410102c1e443c01041001c0c000c2c01201e00d503603100000360395a2106007440c030210200a21003188558081e01c040c2100c08401000410301c580c0341c0d403c02c50743e01c4007684a2118246101864a080c1d00c4500c607150141000510420203400148980c0982e03110140c40240b049802c0010201d52078420404c01c008242d008024595450401e2070b40306000d901804103944501541c185083d40c00d0000428a400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 538470602 1250 538469352 538469363
    0x1120201080612070b1303120c120e1c14070f03020307150527030f06010f06050f070210170c09010e0301050f0f0709120506070e06040602100903030209040c080108061003 75
    0x3d40d007450040517460f0428080d07812100c03910305002c07000a0005191110994441d580e40600d24414206100240e01d2160840c0500c028415074400640314009440040a40c054811140314030510f009408504200421151401002c601154150f16610f80b4811039008404a81c0c0e826116098040046040c030360b0750340400c1c0200301007060144164042000d8900900b413030a82a084800480e00b050788404402086802c0701c0014000c01c64012244d1016086519100c0d041c0f5008401c0075807544510000684180c01d41203c80c26002d200d032110301c0d000b104001000f202c504107801c052025803c110310040c0480c00c658046400e6090500c04c03144102c1c8602070500c00383e02c9240040760100300103020351003040711038140880c01c80034415112464a205400500c518900404000d100c1480300502e94410780c0c040000700000707980080e401445480c0c103940041c0c2c41c2c01c1031500790024415810b90b150400d01304001c9404c0c00d0b410041c00750480c0c80000c1580d810360384004060440c40e034180401000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 538471852 1250 538470602 538470613
    0x70b0a0f120e0303041203060909031b05120c07140d0b0f0411030d12050603060112080c07120503130608090d05030c0c06040b15030a0804061b0b01120201080612 71
    0x200e05104240e204215498280001881c0c5440d2086034110f500480701510640d460702211408182d061050200400c0172140401c64a4040d940080484007010400138030700100d0314031300040c050140301c0c4400701003030169019964400084440d440740c0302c1344139a602c40402d001000740c0c60f080c0340090807103842c0e00c903280200e40d507034500c0072190180d030207071096072900e448401124a548041000310305c1071019444001040703210b9503101059a20050145009410080041041c10138010300044019400090a42c13111140d280c043d18210060348140b211488030b0f41c0034428040080028040303031121201d4220419150781c41071301e9810042d220602d0981c445c0c00c0d0550300f64440c2c0040e40d04048418031b080c0c41c0c07004c045011468150700b42c0c0d068410020300c80034013409104514140c1d11044040e8060650800310791a4140a805280b09020903c821500301d0280c0c601042108006c284e4083d0b058581c95031500c80d4400c081205403030407404554600301003542403501001c0340c07002d076003160020403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 538473102 1250 538471852 538471877
    0x7170606090103090606270b0d050d0518030a06020d0e0115060c061d030c0d111c02100e0f010b01030b0f0d0f0f20042313050618070b0a 60
    0x10000c0030440d005440081d510b2901040803202c180300720104d8200c4150f5641001c00221f085c0c0111912521820300c038086d000e001c0700010b003011a44c11030f04865414810340749c1082100c84031052000d4000c041e0706001300c11003201001020703406040500c482c84400c0000300b000c2102c00d82200d0f204518080c00a030401e40c03c103d418402c0c120060307001d00c2507101081302281e8002c0390a80036007102003603c3eaa00b0201700b00c01050720801c1400d80c0400c1916060700c190008038096901d030000c0c8201d15240c1d1104810703140c42c5500800c080d2020b1000e1000800c17000c000d10140715201c44c0b0f4221041400e50806400d00e0310740d031090181c854050001000380101d5010001040412103100d035044072a80007280c1c0601c041707204030700c4c1e030103050f8010301c4800480120021400501d590446605100e68035101101c200501003060034100710407a000c1a081d513440b00307900c0702ca007004800310003060ba12481003000002c847c400f101202c1d0000e07940403101b44d20344807899013900303016030320311080010304901402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 538474352 1250 538473102 538473107
    0x2a0b0414010f0608011a01020d080a270f0b070c03080114010c12050903070905130609053c0105011d06040f020a2601060504032003070806071706060901 67
    0x12206100c01000180c0102d00309588019225650b01c0500705954031340302241e00f02041580c1e4070b0244024405050809041c80f00500050b0010b032100300d106983e140d000f00002c01000001c0d02001401804040300007582c0751800c015040345104440c0d11a000c404a01c0c0740340196009000d880d0b0680341c0c94240da091000000141c1400c5070000c3c10000c1a140d283c0c08100c0420020844000d65030310640d540144800b810329008913a0302000141c0e280404020a425904040e4005140e01c880c011425641c0350526601e021070105202c20800c950348d00b5024000e0754420394031800040160041c1d8000c582124080c200c4409105254040d00101c440c68800300c800034685038011401400054810b50501c2c0100407038000007100e070041886000da81c90700c160172008082000ca802110402c4a41c1800c0c0001c1c864010f42c1f00081c0045160001d90186002c6400d4641402102804a50350960303a14001ca5441c00c00740c811101242c1e10411030200b031f0450080c240d1044102800ca43d29090498004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 538475602 1250 538474352 538474373
    0x17040503190512030907090501051507080c10020d0b03070e090c0d150c08060f1f0c02060d0c05041701021e0f13080705011b1e0206040806072a0b04 65
    0x8035032500916083c0c2091600344400ba500840115005001076814406a0303400c50308180c0220340705031b4507814400814100f00c022034611542c00400c0d05d840c3c0803038029071858a03000e00e814503651070003c21040303a01040c81e8401e01c01c1d07a01c124104c40107075540302e041041040b23007521008081c0d000100c580b8444d04020b50101c4039248241d4098549503d00790500c401c0301c0d40100300c14005581c080038403280b85090810044031020807036040e00088040028891314115081c40401403100180740c103800d41d900c50042d00c41e24101c100040c0900e4807941c50091495206d03001781015110840c0088031030700c20510079030703080c400400907481e200301d0340031210076482e001003404104142041041c900c00382c5000201c1c800801c1040d0080ca102420140058105000f00140b22020402c40b40d5490200c2d144e2a444100c421070002d4010301c1c80d606001295241c400c50b00000a00d100d85010300c003039641d00c1a520000c11404e000b1088071402c1100b90014020105400034110104450124000c16000c405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 538476852 1250 538475602 538475653
    0x1a091504180f0b04021011060a2013330e2101092f0d0503040302030f0303072607030e010f0e24280b0603040f17040503 53
    0x8580c4070071030300da0341d44607000551034070443c0c14440070000d000c21818984001c001888841c00c0c00700319400d0381c01c4415a1032200078800e00b00d15886261504500a11000c02c0c070301c4000d0f54040355612076000b05162007004503072040e030b00352500404c00040c0b008031050318880d140c01d10001440d00c9081c00030040f600c620031014844e03400048841030a40465510012000c1c03000f1940020807030414a061070300d08960140b04001c070684500041d91618203081d804810a643e044032034400004950070200e10b5401141c000070740601c980c500452281000102031132094240c0d039100d107602d4418208050002501b01c400300d55801004010421141c000d40040c24603c0001c40001112011180c014050310140d030200c0100b60801c0e12064410291026408802c01540048000da42846008400210300041030400151151f860400c007104498000c00c1c0002170042c003083e2641450300b0449403030070a0340822111305101c12131001003c400a000c2e01d08942000b806020704003030030b01034003045440514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 538478102 1250 538476852 538476881
    0x1e040807120519140c01030e0309011110020703080a0b01020705010827011a030f010c0f18081002030610090501050d0b0a030c0605090909150117010e010603061a091504 74
    0x181243c40140c90001e0003140f081c0110080f4901c03a00301c551050424031600000e504040c00c3c900d030300f00005800402c48250102c02e191101544106008482c2020a07800341c0702c0c86070380001041c00a050380045140d004038520803007040710800c1c0c0030059131740c0c840b1807003018086010280003814400c0500b0003001001010390200c0c64603103400e4041400c45d41000981042d210f9420026007803420100a641c980003001c100230003103070f400c0301405400c0070862402081040380071005d400c04040b0a0503004010002041220250013000311050083d42044035801d0007030251400044070b02d44242514000c65070107842d075a240c29404601000580000b8649542240360018004006501c060001c402011aa56a5501ca156810030000c18590107000c06046a001c1c1c00102002003689200794111080005190000e00480c00407d01400800040c0e00c500d500e056400420301c216500540a16074040c400706100960020070040b840c036065031441100308003203402518600f003a80c4801035a01111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 538479352 1250 538478102 538478113
    0x60a0c020307050f0318011103030f061815090901150b030703020903070e06120607021002030612060702070603110a0206040818090703090b16080f061f03021e0408071205 75
    0x90f11010720313100d0061411580c076070002400081d01c08940403940304207203091800b151000c0800f1282a52070101a00c062200417041d00491590f42d01d00c41036000c8418002c4140040d0320b0800c0c00aa4a0400d10340c03403900031a1480c1c0041c96282061045168840102d40c0010303803c0e041001010045d00014020701c1415400c204d0030806560401600e002003110175029001890007106010001e11560340a414507402681408112500440c64609442c00d07000c0041e226559440040c6061310703501d410207030354002c04080c028150750100b61901542c0050b2014808140c40320a001325510400e42d03c1001600100082030004026500501008800c9510072403040340c0780000600550b01030b00c00b41e000c0303aa0340c0303613010800c840d200345150b01101604140f11031016090300a0080c0c90000c0440e182000141d0020744560355060340720300c2d1785041c803d41c9030034001c3d107400103802544402c01c8003080d03444c1d1a012100e110048802c072019240304101400715940340c041d0071184100e28100448090242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 538480602 1250 538479352 538479367
    0x5070e09131b0b030610021609050709031e03020c0603010510050706110a020325171c0f09020406090606020705150913020403060b010201060303081b0c061302180405060a0c0203 78
    0xc101500d003c0c00c200f500c103030b50701c2c01e0801c04c005c0005044130040041d500482c0700f802c412440000c0c10003c68007500b03004119035075401812144c486858000520903a0035030b03003203155615150301001c1e40724842e4003124801741e00b401c100607642c0030921030720350b1040c0c0e502081802d07140b19001030306a4034818000070866800016441c100380c0c0010408500503407011940701c003c403001c0100030034003100c0c40000c40f1004206440312a11018801c100403008030b0001540180c000c111416100200f40c06003080204080c0d1500c0708014100e80d41090340b2031b906043d00490800c01d24030611045400540003814054503203810700518480c9860b81000294003031140c144039072142406a96103055a00340160b0312400d40c50600c080b242c082c41030b20f046a16203031060001941004000c0d800c01d12048546451148c4c1c10740b8101a13110740d000d51a41401100e05229038164174100c61843d240c4215803801505d40000400820240700710b030058810b52140002c6138000315070303500c0107500044a00c15a840e1409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 538481852 1250 538480602 538480643
    0x506090621280209070503010b0f030408070c0626060a0515070c0e0f090d20100906060e060d11040c030b10110c010c030e0f180a0b030105070e0913 65
    0x104007001030a10307014082400f189402d0130003d41c40505401e00c107080d541040340d0078500c0d00401a503c850000000017182c02c4c03102c0b10080e24042e035842130314880d43c0c640f00c400003068400d80034644400442e08a0854a1200030060030f2441840045c0411104c180b4290030440d5522122400740720b0304008200d403001040e00c0d00a0340b030241c00003040e81e400c9428142c0f20341c0302c4588000c0c0b080e031450308a8002c401c9000da020742c0c46d0161014003110b050f18041c46807003243c04c02840202e0414070a103000442820000c107504940304484010b4078070320700c40d59000d00380084030003045001401208c01c07410f0f450f60707031400380d105da035080d159443e0000d024010240401c4a08011103c1c0c000031409024204403000c03030420048219060070729080b4601c1040d540c02030100400303c005240305106028a0402130384407942c002c0210445030080480c00e0400000c004010322081d84101d01a50808000074142030003024001d4040304060242c0100380e498001075030015511038400c4803a1500c8850301409010b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 538483102 1250 538481852 538481893
    0x3090f01031442010e030f030a020703021f050f25150515030c1201020906030c0a021b13051905070336030f0c150506040506090621 58
    0x38041c10041100c05101201031040c5903078242c0351403d540000d074403090810105010030003c0d030001c3c202058650300c6440083c0c203004801c02500000d120229203542c1303850b800a024001c03a4025288260440e4200c81c5000c002c0150300e803000003107582004880403030380e040c2005108031607445810030403416418064840c480d0030940d00740c40045107641c00c0903445180344250307900f081c1441c8640e07510f403901c140460307101c0d8085058a4070407070802da02c954074208290101d40241d600209038a0350780c9070074140300200750440c500480c01032040c0713503206410250b07800151007030110003402094100c6140036404050000144154000800500c085804006900841380101c03070948000c55468032044070400388150058025111401c82210030280c1e01687c3c0000c0405e541600d061040b8461400c82610b2504007040010403084015a00520002c2107510040c000c040485050149840b0302d810070030072035025515a0742c402030034208040e4080c400d9000040442c241802c2c0c039896081501000c5210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 538484352 1250 538483102 538483111
    0x7050d060303032909070c030c06050c03100b030105090c070204150b180109030206090904031707051312021807020c060301090c030501060503131b09020309070e06030f03090f010314 80
    0x20341c903019010413400b80c008103000001420481203090856420024004c860007505400600c803030289194189481026510005601702105010a08040100184a80c811183c0b80803d42d881d980228444000d40200ca0407140001e00030500ba8072000060800c0e5440018101e07401550740d800180c80307204001c02c210017460103031030903500c41c405409200701c260205107581d030401460301011710041e92440103a5200342e03025100b0307440036619440d09603189240c0140c9000030100c100e00b0805000c1d0702ca801429840c450510007400c0c1940d81c0b080050071442400000d5000345600010720b6080c50807002554050003d00c11101ea040c20400840c00d258400c0e0840a800d40e180c1960107201c0303405006041c01072005207041455031400c221b55103180300c0e0360403006241c0d41c080c4030704039444150001490043e00d6803007021596800c018121590301e882501c20b0300214040c3c3c10001c1e44a1a02140000960400c80f000d0f500e0400d00004110340c5074100c00310300d4145a511031240b006154200c0005115 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 538485602 1250 538484352 538484357
    0xc060325090519060c0b04050f0a0b060102070e040506070f18030302010209090606070312090203010617010f1b09060e04060b070b07090905061e010c020429060c070e07050d060303 79
    0x1c50030300062001c100d1000c4200c000c8204006010040d2544c42020900e58680110040100361160f240981c02c00710404017101c0d00744581c5070020f09201400c000d50340614000d03002c884d0041d07510200040c10310030465000c0d140350410000501c03468019030303450354100031518000301440c006030280300c0050241c1d081600181e5000c030700e0041038140b41c80c0203074004404864035801c20240b07a0780200030008a040905046032200c1c4040210b450075001381e00685035483c000390314003000003001c1340205103c2090380c100c5070030030600c040c0580c810302ca040c440031841d5581e0204a424001e0688000542004098100e075851070001020240c800191040c5440707861001021309000400a00302210703504060500c51070305040c051196144c1032000110a002c442c1c03000401c899038010fa40803212090007a40044c01c1650a8640841e81482c1c032205c2c00449110075960b000c1001813101d2401070490f00391403903000c07034800d01c00c2c500080c0e1002e9000000d46071441c5000148440d200a594559208a01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 538486852 1250 538485602 538485617
    0x140a031212090b180106080105010b04051e0405070c020f040509100c020f0f0708060c0a02070306090f020a0305060115020303190b030a0f0605160302130504240b0405040b03030406020c060325 84
    0x204c40207009210080914070001d0109504207042d030342c028841c61041e05e102d011042d0084056071070540d089080d1980040041045180c103941c09498803030140d000324403c45120200300c856181c940704140c011342e542c0f0001c2400c806d0030880e6100402004501c0030035841620784402c4020001c20203102c0c040c0c01c08000d020303a189030404440c9800000740440b814800300f80400604103900080280480ea0802000310340140e01d82003806504030803890181d00020725003008030510200241c0c040c100c1c7c46140301d0040440c070b1454101e860f40400e0302c100050211040c91620340b107015070494109103400a050f161108126900c070340101c1440c0408866554960040180404104803881c055004e6410291b24140d00d0887c4000b00d42601e002d11482a5500c04061258403804064503e001980c443e211f950b1a40759010202c181c0c20500c1030358030075400e0094440c641d04012090b06d040b25881c0d0000c0008207501c0f0100300c5640c02c01450841e180194400700005040c40b07040468407039000d03484444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538488102 1250 538486852 538486891
    0xc082406031e061225050d0521160f05010e030c0109120c020303030a0c030e070e06100302040509070c05010912180e01140405130204090507140a031212090b 69
    0xd51442c402404684500441d001c40083d0311000316040712070381c0074010b00c0140340e43d507200303820f400700e0154000a400c407104003e01d20030850000303401004031317000b884107070400301d441801c0c100d05129030360303003910f03041e400c4e11513800020800c201c1164101d124400200307140f642441964030311740000c2100e9405a443e4100c000134840285111640c140a82c5407901d60038840744c01181d40d1740301c040d0440309a1691100c4415007144281d103c00f50803c9020261107005548040028440d40c0c280c0700103200f0717403c1d404075205803070003482110200da001a000c41010707a904101501c2107000d0f09010b50741d954840c404000001c6a1010100311040c0c0e03500c80c10344010310990844880c4440b038200100302042800180040e07038465a2076881c000c0c04030fa01042c0c82da900c0c0d0f03c80f0514100c41000940044c2400d04a40803c080410300e0300a13210051000c1e6000e2680404001210440b80320203401d03180c2034101c2e005c14a1085484103400542400c1c0460031b1403090f0f0f03c0a40c90b40b07003150100741e6801000c2049 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 538489208 1106 538488102 538488151
    0x5060424022d0609060106090303050d060b040e010806090105070504120c0302090a0b100201060302010905010e0414040501060510020a050607180801050a0b010e01030c08240603 78
    0xb203035104040100600c603a50446a00001409014005002d101c0c000031410f040300d40c0350f80c130340c90002c1c43c64a0a41d020b520240441c854181c44074804503040c0b04102c0104001c040720b2100c510690300d0702c0388513818038002528000060b4100710500281c030758000c0039107059031803080280c458903d4516011008030303282e47c002174110420078100a4000c03011f601c00d410140060f10703110003641180c5412803c90f0342c01c0c0002804200000c0060007954070810080c2840350024000080782c840041000c17900050498007118182c2d1641d00920541c1008040710300300e070300c4070b0008103141c002ca691455101c080c01840301c001c0059000a498140c4e0349840c1e00300040c00014004c10441c00c0c92030100f8054402c076511207000c00c0003041741c140c0e194481e02c00c84080040036512058291142c400c52030f20381040045081d40c907500c1e40d0002c102603503164000e40c013a400041c403049080c0840e600c1d9 = true := by decide +kernel

theorem cover : BRFrame.Cov 538309352 538489208 := by
  have h0 := BRFrame.cov_init 538309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 538309352 ≤ n) (h2 : n < 538489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
