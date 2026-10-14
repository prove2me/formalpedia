-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:29:31.588468+00:00
-- url     : https://prove2.me/submissions/6daa8ec3-a073-4ffb-9299-e78850169a63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425359712 ≤ n < 425539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425360962 1250 425359712 425359763
    0xa14010c080d09050601030c051201060806150a030b070c0b0a2a0e04050a1a0105030c19050403020d12030c03290103060509040b0703050c0712080a061a0c070819 71
    0x10882d01600780000700f0446d00b0b1500c4410344002b12190740d0f190040192490880d61913209200311070740007102003644c082a1054482c00f21310043c1401c0b16141d1642c17524000100c0541340007000070040c174040401c0c000710200e071036003110368210144080d4030145105640c01000004561a507200213140c00b0704240519803420303200750041d20502c81881d207002840000c04502035841c4e109800348859101039072003501100d00c1482c0692000781030054100085801e09503102c0720000b230241c01c00c07001c80542d5841424100c6a48612035a95410000020050654281e149010249428011407001400400e490103101011040180141c42605030040f00038245030b80c400ac1e04003403601d007071105021810004503c00d074800d0b1400d00035a246c020301800c0301c2c802e042000d002491518104000c0314400c14840d43c010011540100798592500d10140e0400c0045010810b444800a0340210005091108000a01c2c0100151940c1360592503c1403d4032400d400c0205203803c040e03031608886454801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425362212 1250 425360962 425360981
    0x30315080d02012a1e020a020402070b1006080601090905061906110d140909060102010f020a02010902030c120705060a030609140618010501050405060c0304030515060a14010c080d 79
    0x84900c078900740c6402034001c0c03480c8a05502454400c0c01c03024041c0c4400c0035000c2c9000c11583e11108500c150f121410410807204203480118010b151301480035a803a400036084050140c8000d140c43e04146501c0781f040d40296100300c061203010b0041000c16038102d2107507030482d4007440b00030400703542ea580005c820030301810302c031031344081d50120114a15a12140d007400d1480c41030225001242c0e108015900a41660500347e1040420810310109082441034950003410600000c03807140402c900b480141d801c111a0107006079503c0b6200c00640c034080182d038280780700690f0691001d40b0024a015219483d5001701802160001500c00c1e20303900caa4002c0c001400340080c1000701102400c40c2c4400c15005a41d0300f4401c0321261441c540c4219000b100078125a0140c41d114a07140c605030600845401150404003503000a0100001080003408000802d0b401d1022001e100d1900200b0094129416000f01205900c07115600c282a45c01180c1d00322001c1d00052100c2e00c41c01c086001c500540740149 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425363462 1250 425362212 425362229
    0x120e03030a060e010801020304120e04180b16050711041112090c0a050418060c1119120c03020d210e060108010f020c030f07060b0d05060f060f030a030315 68
    0xc10400818080d50100e02038603c1a00321241e1660b0703a51030395082c0c1c0402d541c00341c4a002194081d524030780c010400601c504030050310200311060041404d0380e400100b10000e680202044c010801840c10505e614494010f05040080c28401c3c41d4450748429240c03a00c2242c020b03903071110102d400a1182d015190070b400303921243d04442c5130518096131108141105e40e80600350900d00400c3c1ca15060042964444090507981c4c012030060702d50b800a00f01c00c000600500a5642a10159100500a030304404044030441c00141040b85001e0019082e0200000200982c081064001986c0407425880131a510300d00032800090782203045503110b5040040910aa141000c8803000010206000e81250b40080003009a4070075220f226003079114031024803105070002c00404120681140144c07810311301401000400300d6100004c16042c11004d401503a01d64082c10410002c8042080255440242034131048682c42c410b40c04240c3d40c404405004081c540c44041c690004902460104c00074540039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425364712 1250 425363462 425363467
    0x80c0a0905100e03070f0506031f090204080312060105070503030408090f0907020a050f0708030d09050f0f070f1208040b0d0b0a0b0a0201050f070f050c0c030d0306180b030d120e03 79
    0xa0101811103e2000350301c9020b130042000c0000c0703121000c1d00c46011610301418451850b40c46444d008880c89000f8440e500c2b102103505d021444003082d1010700b0290001c200119901c010340001d401140c40300a10507410800300700b1403240015004001d07641c100d60701464103074554110600180d014000c1002003600440e1800400014a500146800d00385000740c0a540505201a1440f1344885050141c810f07103600c104070702d0040c040503912000d54640550281d5082c0011100c01c94144008500c0c078040d16400141c050122030340b090102c9008040c8000b00c1c05444040e6135a011560145108101da0b201002c24100f1000d4001d40100c03111000050894006030345400000c01c01e0b4006101e034000540c0303050300003034952104001c4c090098500342c480301410f2280840c1210554084510b00c10385008103070035208130361410089400c88040d50380b80402c0990829405982c0b124042600c041c10a0801c0b04400701505e01098282e400f031030b14901101c81054690b004805450120503d511a02c0300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425365962 1250 425364712 425364739
    0xd1202074e030c0242010f30020d02120d030f0b01030b1c02030a060c08160e010c0813080a080c010e070e0604020711030a030c02150a080c0a0905 64
    0x4030116098007010039201008910703101c040499864203e03900e00d6026941c12010700d0000c079003c840410340804a07186001400302071819150110000303911a081c0b2907c440c038148110403188603200c01d01442d242e0f09060f0a0f21020407540c1c0301801000280c000c001c20500300041d51211321050f03c0d43c0114a0444030502002040100142881d034090b480c060718002c141460b40d80b02e406041000c94004041c1a4040081e100313518050140743d00c126411301c41d403005000040c50703500030080040000c2e290410b032880c1000414541011140108042096041c03682c4202d82c2c00101c104086034004000a480361030503c1e01c1240d66081d504801050711a1503039000c00c104a98004002034420f804c000d001001801d000c00e6601e841078018040a40400c0d40024800d0600c1d82c060400700d80200c454080a421401c0800d040030100d00e0154001107401c0e0f8114150f0500d028401510307414019914034002e0402070040c809032002d889801c01c0c1100040702c43c0018420060107003c4c0c08020072003031041a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425367212 1250 425365962 425366093
    0x206070b010501032403022b0605041203092303130b030a0e0708150c0702100e010809061018060302040c08010f0501030c0c02040e1606020d120207 65
    0x3480707142c2c002810030460340b0185e0301000380c400107900820503002d0302504580c200502c0d20700d20b5850010b4600140240c43c00f00c4141e0f10300426141c010305000800d81494101165400503001340340c2c0501d81010329590004400c00102e002007200d030141c0045040e2466111801c40c450b513000302404e88010b800100c6c0d0350031908015400351801800c1040f050a07002e0400d611900304d44035007140381e0010968030041888841c2025440034840f00014901075003540010f0b4104100c0c06003c0016200003000201c03942c2140d41190071800c0100140301e189041c2840b40e4840303520340101902c400f441400c803035115081d60403140107540d0040c003e0040301203825008281180034840e8220109101c0c5000440d54041d101d141c824004076500d003401e00540e5000c0c4000340400580164040c815001e01f40c4022980d85d03800405803005a014100084012000418440c00c10040f010030320b00c100084000a41c00c400098a01000001940d490702e5103000c1d001c10300106040d07108200c0c1c10f1410120030201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425368462 1250 425367212 425367233
    0x40507020c1c050304060c0303060b19110106140f0604030501021206011d031018020a0603230f010e090304080f071502190206030603010e10020403020f031c0318020607 74
    0x14003928204100310000c407070003071502090000078040390000c210500546d4461204c5501031402800c0201e41255101c8402849070711289030b10764410410620002902d500031804038070700c44104020712a82c1c0c206000d030b0106c05811100139114082049000c6940c3d1116410f45e03000f1a00038000f151118a0700d40000800d2008480d020f000480000c090503a109010440e89041280600203203e1815800140d000a01105088002ea9020b04d0300320750040c0c3e112041d44003c0c1c0500d41e4081415400074082c850209a031400341c0041305030a13010480403091408410b411180d902c2c590310b1861300c488070043d0a6100320307000074980780182908034442c400c0000f0030404a500410307480744042c550740d0040f62100700ca0310944101c4482c40401d40f02502e080c0000d1038002d40014000200e020820654501d403540d05004044004d401050400540c0380400d00e107507818030305602910000402c0c050240c601e030000c198040916903655440242401d00084544e100e03603001c1d00165840349942056103000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425369712 1250 425368462 425368483
    0x203071b05010b030d0f050d022104240903020a0b060103020412030206061008060108041b080a03030e010b060307120c030b060406170108010204080a033e0f1b0d030e04050702 77
    0x248107030841d90455510854019202980c1503590742e0410840820700ca009c1d41c8060000015500450803210900345e007403484501991160079003d00000000021a07840002c0190100f0454904000600860f4001c0746801c14103a005075650010b40c3da26006800902698000146041420348001c040640014205004550403500706400c0120600b0407144001d0450381075000481035400704000a048031a41c21201c102042080703c0d0945940301c00d4608250200c050f00082e0312208502c00c401f0007031080c3c1050003405c2d02c18038034600e40b00e4006001c4d4002c45960214a039694081c03c10030f58030030b62083c8400d040040100e036a842c0c1d10100104620004141881400000d800010354141c05108a90031074075458040c1070703c0c2e0700ca0b480036268909100900c0800c410740455140785086400510641d401080480030750703880340407031464a4003200c89403484c1260b00400480c104040c4201541540c0d04013101c003c202e0701d0561030200c40c4a5409600b0030b0b0007905100030300c40c8198001c030b03114334a03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425370962 1250 425369712 425369719
    0x3010f14060405210f030c0705040e010e0307142805010b0a0f0623030403170112111002030903011d01150f0b0c030c12070b1e0a0203071b05010b 64
    0x240c114034003000a01d02c541c2c429941d000d0984014a0546030b0008040b8900075000c3c003d0343d49040c0018417150031503004100d1048a40c201020502c080d2400d031160895180c2d510000b00b00c0c038a080381c0c40701c1e602d02c5030b000064401010b801c50448101000c1042240381d560325075440500090042126a40f07034094041110a5401c1c01d200f00d880303040c103003d20803c8990b10030004403040d20b009015660701e40305050f10280c910010300001111800c1e24000c5000c3d5200740c1e00c010352201c401035010400d00040c2c0100c601072030707020701302004240b42c1d4021401c03c40c8100c905031041e07240321105a1440c803503e40c0c040d4040d403c140c4800402007242011000c00300d4004000c0c0111034075031104da007512740b2034001d024680003c2d400c1809080400e0b400b41500c0f1051008030792502401412041c0f51002e0400d000d5280a000500b4908003d6000c03000c54100c0481d8030222584864140b103080901c00003003081c070361180c0c0031002a403410311034a110901e031111b803056140c81e140d990404501030450313509103d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425372212 1250 425370962 425370989
    0x133b2401060c1401020a26100306050c0409140703061d0a020a0c051b030f030f16061508061f05060a180b040b071e0c061103070204050903121825080303010f 69
    0x40b0010711f0f941b410b00c030340b074910b0b080e0f04818107641c0c80400808002d020700640380001c4c4000b0a113804076204c0d1112642d032020500e40304c3c0c9803a0000805a0302c4642294205070401050200704003000108286c110200980150b2110300066086801c0d2052900c090094842c440c1a41d20500446a206007000d07010b800b030361800c540b801c00c0300da9244200c096a000d084400c104403180301c0e9603050000041d91140801064407102220041150046d68221845640006050000042d5096150400c00d040415190001440c010018405005d0f81c40704200307000e45c49201080405940051002401982564544980c0c0707541052503590000c40080701d01d0b00341c0c40e0a0340c0680c52048152020240d0019020541a050500c109d801005400c8644841c0c44140003070f80043c1c0e500d010306445066030034011502c502c0501c0301d03181d41401c00303800c1401404a013043c0b000180800f05030514a400742d040c0d401e007017112400805401c407000341d01c1a40c26000200c00880c0e40c071003850144003101c4d908bc035541d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425373462 1250 425372212 425372267
    0x3041104020406020316050a050105041208060405040206070f05010b13060e0c041a0d09050d030b010f08010b030a0c0203090a03030302030907090b133b2401060c1401020a 75
    0xc91285003c0c00300507070b0050080381958010030319004525441241520201c03405507a8440c01c0d103000740c40c210740e0301d0804c4402c0e1406c03a510210250380041d013264144071a00340358020036840c3c46034250151140000380301c81e00a2010075000390805d40000f5042d50400c2610760f80700001001e0310300621071078086480c003007680c114540040d40c06613030603201112803100b4440c500a40c264040d05c440c0241a495100c2d03030010035820300c030818108080ba00c000c03440c41e02c07090005018208d2040200140154107005021421082003501c2d03000900080004002213101416860b50148001007540590301d182c012080681c5500614003e0108204031040c058864086038180c869202a03143c10442c6040c0c1c00d0000f003146d40080b900c00301d040c040c848000000c030500c00301c2ca10301c41405a102007000200d5014040e000c00840003202c0c030b02e54040940211403c2c1c402071100d0f040c072601c810004210726410500c290084d0520a50300023200031981c60f006140040d002084242400001c00341e42003809 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425374712 1250 425373462 425373469
    0xc030412022427030a0c050a0c030c140117041104090c0305160501050708120a02071509141b040504020f0901030c080105130201230f0403050a051209150705011b0302030411 76
    0x1400f0401020000d541007400000e81100c2d2195800c0050329180303d4041100c0c00710320b82e040040c01842c041c1e2025a1003500b0182128400120301d0805030422504403660403100384444c0c07041c1d410580c0400e01d1705c90b5410380000200030744946080070b01560003176000041009070001d150503801810340d40020389195920019111401121006030401108120000044003405c0c0450382c4440a9040141010a9516481180415880402100c0b43d8130310100381800703400c2d110050104055801040f07062240d51040c100c100740317202c20380e00698982c0041011951855440d4904a401030001a0507603503c1c240700281c1c2142c0d2190500d694031f8007020400d511040c0d80e80449407071301030b1160480c900b84040f0f80000c2448244500321400400d01001415154680040000318080d000800034402c2e2414814207091042500351444803041044064580b24540b01c83c0d5424102d007946511445141441c07409080a06490881340c40a80e41080809815a01440c0158000d500140f6071030340c0c01060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425375962 1250 425374712 425374771
    0x91b0908030a0c1a04030c03030e0105100509060a080303040305040614030132060a05090301050604060e5208090705060f040503060a050f0c030c0304120224 69
    0xa40855070010460101094080c1080300c002e18414002c902408481c4200702003200801d82d812000100d10001c08024903905018400318054082c008100500301040c0c4442c01807268400c05019000c4400000d1403940c4004624004014107025a07035a40b80071701e4014100d9000e030040c6808103511004413081742e11040145c03070580d9000080c409080c0d200c400c0d03a0000ca0060710450464200700d0542e8407254031080c001d440b07441e54a4450a80368146c4804260940714024101c03806146800c01c00c10080d002401d42503000071080c229001d5201402d0a80c1c1100401c40200721401c071042c0840d41100c0c3c0c2c41e550451605032306800303005146000500101da5406003520351b00c0d0581c2c080f030004d11003480d00e8001494621081c0020514095481d404641420b1089aa803402159204100005041c0039180d8031f81c40504e001c4000d1651400c40b850080500018201600d035603030f000c0d0081d035068020407103050307a1420710300890f1156078200803851110340e045809010984600406040c11500e141c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425377212 1250 425375962 425375969
    0xf1605090912092b030807021005130305091c0804031104051003200a09020406030b030f060a15080a140f011a060702010302040320030706052502041104091b09 70
    0x10701d5261105040c108010390220b1038402c1e40340340c44500348019803611342d82c0c01c0d40b695104e0740b02c0f1000c81c40c1c407200c081c0c145007208210f40642828a01040420b0b00e0200d0072030b14103a4142003032a16211440c011508280410b190007040300300d450403100a0000d00fa015004981c0300f00386032402c0d508200c06010a44109940c296003140c070880050000440b02c0c1000002d0803110b83d0080c00707140b01d010004d44c91040c42d0380065611980004c060160703a5050080540b94401074000340b10701d5250071040f0b607854000902e11fa60301692030400103c40f8006228204c010003c6000b25906200142417680350b69106903001d01080c4039540c02090014018003841c1d03084041100d1181c4104101c20501a1fa035108503812810513034200404000101c850b400304d0b0030181c1c0307148402c03043c0c45040c090500c1d0054a80252042c402c1c00d0100400341c07140b410220400c680c17040e80c019107003c2e8503c0454041c045840c4120f510f4130010401050201a070b90203150380000003020030405050410050394407034500d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425378462 1250 425377212 425377243
    0x809120307050d03091a0901020c0a0804030c062d12020a021c1407080918040506100503030304080a03020d0b09072303011d190507050405011e080601110f16050909 72
    0x41110b0711005405040719070089407c07002500e4040b40440305030518090120484030140042030610030b22422407842d001600c40341c103000b007120020b010170000800035503c2ca07051004070380b01c2c0140021310a4840c114030358120041552120343c03040000c1e480b8800b00303840769081e440d181c0c400c20001d0f200f5110022060300307040c0014a40401c94031000542d901204c1403e40100004103070154560007a0040c2c1e20481c002e00240420381040f2104404641d10707580028480c0d8014410b00003c0b414034802c0b10582100e600703005a0b942c6d01b41800d0702c05130039412440b5034040c0d1b00f074080003e03250300452001c4548180703034841d4240710000002c21007140002e00a1003d8248500104030407680045006a04216082c01c501c46015a80e8640b90903a0b50450f08080000d0010030100120358000b6100105824160714075401210b9030030005100c17181c0103040703504109000601d410072401c14044a060b20328600156005c9490940e43c103007004400b4812940911381400001c1c403900700200b01080e40d40c0c081d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425379712 1250 425378462 425378483
    0x8060c03190b0609010e06090d06050f090f030405011b050601060e03100e060412140406230a0e090a061e08070b0f0d021806031f051008040f0809120307050d0309 71
    0x184c01194000080681150080380c02c106550880c0d640120055126100e82004242c42c603141104500b07840016011210130780c84058503040400e00402560160380007841c080401d000602040300785040c802d800a05180100000401c42d50350101141009a00c2607080312500446e0011500444a5400803200c45801c440c01040c000340010b5035080480f0001e28180c125503004004080c0c071031744164020720104a0b4400d54005114400961814031031220404900f06249100054884818840000d2203240340d44005104850700f90b10200241041c8800315681481b405420515a030240c0210140c510420400196031152034040792035101d6207030b90032424203014010200107900400d0803040021409005042c0c540c80e040061841036821031b1024075a5000c00844101d2070080350031803400b038041007080d841d086412020380c4d138000303604c500940c8220100d400c2c00c140c10700901d140070364080407a146001002e030380000074000c07440c00f8800f95100401050760035001c60f80c107020000e040c2ca504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425380962 1250 425379712 425379727
    0x417100506101d030102070213050609010509010e070c08130801050117060709090902221e0b180606070c08030c06010906050d02060c0703060203100f090b010203091908060c03190b06 80
    0x900010f911a01e40250016080000079030001d00315001140c42c000401e43e44104000c0d0074a4606100c50040000b6501003038254180300510107890002070012050024541841e020480d042d012180740c02d61000e4602e4805c3d0f102c41401d0301804080c03103042c44907201340304100c540344800b0501900540c96500c84a003a2450611150054041928141da01c00710801c02c0390350346024450071420500b8108000940402c40d20040c2c1c0c21050fa100d9641c0c901841c011203104245c46240403048412140a1202e10319034071007002482a105205004050348240301001800c07401c00005440461002c006455041ea20344013035000300c030418810503910110400c402000b50820400520820102d14241c40f5203d8682c1c407a0310603a40242d0701e440c3e0305140307104100000c2c0c080b03101d10405014402014881c1007901c0000035503074000c02c0c248512406034540d100005208003101c8500a0211600741c45480c9440980250250002c544201c5140172803031445144048601c10703011580001440c00c1d041c843c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425382212 1250 425380962 425380997
    0x1090b030304150c050706110d0c020a051302090301150602060c030f04030f030905070f0501120e151003051506010314060109170f030304150c081504020708041710050610 75
    0x81c444040c3c050200582608010a5003802448040c201c81e0b11200d518045078000c0c60718100b02e0640030001c00444510303c00c016030728141202d04075a42100c1c001d4071a607019079140002d200f0210704590640c40c225030180245064058442221040c2d020744220755a07801c5903d90511040b210010501d000300300040000340140c41541c5503603c1850002291116980da20746005582c0d004103801340d440c0b40f410001580d004000c64110070300d00409004010051000ca5580c00210324131540328018a0f000030388034070a018000d001540c009040351180c3c8500408160030f114203888550009040ca081354001c9074403a64028019a01030b524618080c1c909024503038009400c5005041e80d000d03030003c5040450042029600403400740b0603040c8c0c90114144448120b504202c1c1203424030207000200884030304400528810240181e1b009030b516105450b010069104a0b000443d03541040c0f0103001e8401c1000500080c2d000c543e080030860b60f00c80d0010003801e0400c201c50703440000e1640c00303154180c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425383462 1250 425382212 425382239
    0xb010509150d0c0806010b0a020705090402061309020409140108031b1606020f010c0311030a090c03080406050306042a111c0c0c0603061a07021516060501090b030304 73
    0x41d41c00c4200340304159010019251a8002d8000d4580207030f80e05041c0701d407150500003140100440c519841c41c00a280314040e44510a0348034003072041590700002400c0d900c3d1b16040b202044101c44040020b244c51720301d0000250000c0c09102c00142c40d0850705022079642c03410b02070503689000025410010501ca46045c903208801c46040300c0d024a801280485504030140f00142c031040d001f502c0c0751210340812034216185405008105801c01152600311b1881100300c0e500002c20110100f100601410000214142640300070154000003a00061103503204016600030042202c0500140109208038658164080e60500c500c44d4006641800f4500581681c07031700524590a4400310a20102c606070301e07150318005000400c10000e5880700b041814008040901028282000000e01341080640da4110004400450300c1e80054944195512100844e40e040d03201d06036660b070765011004442c0b0907503940500703c44940c2810700224a032440da02403a03d640201800441c180351030b01d0780b000c1d40503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425384712 1250 425383462 425383471
    0x9021302070c05060406050a020105090304050901031202030c06010f2904050f04060b04092a141b010f020414010306032a030f03030b09011410030507020f01090f1a040b010509 77
    0x1850780302e070010301c540b0748201600c010009030b15456140c100640780a802e45000070010358240d0404c000034007160f5182903034103065a400c00c003000688039a0900591842c070401c0c0401d2001d21600e0000120210007a001800ba40c052a544404c071000c00c0202401580844a0350181040706002c14841401c01d90070300c0c200900e00500102c4c01e03a0f1368001da2045035000d0b070400c0e18250f031240d1300c1e5154103074401104034017008c044400500c8010819001800c8a421000d080940040020649003038520b8400740d032103000316031000f0000c0104c0300d10941c0c020740c01441030340b400707002114003c0201d42c028800c810880c0c0e084141c0c21a005514000b004810005000702d04480b03003404800b00216140304141c1c07043d40c1c80b946000400041c9401001001c100591041c030303c4440007220a2000c0d00d0340d02442403204103500700400c140e26a21010b070304298401440460542c42e0190040034071418034414410f050250121202e420100750031040c159004a82c0504580800310040105090011015501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425385962 1250 425384712 425384723
    0x2312060f0910090c0e01050a0b0406120b031c120c050702040905070b030705091801051e04110f181c08073e030606030c04110d11031602010902130207 66
    0x1c9280740000082100c00c1d08205031480e207060704c8140100b05024842c035000d00380880384010814078000020742e07144120b0103200b0401150740e0201d0101d04560304124907640008043e200030303c0303002c051006190a100d1600c00000c0301542510b4000d001071090804961083e91494603001154083c0b0000d807610b5203048174079114181001806200c800055400348509584080d40c601d054010000640741003407000e0890305804004002035078070f1a01709000029140d00701e134901c03e1003400007030040061410346482040005050000141c00030028075200e8040015580007d4a400a0142120340f0f41411100000201c0888011600315006010014400c4000a0b8000c0010441500403d1141c80207101c101c1c1a003801182c4081c04281080c000d03009500400d102e183c80c0c00001d5540c1c282c01c5096008540d01c2d00d00850081410046a220080201041c04075141c6004403074169071080b11a0130102c11444270303030380d030382d500c18005d003044c96400810354003c1d100c0038144980254000001241e8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425387212 1250 425385962 425385973
    0x8090a0503030112030f0311030f0405072102030709090f08071410020903061e160903080703020a05074407080f0c01050705100e12042312060f09 64
    0x154100700a5002e0700b110503060742d40c81514030b0094100c0c1107000c0e000080c50300b06131007091070340191410780354031001000c000d6001e40c1712420560f050051310741200b030a450058680d895407544a00310036030081d100380c0c12501090351f1740030b5181c02c503212802c0080503c1c5907086220085803010001d03150490040c00310103011071088039500e00e80300702c3c00703c01c80c0d1598000c1100c1c6070b00d240034001c550b0301100c041d005021000180c510500c00480003044080140b000810a80a40c0d01c6802c03800045e613070205401359501d0b86414080c1d507844003110111460f200c0c0c02004074605c2d21205010140b84941614842c3d440030101020b0003211b111b407840074484c014014140c041c80701c1001024014010f81024050248202070641e08004100c1d4007103061140c2003003000005140054010381070b000c9603800081801e0021001e41c24102141d5400d00c0c10031020501245540000e200340ca00c1030035501803003a585417260f0a2100400c0710708144d0600e90000703c0010001c3d0154000264410184001d513403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425388462 1250 425387212 425387233
    0x40213060c1514061e030709021b0111040e22063603091a16080403020a091a150d05040302100606090509070302070816080d020c030910030e0d0809 65
    0x1012602540c0c40a100d480b80d0106001150406030f070048551603020400030030700704032070b00440d641f5417282c41402d441c168009920785081c0080c1d06100c400f807048900074006081009804226504a8010889407001300404140202c28404401c96520076244051034100c4c0d403901c8000003441c501c40003d44031401800b0850f4030b03086070419107010383e0f1700d0300742c800703850942c4e0034020124683d60b0082074204542100d0007083e405031100b5280703084e1400c98105d407550900c0c40c100140d4001c65000a40000d11581c0125416680760000780c410740003000c6440a1088003020030518000385150f0320300a5004001e8084041c02ca80c1120354007500900445400c0c0d14054009001ca0341c159002c2d00000c0d20b213a005000c207203400d00300c258014000d858190700305a11342e00c1d8100302c0e101d1031000c000000551000141008002802d483d080c03031603c402107403102100007210b83c481d401000301d40d229050354100c0a0b41039000e4400c004485082e0001010804400e0030191070f007120180580a240c49410a40c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425389712 1250 425388462 425388503
    0x606050a0233010b0c07090b0609040e010b06070f0308070c03080402040914030c0313050303032509090f061805010311010507030c060207260a0512060f030d03050114040213060c 78
    0x600034075144205170707a00d5004601007400c190460f044100f0340ca007480d28484142d51002c0907141412000c950005200d0050901d06004000407910745403c400003044150074045116203826035540240c507000c1c45655803850484805910308030007804918958081009820301d903014001e460f1180342082e20a140c0d140078241385030048602c025080d0b000285d030f1442001c5040b40c034402040213400039030031410a4a03c43c0c466a0004401482d0f100c000500d014507984a050403d00a24504104010f4100345d40b4818010749103900411820100c0c0a184000c51803142c442d00e4103d0340c006081c0820012a500115070583c0400000e40c1003224085510340030445510040c55070502c92841001e121010540688090016005025008409010900c60503402c5421519001900d007008115941d4280c0000d00c0c8103080d01c400342d05807041c1602c0c0f451721a00344d407000b03060f100502d101c000140d4030b580410050384607030300048440340f03c00d00b0100800c0c1c0c02049034103429403194001e81d1004652840c4c0703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425390962 1250 425389712 425389813
    0x3031606151e0512030a030209031e01050103140d0c03080603070506040f090605100e0f011103070b0f0c0f071b0e040b0402090a2304060f1401090606050a02 69
    0x10900381202c022140004220350b9078568024001503456980c0c800c03040e6021502c030300500d02864149500000e02d003c1e60343c2e0600043c020180c0290030b0400c001c0707010051500800d401d0000301d0b03400c1c1822480500b03844000400050300ca40c95070300c165000502c3c1d6002c0750202d4002d001d240d0140320307598005c28642e80380c4002c0c00241042c00b101048281c50031000b50705a43c501c1e0320044c010310700e043d5880c190644c080e124405a00098680c856400362000048826940308485030340346010100d506020080c48444042c010b0207001440356041d121000d9070750644c03040800a02e003400007080740710300040b4018881480c800209140300720980e031700c485202d1101070884040f0b5800304113208210451034800440760b00916020030810400c0360421061681104450000642d030511170001020800d603070700521034042c000001070042d00c07080c1c01f44482034002030141d034503500c0c107111011800510403800d9612400183c2d00030400400440c08518007190b400d840a00c1c5860708a280388a49140201c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425392212 1250 425390962 425390969
    0x9010914100c1716120810090b030307060f09050708030a050d150801090b04030f08011802160804060216091109011b0f0f060b101d0d0b010b04170304050303160615 72
    0x2c1c055811301ca510381010703c607160702c24100034065044288003202080003540e200303442800c500051100b9110000074650700914030014a02c074140880268002103540008490320b100d00304030f859075921000c000d40c4a0084810204c00100c0903c580098031400b9000012602600107007090010344030450542990030081003a68940f035031509200816a00c0044008a18400d10308190703d54103001f5844621036868003140400c54000c17990040401400c0441480e041d402190b8559a645d9440003a44030f00c070144140024102c50540022004494001c1618260000074801d14007501c4070015520b0b0b248400003004c100800c00c2809000929081608446600600c40b402c0307044c05c1e40c0341000603034410305082802803001d034400241154001210000024600c850420412840301c04a0a01024000c015100d9a0098000242d00d45158001d10544030000d444561022040b084036580744240d02c500e580680c82004490071501389045400025842500c010480c1d00b0310354000c000380540d42c1c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425393462 1250 425392212 425392237
    0xa021b06221403070b10120507091e060305071502010e06220c08030910031a041d0102030a02030103110603160f050d0f0e0c03070305100e1c020309010914100c17 71
    0x1d001c6c0c00b89034000d0300c5004124120046070b035216507958540e100d504506c01e5546407a00c441c00c80c00102840700b11040600340480c010410583c0c2d81c10003e0383c6840b5032042802c4100b0a240c0c0c45213051060003401d5198000e02c0080507140c5965990001018181c0030241c82241d4030807890f00001c0000040700000c16441000b1074441e240d400c10032a005041c48044020705140404000080c40c2d405946449484100e900281c040120315000e1148682d10920030b55951001040021109681d03000d075060741e004003400309017a282030090041c41e00c41910540d2000403030042c151070b001c4c420340ca240c41980d014580103092501508000702607a00f44409a00c209442d107104600a082c10482e2076002d02c0100c0040c0cc0c543c1c55038450320f0301e40060301800b11299843d44041000d0220801c01210031151444890440e5542c0100003034494208081744c1b80000c00c901c0b0300040420207607440307211031070009006000c04440c1c40410303201030a043e10304403507131402c1031007100d40101c143c000350280d1643d40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425394712 1250 425393462 425393483
    0x1b0106080622060510170102120604060e0c16060c0e030c09011d100f0303080f0f0f060409020a03020901060f030e0d0207060507030908060a021b0622140307 69
    0x15912400c0060080003150303200702ca984524070501c400207070040c629400000c001416220b07074144c0c010032000303034020000504480b0344500a4610550040894422301c046100480d183c0030304000980310036100e01100e44c803190300401c1064108000500826a04d044c3c3c40c3d51815241c0d0301d000030b1360300110a20f400f04008038401c841e0b9007424031001d040010201e0701200350358180039410310700b8004142000072880e03080000500a902e0440803030054079011240840e0079903039103401404032401f00c420440d2074415001180c600a105032285d07001d043c00314051015030f525082840001d00030440c0076a071143d0072140c00005a103404071000c1c0684a10f40c0d588100712a14000901501c5004a2100c11075204082460a041d4042482c2d0165526441e00a0f55071a0038101240c90950300d40144c0b0050107024140312404140e0733402080000c049085046403050302080c81900e40700300301c8040740c0700394412854411024190120300d00c160301c00c085840083d1307111141d084c40d54100c0d032000c43c0e20300c1c2170 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425395962 1250 425394712 425394719
    0xd0f0209031e0d0c05031201090b03100b0a030807442502180705040501090602060402010e09060607060e160503061b0307110a0f020108070c080f030c1b0106 69
    0x82c80a51942c2c5a054440c5510a070400203403551580711010f94000c22154600040c1000014000c4550360503481055075581d5840725260002840203403490f510a1042211130454504c144c06000031182000345a40611491505c03801e0307590b80a8403040751020340044111001c45c040600111141c14040401d58940e100010144007101c88180030b4004848140400044040f00c103040505180f000d41008144150320b1000c134801401d00b094114107441002c04000c502c44e0f1040140c01194400d9a0740d444081c0d41c0d21069850b003405443c0030340007448068201540d4100b8122070b80d04914054417103440e1803440c0e11980c04454044280050b6900500c1c18242d6580c00c0c00b040d007010f0031048000c2c02c40c81c10b010500800c0d1500740075003441c0844002c00002c10303060007002d03112603521044040e10200801c51a266190380700b2500101d0105000314086010184207940c410b9a55902142c1c480c030304800218000c84940004111170b10400c070800101422000803180401c0c04070040e000481d04031308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425397212 1250 425395962 425395969
    0x160209100302130902122a01080403082802070f0215032502100908030703050a050c0715060911040305010c03020a080609070c050303130308010b040321050d0f0209 72
    0x24040c0c00c04203640d00000051001d40d5884004070040c9140300c0c00001c0d216124408503800b02c440d145000c015005081e04508500c001c4406029070707125186e01c8803001310400e03005550000080d0b4001c1d0002c3d4045000074042070700790000343d07090ac1d8081c03050920802e884600d00f06980c0140c2c2c0403216400d500e40d0081c118104540100d44c0c41e00300c07a84503170440c582441c82010b000b08030145410401518004040694001d1202c076401d0300c9144400d120803407190400c0740d01d6520945200c00064500800105000c90340d11416000d220008040c1d4984038180c0c460f0ba8120401014181c40c0a50320040040d4580152140001c2004071540c1c180e2154910b061450840d85050540000d040c01000225103080c0c0c40701c1c649a00c10400c0712145a240c60744441200d50200094004046220010910404a19034030035640540d20958441c500c581c0c943ea44044c07580120b00c40108041428500912505c5e9102950810b8402c103151444c01e084148100409580120403012003031a400200940d00d402d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425398462 1250 425397212 425397229
    0x80d0801080a050a030f05040e070302030405060609060109290409090213060f05061b010e06091608190311010203071206140108011401020114100e0f0108070b130b1602 74
    0x1d0000181c100041d59480e841e403110007001d4000c04010b80ca50052420364020000d50b0b0142c0b40c4401d84064500e00910b014009500c1a0740c20b840301e00c0340c00009502d40c94442c008500c18031042e03541d0342205142020a003000040d180c02d040100a0f07204002418969100152009042c2c122012850070030500500c61500345000500c1c3c0002c1c100b410a1020360481c9409804440c0c080d00d4041c3e4030005040b0142c134a01416014203041d500744030380581903203030000301d0307500078176140c0151188400c110b6414100d0002d20703c42c0c42000d4005081141d2a03807401c91000341d48034002d0402c503030389640040303103c0c0c2240c1c821100e1202240c404815032800001c1e40c815403025261140c12284410005000079040701030500c03890642e81c90b0302c101c81400764400e4206903010f6200403040705407424803600ca504489400e0090003000e50110000614203581a60118104d5a548015041083c2020b00810b007d0744840d034041d03800840301200103000030f1148001c24081e44424210350107031420303104105c18031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425399712 1250 425398462 425398469
    0x2031b0a05061201140103090f030e010e04060f1e080601031a0c0f071502091302030411030303040206070803040c05090a090b01060e18130b0f18010c0503180a0c080d0801 75
    0x610051242d0780143c0b10300b8400c0c5065455a5001c2503c020240c00101d02802d240c0800512040025007800105600065002c4d076000c001d8807981202d81464042c0700444401d440744241c002e51a03101081800c0400080b01520100714010800781034035240303910300c0c0140c00e90045400942e005807660f001002201c0041e003001004501c5480c1c0145135008510034020b80102400b486441d11200c5440c6003d54125030035500090034a8020596001d404d0000b900200c50030b0310f031540b02e6031440c49140f401100702c2c0c0c40303a5401848941031640d0394444505503040208210307200c0da401c1c0d0380402c95541b6150442d00c15079002001103921340c180e180040c145201070b4482720a0006008404059588102c801941e40008400c00081c0b81d594155403171420070401800390000140c0c5083c400040b841e9080e861180da0068406070b050003403010300341d080314001405400002c0003072002c1030130f440c0302c0d040c003603074204507901142e0144010b500c2c0c1d000e07403050f6507000c004180e000341c5802c0da0b003603002400c09005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425400962 1250 425399712 425399719
    0x20a090911030f0105012006150307050a0b040b071b090207050f0106060503130302031612020d0c02060702062b0501050118030b041106040305120a0828050a0902031b0a05 75
    0xc508280301d00c3c1c840c010043c002c913418000f41c811a41003803540c071400302c864284c4e1141100c1d100e050101001c0b4076010520b44090082c00341c8400480c450070320000110485080000541c82c1c42c0c64203d0380c040503044040204c480740009680e640b000501910104080c041d1118016503942091401c2840c112035082c00300c00d141d0500c2c004200c01900602541d03408070480348518480c51032458120f06520500720500044031072000002d040c0068888040d6400c501502110180524000c040d2101c2d210682c0003980554104651401420000c01402c6421503070380c280030b56105048030300070001241070f040c850b405541d48010011582e01c030301e2445114040f481900c0e403050458884201c1a28000e00c044c1003291a4043d1400d01e468400490b8005c2d5044800e64841044980150f0419400340d0000c0b0b00041c03490b8041054046c1210150785210740c4c5159458180c22203070003c8001d00001045500220fa460030380700d0250b1424421031140d2401382c0c1c00070b04002c48100400840700c1c82c58000601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425402212 1250 425400962 425400967
    0xd030b040b032103090f07030b01051809060615121806070c02010e1e0a0b0c0706031a0f01020120040e070e090417130b0d0c03330306020a090911 64
    0x442d5454220340055042640d1903d56503680d40c226607914001501c0401c01c15485640130020620903900308846c1a0764044a5100a0240540700800045c03015a921061034008030041032103854081091079000d000403003520708200c2c0c0d40c41950451001151034401d480001200246840c0040c00b8550b070101107810030401d82c40140e00000c0007054000b0020f809041c92021504c0d084c806203089c0d541e0b50303d00070b0a448023142c0300c0f092003400f50017240e00c40c90302e4401d0349004107401d801307402146884c01c8204489079840081100b04090084003160385170640d540c5410080c900645104403075240e80c44480903982ea2880c0001103a4240e06c020200001c000c40ca0342c7c501c4079a600d0341100c2c0d41081d0045140d80a0b10b00f0040d04005620542d0481c084010341150005070065592028042d00405614100012045080190240e8007902000714640850000d05407405e00d400070103204000c89450340480b45030301ca82e42c00d422070b8840a0400d0106010807820408904140107000c0e91000300c101c91030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425403462 1250 425402212 425402233
    0x21806040803040311040603050604080a090e0105060316030b090a0c080c03100b0705030c0a031706010c121d03030f030910090816080d09060c0908030c0606061b0d030b040b03 77
    0xd80b68003443c00000c0c07003007032107450403420390b80d983e04554040c68111060381e41030305140c580440994404400307500400d4031f00b00000384121141c03907014101c0d41c025101130714640d40c0407031400101080c880700700245951802c0c041d0440e20b507941114450f0741c41d1500010108403000c00074017020801050840c00c90010000c00c00401e007011201000c0380c07501c0d05103545440741e900c1d0480c1980203412000d80c189c443d4506c8007042c198009203144952034298240d921a403074030001100d0100e600f25014269842840318448004d00c03d03204544a40540d06e0023484051001c07000908681c480305070038135500804130a00000700f02c01e100c860112012604200180d42c5107503104c100034000e60207140c0d503064040110606100c00141220560203002404101400c984d14003000104a03611020000542a6802146c0c8410000843e000089043e0041200faa125000c001140d0320503100c0300c1e030500e04e9a4424500b402d080140c0c06a0140036100411010700050501c001c440c04032080601c254172070503404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425404712 1250 425403462 425403479
    0x70b09010c1a1f0b0f091f0e041a01020d1115042306070e09040602040e10030309140315070e06130e1612050402010302130909020f0103140705160b0a02180604 70
    0xb41d00311030381600791795140d60701c800c0003c40340d52070360003402c040898540c10095020362103620519800c07000c890401480c0c0e041004826851002e0080707601680c44402d114116030700681710440e2019001d400c81c0d118070300a4004000400c000c0d50200e58041080c1184d01c0b0284103900740c0c0b640c03601050000c1000d4944168002d040074010407070140104039040102e014410380780c041f18090032100b1301000003400c01e82140d5401611510041d00001d00c18200881c2e4081c290090034170155006000780014010a00000c4a80101501c1c0c40e0910103800c0c0900380343d44070303100034040c0341f450418454034051600018149071702c4002c19021400280004030911940c0001ca01c505502ca0024002955622840182c0080c4203107068403000c0420600d002502c80303403d8011480302c600c00e541004507102040010b40c15110002c8411443d40b0300400081d80c4a4403070742c09032101d160009030f500403a000c7c03900c0d42094000151000360060303800190400000704490200d1010a1003520580c3c076207490302904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425405962 1250 425404712 425404717
    0x7030c0b1e0106030c03020d060b0c011a15130306090b01030501060618090b0f041e1406100c0501090803010e070e030a21030609020406020303060a090c02070b09010c1a1f0b 76
    0x2d8901303042d0340d9101104814400d606070707005828080b00c01c1154030b4440c0e0f0700e043c41c0d40268407418695828200b1075904c00d2103041d1445e00f8400e010b400601e11841c0942800c400d5004000c070716030606042c000c0000861a14010380300e825018610000203541076090080c00d580c2107800c4002441070350030f07590406d01c00c0100050121081c840300094514050000074801e85034140c003e640c0103040c40c0b030341094140395014040c4400c0341141d00300075000d20b54036144c03100d81c4120341c85e562000c2c405070b0020300c3c9801803411004161240000103014030031540c0350011900280c0080745400602410131255075001600c4407040c4070308a00400c031800403991843d15400e641003485007501104001f40d04a54001c1e0480780250141136010b644960b21918000c4d42c0c1d800481d10184101c8045400040000c1288520016000c07d9400350102d01d0914581c1d5245910200c0d000c3c1c1008142c260060215500b80c4003140220000c2c50351078014109800725401e0307000d01e014240c0d0202c0d0f00321700800030072060004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425407212 1250 425405962 425405969
    0x230708060609040902030c120601150207050609041104030f0b1b1c0c020f0601150305180a030503040f0f060e060717060906010c05120310170d0806120307030c0b1e01 73
    0xf4045191445480464184a282d800e01c40d001092070641115070b0a001c1801411307116145107400d4065031429040f070b0740302200d100c0c1c1a00b001c1e04011244150800e90485100b001c00c1001c080d01d080e94030741d40e009114160010660303031140b40c5400c0c0070880400c1045038200128507651142011210048442255490302d04a140d455803011007c46a80c0240060b070100c2d9407940a0b02c0080d0b81da41f0710b28940308800e01c8840d0000b46401c0001e03814090168001f00352400c48802445144250780d010744055101030425a1154103104d0203000042c10011a031010511411010503170800c1114803a00c1c000014007680c0a0040a031a074000c071411640103990300c04400c9400350180e03259800181d900903030905018020780901d41c0400340642d0761030004c50107140d018102c01c0c42c1c180d075201c05131114045000c50640c981c02144c03241e03a0f039505c02d103002034000a006058080400c0740c405c00c3e03483d503401180110003192200307000200344070030b440300390b036000035140c00100c41c0b98101d0141440c1c0c241c0500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425408462 1250 425407212 425407219
    0x190602270f2101020a0203090a15020604030f05040302040218090c090d030e042a0908030403111011060115030f14061210060e0f09070b0f070501090204230708060609 73
    0x800b42010701641c4a01d440703a07000900c000310b688810700035000f5140d61280d00068082c50160600140d0765010002d041000b0200e503000c1c0c1019250342e503003242c1c9035101c43d01000800c0000e10012000da0780f148003c16000060015200c0001c9403e030a10104000c01003008400000600c43c1000a48510316180465980b503e02400c1e140e00d41400a0000d0081d00c08134002d9500b0688805800d07040a281c01280350b52a031205c1c1c1750f0507074418100307540e81301d00d010051a02d0b01044480226081030b2040c0c10600ca92814003820f0368400304102031514809a01c05050760150101c0041c68542502c0b0300c80c4920f6440c06c0c00d01c002410801c50044042c406804107004005502d0700b116000414480408903540340d841c05c0c42016640c040a1040c290f080c1d0f0000140b10345d440101d01940e80018000e000c40c5c0e07003030300c0c0603060203000a280c0070250403100c1d0544140d5200e24840c0d0060b81da40c440c03200c2c038840c0440ca09804106c40000d08a10200c000c00c400d007440207100070300c1000e0386c0754019920300c03c0044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425409712 1250 425408462 425408479
    0x140409020301060b03040c1d10030b04140f06010906050a031a0612030a02061503030a0e061b011b024c140603010b010e0a09020c190602270f 62
    0x2803001c28010000c1d5881510840c0001c03007030008015000042004889403402c502c0d604540210f000701043c0026250031400d4004101e0400c0000c58012001e64410701881d80d680c4100782c00d220442c10010308055580240c0c100100500c225034240c42808050441516440165420359854521150004829500500440001a03001d58421352030a11a90300001940c3c0c41300c4d16081c01950390b6200713544a401507807071002c0000d96030500200741c0c2c01e14012a59980302c924205418000310740d00c80c0c0c4e8480c1a40300102100940c6032000d01418036140c11120b91410a130b000140001d003000b85154081d40d41c0c00c5c258481141040303900480443c184010340c0c901c12034100d4441c05d805402d0014031440741c0c160601440611308507001c02614450501038009110200040c8011504130904141e41548206121414000121a64090084102000102c80d41c800022070008920240e1243c11130340113030000341101c406044100c0580005460300d00540000c14044002a1f420312440a80c41c01682d50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425410962 1250 425409712 425409731
    0x1205032a070803070204060506070b13050f030a0206090d03051611072106060515040e040f1b0314070b0403060e0c0a170c0303030705091905150301030302161404 71
    0x61600c0e04082408980403103003240c1d9164001c1d5100d400180059108503c1c0c40800501410958201c803090781e88900d0341201d664801d401010b0f003441d07165050311944a4a900600101d008000902022030300ba001807416241a540b40741c6404010a01d59003050304000c10b12021a1282c044aa0b00d6046030800030100e401c0840614038240c0142d200c960005443c1c00482015003004105820580c09001e0510001b6110303000d00c21100e90442e5117076034109040104201030070040720003542191141440307204880303a980301d188014041000343e013050310410710100100902452048270700324842d009400114507164140380d240c001ca20000c0c140030f40300c0366002d80440052201100c5448020305069600d074983d525145c0310414803c018100e8491031901414914000069a110322140d6891a02d40381607001030224040000c0880c1c15207644010001c8bc09a071028089000b00101c1c5440e01d460758914100207151031481c2e038072000c4d0303000307814003d1100e403420a03501124070b80e0541700850f48920 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425412212 1250 425410962 425411017
    0x1810050c0a030302090108090708060c1b010614030610030b0c030c07150b01020706020a081b1219090501030c080f190207050304060905010203040f0504180b190501120503 75
    0x5240e8a40034500408503107000b016015800b401c0481003e0b81d8254059540900302039852519000d5000705501040c00140c50003071500080500c422200861444500310341c16203800d484454201c1010705408241240c1305043c1004001c0e8800c044038002200149035458004031140003034600701110f14000b0001d462038540070102c400c0164805500c042d40340c031100d081b50040040c10032050041c040e01c40002007082c400642d42540c03d4114000364500000da04401840c10841c0d01c01445a004034004500e120361001c0280620081c05522001800d043d008006d04800d04d98104034141443d00b030700d660550ba80619600c0e40325008000c800340c951202c0001001c41ca8445160f11006d500000d0340030200710b408005002101c00c140c44010a030b40d21640166203d0256004210001c0c0c500c4100b009640742640092000788e10b040b051462204040c1c58800810500300ca400c000e60700c0303400100c40a091300d84a058014001401060b060035129569a0b8903480b5000f00750022101c2891036804910 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425413462 1250 425412212 425412217
    0x3030f0905100e16081e010e03030103050a02041404030c020405040305090a08100e011e02220605090a050102030c0d031a1c050f01020910030f2004170102181005 71
    0x240c10400b101d800d8141540040d014001805a15280d401000032404078584460344003810307104040094032001420700164480641d400c19000e0715907485071a040018035042c0002c44c0030714003610240071500c400b401440196042040c81d242d906401c00c00b00004643c0c8154404800c03981250b011510b5100ca0400310382e58013641a400d0380c805101800040e00303613000500c011251019240901003103da030030b03c0508a401005600080e0070a485d1628180820340c0c0c000d1009940390740c44002402400f250090003000c50313170081c04c003107000000c5c114628a0020402002420240700840c44c1050ba400c5142d1624142d040e80c006154a03807188443d526075080c0b410035a0308000e0907000080c04030116541c841e6103203101c180c981c1e0140b26007040f1026418001c41c0c1800c2c40c05051403010304003585c0210021318020006a80c4d8558460b800a650000d184d90200b42c2038221000d551101d042400340110601107003000c1004d40e1040104039000c5c0295481c0c031003a4001120340502c9072001c144160b9251 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425414712 1250 425413462 425413481
    0x10f1a1615020f0a201509030708040f051906020c061602030102030a0203040c080f0a021e04050703061d1009090c09090c0f0e070c12031e05040302121603030f 70
    0x900114000821110b42c90142c0302c00700c81503445002c036940405c04044c125003081c800f1005034200040d000c0800c07001403440c54000b1141c0e81201d14001441e03e4801e01c94105070085100103224190412035494404c01c4003071280ba004241c500c800703141203030184d65030400104080c0030f02404110351101100503041d0101c1150060300039540d0380b81c6080048000d500844d01140d0f4201a8a0041503d00c800200168414031201c02042066441c0d001c00c41840c5400e41c81007180c9401e403500c01c00944450080354000d0011f901c0100e41c81b030030200d03801282c03d07110328022007140d00c0c00c2c200300d212500702840d001280d0156100040c04505400d02e95213410752038101131002411300500c8001c11101d40303a42003c884280301c0b840340b0b1545a105076001e01300203591000000741084c2ca030030003291803180004e010681c2802c002a007200e82c0340080803142000c0c181d5028031940c5104102c14150103010b40d038140040549150314017810990a18a0404a080003404066440304415209856a400100072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425415962 1250 425414712 425414753
    0x90c04050405060703290f0406120b060909010b0f130605091005090f06010e0909010b0d1a010801020306061b120304080714010c170c0f030708010f1a16 67
    0x3a8506400e2280c0e9500303041e2512030000e0318018121452880000080c00210020000b1405030000e060400019441d042925940581c3d2003100042d40d4024010020806200b600f01c44090b141072000c003c1c56240050084109904098007184203a55020021071a90000c82e100803071030303101c406071200401c0c01e03070803da4001034080103000103007043c030004400701d030421110341d503140e03564011640982c6403e54480740071841c4400b0440040c40c0107034007907510200300c1c4000640c04500c2000074107082c1c00250b003076406523000c583c0c0828181e030f903422550150020200035031944c1002c7c0003260641c840c1842000701d001e00d802801102c02c800b40040c0264111642082b0b46904260600310030503032080000701c1e005801d100c003c141c80307241070082d03000307145080c0c03607841180120072900c06030804000c15003841000104101213800014202441c0110b113035a581190030760421113600012403d540080340c942d02070002011042c15400d04842e060b05051060300001c40081c60400c550503c9913034041c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425417212 1250 425415962 425415971
    0xa030e0d2f0a081204060b060a090b09030109120f0809160510050d02041d06180c07050f031207021207082b0f020a171501030507051204050106031202160509090c04 72
    0x102130030601341c40c003071401a401003002c8030068007008081d00c543c940e407001141c41c615040000304c5591010740407184001d000841c3c407072540c1d0740c0ca10001c0c91521240c2d02090200c100d811002ea400f01000f540710030078000800d00c0c400c1c10b41c6924003800d12407003050303c24100034103206c0203035209038181d030380200d444241503403036607111520300700800078201240121040400016480785003030380320f1803140c0240700040005504c40c0b4981d100b5941c00401c080d03c2034800e02d40c030006240000c20040c801c8003c8210420072a0414280082c01e041c2d001e03903c0000b030b65042c800754001c40c20709411540b1344034024074520303d1042d110114005016007900444400c502c0d14002c00091001e030380091504c290641d58030b8070030205840c1840410241950008020f0400c4e94a5103055400381e80000d4001c4d0003820000d040c914013031444c4014000859040342d00341d4540104200300543c42ca1042298001c5002070315500b064948292140c844520541e480340d881c240204038140014882c0075000c4001800030302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425418462 1250 425417212 425417227
    0x206040e04050304151d1c020303040e04051501060225030212060115050a140d09080d061d16030b0126090c0301062102150a030e0d2f0a08 61
    0x140c60303820501c0b0703504604140b4445c0894140c41101d020251000036080c5140480300c800c2800041080811051103a84100f4540c4025a8041001e48000c241c0798102c000c0c286480d107403040c1000020310742e0311040b4aa80006000c000d0b004070300c01d04006001c4c5503c0501902407080040f056544d41d1000e90480c004048414104002049150503110140b00d4040c489402c0c200444003840f820800c440018450141c5075090380000d0000c2c9448002c0340320115411000d40c84041c043e0784203204064016903154420003c0ca014144241c041c011804242d142c249413680a10800040080e001002c00d5507840034081c9a030301540b0310310703402e9842c000300740001d81200400d500c0750041aa6201803520030f2140504083c601400b4107000d40d044a0f01c070502013007580207030071070390001302504903440b2548010000c845d113a101c003d040252200d41d000b00b01c2214840c2020305000300120103d08010b44400294021101000010000b0134070000f4582c4424400f2825424040485002881594006000e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425419712 1250 425418462 425418473
    0x3080c18041820010509040504050c06040605070b060a0e01170109061a120f28081c0507030603050303070507030c02100224150915031f061202090a0203040206040e04 73
    0x210007510480e8180c481109200a4028043d03026881d580002c80800140d101420140c1003142c10a1183c4c04603404802d40c0c4001402c60341203500102c0003d10b0110b6600240581c146140d0b40006003569130450302ea04000c0c038040080d00500030300c0700c5006007124805501909611622107503030050300400c1400ca4800d02e014007080744500251007281c950b12101b440803804900c0d0034280c10018010300101c3c00c4c01c90a500c10480440401108404e03004000b0045600900280b1502c09031250340343d00722420fa490841155009000c800802d1714140003440001e400204503504245203080080c0c442c1168a4103c0301c140141100075000f1100e51403c0f028190000303141d40100460889020300c048804001030b02800e0210380d0f40025001c80401801c540c28a800080c0d00602c60403c4042000c903900040307440c0c2060300442d042a88045083c038460070300709100d114040c00301e40c45030750241e0081e600000c54085c0090114003440798000301040855075000d0454008016403034401a181c40e0034140b2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425420962 1250 425419712 425419751
    0x70f020d380718030c120303051303020709240312030605090705090d170703020c01020d111c0c0c060806090a05042301020c030f1b010903080c1804 65
    0x419440810080280010981407411000740d01620a40342200ba40c0344038080b105402c0b4050184503109801c10003201140d00108034034050820303807010708016100d500e002003c544005000c401c0504020b0110000030703601042907021a407203103401140855810316a80c2c40c40785d001c250804850413401c4c00100f00090540c00c00072072485901d0401842c0e80e940b05101181c502290404001581080b208036146400b0b010089550300810300c040800259003000c40c1298004030b01a00540d2007a40130343c0c904d6030304010f4494885400d16042c190316040030038aa035582090004420111400484500100c0c462901103a506802850a402c40c0e6556203016144110135101341d0b00480a400001d4500c0c401c6002d6180a2a8041c52200c5540c0c000a10120716490600c0084000c0d502004001c0f40508104040d000c0c20340d154043c0e50307440e140ca10301c0c500810305900030000e450341400402004aa003111031558081c0d40d00c0b220725924130303403125031101030000b41b1165980035103031042d4000d02c018000c12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425422212 1250 425420962 425420993
    0xc05010f09031205070e2e020d02070e090c0a0b0301030606061b0303230a1a04050121030e0301021314040506060d0e01020403060903050901021501051302070f020d 72
    0xc0100300d18018940c0165004410040e0105214280038520500303150300243c0e01009520f49142d45020382400076907000c1034291691802c14503070295401e095031046203503e100d000e50005040c0d29803420340280d1615514414a40d01c00c402c140000d88904040c01000c1030f0300c100a1403549d4058454801c90b0480c3c000307001c15640d192070302c4c0003c03414a002c0c1c002800b0030158061030b00c1c400380144e0313401c9010380f140718040c00240c90100040c1c6003145895903081d008410703002c00800da0300c1c0c2e5003035014080580030000328445e60400004000000c0601e0004201c100c10000d138181d0340701a401c1c2a102200307a0004290150710002d1000801c108402c09001900c0c01d070340703c0d194240340305010002074a0003a20541e6101104005000306c040c443d900421003041100005403d00341e4075100c8804446541130b00707401081c40094591900c0da03044c030864001761180c1d014031409504000204489095101c0081c0f41c882c0e000071032009000d8411072018010b940185170400c10106840d10a980062580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425423462 1250 425422212 425422223
    0x607020d12030c120207080417030d050c181c03030902031e0c040b03030c100f061205010905060f010305070308070314031003020a0f0b07080f04030b090f28121209030c 74
    0x40200900c4041070007206c6c4910380003d655420305051100c030301080780d46c0c40301958452000300044606001c81e07000b80d92141071075000f215143e076442c50f1000103407110281c10034803903071500100790000d01e440c40d500c0071825010b14002030441c540e072000c82c0c50006601000081c02c207145c02d81c5c0041e004000740c60200344009a030309001c1044020141a681c1c001c4904140981d00074402060a8640652142c9280110002d0104030b06940f124002c13124601d0203020303100c070f175101c603801da0a20104200042c0c1240780d0500540c540e44c03440d2074003525000e940c003000f0300420700000c20038181441002811580341d5000c1c1c0c030b1641c0c0d0619510544620103540310807401054800400640d51416402217002c032205401c030340d40751a04550303410050307a110100c420300005048c4804408124aa0001485803014400600e102d140035490f5620b44514810400c062484808071403080e4100c0b080e914424903800110b2015510004800342c401881c0d194020300c40a00d00100401827587c8408a1441e4030b0199 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425424712 1250 425423462 425423477
    0x5330109050906030303070e1318051b060301060f0e13050f0a0203310b04031205090c01050703030209040e0f0c12030408120a12050106111506010e0607020d12030c 72
    0x10010b0141101d0102c81c616810f82060002a00d503501592001031242c0780103100714010030107a080c01044882e80101400e44c00d42c0e0200034070810008006004807020700c024021301141c003640020300c40d44414042c240800c91802c044090060244080300e68060b0010710007010301b54170b0140c13100204030840e01c0c01d0081d800c21001c200c00d0304245c42220301a003029060b8074520555400025146c841030a000c1608942e03e81c200c10109050048150140c0e2007030340c540040c2c2000c1e10308101a210003500c0483c958000400c4015141c0c0c100e022070b1450380d898180540c0310014000060018611045610540d008900c4144440b107804144070010b088111800c84901d4260500c041c1d80c1d000340d019013082c0b80e104d40980b0200618420140003031074030307906d094400903045812160680340c003a4090404210604020070420a0034003200c2d46001c140c5602260301c0c0f8020000030a42e0341001502c500600b00040e5406c1951142c20f86007807101e8203c80c4900d0203581000c401030090004030140c00014500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425425962 1250 425424712 425424719
    0x71a09010c0e21101b020d210b0402090307080705030f150106230c030403060b0108040b0402060912070b0d06050a0308091020150a060302010c0605330109 68
    0x2d00d0281001e1901600090345208080000312288000442d41d01c3d482c4a12a1103d9080d070041c0a04588500100840e0070f84102ea100083d02c0d0114000400040c03003040c07a000b00c02401800700800c585808800042030303c8401d400414001d00c2014241a014058410040346240c0001401d4044035003d41c00c80d0710301803421b56920303183c0c4103d58441c503403d0300b40001000706c1d500c52825440b400e90092800a041482c0113103500c02540b140030001140e400118042083c0441da20480400050a0030840594646640c40660181c2c00800003441a600420a000e140d101c0e64450501061568122101152038030381400c219013004669415a03414500c01091500f025040d0400b100e80c02a000c50070300f10107004111844405003084400c02005448120941c02c04103080c04505520704054414460314000090004800030162400a03042160810060340c0c8441a03580d50350308000000f500c3c3d103410742804160f00c2c0070801840ea02820745090f803800043c0540203001e14600342c0365041c881c6d07503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425427212 1250 425425962 425425967
    0x120b060d0c021b0d0b0924160503090d0f0e030a0302011a03030903060a050613060e0901050901060501050d0b0310020f12012c0907030510140615090114071a09010c 72
    0x2910711101d80210781d00c41240001006003200c0c0d86c1081c1280705440c1c05101c0400d03691045a000d04000e0419800c40302030084801d80c0d510312800d081c03400c0c5441c914601d80203240c136581e40c2e4580502c800b04100c14007007664aea8403510b08101400f0000b0117944c1041142e00b0000d02804010b65289900ea4401c2841c0c2d071549400000c44040d0384c00640500601d5440e481c42c8001010b0041035507412140300e01e03c0305101c480e01d00c1414041d2400114140c41c50074400081c03421100c000300f160b0b006a15040d003d000c540c2c0c000702a1002d03c54007900100344100c625006c01d0824941c648a00c0c1c155001041900d4807140e5100588a60b8206481d071415076a42c0e2411209403800840030050003100315150002048440e040440c0d008a0b40710484103100c0e62507441c00d203802102c0718903d800d40d680d0600080c05140c448881500444112103400c0d00c40700d4039042c0089445103061081c140120419a01d010360300141c00c0e1520160802c404420201c0c0e1240007000c0c141e0112205503540d40707003003a00c0847c80d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425428462 1250 425427212 425427253
    0x170c060c0604032001150303110a020f130e010608011d0105010f0b072f13090210030510090903120c0302130b030601020c030609010902011b030c03120b060d0c02 71
    0xc1021000307100585554400350b4603001c40c0c401400000078560001d03e0104401d01440300c8041d18004c82030001da18500740140100c000b50340c1112a604000303015000340c0e030380d501541d200010840d00664100c082d000128014803404903404240d50a040c1c1c00603105806600c00c0c0c03040100e82426000c11095005024200d4609000e001071018103504148002141000a403d9013132042040a20f80c101e40e0205407007002c0382180c10396980ca0b80c04004c01c00c5041c15010603136942c08403401844070b001c5550001c1c0418030440700303003001c160307030b6000246440751075030049001844043e5040101491394240104030200c0f2106062565042c0000480064401d1003104c0c10800e41c2e003880c032007040c200030425400ba4005030840381144680e01c10242d05030f8086c466940214811400029a0908c61001503c2c41c180b20600019410002020310b0200e504606040c1c01e040d813525010f80c000d03509140d0400149179401100d1380081022620400303002403544020980c160035021680000007020f0200c0e00d40d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425429712 1250 425428462 425428477
    0x1030b061215130206030405010f1a030303130c030f03270e041101050c010c0c0c08030a021f06030c060203030a0b0f0120030d0510060e03280507030501020301170c06 73
    0x7a8011030b242049010761602d2141c219501909481040000e500000d0b013079082070718151010303551003003c004201c00a100d030782040c03602c400d04a41240a018002600c80c00300a06c4040d0995448404c0400c010022868101566010000301504001820b00030110313444001490203502d050100c900429600ca00c00608580181840d110a0b40da00d958401064202884280c1072100500c250a1810780a000d450a82d10b4644e0701d400e181d2542d420003e00c0c0f0303c4a90700501050b00300700102c40031258046586100020084808520300c002502108010241540003a010103842900420100d60200003140900c44890060000d15800d034100100c0500c408142da0102e048100341400b800011115443c1191410040c0c9013000054010001034540c1141e00410540d088003061100e160088141c0b000904154000e00541d00200002c030810520340d80828052500d0903414002c000c010403001d40074581c004000d540b80e59491070110740c0c801b0f0462814980b80030f51040b41e046420280d042e01d440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425430962 1250 425429712 425429749
    0x1030c0b1e03070e010e090112030c08091e03060703110316170c0a1209080f0304020f12032a03040308031003080c0606011d031005060607020a08010501030b06 70
    0x51610303003800868190301008041141414250740480d9014600e030107103108500c030343c95a5500816000004040d0400400d2181c450075004c3c00500c8061105000751141d50f525090000044090703091406042c01004043c55105013000c020703807100c03506082c410b9200c24055007155041c1d1191003040d410b803402d0740e0001e000ca810070700000714600d14400c40e10100240c941041d0700818900038010540303075805c03a074149101e034000640312841d40d800000c1484d110b007800402c20031401d003603403450814413440070030528849010010030255a1030b01c9410007112030081000c1240d040c0040400e49230b0b001f000c40445040c54405d14803c0640d4000c1c01e20007003107034210207580303014250303550280a80c001905082c00c0a00034200480082c1140000700b8000802100a140b145400c8000400c9410503161840c0310074140e58103065240c03000030b0060584010008049a181d940e1400b0803c507005207040658000c440c0380740040c0458043d132000c2d050b24010414941190b071a81c1c20301c0303816184048240d94 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425432212 1250 425430962 425430983
    0x230909130b06011202090916021621030e0303071a07030608030f03044d060a0305090c0a29070206070b040507030206071103070f08030703030914010203070503040b060102060103 78
    0x1083d03104031412490903944c203a005003400000c90104010309400c0343ca0b00c0148050300500d000407501001042640041c10362461500b500b403890214282e58411641980100f40740707200b0f005c050068250101801c0081d04903a115801401c100300d6101c0143c0144040c1e01145001c42c501c03520a020320020395101708011454404d100b10030100c3ea40c002803050b6510307c0401d07420306400c4803001600040403441c12640c0505014078120540000e01c861000441031701940e42002e00d91541c4098030782c02145800d00145994600c2891414030309072011091307100000660106984280d0045020402050346a103c0d000200178070601c180e1055283c06035210b0400e10180780080c0b2540c100c0d66000e44600d041c0e41000d90b8946c00f25100380c0207a20101c402d002d04031456002030804018490090010420868a251500e0300150704e138410444023408054840350940e0501c900d00034444a00003105000310745c0d038902404000c01540080c1c40442d140c90030440410050340c030000740d4078180c0b030301700040c0b49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425433462 1250 425432212 425432221
    0x30e030703050c1018060b0a060c0f03030f0e07081c08040f0c150512060a05012106050d08070213020309060a0e15040506060a080109051c230909130b 66
    0xa800e82c1000b4180daa040c45070013074504510380c803030144810700b00d40148860702650691400d0419240204082030082c1e01c902c01c00c0102030345c041d091122043c0c21944201d2102503a04040f8060511211103100041c140194a080041c1c009a5002190a0b05080d41e0140504200181c0b450780c0c0a4880c4000a40000c007140100d20710300c4203094054841c40031540243da948007902411030310b1b0607441001c41c0020038044044000240a658801c40456075606220f0501e00041e080700e100c14040300500722442c1001d2041c204552044000e80720050003004c00001c0d40c60081510707400700004134044d055808420710300d5461402900d000e561040c0107482d0643c1c6042c06e401c0140002090586a482420303141414108007400075405540640040c3c00d540c0703000814801d0001082d03218207501c0e0301d803040682c0441c0c408180e207043c4210b1646440901002d510040b620800d200c0001d82c01004807811200c2c912220b20002d0a0601042e5a0b603802942e9418040c0403440341108050f00314003c54001a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425434712 1250 425433462 425433467
    0x903030d0e1015030b01061e0f03090b010305060403030b06040f12021302070c03060617030d0c0507120e0118050306070e0406090e01060812070c1701020d021204030f030e030703 78
    0x12a407035035225080b20801d1040d60b42c0c840a40720301c2d00c031200070009041024010b012040700c40701c3c09003001d410600311403981843c010308107450f80d901050802115030720040345103200c1e8200248031500f03c5c002105030358507030614030b49550301502c003100481e02d0600003490b64280602541c0032110145480340c030461400e50f40000d5000c05100890780040542104903c02c0321314405000800c0c0240f0b1620314013030840c03415904652003600003515040d200c5004044540b8000102c4251020340b40b8045a0107840810030384060140c1c91006052036039540c0c00d500c0e02c580c0a040360444080c242d031360100e00381e12030300c0c048083c10540c0505501600540c00164095000d00c0407090f031784401400004455641c0d141000403549115400602a5182d03a401c101c441e80403c02c46a6a84007960102c0c907000d0306565400700455a4800c150f500944021240f40d058020741c10744802c1c1d28500429561307180c030441120b00300c1504690440120b00040f00300c0301d59038401d02c199100016494015882d001040c0c809 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425435962 1250 425434712 425434721
    0xf05100f03020409020309160602010605060405060c0c0405090609010513120305250309020102060105060c070611010b09282708090a0f03021206060906120c090115140903030d 77
    0x2003401d0540811001803841d40030300c001e5200345003903c050300551700c0d501c00c03d10700300300b0f9548014110383c10310105000642d6420200d07400c5600450303207030b60f40781c100800c1c940c241a503141c0010f5000d480c08081000105011610f14450081c10008200c1690b40c41c24030404880d0000b00503000100710304d00880c985000e64086d60f00209031001052000c0c040c44001b90140c0d000342c00703800019440b200f0840455804000c41c80c003620040320294100700c00c03080125500c40d40c03803050500b002940540c00a40410a40c440c030840503001d4103014240c6800403140d800c10154400714031440001172a100c08504080c4038001d501014407440249071050207070b203440d455408003c207550352501041100c4c825a10b1075044401090040c01d411004d03031941c010041500b03200f00911060741c200d102000a140d607070b1108598802d03021203107113003081c483c10b01e0b075450008860030b40c070303000700e4401d00118082510000207140210907540340c0f07440203424411440c8900a41c2c2100f81c060b030041c4a804600c40c250b802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425437212 1250 425435962 425435987
    0x50a0f0308070210020a0b010f080f0703080909070c06020408010218040207030e01110f0109060506010f14040b070c03051005060f0f0a12061b03020c0d0c05060a0f181b0f0510 77
    0x1190f241d01c001f51640326001e40203a1018640c45c03400e10040041c400140921545402c02801034240c217840c585800310a403040180c5607200e202003d000540941c018851039060540003002191100c3e140c6803000e00075402040840840401d09000d803845107004e001311800c259150382c929484400c0c03040152140348004202c0b20040c080e80700c1986500c002413140e944518001d050104542c280710b00050300c1461229008810000f4034061080100b086504071740c00c41c0c15200c20030b0764492160900c001c032152540c00050441c040c031003860b070b800c080c80d0b00120b0148038211441240c02c00c5040800800422481c41140c2110f003003641041020f20701a40356a045002e503001148130060361030340f406400814070221001c2540455000c032506c504000380c0b1803c041500b05035104034855100c203561288010710241d4140c0e12404000c188072905d402a01d008604a80c00041000b800d140c00c0f50300c4400315000c2c560341300c201c502c00130781e481c41001220101c5138040c041d601c01900012044a0385100d00c80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425438462 1250 425437212 425437217
    0x11d01030605040213030c060203160308070504051302030406050c0c1b06091206090f01020708030f07031508011d07031a09160b0a1d0105220308030709050a0f0308070210 75
    0x214000340b80d45850000346140d8001c841030745416415403504042d1a00a6044542154405e100d60201864280da050030102d8050800318829030f104541200d00e03100c1c0e600090b8000d02880484020b214481d00618040d5105040a10140d0b440418941182c0681c0340c1204003640042100351030b641c00b142d41d0300860000a0289803400f11920046041221104006500e50b4421010414440310a2018a0300000090000d40c502440d5846a5119010142003031301c0e37264022003c200400c1c0680d001c1140411000500a09103030354031807813402803121140500a507584040c520302c1c00c84001c5110402e0300d0388503004009000200107022809400281039540c82c2c41441106c03401104101c503014010718922400c20340c0d0314507984006000600d80d903038901e440b01c2085424919130b81c0107402d488800b80211390540200f810b03500c0000c00c81c1e05c503a0015141c09400400d2001480c1c0c000c40240a0703601c20307103c04061665501c1c10801c110030622001d080320805100601c018038100031071408188851 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425439712 1250 425438462 425438471
    0x40605130504110a140306010f0e010e1e0a05011b060908070b010f14040504030c02090c210403090b0c0c01180503100906061403030f070302010e0f07081b011d0103 72
    0x32800b0074202e07034003a100b103540d28030701140d0110b14a41c081d00c122082120701c40c280e4158140100060070402ca0036001c0414445014481c42c1e00380d200e0304011100640c01001e00301d82600c0307040d20b000c40304110503965009061155000c10154015030100c0c81ea21204032026100d01d1050b15031500400c0910001c031600d80d41000325a000c108030a199030f0181c48200d04000056181003d101d100d2240c510b0381c140180e00308010040803130b4011020f14400e40c0c05582c060f002d90780d0454401c140744116021242a110148600c1034a501c40c10025407003a8403a850b1100c0700b41c2c0f82d2880d1811802018000f40c0154002e100882140d441780c603002c1d807840000c1c41811070003521840082c3c100442c520307100030f0782941c4801c8041400910b01a5400601c44103083c1d6201000c00800310b0f03101d00c101171404800e0b6000050341010580700b58040500203005100707503030422501b03c0920361101894820441c092094101c541080051900c500c2c8a00005856a49071040900219880b11030034446050500d0340d034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425440962 1250 425439712 425439719
    0x10507020703150b1f090f0906032001030f020a030504050c09010f1a160501050a0506090106050702060c0309030111040806070228020a03050316060f0204050303030f041403040f062304060513 84
    0xb480d0303481c5c440c19003584a0b0b0f100507042c00d011601c100b10710750014a41c135080410800114884000c079040304502640307030400171441030f40181d01400d03202465200c41c6200090400e8006c3c0e15074031440c00340b88100c0c180c86c43c1d804582c0400807040385c00e0041003542520004108a186031080720310b0450034203641840d081100b101c5801640f200c031028142c589944800401040f24507600c00c443d840311044a088140d0f50510900800500802c0c0009019140008900005080c10010b4070003107400100240001106500d1039103136134200b845800110302c10540854a0303540081030181c448190000e041c07a10103120644c002070090503140c1030385c202841c0140480400c0051004068418101401c1c90050360240303000d408850310700c440582110302c1030109010554010080700e4001c003030703810907000d5074489003130019202c8a10305280480f40301c0014000b4110100c101d0300d00c201c2d001070311544c0001c02000c5901004880c1c0103843c010401c000c0206002c080c2c0558082c4c40440381d9101c005008649 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425442212 1250 425440962 425440999
    0x21045094503110c030f0c040b04020f16021302190503190c0305070905031b01080c1b0c01030f0b0d0b0a0609020c0307021c08040302090c0d1d010507020703150b 71
    0x4011070a400280c0c2c42c8800b602070b64010092002c110f8801d50040850784003c00205031100f140c0b82150740304989540f0b8042223a9125015200b80403000310704196a8030f4022000215140e080d40d08900900d0700c50418859601503200b41c03480e00e18440303800f4118a21050b1b04803040d40c001417070072030f440140c8041ca403103200191003002420b450740d4030001400e08040201606443c001e9000c54400d034803a0b203004510b0b42c0300d5400e07180c20120a0070852103039201e0002803546406800d1030b148010150320b009406009000840d0210507000781c80420000c910007007400c060b980032031040780c0c00c50b07412a1500c0004034030302c80315075110f00e0b050030001d44542c40e8a42103040e0ba01c0843c0c510b01a80c4041104400d51500c1104d0b80210485200a121b071000d40d50750f41c0d442c0b40524403001c0e01c1503882500103010020340e0b03412590000c0c2d6484c1d0070044030a12908440c4070388030280c40f400c030039860040020a09800003461206407a0400d1140000034800310100026100144800b0b400c412080b820412410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425443462 1250 425442212 425442341
    0xf0510050f0310030c050301021806070503071e0606050a1d0405010e0a110415050901060c060b10030e151504180b3102104509 56
    0x80ea0408042c0b081c3c1c618200002080200c4d00301b180300c1c0c0d02c1048880015401e61004006003401603403410303207840e40380c103210f030031800340400c017801c40d41c09110401c2d00b90703840032078000c2c1d104e100305800c008a43e260024809c2421043c090701c1c1040b08029001e800301d43c400050030342c0c041d214a00104058912800e02e6003404101802200c090800118801861610b402010221854940026803041c40c0c400007541103030040c420380040c80b42d9100180c0030302c14140c02c00301c001d50015280b41c1c3c42c20b12401c0024001d011085c1c1c43d84031030040305280440302d00c1100407203001d404140f0681c2d10b0070b082403007040000c100350401010444150354082c5d001030311480c0400e11806200c0c1003201050300c2d400300c5410001040c41c0317110050350024900401695420f40c814058240c80c036050300d040001100d110344080c0d0300c6941902407000d0b05039070791032000c6070b011030324032034086109100000340d0352400e04007500c4c0388071901c814403010b0240b0b5410b10888240003400c40e8001c44042098000e160100d1908038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425444712 1250 425443462 425443471
    0xb0d050d030605090f04020109060809030706140103030e0a050109060e04020c0f0a0201080711070312052205040c080c0d0e100207050d0815090c03070c06060b07020a06090f0510050f03 81
    0x1035281c08041102e031078820f100c15400840e4026217642454240d0001344040524001c1c1c1c014020f070340011550301c103804c2095803020b95103d1020081c1c80142d00344a2601070b424071044000a9008c0e0b964100c82c2040700803001203a2041c1c45400d5a2400d02e00c0603234024551461441e0029801c0c40f9107140341c0d00030001b45003c0c03807007440901340d101c40a00004250b080300401e00000c0c04410907058882c41c07000260764003108e07080b02081400403001c0070110f405106184020507404c480741c11a8041c000d81c0d554810848000b150100300c840c540105c19208040c04581c5103ca1010602c41c0156500064004031070811000090b074a410000240001c2242c01150043d00c60340c2c841103020b45015000b210107900945103c1c001e240e00e10b030900c0011071180300101203000390100071010599650203000618040d6902c800240300043d16010144d0310b41d041004160702c105410407002400e107024041c12019621004528654542405d06201d0105c805103000700c01c003c02085060300944080e0040c41c0035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425445962 1250 425444712 425444717
    0xe010b030304031a0f0c030c0f0c1c020706110c1003110a050301082a010e01021207030206040c141003020a0c140d0201050108061509092103070906020102040e07030b0d050d 76
    0x200132200f00e0340703034803900042c9510303c0b2400f21740900040c1e00d0480c00360380e4442036a01d10555a070000038000251800b65010491541c4a9051810b1224000c0500700710040020f074202c41ca42945e0f52000c65100c10784608100e102e07040464800c20304e0410103100c0c8491502d6080119000101d80207154080e44036a002900082001c801417000340c8051108119808242854804140104084284e00380d07031584242d041c0884642c503131340141d000780150000d003010160526160000c80c10069112030040758215466180c8890202d01800c8019540d0380d0f00b28003504905808078803480c140c0003548100c9a41c000e12015001260008540c001a60207041e0a00e000d007089402d000c0d406420f40c3d8042c4c110005075040b510802040c040802c02e1840c0382d4004450400e2903840340c0c001903040484103048652610f81c010761001455000c08015400790f151903480c040d485aa0303180490803070085001c0e01d5a003c102a0125040d1882500a02e403680c100400e15400d407801582d0b02480c1000c00d00c2da8401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425447212 1250 425445962 425445983
    0x90b070203070c05010503011809150501060e040b1002120a110a0c080105310305090306100e0f0403050a050c1e0d0f08010e010e040807050a05071503090c06030e010b03030403 77
    0x8101d0f030083c0c60402040c003130a0460865050841e80c0403103080504c0400344040d41c0e0810307082408080c0000c06541d00030340508101c40c0d42c6801004004011444000340624105601c0f140c15091041c000040e81c000740d40030b04541c02c04100007010b940d0140e410601044840c4103842d500303403000d120301411b0603c201040c50401745491409829207000801c240d041100b052651310f200d03c00403041c0e030071242c07652100000f80d405a142c20b4a06009100c5556014800c000c1001030b8015404980802c1e18403034404501340340d60b100c0343c000039542c085a0080c0040c006100340d90740c403070290010b440070f50074000540c3c454603869001e107200c4800c003809000240d4060b100780c00c0b203a0341080860100800314a031140340d41d81070090070340602e001803040d110362450f903500140078410b82c20140d903207580c1c1c0501520034504644c00c010b41d0341d80180c054030b032a00c0e28003c1500034140c040c0c8a10950140d02004a080e99460050150000d0402d0045000155220201680280c4e8144000c1022750b10603200c201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425448462 1250 425447212 425447227
    0xa0207150c090608010b03150621180c0603070509090a0b090403021006090207030e0f01090b030a05070815030d140408011409190803040609020f0607050c010810051012090b070203 79
    0x800385141a440309400c00d501f0824084010044a40811900000e071501aa5034000442c029081c040090440349138200c00c0c81407011442e8a55200b020515450044440600021041041a1100703031004804540200003134405410900309650380312403481c4000581c160014003044242d2411038080300160891622100c1e60107035440780308045d2514200442c10118980d0b4054040850903102c6841030070b031a104151030760310450581c005081d130342001d941c0343d047c0000201d01808003510301c0d1000c6118140083c0c404c4a8090601128180003401040c2c40038403444142e5102c061a00c110046513000c0101013540d80d4240201c1d01d21000c440b000d82000d00e8140c071005e0a0071401490303100c840300300030100404140300c0c100741c0c1e41194201d0400a024202440011459004042450303000b15010806605000300403c050380360403020b88603420182d54444030107140c80718a000b0164800601c0461140c9648290f25054060b88007902c000740890180d2590030143c102154414011303440041c036403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425449712 1250 425448462 425448467
    0x302010903030e1f0207140307050f010e0d1b020d120c0b010e0603060f13050715030b0d150f0b03152e06030903051204060609060b120a0207150c0906 66
    0x5050100b4250042c081c2518041c100800c0c000b42124060030395174000c22550103125140380d0b034400d180c2c024000c90b0f0751084240381c856100d1554410002d255440d0165910704000302145c002c4609075940c1d200d5007003442401c005050320240300c00c1a0380004400082c400050242c02d40d6078560207840e200d2190354081442c1c181d941c042c058120300b0020040a0a010041c0c03800608984c10130501c40644180342e40d080320a442d00722624902600320702c640500010700070882201800c0c102c15594080c4124004241031150281d01b49000601c06c1e07440f542c0902c2a1a0701e580100900018828013140c0c6800c40000a4034100d82d001120398103012000a200c20014018688800c1c3d0381d02d518041c05892084103107603005c02242c801c183c103260b11103030741030205032083d0102e03594030f81c0c50503251009080909000005019600940260710b1600c80082100d418171415644800740c801c1042d100380d5108403050000c0d410001b0211050203650000b8210340415000e08000d480b40f942d01c1841c06480c04a00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425450962 1250 425449712 425449721
    0x310080109020306040b090a050601030b0a0e16090b04060e010b0a17040b071d06030f06120a08091e0901230906100e0a090606080a0e1212061507030201090303 70
    0xa400980c5011103150041c0c8000c901c41d03511940040501c601c5980300c10031541030094040c0e004000780208030001c41044982d080480c0a2411030074100440e800e00c101d00d556a030a403a40c001c2504881c0c141c20848240b00307821100100d0b03400740000c90b106540321146a00920203030800081e45101280d840340181d4001311400080480c0800011907041685841d065100c014120800b0407603501001b441741428401b4803d480500904155920303d8030144001d284a01900c0f80c0d8816a10780401012500001503004801500301d070040e8a400e18160030044c600411040005803640008000e00ca1581e40a01369030007404041c99a128100da000751095030b0031064001e0601c80c0c05100f0500100b9200c0c0702013180e90050303a0401520f95003030b180c0040e80000c0c20381c1c4140b00f5a030804202241d440c0d48159154003860307002409001c00806145031944035403019012807003c820500c070020380d09007813010042e00302c2c1028251500207000310071400c1456200403070135000740c0c0d100d48423801019130600c113 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425452212 1250 425450962 425450969
    0x1302130c142709040c030b04081e2a0d18050a0f0303030f1419090c060e091003170a050f040b21060a050409050708011503120809030717070506010303050310 69
    0x30b44616134640355440715812451800040d06042c02140050b007008251700864504c0d040034403126444040a4040d0b641c1540310038220304481002042102ea110204200c0040001100340a040e07602e414403030841e000e0421400c19403001208250000b07043d21440f07654000b510710050090400d0b42182009002d0341d042080c0c4540c80303071424820f42143d2034001d90301600300814ce507134120281e5102c0c07100c5020b01500000505001c94504002a000741c11400c00368800c00107071140c04980c1d0b01c01d081414002d24610000d000320041055144c8010501c50003410504a1824080d007001304000341504990410341040391304400c001384213120f008040c1c004070380901030394030100c0e030504d4448007092140b065031007200c0c011a1226990380c1081000e100c82805000040c00070040088480889510344c41d0f03a200a0f50343c00c1e103000e541c0c407030307079104004030740c0318020050080d0300d010070555a40655100d4050f40721250704007404040d00059003480310074025400395691030380740d00746150480702c1409160f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425453462 1250 425452212 425452219
    0x3010b0a0905092e23090c010306140604050d020109030506010f090b030c01090e06060403140105070f080907060c0309091a0f0f0a0308071e08121302130c1427 70
    0x228040034a103101c1e02809900400ea1901048060401d01968203180100080d88282c0144400b00000541b000802902d40c4000766801d0044c15501d500e84440b11303071542c2449400c07a0040105204c142031002682c100c10b4810f14001b6941a500d80b2594104203080e007040c0c45020f58400204540200c84c0113030400c6c1074044015000e000d4210340060140045446000c0750701c000c40c4006801ea5031060140c400a40d0024100070078014414446402000110b038004045a410712010000703234484c001c0e280c850703031510300203021250801c20181c40001c0075a400301e04010b40e001c00445d641c030450140782c1d402074903001e500d100c0d441440301b0042610903008900340035020440d58060207656035210f0744d04494100d00019664002030420040b01840e042c000307400e0485e56804102000204070082078110440401c1c1c022640b42d440b014201c040b803c010217540155102c1d07002d100c202c801c2e8484484803031a800c20b14084820781807454441e421100c20548040340ba1512603100070300e459001c905101044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425454712 1250 425453462 425453503
    0x60901050619021e070905130528150506030708030f040e040804030503040e190209060406050a120c120e0601052b05011811010c03050901030b03010b0a090509 70
    0x140480d0303090050840c1c0307501c00604001c2c000445802440358a840b4413014682c9802c4010401d07040340d40343e02900c10110380518240c00140f014152041c46940240e112015100c85034a04804024051020119030100c070344020b08600020100c0c1030440031161b502c3e00200305464150201400d12100d6401925641c00820044980000040450b0152040d0226550b0a900c8604000040340910b82006000b44000900410a90120801903100f407400301021840907080c044118103034010304401c0d0740c0100e4140020302196000c0c50180580c0180c030b141000e80c00b02c014103080c0c169001031200c0400705001e91040c00800070140122540300b15003c0080c01a0f514007400300b5007058004110600180d603d00401e0312030b80401d00341d42c00c10740d00100240003900d200d000824000180c0715048401c0002c80f6401c0c0c8080d4010070500c0681d0781c26840352800d101b035004c015000f400181084c282e041d507035403c0b0486150783c1d1038104400340401510010f12403510f46042860480d1100c0d000c007068400f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425455962 1250 425454712 425454719
    0x19120606031a042f0d08090306090a120f0e0411030a24150504030b0f01060f030504020f01031a040614091b03010501031e050901140601030c091a090603040c0509060901 74
    0x75440c1c0300031040a07181d1000c58071200d9841c2c25092100707040d0050b1301c4844041c0c40400d1006c0c0c44090000c00d00114241d030a2900ca64402c1680c41407010b0f0014044540604641040c0c0e0043d41c080c501154503003002540d2800600000c2c088a02c502a0380c040001b0100a00541035001c0c0320b080300c824202071a520001039102450b13115051a8800c40030303a030075003021400d1b01910030ba05880086600c6203100f82c4508201e01900300a07170090007200005503856421042091181c000c05015903005040807400b080400c0044014003120044900c562510105581054071284a850014154410040c450845003130410030b002c1340c0079159045040620808610b040800011641198003d00b03001501d040720303001f80042c034500a1410801c451511003080500310041d04030200c41d1441001040859aa40b00103408480d1540c484600141d42c505041c00b90708070000304e81c001424071034400d07420201c0420018856603c200c804a40101d10898204014240248516001441100d09401d00d604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425457212 1250 425455962 425455973
    0x1509050303041203091b0602060c1213031b060b0a0b09100c0f060515011119140304050613080118020f0103150519140303160219120606031a04 63
    0x1000d00043c2c011212040c0d0601028005d80c490041d8a920074485542c10880807201d8040c1c001c071b8890070015010b0440040d44148040c400c0342c11402007055082c845484800d030710107515000e2101242401030021b200d446441d54040d042000030b20030701c008110348200405010103805190311858076001c05100100d55966080d00700e9070a0291031800c0022420b89040880741c000700c41802a101d10700d82030a002d150210701c001e9959454007030322406400b0401c02c40e0507030f984240302d241e80b040c8a01110f0768000207410756411000c20850404403414540c40c6c00c0041d50303541c828031050300c064010840c2009594070a000324240c82484a02c5000810055008903020b214103410244c1003564404e948140308410b001c60710043c02d0040c2c003804421001c0540a006c590f00c502807800e0303980d80316054403084e181c000119664107c13540c604240d4440703540e007071080342061000728880411a0580101303410700e000799009040c038043c0c000425030300d1442c20040701070500c192030b22058407001c0701044045103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425458462 1250 425457212 425457217
    0x705030f0109020906150403020a030803010312170c1e0301140307060201050601091413050a1e1a0d14030d06060e06030411100e150301030c170d0318081615090503 72
    0x401035860600c0d4201510601b10711788541d804c02584181c07180c0000c000d0010381c0015505882c42a10100500380314018182c407220460340850105511280004084125203c00f034000d11034180481051184003070750b03404041e00b007600889407007520050401614681006210700030400c81c00200300904003c0002003000c401c500512284e43c012216480c025114101c0c00e80d60803280c210100002d05205a14074060811041c00182580e203810701c1808016942c8611100b5144042c1504004c1c80003134244480780c11868000e0382c19405074080143c001d2003c0c4000d10261410307110000e13060307050040151680c0005a1501d004120900401c00050004149403204030800c507518215614100030498a46149621181d082800c1503c000c000c03908450186040c0c91003428615840c503215218061411408803603e000e5504c100d01c041041d030b0003940011141076109000e0243d404598590722501d030f00c4a1030a10000e1304680f10581800a02600c41c02003800744142440404656103500c0d50301d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425459712 1250 425458462 425458471
    0x6030a05040c0618050907090e0a0504020a05100e0904060b1e090c041220060720180a180b1e091207080d090c0f0801050901091a1807080705030f01090209 68
    0x400e603200101f4402d9024100342802000c1c0026250302d1480c24101070700181800742c80c12802030074040b5003c103c519140e044403010b00c000d44e40f81d0305140038030401c0000c544005002a1f482d15550400d220301c945981c82a40310203030f0010320343d64105200009118441c08000c1104000c0e085c18801807111070411070702088010317080a11818821042688408018244c5020b40d50004001922208020509010096103980c1c16045454042c0c45004e0040e1500c9258034504080b0f92030000520b543c80650100d81d06c0210020148440841d42ea140c81c0449000e40303810070814111003900e030381825001c58895000784c1c3e00c400b4142d1226602c103480c031180030707191004010080c0800c1c50b00d26816030b0343c01042103503004803041c0c1520f666010038892500d90340c00740001c03a50810000032070261050040108080e40a40c030f07000180160340c42c1003441c402c0035113141c0c12291076031000c406119003001113501610a206c09001e00c60724040405180002411680050b80d0514080a015a50707040c000c60f1310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 425460962 1250 425459712 425459719
    0x40614030f0f0a0e01020d1d0607020d050f04090203010902030f1b0a1d040c23070816050c0405180d08060a060f140703080402040501291806030a05040c061805 70
    0x6626424896070281c0419900f80c0039541c8046810915607d17039400c01e0b040901141401c1082032060a01785854070300494501e40982e018045550200c0c1c4294001c260038180c5c10134181c205038031100a40c05a81c421791100b8000707030b004400d2000140703d4417200c0b07030000c0c0034100301d03a14124030300050349980c011a8161014054500e101103a0855854108895040001d108001800e0b0025019210401400740300e88407058810106420302101c070111a1560781084400c0d0911138070345000300200c00f4075281121580a03919500e00300b40c0703d030300960b4040d0741003a0218031443c118020451405012904441c02c118007003081c05041d0316107100c0f41058074454908042410f0b280981511040840c00b80a148844002181001c2c07540c00000140541e208440070300040c3d070f0300c0b51003091400100f0141d5031003c007001e1600051400d00c200800d40d880d0541c0a00c4202d180000000f20143c108580c0d54071460f4423070b800c000030002030b40c040901070320301c030b04000c1504404002040c0c07082c0345501840f800b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 425462212 1250 425460962 425460991
    0x801021608091207030515091f021803030333091512030a030203090610062705060d0504060f0525170c0a02010606090614030a02041208040614030f 65
    0x143d032281c446001024841d0000c40d40d072036a984c5081c41d5a440e100740c1d020b104160f203c4c00b0452002c0007048030001c03003a41c4421030304459a4000f5480c002c0d07200b030114201c0a50908140440d9480030300180d807142c0c60101400c4401982e06200d11124000345404100640b038110340810190ba60f2006940c002404403030010b0803000400c0031900e090f03098600b900d118840814403008555042e0002d501c1076000000b40c86440d101c0c088018580e482e94024400030031010105600c0020070340300b0889000b510303d0311806455a49002103042c5900c00c6002050030fa0301c92042106004440c014510800b40f0302c10100114501000e5010307900980c0c0d0004610200341c2810945003030b1081d080304061003001d01d55000d0301c0c10718101c0c0040c1503100b0208a0702550803d5000500c0c913002c2c04481040b5641a03da14881c58100d8541c05695800100b21810b001d41c2481301150310709411142101d11417040041e03690b42c4d418050040d280414841c501030b920a410400c0145a0801043c241d40200c3d207004520b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 425463462 1250 425462212 425462227
    0xa0914030703061b02100501050a0621060f03050609071223030316030b090126070f0303050915280c0605090705011107080d0e061603030203040b010801021608 70
    0x904001807036102910b182e0816101c80d201c04111541300c40071800039021240004212010802079800174841c943d8441c80600c420407003a405408140080030010094407240c0580d8241c440464820790041a000c1a22080a000b00041000f0603031f0010190f00041c5020746c5030941d500160315010800900b80403000000c04003013520b030a491441c11000d0005c2e00d8407482c0009850880803417a075107110002e8201614440f40d030030140c41003416504007601e000801741c6000d5108070b42c841c200001e400240316503040012187d09640002c070185100b81d841035034403c1408100214180166040d81020700104030001e908035804c0071002c04600042c10400074426215400c1e00c1000043c000540204d040dd010403240f000c0216070300040e12002d0300c4094404991800181e69100c01f8002c54000703502c00c0b800c080c0c0d441e01a20b4070501e03543d4020105031400740025184140141c40b007408401013600401031200300035640c103a440c0901801d074001c50401100b01c0d4002d4001882d004098800c00340041c061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 425464712 1250 425463462 425463469
    0x905030c0d0f0c14100e01080f22050601031a280b130603120e0109050405041e05010c030f0b030309040b120a1103063301020307141f020a0914 63
    0x244007036040580400c09076034501c9110851907031200381c3ca1180b1503920052905c540206456a261710042e50360800f41c1da0b80101c1c20500400c064414241079050b8030744030751060103000c0c0c000011807007007001c0c010651640c5072000500b40301c103a4800700802d20208000300200c459010612198035a6441074140c9221000c0310001c04d660070301c1c180c00000d02036100c2d41c444010741094045901c100410640500364003000c803803000c41c00c2c1800d0300241d500903080003940b030690810b68005020316000102c00c00d6010740003d007160090022601030b5140c8a100720107a4052141d44400c00c504003090119805900000e9164405d001106108603650249100380b502d90070802114272011104031303940b5403041e09046001c0180003d80500c81c1c801c20000901e120b2504551100c0d0f0034202e00700d0400903d00d14404042140c608141034118807040c0b100b2800314514203440c02946084c0c501a20b1041c0078114000b112001c080340e025002c0340100000300050b80e00c000074000300c034071020904d8007190540001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 425465962 1250 425464712 425464733
    0xc0213050a021201090920010905090a0608030c0f1912030203070201060504020d0608010605181810090b0708070c05190302011401032907080c090f030a0311010c0905030c0d 76
    0x701d074000344100300200781720295511108070b05016482501200d2090209004000706a1712880d002803110282042541448007000d13400c00e00b00302010580540768812103185802403d281100c44d802002c3c0581d568105200740501283d8060500b180d00690351112038044900990910170507a0000004600038403c0d80f0080c05030500070b00c00e41d9248170518078031001d00710303d0044070810352900600203081d00c0c0c0382442c0032010110402d415050756840c40c805905690000c004920b50140a4810030300215901c611101584650756900590400f540004c0001c840105403100748080740300c02002051340040c502c4c80c4038059040d043d0142c111850201d02500c1c1401000700d005041d400040100310070820220340c1c1c841155142c9281c2a03940c210710741c840405951080101c3c2226011030794404490004080c03010020303254000750340c0320a002c00d15040310404160001069581c03081c07101030080c0030b20380d0a110b80380f400c41891410000001c0d01e84c48000036052088901000c0e120070010a0140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 425467212 1250 425465962 425465977
    0x324080a030e0315040507090b0405040c0317070b0f150d0c170f0709020903010c09120f030314100311030a4101060816060509090c2b0b010c0213050a02 67
    0xc8920650a05190580d5248100e004100c223040c04c10381d9150740c0c0c0c1818490184076640045c1101d0601c3d29603118003211381c0340d41e0800102150304010071004a41d40e00c45460144981090314801031a02d50728244240501400c0b0034403c0e80c0810300d11020a080001035001d0700c0c0342d85900030800040341440340c42c00c82d102c0aa94058024024001011030503540070b081c60640a40003445542551401114044202d0144480b0f6580080f40d44c6c0205140a007906e060502c2400c1c001110f102c8512002d804c250210340d01980d40c00358100510801c0b40d10701c0070240e0088290020900c2c0b0701103941e11501c200d41080d000010f440d1611403207001011180d2044070030400c4c0e440803000080d5412541d4083c0c41c9a01401416118000d80d034207181024144040c202c4030666034050800404904001144d030020304240300d001c00c10701525200c1c0e2411007054070140d0070300340c02204d41c50841000030141da0003006101d06201548200f00d001da198107103403400481001e0b90006442d5035581100c00240921780 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 425468462 1250 425467212 425467243
    0x4120509150915131e09090f05010b041109011b0b0f040b070c08040506090f12010f0e03130e0405211b0111090f04020d0c0324080a030e03 61
    0x8031095104603040004040c1c90b20300791800000b00200ea099070107030b48030700071440b0100300021000304100341d240802580c181140e00312910720079030380b40b48001c00d840c2a001c003a180744940080c0c80e030810000b4800c081110405440c140500081c0032000c41883c0500c08030303603050000306242c0541445040c454404e0035540946044078900f060388803040740c0441100c00b2640c210b1240e004c41c00860098010818150348040c4444c40c2506010510070160000140b05400004003005030309541c2d2036200d18500070303503003000009141c0c0b00d125240d02a5100018280b585400400c081413595101c5e140717903410344440b40581c0e019500d86113445445c2400e0345242c07071407142407003000030002d43c009001405010444c80d124031620000c01602ca007241c102c2e00e00d04140c282e0801180c0c0c0e00d03007021030034841c82c104018001801c041d160040401541c860000c01c9000070b5030740084100064000420030b450001c10118407084500f04964295500a5114090140440f4441c0d4800d1958100541c80b420074250 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 425469712 1250 425468462 425468479
    0x150f09160b220f080d141b1f020315010908030a050912010213030b0a0506030c1c08030f0603070b0403030206040f02040b10110f010c140d0b1c0b010f03080304120509 73
    0x1000511004110750103280001d003e00d81c02e01c90391622600740074141e245486c01e0103280559103c9144075011410100303104c1405000a41502c0d0150141048403c42c4450b501507540c0c0392920315506440c0c0503601d1a410b0140c0c68006000d8a0380c00415203a00d00e10302d062407a51980c03140001907004400c40c108030305035030001a10310482088911500d085a200d440c00800b030b5110069400244c0d90b0444015070541c3c0943c40c014040c0c42e091110030148020044142c000c0e1045031105012917000f00c1303860658904460a01005007404c01c084002030031070340809405c050465800a4a5483c0600301810042290252101b595101e902185541790300074042043c0c1054500c010f841064500c286150038001c603d00541d070039a0600a2043e00c1905540c2c120442805c22400b84c125046800e070808069604d094248060302c440b514500a01c810b201b4680d030783d000c586451490000160003405070700260080c01c20005810100743d90b00700d98072068140014a81c1c0d0411a2140075030b081d8603a00c6400d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 425470962 1250 425469712 425469719
    0x1201290a0203040e0c0306100804290f13080a0804030e0a090902120106061b05010b0d052104060801060e01020a050102042907080a1b05150f09160b22 66
    0xd02c02c0f02c2e0054100c0510343da40f111000514001210f8a9030010304803421034412a10034100c03c0cae0302c1440341d0f04041e040a03040301c2d005480113080c04200480507945052104a1014026003503101c0102070800c50211015a039081c16802110301031002e100301c0d4070115040502600c010034901c240503103c200700315030f070b6007a5401030040007100b44c1c0110842d05080303400c1c410601558059403001d031140c000d500d5038448040c180e641c5c50728048d01c00395a950350301301184d540c0c1098241114010b000030310302045102848170f0040ca0706450804420380c100005c00c16260003c2041c0e04540e11800c005004410b0b580043c0c1c201595464000c195510000380425000d18a048030320b507005103000d0644805a0261500303049126948000e0000081441030250062040c10444c083e508100c4015aa1442c0e590380d40385002d54801080141400070010003115440720140c045c2c0c00982100145031901c0c0705030100c01d00715458051070354182c60004090019131218a8280d1300d00003e042c50840c03460b034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 425472212 1250 425470962 425470967
    0x9030705011d1e0f150405060a05071a07110705030c090717090313050301140c03061815040c020c090a200d0c110307150f06081906050c1201290a 64
    0x10f034880d4040c420302a50155801c2414859400c0e00401c2c08500464500750410b01008101c0c2c0060176200b04004082100000088004180708400390304100c14031441c1c20302e118080c0160b200602e4100180e17005103020802d55074005034a5030800015114150941c55107a801c40751403120900300c048041d041e07414080d070403500000502450b082031807994a41500c9408041c2a1104441004c02c502001d0020400c120b205200035500f2420040c5007245040403104901c074000c200703e510a02000e040000741900381810b001d650055525440a41012455240000c6e083c80b80070717006945203035a03401c00811003020901a055004800b40d8603546901c2c40342c246c10f001e000804000d10000e43e40d04031545100c0b84c0001500c206d96880302d0010007060b1100503103001400714203200e6002c0c0761111400140c12000340655501140c0c402c0450300c464456042500540c0d00c043c08120400404202451082400980c014155112243d0789420100e080d02c1010000340c804015602d91000090990328168 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 425473462 1250 425472212 425472259
    0x20103110a020d0905010201021305040b01020a02360921210103020a0902090108151302072901080c27070518010c0f03080916090605010809010209030705011d 70
    0x41413903803000e441d503071118012070a0f400b400b61272601d01800c56405004914060b040b1552480d01031044401000032900085c0003c041201180382c0b074a024010b0210030348001c11488034050710103441004a0908103042543c0721003008140d500a03070303828401550b43d0781e140101e503038020081c1c04500310420b603985a082924030070300c01240724a510400000302103100307000791203001d03105071282a01e60f0340e03100d28003d032405101000f40c0c1c030801074800c0e04e12500c21440640f00450068100c014041340b4000c44a04601c2c0203000e05021f1024000100300c12100010402884401902d180d1800c03c1c0120041d0700b02002010a8044980203904001580b60710401a01d0303400b20120079050207282000041d140002c02000c060034409440c03668000cc81d00800480c0d0300158a01704407070f135180710001400107165843d0410a440d503220401048150f901c028a150006031034002140351050950020743c0d5a1030a11406041c0400604005c1d02114035071020402600b0107801b50440d80c54050100c030340386 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 425474712 1250 425473462 425473483
    0x60309030a02010f060e010e09010f0f0209040f0b06031306181a13030507020907110604150606050f040e1905070306030b090d080a0e0f070e010801060b070f030309020103110a02 78
    0x198a0302c0c94003a8012400d00809003101c440b01b104901c203034204200c1340c152103c0100041c146640380d1890301074040162007041c00e06009030200507140c0083d00d081109940c06440140c950b5030034401aa4282d540d1070084076082401d28a00301e2241005103054805818500411749050440c2070128040c00101e14004040b405158541c13200c2c0e40d0f030001011480655140c1c042d001a00030303c070310801420982029500a4a142004c00d6003032403140315140b800000325022603280e040440351b00c00e00300c100c3c01010701400580c180700c0c1c1480350741d9400150078000c2d88a8940c1c0013044070042442903040300c1e80300100340d4400d00c050105140401015001c0c0c111031002700d80c81d01301500060407050011901c142c101115594841107902d0709009a0090b00380c04414000301d0282c2c40301f15840130030800000b00200360140c0354203803540c50700225a0841d59940d21442c451a41005084005290b001d80408a0b0360f2500300020689150b0004030010042e100e48450310313210000e18a400b6580001d407040b80c0c5c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 425475962 1250 425474712 425474717
    0x501050406080613030e040905061302190b1608041508040c0906030854090112060504050a0204020f1801030b0307030204180506070503070801050d0f03080a0b060309030a 75
    0x4440c0d40d808560383d200703812228491840b1060715000002840780d41000a5020014404280540c1a0310748500b010300c103650315034035184031648034411410182c0c0b00780300c0e03c511030b0341103800545094864003851040c84c3e100d600e0000c60454003410440010141e4010b0310b038408500803d076080701d0019208100aa0302500c00184900002500035164003440782500c2d8403c03402820844580d090703e611061090f08101c80213151900714901200c005120740c0d810924500c0700c04127000e600d000c240c542114100c42805000c180c0c0c0103002501c00140c01c1c5503100d90101c0d0014142d9075508000b07041612a02c8029485030000031080c03250812100a4240d001249004d009110718170001502110501800e494140d04440340c00c0025180544c80b8889099006001c1c681c0313003a1a95a070303420a48200c60745004150b0100c140410264415034036400740405a59042d150b060300c2d1515902004a00d200504001c03030480040e6805070290403e00b07184102400c99034403828070100304c94407034020b0402c1c1ca00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 425477212 1250 425475962 425475971
    0x120102190201110f04090b03011d0c0103050f0411090903040510050901171b0708070215030f0702070501120209130606020705010e09010e06060901110a030806090a0c08071d030f0105010504 83
    0x16150803c00c50300000d01c036a0300c9926161030013030840080c0c0403001182d82d05540e6280100e4590464030b4840b081d83e0040d1003d088440301c0600094221203002c0c2c030000810040204110014001c0450403d4641d000c4403c03201503034031680304504d98407454000e560045940030303d941c8540c2d0004060034858000746c80c1d0040d070300025a244020790604994614100c1d81124150307000d40000c00040060f075006201441c600112078002c00d245003074490040c1110180003003000781003070200c500c40c0e8001c607140c03015003d030314034000c002000d0042c1c841080d07840039400585c0d490595107102c0800c085010680f41031140a646010103501c424041c441c00d80460780e900e039000d11519248581034140c0b00040050b0140b0b40b40c02061044a030403210800341400081162840c407203404211503140c0a119a481900515145003403080740500900f020049900303041c606007002d40c00051080d031000031844d0405001740c80c14168156085a11413054150145000d001c1081d03030190442d6060352800d50f030500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 425478462 1250 425477212 425477231
    0x207090608010b0f010f020a081204020307060503010b03043c0b06042906090a08010906110a02030915040b0a170c040807060804020604211a150906120102190201 71
    0x5083c0d8503050320301030b031240c12458103e440758051380d00c2e03040001c51441140d0304069955150b50740350307000000100305100340341d0800045140400c407100144c0385501c0d016080d94500030513402c8500016000030a8500c506074406100d400986802082c00700380300515a60714400703121546030100700c0b02c041c3e92200d103800000e41c4900341400b480170b2a08110940c6c1c116192a014a44260702500060580c04030042185945c103583d21000300020f8100c003800002c0800030351601404881c80e585126016070030a004d0800c040d030b004400d03240f40ca4001e03200086151000c01e018a07081c82180c00100007d0310204401c4042c03940711350454201040207140c98141d88450b86002100d0046201d014129440858140310292080c004e498000348090300e000d017006c2e2a03c0c0191001c0c1201c46488030104144646030b014404034880c0120040c409800d41146810010030700300b281c0782c1200034140100c18980100b0309940b503040c0312200c00c541e088021511045c2c003c4180402241020400006600345031624 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 425479712 1250 425478462 425478479
    0x2152110051804080c0a050313060212091e090a0e15091213050d030f17010b03220204091208011505030f09011e0605130501050906280602070906 64
    0x6441c801008400010451070018051841c0180111070b0701d28144070040c0418810041010414403a01c060364031101c1d610200301105416500150031540f154550480014403482207840c0d854080d2344406001c000c6000b0303080c4a000303207130f8010340043c401c60800621102980c4500480c00d07003041510003c1d0240c5d031038010480b0045e160011b464210020026400768180018040c2c0c2840000e21010f80c0e69900004800c1d10250350203034042407241402e2103800360f0200007090220700c4481c1013403955050020b841103d001c0204080d00c1d214180c0200038940e50340d200c6051040d68020720520034050189002d00007a5086c100420214520b40008200095140710360814102031380e46044c25650790005100b12904054039012941d503942040d514190200d08140e5041041d99402040d8180707008140800507081409d803500c030354039107401404160307a40150540c00280407500542e4014074280320403010b8400f001e50859041301004001381598000c110002100d071000410008140e440104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 425480962 1250 425479712 425479741
    0x17070605071a1b04030602040e0a0507120506010504090603080d0c05160f0212010903020d0e06120a02091f0801090b060702030d1404090c05190f1b021521 68
    0x620650ba190040b4407422109490540c0c811140d218600b40101e1828285520741d003e500199007281d0000741c03e11450140080135508600c40c024100014170b898107000b4400345811a015a800e510ba8002c10702581c89a4241d07005800b41400030400070781d0300d240004a0f0340c04024203100c01030030a240780d6140740c028010784001110000c001c01881c0099910070345410007400c02280d0040c4281d0001d203150000344149100540700780c0040c1450176800d00702030320411101c001d141c410301040280c802e03621107048445030441e600e5100581c8407842e840000da09207010040344ca401050386255240c0c901e621100d400d04070703000c0e10070410030340305548240559440380101c00394141d1310898162140d43d1191004c42982c8000441c0c0380d09254984076040c040c2c54507440c000c0f00054001c140d40c02c01800403179207544c6944180c108000880109003028007400c00000c4c004060b100511030903403c2d902c5648080a1644507029602d43d1010a40340d44421004846440340020510380d0008040d095550074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 425482212 1250 425480962 425480977
    0x2d130312181206062105070e010807030b0c07140706080f0c030c0a032408060907081e0f19030e040b06221a04051503190e1617070605 59
    0x2401c0482908045521450031446201141c105544000015034140c1c214030041d907402200340c1094941615007080c034a0103902c0c0e0010f0202c400180010050840e00081020407a0381c40a1302d0702c000c4d607403800050450300508030b0140c980c01b010060502c00060105040003030314695154000e0603110301103031154105086407403182e40401000429084041e000281441c40d02c90302d8080381c0d40c0184088802484050544010a01203c41052110240a2014503407244a2800500d20305150500c515503a040122100c09401030150b481941e5403400c2c4100003018100c0021a00300701c1c0600103200070a40b02100c01d4000900100030091640b034240a00c041c2d0712001050035090a9500c1060700790307450072443c01108504103900000340304036220406860201d1600013140c03181e2900b0b040c8218040b6000c44a94500c40400070481c00711050600142c99a990032000509840580c101c1c0745800e900c841800c080c48240c080009603100d166840c1444070500c0015108001d640b4601a03925004140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 425483462 1250 425482212 425482247
    0x2070b0f040c05061c0f1b0302130311030a060228020321060d020411250f0f032715030e030301210b090309030705090702032d130312 59
    0x410400c10761505102a1201c0343c00a2606624902450a03500440d080e1034052010980c403161505403c7e2180c5443c11004980e6060561400d2010b010007580300c0703218000140300245451070303c446030b02c04225101015a005508558502c901c01c117a0880140e1101070194400240502c10002c0e48048140c507203c85520b05581701000710500a91425000185007079040130340c094903540035956502402028014500c01541d440c40300f00a82d001c406800b40181d00340c0020045120005a030f00c03201406959002420213890030340d54501110a1188980040507440704905d0303c080c4420b205031600f048500800d00d44030f07400d07000e40065013566040407810345d09070000c0c00100800080d41c03a0803003100c84900080032258501d0780e211117420000362201300c03541d880498800e0040c21b04001000241ca400c0310008000d2030010b500950783d09c01e50240881544031401400404030280e82da880300c25140c4941c4c1b90320349030040008090611280301c15680c085190480e06a01c0c1d0140303480c514a00c4617072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 425484712 1250 425483462 425483483
    0x31e0306041802100e030c0618040b0604120b04150906050601080129070c050a030305030406062306090118080a0303110c06130c0914180c09073002070b0f04 69
    0xa14141c170340303c440360041c90705402044821015595000018034603070342c44611014541070120301388000c03140b2a00c103142c001c04040005104205552650404683d44802c803403002c1da59602c1c0080b1a50122446020124102102802045441e400c030310710a4a00f030b603c0038901d82e07980c140310b980c1c00c171a101080313040800d00748146900403484004090b0395000d80c0003001c185030b83c1c801080c200700580c1d0040d40065404001e1200300010350260500074646002e900110f08403505d0003031004083c987c0664440d400000740d009007640200034610583c40e10700e9072814000d6840d180f09403541e1030480c080b00040e1030310248200803000b4030155203010b49000c0060055070744088400071041c134080c900351284807140d040091840c2c541e0191285800e17460400ae0264180382d03411501658008100340c450b40c00400602d000364460f00c501c00d5100c4074a00d400c044004039604810001c4a0030402420001c1c00c902d403100c8104683d07001050010720540d8060a03580e00c2c0c4020188181c41550003c0011158 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 425485962 1250 425484712 425484739
    0x80306030c01020d0f140f03270d0504051c050f010617031809040203030403050f160501080f0402012001020d0e1501080a03030504061d150105030309010903060c02031e0306041802 79
    0x62030702010500c00f1051b4803440c000c0380e00440c02c43c6800480d16007040c845c0c00c6001c100d900b40d158006c2408040c0b094010b1100004489010307020340900d010341c60040c0c1101d10041180d80d51003001c1550300b0740100c203448500d08040802e40c042d00c650b008100d01c1030302800c08090140c900004403a00c00e0140c4d5045008115980b040000da0032010304241d134144000e100c04804038805101b5038070b40070002230081800e0f80030174442c04a080d03480d901c0315040c0000501000310700c0154800b85548a40e0904e40804400500f02c0204480303c03c60780c62007065031011a080b40340384500da1200b41061520f20071605100b80c42c035895000341d44240a01d5903550041c0c0d1540c000640207400c0250002c2c400c2002141010b001c0070510310b005001400068207034403030307014480302864203048940034110a0f0041c51a00000b000080e112102c144001010b0319518420018050b1007481512201c510400ca4041c00b80f10241c2590703610380064030f61038800c0d803070000100c0100070540004c00750704c0c1c0c0c00b074040b02c44200b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 425487212 1250 425485962 425485967
    0x16030206030105131103180d08070806090402011101020d0603150c02120a03021209160b030c041e0b040b0c07060c0f110a0b040902180d03090b0c011404080306030c01020d0f 76
    0x4c000710301a034565160500c0039008400100558880d0780b04586000c0305a201d10f948038505042d20b600e1109110340002480600e50b0701c07480d6150b0008007500c60010366200c5200480b40d18849960021b03140d440480d0400850b29113070422000c8034040d108003924200400142411215141c4205001da4805c0411307031006c0b08840c02074044480d15042c014105040e401c0c2e2042c075007000f1103500078190049440c8003a00c030480002d0402900f86c075a01981036292a80c80d00c4403e20641c05884c08010120807a072088201d8103c02001078400c1e40c02040d10389036109456034041c1c10030b480e19a03050003007090100310140701c0c40300e1f921000d03004021702c034400c40742e42c17206d05040516032083c5402c14070440c00440c0c0c5166440090000b81403c160040c0d65502198100103070b54a46d13244144140a4054654046035000b01414103407080d800c425551800014106401003030201c69078218203015100b00424004084065881608182e064465400421004a071a031650000c45000300f4000504140c0561 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 425488462 1250 425487212 425487229
    0x15120f0304061803081614010b0a0b09040609020409062402071208090306042406140118270c050a080109150512103e0d02120103030216030206030105 66
    0x283c0050786014800c0d141c1e20340d42030681c002d03a20003050503141200a810408500180000d12030024001c021042c43c1e81d00145104160744107002031124081380707106641c0c1e82c55101c00001e00c9030341421507885a581758200090b02a42c407850300f10515070300c102c605e0045140160f903030040c4598003501d0000d04120b20b04a0300d840061041e2006001481803080f0358800700074203405a4042d94000118550708000110100d01260200015a0400c1d400b0040201c0e01c986060001c0000d00380814427907021801d407030303000d0055070003000c2c41c03031040d0744003400e064007080d41c0c0d50405d05144081c48500c0c03081009031020b01c0703a00d04440c001030210004104100d115484401180d90300b486001c00e441c2d940d00014004c80302c2c0440000e041c0c002e40008802080e66114124410001030b554041c0c500a1020380c820005d0131030b85403d80301442181c2e80f61407000c414211401d80c030b0404421500c0b10392925514510400074002103015220719880c481200c190112900c040b60360080086207180e003000309000f401d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 425489712 1250 425488462 425488487
    0x3120a0f050403050d090311061e0a02010917090a0e0f070c020307051302040801050f0910090501060b16060f06181802150d0f020a1205040c03020915120f030406 71
    0x401d041c04048002007043c00305c2e01c0540d82075a03401c0007a90079818148881d20b606114180305410401c441c100c0c1c1c440300014016014840d200603511422444000e030701612424400070f04c11003802d40590101020039010309a2110305503071941c42c1544405888680440c00c2e140ca500031411600041c2e4640c3c0300d02076040000f0b10141c00c0d00d1489981d0300100c0e0011814100b80f458041d0003280c140030300d0100344039090780035031405210000c0341441881c0d607455040030006c1407689505c418031613007440130075004034000b0245100c1c656600d003440c084a80440140c64021180c6a0400c001c86641d001c041c0102010740e441c070011041c000741d9180400700100710122001a81c44640c090b8803026039102c25a040720071030501013155403041c4002c00142210501c070a140c00f0a031060160307a0450b0740c0948505030408000030001801e403158140801c0c803c215a00080d80203007500d00300a0085480f941400c0b04017004d607540d40c942400c1d0601c1b5901c8030755116034055603a2040c4010000a4450f85a01041c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 425490962 1250 425489712 425489717
    0x60a1d031c09050114090105031b0f03070309110d050c01230309030408060f0f04021302070b0a020a11120304110a030f110a090e070504020a1803050604030e03120a0f 73
    0x108201c061003440320511140280c03010038403014040246582104150500c135003074544040c600700500c00084e003140805409107281200e002002220704c0890b00460318003800000002d5124039040000501a050442080742c00c404800b10003402400c005d91990b07615580b110242070048060f20045500d1031748400b10204508003170185001c004c010900850150f4000c001465455080c21134407882c1c0341d07001d0100c07204d180300541000110511119110741055040760103184a00d04020a4006070080260207007545400030144a401c4500d90b004100001007a12280595260000541d89544401a12440d0703002c0401c000743c0040e224800b58144c40500078030031002d1549036214003411081180042340d401000601c42c040c42d00c1c040c80c0c00c2009041d44170f41801485680d01b2415241d10251180d01c0c05182c01081986031036010766010f07402d1982801203a6055a500c1c03d100b81d0310035040c0c6064022400524803005170317040c08681010700700e010718111440e240004908a0f00070b8251701c07241d000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 425492212 1250 425490962 425490973
    0x504141b0d0b09010f030b07080c0301030303020702040e010510090f0603110405220507030615031a060310091104051b120c1606140606040602120708090d031d060a1d03 74
    0x1180d940e00d2010b0f0f0301030058644d015000a0440c5448400c15202500c0c50b024007103460f04109902c0e0001040300d06403507040c90096203807180380c404039024040d601d070540c216508010400c0390a04200c5142e20407200005d2040c00b40150b0180d211086071a14080540422a9001d00303004a0820343c21403a0041110130301201030701881490703081c07046040401214079812120040061081500400ca00d507042c0941c1510007515654503205003203003401c0e0651141400c100007070b905030f60034000c1d0710101e40f03013820034441c44240d480c08402c106440441140300314500004178440c40802d940065024080744c5e605840c0c80654901e242c0d401000520640042004010ba103d00011600f0006076140c8251070100ea01541c000084140c1103005202070300800d004c1c4020000d09900042d0b408415040305403455039141c40382880c00031445100071017600042105228407c141d40302021000070010841a14840d8804000b004028400c420700c10000030a501c5441e180da071030020100c0d240340c3e0700504460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 425493462 1250 425492212 425492231
    0x60609040b0d060e100b180f09010e06070203090a0b211803070c03141617010b040e0303010f0b070f0201140c16060e060415050306030a0503030a060504141b0d 70
    0x5003600d00207400011309400400720130900381d20b2801075181100045480c50942e60101c42803074000c0307000500050080000001140150100390300c1041c0544040e07060b03030f0f40c5281000c0080e589070300600885000e00d0142d1f50010381d4144102c161007008a140c4020090800f20581c0d50b0114600907128410078507070310103000300b4603000300024032a491096007011502c03841d50500791400c203044d2444da032840d00011108100045404900b5081e1500705e040345101030503140d58640105a060800c1c3d400c43d28007003007910360060002c069030413a84070201590220b82c407407825004078054014010b2214605241010040d0300032610355000d90300c003020080c102442c10698910f0700d05210b00324224002298810300c2615442043c100500505466851809240c010f04000d034600c9181400704016000c030200e00b0980c0d050261a070030540160890f5100d040404082000702542e1203603604c150701e04862009048040400380c1d2040440b48400d203568500d10940b6103ca9018280c0d0340e1203107a6603a20300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 425494712 1250 425493462 425493473
    0x50705190e0a02130819170702090a0e01062d080a110103020f2106090915040b060a0510050309010c0f02031e090a03031709073006020406120c08060609040b0d 70
    0x6c0d00c0e0241c49105220b041d4506000c5180343e07224042d540c03107203003c000c400050388810401c503401040c1c0782c0000844c5404030704030310300404850b00040e8240041c40445850b0009042c1a520b41880070b030f000c03c00d8541e803211389507940e088100c4020625040ca040d8940607600a0b4058005a005007040d02e1230000440b00c001c0d100c5c4240c00240c0d04515900d000e0280b1410165060799204030000001d00005251002d498070380c0720001c00003230058041d8800500c694885c0c2060320000c04000d410b00c05594100100a40140c0040341c00e0303909903190640d902c850b0b600ca50404204030807290051480c15200c0f101c030515840703441000b1310310f940080001528540310307030031460000d501a590304004001e0380e4113900303c1590003030702c40300d03596000034024040080113060b400b94000791030b41c14444105600d4003081061036050f9000d011a48085800143c10f82c200c10740d04904900240100400000001d0075210041d09844031500010180505202070806038041c6101400007080180c07184941e50b00c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 425495962 1250 425494712 425494723
    0xf051e04080a09090c050a0f030b0a030605060607050a15053d03050d0f0909051506030403110a06091a010f05040b06090303040b04061701120f1e050705190e0a021308 73
    0x240b500190001403001f140950010203010310700c1682c0b80a1028003032440c0002c1442d1540c1c0809004c466482002c42c0003a91000100c41500d507101c4140d9880c507a8908100c4041d8180c0750008016074185400101402d103d034840f038142e45d14411400c0c0310850041c2c1c1201ca0303c2c516401000000e40324440100104008010407042c080c201c2d50781e22609c0700100c1c00205140c00d02d030301508081e410a0305000003401e61400610204106444c0c00b51a50b68a080840302c40d40114404e81c21801801900c0302404440d820074282c040c0550000250942d2204100c071300e1040900c180344030085044024001450550808503001400421030360426500c1800a0309540c070943c0110f61000000600f0807090b42c2004044a0320341700c50b03c403964158505123010220310400f01d80144061340c00c00440301000403010445e6005c00c1c001d03040543c20512407824079564000f6020300742c13098000452105503000b9900c00c06040d01d04c0e445040800d5200d800d9140040d401520b203007038014098070404115141c08010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 425497212 1250 425495962 425495981
    0x30a080604091a070e1219030c060212010312020c030c040e16170f030c060402010e06070b0f01031403040f030816050f010903090e0c16020a09020d0f051e04080a0909 73
    0x200f06809060221010349046464204a4010401940e801c1e40d407010200c1c20045000720700280300180401d0389000c88003240460300080443d0702c042050003040350410309990589200340030142c100494400c00b030760382d0070640b1000d0740c0c27641c00220702042d04c2c20640c208414030103004084401090a01c1e4026406c0000e03904258108403800b2506002e40d0b10810440f0008119000503510b0030244840b10354544000403c0613040c070803010000885504c9602c1103440d032682000c4100d6450511100e82507407113100784000e440321900380c007811070144070220440302100c03641d0380040c1500d850365441c00c5854001102a1400a508545460204006210a0006c0140c0000004801240b0700d000b5022040780d40080c00d103084090304100444225a045400545002c022a0240d039035500c0010895181c503040400158004215100703101d05030740008800e080400403d00c0303507a03600300c0f0010f00800140710201400f40074001260104403d41d0040240c111203241c00040582c440101e07806440c441c03070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 425498462 1250 425497212 425497253
    0x30e060a11071208030c030c130e0f0606131811040611120415050c01090c0f380706060305060124091802090a0e0c03100902040503030a08060409 64
    0x210002550719050000c000070b4408074010307866100f5540c8401070303240001082907204020000c003080860b04500151642000007118090815443e0700a071603c10b0340503249510041f205802050503868028141c522170180c0d0208040c52603d80440000055003040310380c45402c0d5120752480d000c04140c1c001708003800003915240041f9240c0186a8680f141c90540016a00010b00080c0580c150701484148071140524007180c840881b041c00500405401c50000c00510071003000081140c56042c1480c1207840c0441060b080340142040d42ea00d0780e0000c0043c800045440c15008400b0010741c1c00360080900503800000d080d600d81d03544516180b000c1c1c0120b0303408580e01200f0003071041e5291645d040743c0480e10300001400e00d025510484801501020021260082030620441e11000500d2004058201515060b0b007021550001c1d075070302c240c824030388641c0c0300200451401705500071034007181d201500446c80d0020b00002220501406090b195100b912050494082091020085c04065014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 425499712 1250 425498462 425498477
    0x31d0303041514070e0f0409030f091d0109091703010905180309100806041e0207060c0804030c020405180312070f020a020901090203180f1b06070b13030e060a 70
    0x50402200c4280b000c00580d4007981014005044481940380307043d0001501d0070884600f20000380042c0d01c01002003400380d001407410380c0701d500b415403181c1c01404040f89c42d10384d00000b80e101d01c01d140080240310b18020701c001c3c11000400982c11198428a066800340c0c031407402e4a401c01c04481000d900c02e030b114606294440b024000c000c50701c641c3c1c0011130600030000f0751900b01024049402001c031001c84400340640c1d100082c5107a261500103411a80c004541950f0011000d140b8600a410401c016100e0720719240a241c405070003000030034011034047d2134a2207098001e0f4200b0001c1c01d4000c0c8020801569050040441c51040000c0c0c000d00c3e051460b1000341c1c0ca0701c148001c000820959000045501c002e9046001d138a55104c040d0545004000259480d51400c994090381001c219106c6110701c541205010722043c0810798409600c003071840c00140142d84010480d03903004500020f4200140071000c1280603040701c040a00302c81c802d0600105c00000b07040050840e40002000701d0106400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 425500962 1250 425499712 425499721
    0x905030a1710030f140f010c180605031009090c030b0c03071d01050a0c0f0506011805010806010e51060c0303040206070f0503030a0608100501031110031d0303 70
    0x8010740190b11000310704a40300b00c0c6140d51500110380700f807a5005040100080207201c0302c1c0030207020b052010008403009003d26401400f00600800c000181c1c00c0489410100120300789118504480c09844c50071100300800303040030403980050590500880300400d501d800000003d00384098540f160707115444190710b038542810060105100b284051001004080d03d1802e140e07000019500030200394076003208801100e182804035915602005482442480000030303075409144c02c410041380810b1010b1043e40d0f07880340131540e00c040070301030b000741c891001c00050322040440c540364071f10f00c05500b0070203101c51340d800c0b1600703005903102505070315034103075051f140a02c0042c030680c403030600c0056030418a001b00001c151500d9003c0030b07000034450500014294180b1855420419006400400f0b89030760b41400a1003e00814017481450138078002c02da2004505296032040504036504800245000303207000d0100314002001d000804141a5201e10104240015609014a424003440115a6401d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 425502212 1250 425500962 425500997
    0x204061d0604090b01150504120c05030d08090a080a0c0b0709060311090a05040e03190c0c14100f1205040c03140d0507020d020a0b0a0e3f010905030a 66
    0x50080545000b1030070280301800003480f6101c0c80e8111401e60404418074003850500716841d2090ba401210440080e0102006002005880340304466049007151a04c000e40d00098400e60f00841e82e60b61517030030003c411008290260014120700d0014034004407101c00c10ba4981040361b005030381d44070000e092050244a440c1d014410b40c9040c2500101c0c86091500c0000010300c0200107024a5010381d8541c00705c03c0c1c040740d08005695180312209003052207181004070007040000010029500c45407601e40c0041e450034016944600b040011340701d80000c4030b255205585003c2455001d40401c0b503518240208900544944c17402107108441004c0c00380d06c1c5003070040031100c8013200307001c4039006840645001c80d041021a01c81a0f030550b017044000800c1c2c0000b41d004d04440d03008800042d0005607c0c401c00e90b014038402c1d80180110ba10f58241500c54000b581c400781d090100300d440c41c1003805800121900101ca03622000346043c0040f80c211011f54800d03080d0740000e08032001080c2c8403c3e00d41013448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 425503462 1250 425502212 425502269
    0x5060a09110a1811160b150d150b03030903120c0708010506010207060c0201020321161b1b15050c0d020613121403090c01021c0c03110a020406 63
    0x8440c0d40c10018148071925848081e01c030300f2002115554540c03000000741d09003d58400e070040300030000e000b40c0c82e0305101e002003004861540307110011004e1387c00e082c5080590440c110350801040c100440c02e1101e400002c1050000c1d590b814801806540404e550401c3700559400520030303115240d8288084081c5010090b4005d4019070341418108000350342d0019042c0100d802900c4c1c040c1482c0440c2c0010f03820342c8110310445010005050444107100c3c00c80c04c1d281e01071000d154018011500e001001c580815003012000c612501d0420701501242c82d1020600c2c2c81c5034201898443c071507480040c2c10516514200b00400300700040384042140350244902c1c059601c05002038911031520040ba002d00000c613040050140b03220b078842c0b280181c85001102500007131842520750b030342059202d49c0d6682e13602c00501070040c400d01110220050103142040070f0340f106a1213030407030040035580a807040c0355101d514141038070405801e070001d40d85900814001b0301c8421114040f885001c5c42091080c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 425504712 1250 425503462 425503493
    0xc010506040902010f050d090507060f020f0f19050c0a08010e07170a1502090306070905040b04140112085511030c0106150818100b0d05060a09 63
    0x542c90310b4060070260360015140006a1018030701603699255450071740b4010003c0980c040d205102d40c40e0041411030f0031485030f44040106800312001030034414541c503515581003500c0744054004400d406001d82d54012604800b41c41a001c3e0384003500204003140080403a64403031341141e034450303102640d44134040c0854030140010b0481c900780041c44402060b1380d5040a1700c001c1210184080d00b0350007045507170642c2c3c0d4000009056440b40d040610006249242074080e03248a1840c003002000285024443c01c80c42c162500c0031510503a28001e0303403445401346000c050b1f070b003000104050220301010b4501480e050f0748185424130740003407245400c040d91113004110040c51901c51081118810401c00c0c01d0f0300c05a0301e1400040c070340c038031078031060030b60007544400c461a40c2000c0e800301e805400d081d9054080200350f915042165903a0007041380c078080b4000b040b00c06030840b240e40a070b100151b07045480c903030b000074140c00038031300150b0307111443e048040b1012140d80d661510440f080140010203500f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 425505962 1250 425504712 425504719
    0x6271b04080c1005070501090f02030f010b010c02040b03010e030409020309070b032e0f08030712080112080706060e0a0b0907050a0e040e070806070206010e01121502070201140f0c010506 82
    0x406040501c41d682d503842d200e06503407080c3e40b40041c61240c50301c42c801720740640798400020310818002e8501020650903150b4224031134002c01036100e1029005204000750708505030358050080c0c00c260240002400f180d10074542554035000d41c155401c5003040284001c01a5820040e0349207090b50b030321414120781e0b4102591402040062004699480e05c0c0c031100c103960442d410031051082d42c0c02d4003090085a00122a802c103a4800041c0110048040e18295020764050b41d000006030000302e0303407100240142d150368440c4c40b510030017040d4820080d0845520400d00020900d80300c6190101d4610101c0d108150103440d1100d0103010705004402980010a41c1405400d00031000320240042c42ca00c1103240c000c039a40c01c8100080c95007007014500030040c1c0c0c030964134181012030009454840902415202020040c0001508100d40c4640e0171342c1900a00d5610b1212103506822001c0d5108141c160304004000c0c070404096001c51000b40f0780401002442e59a0748852803845080d42c1e00100310f64032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 425507212 1250 425505962 425505967
    0x61f0e03150c0730031508060c0d0605041413150f02040501030c140f13030b09031306020609030a0f03021308070602010606080f04020f0105131d06060c1506271b 71
    0x84406440c840d00c0240304e144c00d000c903111040402240108020380e004002504c210b8081c82501c03103942c001007080004c0f001c810300c00c0c141c580081c0310558104106034918811b0328400541c141c0041805109640c3c442c5012880b01d0320341e41500d070192605440d102c94080e500090422103036030584501515484a424600360b5030051361043c420300d00a00191040c0003000103400b51120140381a5200a15401200d08080f4141020f07510780c0c07500080b03034a0403c4101d01001150240c00014100e200700d1020004515180e54a00c04498030880c02503a441419004e1048114030b1581000740405480060020003107030f403921070000c0c01d5a0751035200d00d05000203801844540750f1050416584540c069606901c03209180004842a00c980b062840400d800b4210200c2c0150810303081e402c002c0c4408040d040251141c1003009000e120340a225a500c0c0e0083c0540300d5110540c2c00319960041004106420071560380b80c1100c0140221207203d0f0782e06542c10308000f41c108850780d8207075000306949c40c00e50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 425508462 1250 425507212 425507273
    0x90e01060f1119081809010306050a051b0f0711120105071e05091e1816051809040c12060219110d0c060204031415061f0e03150c07 58
    0x8000401501000d8881c0c0f500082c034211179003800a40e00c4080da4040c1c1500e0700c0d981c7d6410500700500c41580d0130300000d800c0c503003c6000d542140c101210f107150301003615440d0800c0242ca960280c0c2c0462002c413078001400150b60580c1d0343c0d2150704501c9080c694004200317854502c00040c40005050701e003a03000180450100d0300c995201c01030714030400041e04c0040c1000c3c4c0743e05012180c030a55141050b8030000038483c015005815100c0940100c0e0f00d94282d07204008510003d51340ca005142c810007060840d8070801c0300341d00c0d0050045410500981c2c0c00310700d03e500e81c0c0500403401024202a1034454001501102202104014200c1180c0030702c2c111904803030200301030b40ca40503071074000e408001d0720103100703c28450b844c1d0444000f554000e00700b90391a4074200300b840e2030b2140080c44a940c3c03184080022140d06180b03140070418000b01c000c1000da81c4101c0016601080e401000d03a8062049000ca403401400d56034469000d5245035104640742c10141c9428242c01020a2440503007140588404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 425509712 1250 425508462 425508493
    0x21030b09090a020603041505071101110301051e0d060c031a060a080106120615030605010e01090b030106050c0a1e21090b0c0c041104090b030a020306010312090e01060f11 75
    0x2150550f046a015643c3d440e24107016101140e043d00c044001c0d0b03e4030083c01051500310b0000c001c0600e84400a01120090001d000c043e400309103c2d281c2c00c01508645074080c8017410103422800301e80200b1b0100f002c21961206400c8503011071080d404680c1e0f925032040441100e0b084903103517460894506180881b0350400074104001031180c18244450f00c50f015412000c180c2221000d060307100c18404209103030003401409000140b007101d000c140620b8802600e944611848400d482200c0511442c1da4a0850121480e17406000520302c54050f003440c2d5400181d6007480e580e00034582c1220a0000e010301d06024000103c9400f0000440300d06400013110240c2101001c2c00301c41c85500088d8603040000c00c2c0f01e0a080c0d909a00d590f20510704a16500750208100c003400035120b1440702009141030002c1803503a500440308020394036030f11000c01000080ca881e07800c4100c40d0480c0ca06a403000f565072010100c41e0200382c000701d000c13420203a55101e074507030b2191007400c13005403210003406201d0301054103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 425510962 1250 425509712 425509723
    0x30103110103090302190b01140402090a06050a030605130203010f1d1b07020603240d1e030302040e0a0603053703050c07090e0d020303090d030f060321030b0909 71
    0x3a60305168440700c100041c58001d102a0918041040401c0c5c3c0c3d16a5610703100c500403009000790b01c003101c1500d40c080d0083c20a0310230b0f00e0604c1005003c00741424207050041d20390341c22162900003003503103e4901042a8035043d01c0c07200028851036002da00c0354149003800c00c230241142c001c0014001c504038503410180c4450086070308295800802c2921380c00341c800030000d40c813454001a412081c0042801012001d1100e034854880415034561341c403401c80010440c0d90141c1204c050700d0b000e540000c031714000a801141008281c86820300524055a03403034241c010f0b800840d0420140d0340e07203010420074010140400c4c0040346220703880a0b46a0722240f40140c0c1d9022040094082000203a0340c00105405141100c0086075032400b15920b96944408420142014003007007240c60286442980600e8000020349010f03040300406082e02c1d100c80401100146840c0e811071580c29180c500000c0400c803041f6128080310320424808840026001d0702a00307541910103440e0041e21100200011428045030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 425512212 1250 425510962 425510993
    0x305120f0d200309030a020601051903030509060d0c020f01050114130207061416090b04030b070c1505070c0317010e010902160c0f031401060602062d010605130b030103 74
    0x40003403503560600345000c0d009021075a24100d81c1c2c00000b4819103510010240104000a900b180e2a80c1e80350024000d104a00c2240c03803842411140080c4006400b4a000d40b118181c007070b06043c184400008224242c5000040e0b001c0980c10503424041c03052401e0203020f01400c2603004032246045140f001c110300070718032804541603550116000e402c10815801051001e020500c42d00042d0921002c40655230968102c001c000ca15400c50010703031000c001095070201c1350001e065481640d03400105807640700300482d003104e91040305010482c08940d17502c141c0d80208050354070413510240a1030090110400c0105040550b1150001000040d103144111b07815181130320b0000d6194104040034030800f64011030014a111240100880c08841c40c0c0c034101d084034050740c0703480e94803c0c1c503403903540c202c07500350003840016004040000c04000010b5000c81c9581c091000c0e00700c400d556401034820b588000e0304141e0000b4000110b20282a121204003005005000d40b418a0b651550342c1e048800d4000741c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 425513462 1250 425512212 425512237
    0x171225020a0f060f05040b0a06060e060405010c0320030901030c170406240e0a1424011e033204020411070c030f0b0a0b090703090c050d0302070305120f 67
    0xc00802126804c21600028014402e0000d802c0c1890280d003d210202c4091050900d403200001c2c1c014880d100480280101500c418130306070800c0011111400d0080e0140d05100819104203204d501000c0700c0000784202c000a992982d0282d0001000c0d200e040c075a10040141801e580d840070b081c05500d0a4009500600c0040d01102c0d0158441d201c00c1139420803d101d00002200040340405142e40031722401d0012001c00091030003004940304490b054900311054205451001b02010182c1034101b2026014102580300c05858030042041c0e9888842070030000b501c4041ca441c074000355910044100c03181052841c2c4400900703140f041082c0c1c0050010348a651115903014074240c00c4000c8424990f0000742000ea0f80f40c40703040146800741a1071044403249150300020307601155074071500e08242c0004013504080c0d142c005080300907094102042d80e0207030201100081079a906090280703102e11030b4014066151840c20b04c1400c242d0403803500b40c1031810070007006840c1595002201c01e00401031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 425514712 1250 425513462 425513483
    0x906080c1902160b0705150108150a09021e010f110d030207061b050301030b0604090809010e0a05040c09030606080105060d081b07180c2a171225020a 66
    0x48002c03881d0950304003605007045803002c0045501c10030740006140d542e005104903510911001141000318209104200c0345400c425800e00e28400c0c62055960003181003000401d000c1c0d210340019081c0444801030304102d07002000c0c45101960003402640c4240f841f420483d0a5004280384952200790303c80c0394804140d40000c04c0360030010036030b110109081c18501050080e00c0301c0350000d000c3e5442030100b6100025004005082c0746464000e0003640782d4481041402c0c010207000651f0300c506d210f41c503242d1180b00c01c440418a92183d10030b00d40496110742c0e4503200945141031080464010707420005a603414081004200d890340c08071304030729903070284596a031244449603201c040b40e208403a003074440c05407400014902040880312000b005480301e08000d200d0f01d10070f095400c800084240c800c14400e880340c41d40324024140180546501403d1090405808004503020903030201d1310800009245500b404022041c40c036150b03c0d807000703c1ca00c80c0c487c01d00083c006590381c415401c00420b864840b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 425515962 1250 425514712 425514757
    0xb180709091a16110102190516050f07050f030106050913020112111e031501110a05010509011d0a0c030222020307020d020c01020a08121b0304050d0906080c 69
    0xc0c4000d070030b802400d20429210038140011140c60b00d100e9682e41e00b001405007442c401c01c9031818400c0303520603801c1d03801d0f20540356540802550107421119540850b55640140745010410902003148480300302c40142140905100401140801e0303450380380e001e40e1404900340415203403000000d420500329071000c0003d081e10f1004070382240614510441e00740c10401d410340c081c481e51000d842c1c0740800e9104850035031003c2030905018001150b5901c900041c101c41501c4c9540900c0c002c0c100c40642c60151608010662502800d4800503514003d0503950750303000c04481c00f00103c2e0080000b0001d00076120340380d85038072800000400c1b030001034800c10441200130100300311303508106144614580f0641d00c07403a10b420040d403a40405144400540200400c01020750720114200c840c02c0d5000034038070704001c1850085040c4070002807482180e90080d88982c41240280c9001d54800d0b48140300429003034510400060003244554429424007045030148400150f100003600c00c0068140c001c040941c12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 425517212 1250 425515962 425515973
    0x20309010b030a05070503070b070b070c08130608180a0c0b18041e0e030c07060309020f030703080c0c041407050304020d021306080705100c12020c13090b18070909 72
    0x907050740042d894494a40e034101000342c0440e0150442c1c8046007036030072003036403241140c0b6035125001004203040c0031203000403802409180d6000003140a00119410100001044c5e803041c5003d400c40300100d0302a02c00c1001c0440c1c41c41d004045107003001c0240c41c00301e002c0d98030040900e1070b50007002e1408801043c0e44d00503403a009035a8084101c0280300f070002d420030243c00e0030340d1105a04031103c0e00e070030680c54400c01d00c030001c1150003800702c20005120301c61800b4800c8008010110040b80d1000e022410781c1041c2d03400b040f5280c081d5000d00f98a0340c0d50800d01075042c2c1391a24100009004a04000c580c1c2d1a0060207210240e000b001350500681c3c982d1f5520000d0305d40019908e00035807080e1503104441000c0a298412029a014141150742c9103813520f00700315100156034101c1c4009507880ca0160009011344034049425841c42c01162064070294000036140661025840905a50b401e652414051403c4240780c0041040050903400741d00c0d00039045d02c6100c60b0195146050715040c3d000304110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 425518462 1250 425517212 425517221
    0x2040e06090a1b09150320301006140703050f0904052701060b09150d0e0a150b0a03020405090a0501020304050714010212030f1008030d0b01141c02030901 68
    0x60b6020384942000f40c031000940b02c05014051028120400300308400400d001c0c0c4510003040000c415403c40b0240c10762840030840c0e2140d940b00011081029400d1443e4140d0f4019a050b02201c03818100e2505e041421540440e2141d8010010011201c0c00c1c240548200011140740d55058500790341e540c000b00104041ca441912619904946030504100984040c1842c6001c41d01d88004800061039008400c18241d6501740245a0603001c1001928494940251040c08030407103182e55504006080041204454a012085210342c000428180800054090151240e2604801080324140110200d01d0082e901e01000717025903611800301341c2c0b0790410405032001035440002036660385007070714046171606401e01ca00c050780700800c1c002502e59070010800b10555603180302580c0c11a40e8040d856800240c014041c10207e07400d07501e010031400e10501c01271100b04e18940000c0361101c10803000406200910b01c0c80d25541009000d001c04400c50014402c5081242e03007805031301e1342c8507076140b5070040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 425519712 1250 425518462 425518481
    0x80c0d020d17070804081b0d03050604020f0f0d0902090405060a061a2d070c03020f0d03050a0815090103140d050a0207120203031209070603050109050c0403020d03021f1406030102040e06090a 84
    0x49200c80d880302807e001c00074054070300ca4020381c2e0a21180e04c419050100f170b40960640d2554103c0c061082d0310110f070442c2c01620b6240c0c1c080401007a84a00d0750045140c82c00301341c40c00c7d10560000303c10401c0400c050300a40c0d0040c81800c0096600b8820001e4040d401d0040c0049030303840301455002285800890728984c03001d1454404070981c0c65505d031525808407400f81c030049015801071400d0111a107040c1807003a044a80586605150488005080394045d00c000e00746580c00200d031100302001e444480c0001d019610500b4080e505c02c1070031521901d8103503c0303090642040800c0003a2201d40f540401d10108803004544114140b111500c0000e09600991441181540b05070b0100300c6492030020740721045a8040d00d00300b100380d0b26640c104c0c064500403220410b40c04020403003040107092a409100300745000f841600c0c998428075403805003640140060f403402d1038580420f00314401030f49003400e420201c00c40c000c40c600382c5402850b50105e500107104901c6135594600141d11b480040c0c00c2111070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 425520962 1250 425519712 425519737
    0x40f0606060207031103060906041e050a0b190902030706120e0303070f142701050c010c0306050a050d0c090b03031e1c0207020f090a09080c0d020d1707080408 70
    0x11a901ca580081d030740d8001e84800e0390345001c507681210843c10081002800b60040402402e15039035192140c200c0c962216014441a103070810340d48005c00e10521a094910b440342206030814105004480440e41c0c100c0c03c1e00d0402c0740b40040800c010707503002644604071101c1e81801a10312036550a000c0c01021060710059860000104001d10f940d4040410000034040d074a078644255001c00c4904010b01540541d031210171030345004048a441610f504503400744051500b0b51800c4281d6a05a081d03421040044000caa100c250500240c034290340304801819054650a43c082940d0f113502c448610503115038480a507980c40144000d490520440d280403994404069204002d842d0882d0240d1141c0d130031100307007810700700020200007190003103030103164004194080740100c071000c020ac4110003400c800b07a26135407081e410700014120b0001c1c10400e21030741c0c007506507410401b40103420000342c0803000041000b0416400a030301904001d0941103022031900801c0c03a61a450207600621440406101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 425522212 1250 425520962 425520971
    0x20c0f18190c0906020a0f08070f0303060807080d17101725030317090304271d0d0c0201050702060d020a020106080c0303070b0406061e080114010e0708040f06 70
    0x24469005407402104607000c85042118034880b550445498969000d140010b821580040001c150140040300c4d000f03004503480c6c0d180000d5039440d054403e42181003107002c00e449240c204900841480998000c00c184405440944103e15005001e100c103941600045440b00c0045080f00e01d20224a00160071900c98040204100214056031030314292800c440e2322020000340342842e4840c21662085aa040d01c0790416881101c1800c940003400070640b25044c4003d000008140416800c10380b0045e039070b800000c0354484041a49402d0b2414101002c0c0c4020030043d00390480341e8005403214005459203005181c0001d54401200e00e80701c4d0140182d400315011030300040205041d0700070100810540c0007081304a640e244850b40f96502c80d83e03013030361641007804282c2c04a010201c0f200d0f8400d00c035910014495443e42a6600b2030140486407505122100c0790510102000344078013034a80d80c03040740030100c642c5452100307003100710000d00d05400c00200d038001c2010440d480c01650403581c0c1c009401d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 425523462 1250 425522212 425522221
    0x2281d210f1207060c14161b260a08040e041110050c0607110318010201090501110703090609030c060f020a050703030e1504140607080d05070e01031b020c0f18 70
    0x680035080124256059864100e400300100d004419000b0b1b8850000c2110781410410b0940d41130b5817049881c192070b05410304441036003007240c041e50344000c2c1c82d503401c0035008401299980c11010300b86d01c03a0440c143d0320040102d4007081045058030103c5900d00200105c695551500d0014003000c041910740080b50500c9107021140c0207400fa0000c2006481281d043d030340c0c0d030481159110450381e90101d05400030000c280070b811400e48600007644045c0008610b401702c540e6554215036004900b14000359001c07600c502059400000c42c00101258644019840d096846041802249120b05014440c9405070074004038002c1c007222600342d0f00f00d000e07504125602d0038080d11004419110358403a1102070b190014032881c1c40c081d2010f40d201610817080151142061200d19884050309440352001400483d440e500b0500500d4030034070090303403095a03e6030b00100240540d00c022000ca00e41e2414641207281181d030010342080c2c41070007112440c100c40307a9400401d001c2c401d5040301038035001c400300400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 425524712 1250 425523462 425523493
    0xf070303050f06041b03020a0908032205100210021806070b041707080d0e03040503060103030f0210020a05090411090a0b091002060112120302281d210f 67
    0x118815140d8415032007050fa140b004010448140e140c106044121643c920010780d4401e80c054201d845981c20081901a11815554590313080307a414409a003402040c0501c5c10044c00000740020b10342a03410300080209180003035140d0700540c401c1101d007580410b40d24004202c20310f00d007130038100103080940e0700c00850070070f1025a4000c44080c0c0b403110f8030801c40004800842c0840b03104942000307001c1d042501c540da842c8040c01c070700b0014074200c0c0f005000c003040071381d000d010085c002c0d4803903101c0c8648200340300d10181c1840c5100048090310751060040707048a40d0054100c030406d02c000c07100007602100095031140280210b95070740380c01c031400344400310750203210100629510740100d03818940b01d401c0c3d010480c2d030340c0b030700b4061866848451290b000c00103401c0400700c40342c0070103030402504080c01c03411036031428005204000005001c041995065540007807a444140d6510340740c60004072811030106844d5100d40d80748045100c07140032402c41a0109021741d00501c650181542d07001880311462 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 425525962 1250 425524712 425524721
    0x2150901140c04050d26270105070c14040603060e0d1b081902150f0103030f02071a18040207050102251709030f060c301b0f070303 58
    0x80907110580c04000c00d0440c0d41c0e0000740c40444500600f055661040307540c844c003000301141c400c0c0c1880d51051600c584200b464101801000820004a5010104003841007251214100c021414010f0070084d410205484020301010781d0108415480e12100580c00329008007503d500c09014503140070200c240454000c41c0032280c44016944068100d0030034140b030000109205402418003200704446400ca28030340300b01c601c00402c03a006071011040996181405203600322950443c048190300180105a0001211050320342d05200406555007480c0d181c0f005032032400c00341000c103400030510301031030701404401050760a0003030030554503144140340c010b010303411414489100022090050200c900342028088015410084039082c3c0b0140000c010905d038000c680e50b98160165144200c40180104a201e016a14078440241d442d000130400715400420011b54100b00418080c61b0f004240300300c46456002091240080e10018040354094800d11600c8042d04148002207920402d05406910 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 425527212 1250 425525962 425525981
    0x209070206240d020d0206160c0f09050f0106110c0414010905060d050d050d091202060702100e070513021207030b01181503090c26010c030e120a02150901 68
    0x10300c6210040002c40d000340408088070407504075126801c5100580b038142c5d442001c0900241003180f42406466070700d008000c0c540e83c02d03903019640c0441042481d10125106000340707400e002c200241c1c01c1c00801100441c3e418030508040040524111402400a00040540c844000c1040002c030010281480c8209024131854003240e1800000034164142032500300529640080601700b40c031018801628250083d086101c0e11517500c10a980c005038050300c0f008052515900200210701d891500213107000040b500c06a5240d003000035410589400003041011394504444114540700a48100b8000340a034054400c240d02c1c403203003844461a00b41c2c2c4140301b40d038401c2e40c1d40000882a000c844402200c58030540708100c805081c0c031021684030380c0c04005001c0c030070794103007994030395a8281289140700c02c000001a1030080044007000c074400d11810303070b0301c4007a41003d00030707d6078074031040340c9620126003008040304c00020403412881c401c1c8110b4007100e07250b600003c058100315107214000c3c030080c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 425528462 1250 425527212 425527231
    0x30d0f1a090103030801031e0807060e070f05150c100c1e05030c030a090f05030c070513141b130b040801150f050114041208090a0b09090f06030a0209070206 69
    0xd4503a0941030504020b416243c158031204503591840d50356008814411030070301103900b0f00040d04000242d404c0020402e036801000007051450355180040e0500701d441d40a038500ca5201c210411142d101c5c0c031009034021550307081042d04d031401e03401360b02e080c03800c9410254010b91070310103156200ca82140c02d401c80000d03400b41030460911616810703034440c802a14190415035041c4000b40082c42c60340c0000c11140d11401c2c841144444c00d0340c5d42ca10f117820010080d100358225803400d0001b42091083e006004116035018807662040c086000b4007080064184050034a0002118003100344000403540b50640c0500743c628029a41d0a000f03c840c0c201d4040c0403071550920b480080c1400203d040380c020388600c40c4000c0c0c80b40b0700d00001590200030940340c001805a040c00300181c841c991548901d0018000d6460981d00d1242000300000801c1c0d40d00651100c03013007400f1828943d1200401c0d075521140d6444852500d440d1000001d141040d840320081d8031070711940400121aa022400c14091540c24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 425529712 1250 425528462 425528501
    0x50a06030b0c0f030105040504050c030f010e0d0912020d0c230f120601153006060503040b0106050d1803110c0a060c0204020a0315090204050f04051314030d0f 70
    0x903602c1d8100344101c00c01441d401c4018401070005140944c02035070824030400c112840a482a400310b170810040414130b0b010703a59221010307440740782c06020450226006103401c450607414001075401d54211000c0107801103070062400410016108181c0015024400b11300600440310712030580d4004403101068002e48130700616607401e040c1960441b2101e0408006850140c0c24011040105061404050108107100b03002403520540c06840440c107000001518240c51804085507056900c0c50344181d081000800410011a1100c15501d0644071546401a42d800100d041c0001400400c11041d0b40340c2d00c3d1a644508243e0800a86120803025100b9620504813050402880325118443c44000c1107000c0c18850051a00d54000c146010150030b000810803240720801e0390401403904074080e000d50002c0e080c0720500d00600b0794000d011048405015030b03c0c011402034401d66500e03400a000b40046c0c0c6440c8260b00041c0291015607a1102007000180c3c1001e010402800c40903040ca95520401d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 425530962 1250 425529712 425529721
    0x20f0c010f1a030d110115062d0807030f094b2405010803040e15060711180a0209120106061e03140103080c1029010e04050a06030b 58
    0x1030800d0b400645a005000c0c00c020459000203950114403080c10070740b25541c0d801c08240f24200e42024002a1002d80d4840c8003205064007048000006080c4081c0412100546401015032244400354000c0b424500803900180041c400300c09405440e4000f08000041038102903c0c010312800008641401c10700d4061251101e28080000d0004500042d072081c1444400c40200d0000e186424441040c090091808101c011003042110801c0e045010030fa000000c0c1008109540c1d00e981e9084a05000c56800801186001510900c50360000418000445410f00060313070318240290506804251131981500d841090b0700d00035409800c1c2d5510868410b01c043c451094140b02d41d100350b0b001a00c8201841030408a054501c031080701c0000d003015210f02160a118a0016007a802548980d1030310351210b0004070350381d090008100c203c041c1d007450006690300c94180c0251402849801c20410b00d500821400100ca0013106484941d801505140500c1070268461303008404a0380680e1000e40780380c0b00d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 425532212 1250 425530962 425530991
    0x120f18030b0a180302031801050c0d02060403140a020604030c0303020d0e0d021e070b0705120711010e03010c020d080a06050307150305010b0a1d0f0d0b07110304050112050901020f0c010f 82
    0x40c000300c0940146c3c4240035401035060300000400303a41d40141030031030601043c4a800340c80c1c00400361200340160403500c14001016003006805861900103407010b41001403c5a00a40c3d8420040c805420080c0080e001c1c803d05001e40d046801080001c5403d00c006034510040079611400580800c0051054070a11a820610610052656254034000d41515480d1028044075500f0800040e01c03d401181200c0728140182401000100e10035140c1d0310f43c18290304009418043d0186000b80a030741070810404e00c2550100304017680003100d082903882922280c41120003010311790440c540600c9030031404900902c904201c4540021917680c20301ca00c1c2e0305c03612800e17168044c103200c580100340041c144a1650182083c4000301d00406010503603481309103800100c8881c4070000684603170040390284000594081c800740a1401c1c50f0f0000c525007868000001c0030307075800143c040d40b00f42e650030124213a0740c4290111131050862540094950365203103030882c000c02c3c07030300c906031103092510382c03161075070328 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 425533462 1250 425532212 425532251
    0xb10080c010207081903020705060c06061516150f15080105010f3c0314070603021804050a09050a05030c07120210030507030f060b04090b0d120f18030b0a 68
    0x500c0d1320301500c50b0368003c0020904141300c1c031104a040d4010408040707400c2d00c80703e01401d41200020000c00b85414204d003800340791020305080e14441b405c20003114803202c180088501c00706a01c88150100790184102080040000b0080502c03da4100742d42c03802138044161004041e41d40e5035000b0807250b43e98101c5003000035140c0c404d503030036094120407600c80003010a80c1005e81c1c810800c0c030200c15009541102c5980351882d002120071000b10807004161080402c51240070701903909007146050b00c01010944805400075500e84169182c0001485002842c0c2280110640c042e04a48151416142403502ca0300300031a0180a44204034000074040c0e502800344100301d4000c0c00e960100c0454100c05c80203040001d01d807a040c03503120f11003001248404d201d6080208520080541c4443c1410f4050f0b0a8684a801061241c04451028004071b003060300b540c0c07403200b00b5003819640806400002e0301c50449441501401c9860b4031400000c1c000150403152090a00c00307030800510280b0080c40c0c3e05c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 425534712 1250 425533462 425533469
    0xe01110d0c022e05130803030c0703020c221a0306070c020910120822060203040906050612011224140919031d0a030606140d0b04020411070b10080c010207 68
    0x2400403030707848140f0a010390002c00700c100a0654036104c3e0740d1105695880d40c0c0c0b055074100005d00d07002030103005040e4113019810724040b080b510040141c1c103921007881301000c270100d81102141e5030808102c4601e01000a404484009010f8600340d2500d090054035280300720b03100307902400d15400040e010350306842249080d40c1c9000c1c601c2c43d0854198945500e41d4010001c4400042c2074038442080b80108071030854010003140d401940d96504010701882a01c11561001d8003807801489180104515004118155500c5065121a520307603810281c0c00090a10b40b8140c0890f107114103e4a48000c40c6c01482e1a0103851856140d141c94109480d99907010940c45001003480271103a2400080c46840500d0324144c000e15245800100c800c0011000103d561040b900c00b0b40d10007040101c1c0d490209a24104282100c640e070396046941c590007004200240000d100d25668140740704016281010386403401d4000e81420030324a04800e10b00300c6901140244040d5119411080441c0d604c0011003c064 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 425535962 1250 425534712 425534779
    0x5010506160609020a0519030c1505071401060e01090905060106052109071a0309010606050306060f031b041512051905090c120d0305150d030e01110d0c02 68
    0x40c01d806484003401800101012039010b02990b5000481d5034a055250032001080c0101c42400c03451494a6a00b4a1881d130100041103010200001181c0c0c104041d108410313000101038078510b16204405004003402e4001640b030b00b40d8100041382114282d406424801d103d48212111a6210101502e050280c1000541142140d1880541078400f0071480c03a04507070902c0441e2161a201c52006000c004664a44800d140002c810090041400d00418004020b41d040280c41d50501ca80495214850243d00003003202000001c101041440d0059408041484041e140c540d80c032902c8201d01e64240000c1180029410041100620040d1003418060228240c1001c0200d6007908943d011700760080c00c0303400900440109203040d03141d010300c0111402414003e40a4507115020140880d04080c14007540c0c2d84414040f0b52907915030980741c3c0303140c03038060400501d8104030341c00485002043c039050f00c10318001d03407020b0241c0310b40123440f880c0810300c03c41d01e0814401d12140381700703d0b81d10491420180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 425537212 1250 425535962 425535997
    0x70830040b0720210a06051806010504050601050306150f16050c010810090b04110708120c070b0f280e100b060d020a0c06060f140d24020c01050c030a05010506 70
    0xf448615041070310900c082001e0302e20003030030346e1a41400c50794103c440c1220071082100c21003801200380900380c007604003124100954280000000e01c1b501000b8580b0380105827074403c40d14800c003017400b0742c0c0309454064002070342c1c3c164070011070002c940d0448040f22076114544201090313600034035140c0d22443d028900c2600040c900001031020f80b015590b843d0704280c0e14050100b0090068004081c0240a000c12580c0c8500300024841c0703d11004146010324401840b803a4001404180c410340c0000703202d201c400e00e07510342c44540d8500031502c031100c41030640b9081e2074030092603083c2c0122400c04c19540c2038a1001d29041d80c041d09a803010070040d980b0003010045d000c103d0685501130400d00d9224500700d920090545d540704110380040c1c21201c40c2e01001802040340d0a9002c4403025400000d43d2008020300c001d41c2d0b0b8101010811b0801e1078001d0440300e4011814180d80d041e100c3d0714000ca00244114144007551648552084c4d071054000750030080082035a0030580300b1580001c003111203001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 425538462 1250 425537212 425537239
    0xf02010b030604020f0a0306050a0506030d0c17030402150309060a0b011d1e0a030c081902010c06050601020c060d050a05090a0b04030311070c0e0711070830040b0720 73
    0x10b88032105d40d006540c40a80c248000c40030400794810640300c0c040c0d010f000281420507904043c540b80700a071078941005038000c4503500040c14051140c0ca030200218105440740c6503480050100510010803002880c8007004015075000e0000b005406030140c01000c1002e0034007400112100203a40485044e12480481e41f0052030074000c1d07401c10300300c410354000f000124030b03080024400d1940e58015103034140c80c1c01b4244080c0d48107005c40c40342d84500d8000f40d40c483e4003e600103000781a2581018007019583c5d00040c2403070740244a010103000009100580c0c50b002e00d045000100320030348000418524040020300d0226000522080c50307a04001015803945ea00d65044014000015618010742e20078001d1000240103c01e07864050148924000590301e00124001c051070f41780752072841c903030784408420042ca60000c0780203041102d202c01401e00300c3e01c0220400081e200304250f55450729100041c00151541c0560103400c08911401c1800c2c400104c0640300035403d030100003201d620602c00703030505 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425539568 1106 425538462 425538469
    0x203090108151f0f0e09060d0218191107030903120309020a06051914090d0501020c0d020109021503010b04050405090a0501050403030209130e060c0a1e0207060f02010b03060402 78
    0x5e408081c41500103440c3d084080c00190250200b140ca400a54a492a003a10898040c000e2140c090500075407c1c24600082c400999045180c0720309070000034007600465407045d070903646038072095082d9190400c0c10707120411340c10305043e903504d198001611410090402070419890f0180c403442186070a00702c043c0303d107604c882088009508081035000701c0c02034442c03003482a0748130021001c10b0310b00300e8024403403d84c41c80a2072060050003100903034150814180700d4402d51701d4080000800e9540300c146d0000780590501d80300184010b0015051039445280d2044005040351807860f0951107032421184107070360660010f0f80001d50341030750742040031210100c5a00d1000410413a00d02240c40d0741c4a6001621808100703100041041203544206288086000912240110250401d00c040d41d5400c0c1c0d03214000100c1d045501c0c5804150040c415402c3c88940900034182c0e41d5034a6080 = true := by decide +kernel

theorem cover : BRFrame.Cov 425359712 425539568 := by
  have h0 := BRFrame.cov_init 425359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425359712 ≤ n) (h2 : n < 425539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
