-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:17:57.781657+00:00
-- url     : https://prove2.me/submissions/f9e5c555-bfd4-411b-a2ba-d6f3f8409abf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200000000 ≤ n < 200179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200001250 1250 200000000 200000033
    0x1b060603030705060c070c03141006060e03030306011d060d05090f010608030a180515310e040602070b04030c030807090b0f09040b1c0201080604090b0f0403050702030106090603 78
    0x14628000b02c940b9069075881c0085c040444c0004001007850510030840c80c030704050341c0d0200348002c03412600e001d0030703607a1001e24020242403031070311300c0002d000e50203a0301291844401401440c03c0d942e51030010344054401c126102c8250100103640b0b010b59650038000e120b07400b4a000c0c00151408c1491003a450000fa8480481803a0300d0210244005000003045d00c2c0440d41d240317441d44a02100c940c003460030b00104d80c021500404444040e0000300034140240071a11340c00d050030108405480d030314070b10b02c3d4507202100d111202900400c2c0700c05031079040788a502c030f80030350000742c40c1000c10b0340c1c1c0c00b036000f07070464080c0d000411102c0402c0416600c400358940000c410300d0803ca06a003030900004044c8203400c41000241c2000900e81040d4540750401b28500c2c00003411400341020800c1100704190b03601408900041c0000000f032203070301e424800c503071700140c0281c4007079043d40e40c40e0785000a0400182c42502480030510010b00140e40900450002d00303050980411014558501092440c007407020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200002500 1250 200001250 200001253
    0x120504090f0b01080f10081509100c0914030a08031302031005010e0c0a110a030206010f0b04080703030f0c08071208091f0c050d11041e0605042303031b060603 70
    0x1103030107070b07804803400340c100c418503005e2140c81c2c8440901d800725058661103141c2500985000c0d1000b403e000301da851250802e5801e071142000c110340710400321003019082c0c0c00464451a814068083c1c0000b5496907030001508880802c0710b13684540c20390340c0003101e42d40c85007500740003103104505041c80f01250f03080e00c00300d090009504001c5a507560b40b000805086000c0004a41c80300c28a00c07076282da8005181c80025540b41001d00c0c2802502c5038824012403400c01005c200028400c0060b10480e404c03603056202824200307040d40d600706d8031191a00b81c03080400a1820042d4007142d1034500405130103100c0c1060390040b200d10707080078100e840014801040c03a0132903c09140d401c0050707440c1810f0300942103000105103814401c1038626024080d002f01c4203902d803503407180c42034140100820550f42c2c40e18401078080a5000d5240f40c4d000c0c18011040003c400380810000303441241c003d41018010780030305140021001010a02e550000c0c2c10880006104206501400c3d2046c409a60032610580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200003750 1250 200002500 200002511
    0x605030124120c0b0a0c050106080c1302340309050901060c02090604020d09080903190c090209011407050607080609090a030c0f0b0907080d0504031205070f120504090f 74
    0x1014000e0741d0500c282c0100600703202e03802040215264540c00034020715000c081d201c80740c40b40001e0562148401c212099032800802155981001032194600714004200100c020a1059118041d4201140500304901ca40d18145400c2c03041200482a50555540b40d0206001505008007030308c0441e1301c0940103000840060140a910002c040000e5406403840392158551b01d000c01c009200390000058914a854032000400c0300410080480a00441c1241ca070412000703d10440032b186c10800900d000d1200c44108022503540e0054204414141405000052080802585640021811a1250800030030441d01d250840e69541d08a0b40685415100b86051030200343e54042191029040c4169440201c04001404d4000b0f9000b0b80d02c500700040d141403901103566204ca141c0543c07003d03406504079a880e00c900c2902070307504403500f2a1f0103600c1c3d07071003104050311107511000058601c08011000303040070a013950f40700c01c4004c00640c1ca103a0307202e02e0100c0941c101d03282011000411030900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200005000 1250 200003750 200003801
    0x18070e010501121d121804020a0e0112090213050a0e0a0201050a031104090f150e0c040501080402240901110a0209010306051306060b0909060102030a02070b0a020102130906050301 79
    0x2540d8900741841040c006001503003e0b109416044450300401e80718890f54000c105540302c41c5d8054002501804204045213040200700070030b0340105d07001140000d010207100300c1558410440340c1c050f0401030380002004440b030f4010807601c80c03461003030700445900c072414040810554480c0c81e055242030340247c900d80080e40d0000300584920969030081644480c001a4520aa6812900140000302040000340e940c0020345001c0c00d080500c2c4031030000c1d104800280b00e012681030611411103104850b182c1403d1000554a101020380140e8103e108001c402011014885d0080c000c50300c50118140c840b0801c1c800100300342c059203020182030304444e42d40710050302c80342c21a505480e400000801c05075601c20580d49400604880600700908003100010003240300001006031980070b030350308100d2b5955003005990380c1c4508680b400040e40714640800008503518042c24490005100140c50100c51005128032107905030800a5403507900d01c402c1000d40340c00d121303109044041c0c01d002025000725 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200006250 1250 200005000 200005007
    0x4021e0a0501081b160203071e03060c0507050f010605100c20030102090303040b0310090204050918120403062f1c1508010b010e040b0f0f0402040302040518070e010501 74
    0xc5115041c1031007044004182102c201c2da06459400c032040400b25281c095000071380f40642c003094070580c024080e6041c0480c49401c000c044061103204c04015038072013847c2d999440c000b040110071a0302080018014000002c178248070400d0006600310000c00d11600789030800c00441d524844403000d001e003180524000502d20440000354440c044400b400307248442c008170340603200c0c0c0c2e90404c1d4140030005011880b1040303100518080c40031a01004881c40e19500000f08910485c09402d034408030340b0001607105c21403805004100300c01d80040c0c9580c0403074800054041d0700103410072188a40c45802e0202d010101501d403031442e000d00001420f5401801c20100c04604c1241d4160041c031840310701100000c10190411182030301603400424801d503480b00c24030b0080520004090001d010140281c80303503e880d0060050021004200341c020742010010400e1802ca00d00b88603130000d409000010142c1c1e40d5100b8548100054200e003200702210704c0385681002d4031a046034084031b0303040c0010f01240e41c0c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200007500 1250 200006250 200006269
    0x5130b030c09091207211106010e0417031f091e05160f050c0709050601030c02160510030b060307030c08092b0c0c060302041e080c0405100305060403050304021e 71
    0x890f138901c00d07525151400c120107007803070a12550542000d85600c3d83c84266000003414500304c920070030303900380e66202c8070361000d140c80030707100035054a15152000a100303090400a58100c0c1c0403121752400b118140200b51a04a0981e02c0500d0302950781288005008198034001c221001580c420001c9240c81e04070f0000a0300840b40650420000f8080110440d000744102c078007607002ca808542d00580c0e40d400c0f44005d05021620140042d06241c0a51011170000500800041d0b18050841110381414244003003004429020000c06480304110f007419240c14006501540d4103a8010542c440009005130060801a00d042d801358007402d03050f05040d841d130454250402c000d00050348403084015086407080d000800150020081c01000142c3d1a0580d00600c116200b00b20308000505031914440040400e5100f0b0481e1504910791070101ca01d03244e0301c15580300f0b00c0401f02d080300c284c40781c44075450003d0499084011801c000184010342c50034400200032402960001d00e106580d00002c1541d140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200008750 1250 200007500 200007523
    0xc0311040902090d0f05030a111f0e0304030606030f1115071e081303020906060403080d0c0302190206011a0c0c01110705100206040606140a060e060405130b030c0909 73
    0x95001c901d182c2c85135600c0310a400d4007500000000c42c3e0398481c0c10f00c0c0e9120760002c0b1106010824254032401014400711b02400c040c0c070f801e1f424980301d10070441038002415804030100c44078042000f0100c0000c5882c4201e1010b10700030140b40c4291040c40c544100e00c460740b44030141c49002c0c3e64091841c6103074049c0c206d5146540c401d00f85161b586030050a420109031054000300440e070041602042d02407040700f0101120b0085400200584650061040c2d030700ca5400007501c280d804000c007102c01c6005821000162070640390040c0b03005802c4030041d2005012249000041c1c0015004100034014500c00310481e14094816514200c02031080c0d030f43da41c1c58245a0303418442e0a0031225003041c814418040100780c00380c0350503a103146800c2c00030344813542140c0441d0202e02d09040412050001c1030000e52251002d040340443c1420540d050310280c45000440340d010008200200d5191503c1000030f9001d8082000491448421820142042ccd07480d00d03d207000b0f003241e00410244e5000000c0074507004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200010000 1250 200008750 200008769
    0x3010f06140d0b0102030904110c01050f09072c0f01090c0509102706020a03080f090c0d0503041d04060b010f120906180b0f0901050f010b03190504050d02010c031104 73
    0x920403d0045c1c1c250301074540b101e82c0c0246445640c0c101c448080c0c2c002d0010600c0030380200b02540e500c80006121042c03c0d00d040740d50390300c40b80b0103108101c003401d81d040c00d4414000000480400d11107030b80c1c0c40c1e000200c0352265090215401040141c6c458041d001100050b420301a00344254000491910010503000a08025410105078071611040111403441c0c550886003414158407103c010303542e0895050101c000071075060004035031f41c0f0070914160003040740b0303000780801501c03010810041d220300205c2581c1a0008201c00540c001c144c1c00c1d840740070b1074140300108941c54142011401c8543c2141c0850620001c41c1849218a82c0030740c40082c4204000000101b103501800c010004003808031081d042010384840c0032040c00110503a0740d11500da602d0a4102a94860400e24242c88042d03503280103400c608d40040c0404d1900801456108042001c0c0301c9990243c2514031050b04c400707507401e039400d81103c0c403030300291745c2d080c010340c10394040070304003846041c03010b2490f000f00d0300c03940c40307803420b032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200011250 1250 200010000 200010011
    0xf0f03041203051602040e03041406040b0703030c0219060902011205040b0c0c07080601032604031e080d05040c050127090b120a03080a0506041b08100f03030503010f06140d 76
    0x1807038071310009101c5500504100305544000b00c1d01c0c0c0ea690701c1400b50205009044a00c1d070480e08c1e0105c01c460580342640440d0381000f85964081d80a404901c1c1d0000550081c1c40c5551928403501c030034801c1c120300490000c00c0b040100e0002411001144146010a50811007040041903108640981007501c0d40042503441503580c92039030519105412413115400f43c84000024080601c0100040301a40c101010200d80c010301510005d12441c40001c200c040006055a4410400744840c000b0b01d008030082c5251541d22060041110000c540403603c01c1ca0b61003081c8490b5a00001c18658003100030b111402c1c10280500c1a281645148104071240d601d6418615007519150035007414443ca000445800070340c10715018140039411500c4601342c1d171a00c0001581c501d014000c500c074041c058101000e0014076400c0c12034045800a1402080004441d0006281030700810039400a600a0751541e40769410681c802d4202c007001e61210082003070042e40c207100035040c0b10450b8400700c4810303000100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200012500 1250 200011250 200011267
    0x733020f0304110a0909030201150501090614030415020307020d030b010302030603071701021909031506121e02030609030a0e0a05030705120f010c030608060a09150c090b0c0f0f0304120305 83
    0x11012583e08580050746c01c25a02c8001c154054106507002b43d4114841c1822548400045424115a20402001483c50039400b03041c04180c50003075400c82c1c01502d26420303080c401d0901038140c0e802501c403000168800000411400d605110794258408246402d5141d42004800a6070b074043da401501c0703607414011105512a182541160200c1582000d584818801d440000d08003001d244003d40d90304118060f03404140000d445440140da1625100c0c2d0200702154a0342d142e0020a150fa0f1200d080894100e5800b503602000400e02c101a11001990b8030f044040c0020b000d0b01c81c40000b42d00500000400384441da40c08110842591015100711480c591400c10251074010503221842542d403810010303a2025901d5040300040d640c10000300d9055071155607002045401e003c80150540410380f425810811440d0400c407a85e84a91800c41c4406880d00c5850280398441e0741e51501d1075108400c6a0103507032080c800b00c0a4003c154025604151804100ba0110101c201c4000c003000000034a040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200013750 1250 200012500 200012509
    0x306090a1a041d07030b07020d03020f1e0c011104050f0a030503041205070e01080c0111030a020705040b040e0615090f01080c1003140405070e060a050f04110733020f030411 76
    0xf55a903480c841120090356076070905814110b0181c0d00040140100303c48440b029019008450340180300e0000d0905c2d10030005100c42049980b907084500300389080222405c401801d00500040c008440171030b82c0e45900d8001000415592103d501d40108200c043c01c00205901001b80c3c2c045407070810281035014003e21344142001c1c01600285444007041e00082015003000440c01944003081e03e038604a0182003004660300c0c05000314a40050784241024062424590000651980042c1020800c5007120108900b4400d0440d0100484401c0c1c140c003008a143c0710010b02d81200c0c400c00042525414146c400783c6400d282c90840c1e0103039441c41c0910072424401e62010400c00c40c11034040d200c3c0d042034070700252a2f03059031084042c2030030501c000c15040d1805030314210480e070008042c0d403200c014078002e100c0078019520040d0030b802c401740050404240d20030601ea2003411801c158010b05411030b10080d40044521910410076071051140c110010200b408481d0003580040035652003807518030026 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200015000 1250 200013750 200013791
    0xb0d030507060c031113230f0d020a09020a02030c07171b0a0e0a0b0a06030e030a08042a090f09020d0204020c07090c050918090616051e0306090a1a04 66
    0x51750207400046d07103121640b0040c050029500c000c50003070701901c001580382c2845d0307803404546640010b4042041200c2c2c80c120b601009090f101038030203100c06a0fa840c0d03540498010300b4954000d45c0001a40c04242101448900f010740030820107030840c0010800104c0d07a42c023040d41d140e1400c104424500346150345a4018100910b002040f000c8903180040c00c42d070140c035180031030354099034104002045540c080c0c040c1500882038500194203003442d00b40d0480b04980c0207481039801d40c50550007410202858140d20034070070710f801c000203140d40c68a001c04d4216031407400082011480d06901c88016070f5040040000d8580480780940c42c0d241c1c01c50f1a82c10034032130343c6c810a003041c41e1100707030100c1d1500007000d008401011200e0f0b841459180c0740345d0b42c100c403049079403c1581d040f820021780c2c030960b8240e10b180c0450300c502d0034034240801030383c07203204072100100209024a00801044010b15100400e82c0d80050b80ca4000e0080e2803a180f01c0c09030801c4e03100072051096444003039201c0c990541540a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200016250 1250 200015000 200015021
    0x5030621010f02040e0f010e150d020d0803160201020406020606040f150f0f0b030c0d1d030309100b040b100302030903070609151d1c050705030a02100b0d030507060c03 74
    0x3000344080c484502c1000750310600c280030800d050500091000318148071554100c1d42c8640440d0000c0c1d40b142119004c1c00101410303194805c0b2014440005a195400501410f51180702d08a981e4200820300d03c0b10100e0b0070903003004680c01000248041a07004c0b8009800180a6401282006010120b80c0140042040d0000d110200080002d041c001400e101002c4a6010710b845c00d4250300c890044409200880e10440c0c4210100401640001c40740d01c0030030030140b0140501000001e24510034116407003603c0085081d408101c450031010201d1140c0d202a40c1c04543c102302c0541c6000100b800c81074825440410302d94084001880312800b4411260006d0380a0f000b00f144050910700100d150594160004500b45020010702d9540b402825003000401c0400090800c02e00c4545614041c0703100000704c0b41001414020b0b0310014104001400d01b14041b5000760001d00022920b041c11a00405203407441009c601d622400800e400c50200c40c84c181c3c2180c00801c644244072400d03070250500c07020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200017500 1250 200016250 200016253
    0xb030c0307202d0f0d110309060702060c010605120c030d0c050a020915041104081c050304060f020405060708030601020d02030906040e0a020c0a0f05070e0606090603090c06130e010b030705030621 86
    0x1820300700301300c01245020000c403064035081d40800500340020340c0c0340141c842c22038000f0410000100986041405001a03010850021400944440215000d1020f4030282a03195100303540f291318a24040c080303410000c00e41d14107030f03d03052900d4440d07507900d00b07110358064080c0d40f550020968a410600a90410840c041c0051040b01c2c0240a004600c0c0d0042c0b00c3d296090058403003a544c00c0c42c020425088001981c0e58031410340d100d03911018004d043c03180c0c1c0c4081556007048000341030788411020341420713401402050744034900200060305041595103110119042003010190b19620441603409584010010440c0f980c1ca4440900c02071041007102c0031588035541e401c80800290041c02c0324660b1086003901c1010340d0b81c207502258018142c400c2e039840030050010440c00c0c00c104001e158002804d1040b158180c0e854004a0300e0307540900c0301c9600b03490302c108080c00244031000015004150081e509459403510240041c80d80c0805440c242c810900300e00f175104680c00f80b04e20480c0c06c0d8540700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200018750 1250 200017500 200017513
    0x30b090c041e0b030711011b0c1a1b130e0c1c050603030f07030c0f0506160216050409140115050108060607030c06020a03060b030c0307202d 62
    0x103a00500c40e04140300300e510381482d03041c000c00c0c40e02c4281a01d0b42282d242c001000d0940e151010305440e810703002d0409004542d41c460b145002961080e0400f0a14981522001444003050411034107800040e50100c0d0b24400813800e02201d07a07400f4511a01c4140d40f08130198440e00c0c1e1112441500c0360a50103c0c0c1e0315902e8405100c21104084005e041e01001307402000703440a802d490340c10035914111640e82d0305401c288804054420710030300074900c55100345440300d041c200c20741d03031105400700c04d24083c0d62560184041000c4001d8140c1c006032241000c1c00100180384802c40341c299500e110f0301600703000710344a446500400ca28105c0884020300030300d0090014688640c50700c81c0c11682031040c10300141e80360000c03c2caa810504101c0e20084d401d56a040300110198550001030760040100340c0405075a4500001c40c0940e01020350702903c0410304e0180e6a0406801c0200600301d02c0040e884034991030018140500000140064a0342c44190030020000c4a01c00d01000c0030000d4481c80c0c418050003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200020000 1250 200018750 200018761
    0x50111090f0a080706080c090306070e01080a091106090d0203060f0601020d2c150a03020d0c0327061b020a050d020303010b090f040b03070834050105070201030b09 72
    0x405064040c0041d100c1c4100031041408204101901e03220b001015003141e4014800e40c1d00c0340107038551003000c07000114581400b16002c03034034210007110a03400042072542400219a4050411a005213244006200c000140c0e211110b42150f8211201c0c4149400034103a4150b8503110000140b582d0000c0580d4158600070003c03508000b4211542c50041c0169601071003401d00a401c1d5816240901c0d40b040903040c1081058403c6400318066940d1241c12104c000558031081d8005001c2041180d402580b2005031101c0801981c030108110700034503090280c401450a0036032010480284e10f180c0c840422040d509140b070042a800341c003201030258007810040490380000f04003101c0c610400440e800c94a040703904907120702082c014004521000c102d501c003d80340048100b0070040c0003c1c00019540021070010340744c44219400950301d9000740c0415070801d04a10019005121580c114008640301c201d9246940d13031040c018507040c04404991882564400e510960030b6403000b410300070642c14035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200021250 1250 200020000 200020031
    0x1030309030c05030a030c0f0317071106010909030f0c060f020d0605030f0a052d0a030e01020f0a02010503040321050103080910031503170c0106090605100305070c110d0501 76
    0x40707001c2600c9044800c5400101e5080004800500c4d903055543d00d010a00b455540c45038085044070180c040100e40300c00b48442300c1c3c4404c05640074032040c0d02c8050303012242181a9060600507407003485810f02d02805200420f8200d1040e144182c59485e00310000912890315200030540c030366000303008620100d142c04203024640d1144003554011000c55540c0a0540c0c03141da0341e564260b800408070381106d2843c00c03001e200ca040102c1c41034148140b82d0711000b816070b2200c1c50180003c905030006515840541019601841010100c05000020b04904803041d00080e0461002034801010402e942d010840c0d2043d0b03901c210f02c2e2580001c032041c00b0a59403414100744541040c21792a2080c641103119090343c9000b44100303580702d21807140ba03024081c80c1d6190f02d000703141021056070090301d0400803040c5401080c0300710006440c180000007101070810041c0055450340d00c1104013854034040c20b01c2085070700030803d0054103a0101c503102c2d80488500224400b071290120003005c943c20002d128450594 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200022500 1250 200021250 200021267
    0x3050a0303060b0319021b161a0f04031502070f050708070906260a020a06030e100606120c1806120f0903050a03050606070b04030f17010b04060c1406010303 69
    0x2070350381441041d4403421580702e40c2c801907440d55071000b08034258200805d815000b4007043c00e40103c4000440e51088210b41c101880c20340c1c615410b110400d418402018641c0c841c441001440500394140308011200c2a02c600c01c6c1e0101070030442e01400400c4449a6503012540180e601118402044001e03203006940d801e0240202242401040d8020400c0403903031284008030389920031140d1000140c07c1e0440e8243d60143c01d10980f0340074400c840780158549890070703401041c0e15a000180b0869280d811818003403c00070030046a41452020052150700c10011800b031004a40d0020344e0005a59042e914904d00c6180c590301c01c030000c1400031b0100c0d00808101780703544901030103114001c8051074000440c1d1684000031f010841c01d002c2c680446100c0d601c519030014001d4140c030710b01410b81c0c84240c42e01401311000c40000c0e00000c800e40d1525809580c140c440001c8400303480740d55044c2015020240223a00940e410003eaa0441d6030a000101741e01e0941500003e064030321035612130400520991 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200023750 1250 200022500 200022503
    0x201020307120510090e030d021314220e100507030c02060901090803070810260c0103290406182406020709020c01020d0c02031b1203040204110d020403050a 69
    0x4450303040719250b80d551800b800d84500201190a0700300d5081a09190050603041c84070301003440b0900607031038202524030040ac1c101114078401e40003a03140ca0400307506840712075504c034080c010402c034035500f60700c11208070b0440700142e500220320030304001404c519200401e4a008580c600740814800540e0b05a444460700e08025400e076000c1d50780c3c0b1724941e17007a9500480c004051040c00c10006964038840c4181d0b981124000c1d48003004995a042e2852440e600715803140072401c038041001080210400100c400210b01b820b0134041d03d4403075080e41d81903a060b9000564900410980d981c1c455441c1c3d80018083d00c94488440000c10703c00d03c4540040541a800e180901d02c06040c10840003520a12081255525402080094100341d10180a50404081c5001941d02400b010103603404a00070311240ea0b40a0f4010b40c0c5804611050f000c98401d41c00d409610b80c0c0110301c404040d0300c0c0c02000c0721341c40b9806a0340401c0622015003407203071610a03151361070409440410003008101d80410a540780c0c0313 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200025000 1250 200023750 200023757
    0x22e030c0207210b0903040b070c2c0604110702030601030b0f0606071101030c050412061416020303060f0d020915041413060e010f11040e07030902010206180109080a0201020307 78
    0x1240c49010000184076082c3d88107030200d06034a000e070000303200c035501e003a80540e0b0401924149942c07213195942d2504107180c12688500920000e002902c3c503c1c002c0b9034900c001540510300300d0600a080410341c10b000d81400d0249440d03129101100d168141219412a80035089a07465a901c1c10701500c580d00c240c0b2490f82084680002c10001d18001301078407038450b080008422910007a10040d402085001c401c00c0920a0a21002400c4003a4040e03c110481c094440070070340b145030004c0b50040c9640204862880e903400f000340e9000c90307400004d81e5404442642d040c001440d4020000760301200030103000794040d80c500d04120440c44c1441c003181d00713110240ea05104260044660056500d0100c4581361181e4002e00c3d040007003055030300480c0c000501c042c00090500000303d180b0b4103507801c214a40041c8000000c040061380003021000303621040310f103000c00030950a5030001f501d800000d000c690783c01c4881e0651080c140c0083d03000307940702644410b02079500d0318000d00182c0070f504101c6049022 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200026250 1250 200025000 200025013
    0x3090506160b07050304030203160c030c140906010504213f02010b01080609060a15180f0b0403140f0109060c1e200102120405010605090a090807022e030c02 69
    0x200f9001d18162400384c3e606402460070140e806c08041c100340f04005080d985802460800008118005a424040e140b090540700c8105005018016602006030550b0b041100410042060100341d100010700140350100658000c106070030320392900041c00841032034a0010341704400742001d54030000d62030011454a01e81c0c03080c0d9400c0e416030032036105100c554080344c4501d001401d03c0ca090060f99510140c0103103401c00c1161510004007a03001d14925900205078080300c01211079207660075400c018013a1480c4088007908003034100d0002d0040f44401408255201001c0c03018243c180000c42c0e91500c41c20082000c00543e003003040c042c0910f000700c500858002c1c050f00d503540c221701000703401901054403200581c00b42c0b881d004510b800d03149901419075500340706410465140d0903509024074040c0f0000310b22541440108aa0001e0103001004054607100a0340e0024240000790341119404451440640660b0048480d01d400d81203a000e04242d004400d240030580c00d41c0c040300703084020354211540f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200027500 1250 200026250 200026261
    0x70f0602030a12060b070b060d0f061d0703080a1107030b040c1d07020a02010806030c04090c050315090c060d0612030c051b061c2007060b01030b1c03090506160b 71
    0x4a44d074a00882c04c0c0040c0c100800c1d004540408107030790f00b101703000d0158001c2c492252140e060010140e031045512548403d500c1c0385c0442c4111078603820042001c05840700351316558650b071003480b5001c080405c0c0f0540300081d0030300f41c009005080003103802c40c00c00704140c0740c1072800c0d204a00c902d024900030666a004502c081c80d02c08240607218030602d80080c00440c181d41c00549030110018400c1d9418031501101d5400390f00c1d540200e0741c00e544207401a08409040404240c1484840c508003500500804100070580ba4000385400e9460343c143c5402d50796842038100b0601420b003e07042226007503040c0803003800301070380328002c1d44050340208107807010400d85940c00169103501c0303002039500900510071402091078030f2030400300007403501e00b00050f21100c80034040c05d0403141101c901d10481002c18504140f25181c060032003010424a420080c01a0540008403007010007404100752079103d004840c1010f0168420b18050321005025a4031080c0190500507c074668000444800101d03201194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200028750 1250 200027500 200027537
    0x806010807060c0201080f060f0a06030e0c010c0215070213020f0c0f07050d02040203250c11030d052d13140303040b0405090403051c0c020f0c03100e070f0602030a 72
    0xf85400d505946440150302d440c10070410140c0042c000075802407000340c1c08031881d5181d02c00503005100989001c6203140a88001a041940c0c41094906010004034200e00580c0c40803072201c008a0080380345521003400b800490310401200900341103140c80011040768503082d98010b41030350941003044400b181c5040d80303140d444180521a80f0b40100c00400007400500e4503030061548144031844103800326203c500070390011005201e0042c08150480c070b001060001c0811000d00d003250603001440e0314411004001d10520450b90303545810315802d11800c4243c449201c03d00018003030003003945c0d261006010821009138262180c8101846d840780c9608580c1004420b0b03030f0440f42031b0100a402c2500d804144182070800800442c208041000a03035003180051a00b400c0c800487e5600148102d03800d81e000e45040524605001964414103007102a580e000452095820608d4000f04010401c0b1141c82c3c50884907400060300b4891110000c50f11550000c00350282450940c5d074824100c044c4803152 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200030000 1250 200028750 200028767
    0x30f02030d0906020303060d08090a0b03010e090c011403060301090609080a0f11060a0903090801050a05040c0803030411010f031d010c0e0603100501081012061506051309050606090307080601080706 87
    0x70f40160f081403002500307601d01440c01c4040039001d41e0410740380584880010301100d0700f58000442445c000300c014010200c414008652181e80c5070010580c01e652200040d0116000306500c0d0170200c00000024502d0711b00b0f402c004007482d40003205012000c1d0a2601c0100f50f00300140700e80009030f072000a8400c02d40b0545050600204803806400940c503524425006000180e0041d4203000e444040000c030410300b4410306114042c00c801c0014141040d290a40a0440d82d9100c040c180c0c1c82030044c080030032092810150541c0f001d080c94001c3c0c010b000c030198040d000c440d40d0030203000001240c1c5081c1d100190461802252150b8910035600c4e0322108011441c001680c803007640f00f803001d0303051040c3d50141d495a90020342e81512007070216a254403048007842c410404503100303a19501c1285800440700454006001141410341c00c01c440f288442d14424014031415a4080d1a9000f1a40d261107290407a540c564001d0280c038012502c4895030b41d503440080c414244640308403040000c2052186200c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200031250 1250 200030000 200030009
    0x303030f06030f08160b0709050a091e0506030f03070b06120d12110d02040b0d0606080c090d06200a1e0f120605060a0c1e0203070e0a0e01020301030f02030d09 70
    0xd41c41d502c0100d0700c81d403105801070503804030a140c5e01c404400110389540040e511801c065640c06004d41c0c01c1c08103000f400c04042c0e10107162a07050200419104200d1008403488105060001601e96641400a46030080f29144803005000004107030080c00403400015108000c190f0304615001c1072002065640c0800481b990300003400450003440c45100f980101c4140c801c1d0b07004441c2800f40d407814480c2282e2069020384640300d00020b10750700c006014050300300207040a0814001500e0503040310441351144040e400e214522801401041243e10f900c0404115400f11100306d4110400c02c030500d50794820310b881c00100781852030a83c0c0510390708080343c07044080e0381e40d1060130703000307442055503400d0100241c06509616282e0100780d0343c4a6001400605101d03988504440d02030b0300303180c0c00e0844c1c0400c00584207040071035a00d0241c1c4000844104980c5a01c5410005546014085005242a802600f0654000000007051116845552a00310b00031029502032030305011060701d001c05180304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200032500 1250 200031250 200031263
    0x22b0c0f0b041802130e06031e0601120f080f0717040303020a020409031106040309170604170a020a0f080901120b13050702071d010801150e040b070e10020105010303030f0603 77
    0x818401c000501550802c41c40f115076001d41000882c034280d403610030f038603000383c0d100301c620b0300402103146410054400000700c0e090403c42c0c80d5103404030440c0c42e11014003803126658190f094210803c00d0003403c0c1005641c000744059101c95240c5a49801176000030b0068650b5031111611404104281d41214101ca41c150010030b0303854619403c0c0310140050301400c1c0e040c4680641e07046225601848102d00ca581700355a01c50089081c844c59031070703034658013000c0000c80e8089004c020001d016000803441c5600b80c2c0d004240c030341840e03540491424081407401001e641c0c075901c2200421840e000603100c3c001c001d807142c140007c0b80003001c1c0202d8000c150f565900c04004c01d01240b0849a6901403078110045105880d80f060700d07180440e0981c4c031000c8100801807401c000401c43c01d070342841454104032044141e80911450140388040322003010700041d00c0140c40b680443c120303500031804540c0502c5c001d00030003080000e000c0003038000c0400b44400d6002c01c0c2030161b0b031032015449202d9070080d01c1d801131 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200033750 1250 200032500 200032507
    0x601030206091914041409101505031f0c020109031202031008032106040c0c171605060f0f060307060f0e040c08040302010c0302040803040303110f061303020712080301060804022b0c0f0b 82
    0x181c1c3d002600c1c109d448040d003045139200118658405000c1d503040790300400d010503c0c86c0d4802110708110b5080000240469250549500009a00c03601d5003080b1590044056100c1d2544002402a240180d1241896210000750212111141b036003000440814042c0341c0c100750380c0e070310602081c3d400f000b400350001990084400002a0742713070064032025880d12035032820087c0030105a4071400c45a5000d80c0d0030b5014204000c50003058041550307102c200c07860031118504001c40402c0c0d440805008030b40a01c041046694140c034402c00000c040791b10028010301040c190361002900002090310191300550030004a84001030181c02228115031405008614140c51034070202c0780440d864048411034080c003440040d5201080194178010310105081c002b804001d032801034948103541c1d01c12060854001d40500c04607141c0001d503411114a810710708081e580364800100d280f010420380300012400d00826241642c00d40e40b9191882d0f1186031140c4140f900c030003001d06214860f200b020542c10042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200035000 1250 200033750 200033773
    0xd061e1a0406031508070609090f09050303040308250914031209060c010908131d07020d0f0e10020106050a0519050114070b07020d12020304050601030206091914041409 74
    0x4d5120220341c4c0c0c1443e0052a20030b0f2150701c140c2c144400c680c8070000080c007604082c17120b26070a101d04041c00d41140300420642d0304680d201034407400000e00203400e100c440c500040310b0151383c521044034080d50a500c0045401b9805000e400401c940c040d0601c541000c240040840c01c000940e411985643c42005042541003020002d55601241c0122201c0d5241c0e0510341c001a0310b24054500545c4c13080c100945107050900366144200704501442c4296032150070b000c01140c000c03d203200e191303100b480c05040301c812511050710300303c0414440700c0e0094203020f501100a541035018100750b03201160143c0d142640d4000304920b58001038400a100584040200700d41d40c01605010b2000700c009510302d06155141d00d6100028408032501c0001d0703004540f5504145510580c0300ca0b104800c05c40850550806850b001e540d80c405010003401135500046000d1655181102030a050000110152400d0b03150034405242010030200a40200e08000e40400c0070b4010080c0c1c3d61294000c6d200030803042c11300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200036250 1250 200035000 200035007
    0x111191110050c04081606020c01140d090303022b0c020c1503090109020a0308040503010f02030408070212121602030c0a03031706040209040e0307020f04051303140d061e1a0406 78
    0x6031103046000c3c410803001407401c01c1030080c403240c200440240003840345000c2c4081c2c00e00c0c950020b604c0c104a00b810b41144203015840070384601c02090030300004e041c0c1003460150000e20803084956001c44181c0c01210f100c002d609036a00212482d8102030101c40070030030059030399820300d244070713640400580b880c2c42c001400c4101555211041c0000404d40560a4021429810140d041510038000020341800241024019110a2540542c0441c41e51400f501c03004490b0140800080c4075a030700c06140490203c0c10040702111540540100c1d5076864082c50024007503240d05d001700d000740248646c049103480c10100d0a01100c1d0103485414656541c13066114900000a10440d030080c0c0c20b02c405140c9480e02d1103848982501c0f00001c666942c080d00410001e4400011a24071030760030641004040510000710100e03060381030810860402182848040303034010700129400742850001e0002e2400b00c00005030f0594124428068441da40b215050b00040105000d00310402c00100401c202a070310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200037500 1250 200036250 200036261
    0x10c0915320a020609030a0903080711120d02070509070807083c0a060302031f090f0507050108090309090c0f07050d020d0207050102010902100e030a050111191110 72
    0x5604584858609080209801c5450101d40c0300c4100204144240301d03010003605400141e14070056007401c0f0700060081004905000c01050041c004c03a940f406c01001544a000240e0011b00441c0515201010999240c8000080d0030040c4914140044c450402100440c02504141e50725411907440510641c1c0360301014080301990701c1c0d01d01d0306010310000c82103841464900d0090320382000c0d502204460710b140026002554042c9040b41c00c00051b600050080381400641030142d001002c00d40b5440010030b0b19040180411304802c2d6001e0802c080800e0355025220241c845402c6922030201240e41c0b07001e80c0c180c1c0342e003082c20031000c47c002981c02005400c56580d0240d20300e19200540da103c1e41060041da400c50b02507804501e0100c2d09039010300c05400505800c4c4002c04c00401070f03400141c0500c00da150760101b17100e4204001c0485890030302c8040712442e0010024031101060100754442e680c4048aa0f1048107451040144104d110b4940310491610b9500101018070300410f602c0700800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200038750 1250 200037500 200037527
    0x24020310050f0a151722351908010b07030305150d1101080109021c020a0504030807030e0a0e01030302030306041a0a14040c050406080a110f030103060b03010c0915 72
    0x12111500061184139a203410078122119036a10001070310035214141214001038500c9103041c80c0301e054024507403c100004030101d0b0304014102051654104601c20030105445a0340c55141d001c04101030b403042d8900100300103600d1003000800440c0000d000c4444441c28000e0380701b0f48a0030400000030a200b604003e4124410a10816001123202d0004441181c071000443c4c030200701c0d800140107036810030052070042c01211801e624010a104e184100c503440d040741c142c11940e001c47d28148082c403550940c0d02850784900303015a500024100904006050104c1c14800c13905401c0220b40340042c041c6d003504a9506800a40c00c50701c5403010000681f0710601248003400411108003a503640c3d949202000740178090300b0b000714403078000600c01507a5100a6080521908000412200303034003060f4150301030500000003d01c0c0c03c40c1c03a21403809110381c40201c4046000840044207201859010b42e0312118200c0003085411907004041d50002203038070132181081e0210307451129090041c1c10340345151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200040000 1250 200038750 200038759
    0x30f0209040203091c050c0a0308100f0605040806070306050604063027050604080c150106030e0c030d022d01020a0c0516030510020c030c070324020310050f 69
    0xd8080d8081800c03038104603103000155201402d0b045c84846001460007641945182c6180341103115898607545400101c4000d0411a0180c00507107141c03403550081e400f81400c0b1505240680e91045d00410a811030700428035076000301008500505c1c080c0c412027017240d01c054410303030516150a00c15034080e034409110303200500100c031b03100c51070700c4040c1503c3c441b0001d0003030300003805440403d95000c05030726542c0b0103d4415064504001207040000c0c4561300c03d40c032050042d61518608901810811603541c10310084400701c00114029415800aa1070b0840c40070840e150700c51314508050b503441e002107000000da004034081250102c00d41c003031082401d440e28100c0ea440c940c103003d0503003241d22a041c80b2000a00306a02c000400a0502108003546050002d04912070305545605407500c0a00c081404c545500107a000f072070324024001d0b81c18031040502516059541c0317090003c0c81c0e000400108441152003460711a00401503c2070341d0203054290107600006003031170107001d44000b11001d840d42c0b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200041250 1250 200040000 200040007
    0xa0f05091803130305030a030606050c0a080304140a030206041403031911040506070b010609081203010603020304030e1e0118120f050c0d11090c0708070f111201140901020a050406030f02 82
    0xc203c0701c01c414030046120708001d56841802c0c000060480749983c03c4002086010401070112000000c6d8170501c550b000796000c0c0e07403510365203090000d81800c03400c01d1019002d40c1a8070300070300d4ac000c03400522031400740718402c2c14031900ca40d038152240301c02c8480a00044010034640305a0205038050500c80c1c9000e045240b4054941d0f0004011380c02860044610b184c8a10052040b81c1c2e12802e09001040c40400501c00c035021000e034100c150005000383c10801d64040000750a0600c20100703c0da9801c409800c40e603e64503105080a0360300f89802c0c500d0701050098941c000204c0d4140c00c07460032195880403074409001b0aa40b00e101c2440800400d40d010320032040903400c9540c82806d0050312512036000c2c0c0075490301800920814090003008940e1421060210002085004d01140c0b074490f4404941010302d0703454a03180380c1c0c00741850311044d0441094403646a1052056120018008240e5412005641ca80c01418281c1c49805070490000d5000d010801c110750184d08040403101c803444c0e02605 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200042500 1250 200041250 200041267
    0x1a090613021504170c1f0804032303070e01051306110304030606081b1818010f020c0f010612030c080c010204120804060e09012306040503150103020a0f05091803 71
    0x310f4002d40c000300d40c20000d085082c000040200102925080140d406165032410302c5c0c000820410748080e4003040c0004100050105441070640281d040d0003000c9417180b0300c00c80120f080031504211150004904401000ca0580d0700a5040d81c02a200c29082805580e0816a003165060080c9000f291580f2051001000244090051401a0005c20b000b0489034100741100c106050b0700c0300400b8007408018282076858240392810943c0403c808902100c80d80c0303d50794a500601c83c91075074520041c170118a849503d40040f808045409a040c007d101c1e040c1c842c0584681c140151400a0129452049050010340e140c0054552040f00000044c00c0554410028446c440c0c10101140c0410001034107011041d040100e03c003d80e401564004825810304060503495881ea91160000001c40810900c0c281e80c2c01040324040c25000e0182c418404900d4140907441c0f4082c0001c80c404c41518001094280311b09a020045540060040803181c651100b82e4480e0900340e2462540d60000300403280 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200043750 1250 200042500 200042539
    0xa020d090b011d0f1e15130b12190f05160807030209011509170f19140a030509011d06030f070e030d0233040803041a09061302 56
    0x18000c220b100340420010303e800b0070003400c0c01070050a1a081c4140b420901c1a0f520800e81c2010058090084da40e165444000c0c04085444c1080c503001d92100414048500380d9889402c4880a064180c48050002c140c007a20240c8581180078050b09100704224a080482c000080030300000c0c0c0100c0c1a105942d0070102841e00e409800d03040380306c0d55402010b0170021810402d4107a40100710140c040030340070308031031300040503144984101c68814034010f08a5001200500c070b0042e00050300070466000100003105542c000c2891a004d681e003000b00c0c100344502080105804002c42c0d49036076018604214640190b9494a01452a505525a2404c0c48416440d0700000314084d8641c20200e40b06480c20410042a04d0b07001440d89001e50021502c94510130740000f0f916080f402503407041e0f200d00c00501c880000380f0704030b14001c8558410701c00a100511804400a41c0118064070744c030220040051503c900b2450141c49004031a4040400601c0445022215611442c8014120300320841d5004025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200045000 1250 200043750 200043773
    0x90406091b030b010302030d0302030103120c150204080c0316030c0605031f030b0a06060e01090902030a0f051f0914011e0503061504060509040201170c070204020711040f0e060a020d09 81
    0x11203d442d40d1200520961804004030480100740b450107520755810756651680c40303100c40300c068041c4002801c5000030841c2c0c02c0e0403203c2d40e030241342d001c548607039481c0c04841d030fa05098102c2c24064010100c80071000c540611810040c1c07504603070bc02011070b2800e08101c83d00c3e400281282080340b014440300040801c10f03051031000b1070082d00c0b1183e45c0d0030581c1d00842100c855030300c44000d12080c4406045c660740c00410801c2100c089103070058a0b0355600009501910001c03a08103607452034241000034100c10a900003040d0540502c2c2503000c1078503a280c40c1d08503080140d4205c1a00b45410040160030400504006580c882c455241403040d5514042031800c2d6080c2d415a00c001c841111344006414248180c100a0030304489020850400d500080c11004842c0103c41c254986100010030040a040c1111b641aa029208541c0c0e0340950a000510200403480c25100728140007075603403041c505001b1071511003c5100902b680f0348492031164001d601041150588a4440101d41c0c04039030020f0741e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200046250 1250 200045000 200045003
    0x405011125050f090103120e0d050115061103030106210b0301060306020c0f031c02070c0e0106031e020a0f0521010b04080c0d0b0106140c012901030b090406091b03 72
    0x41c22000e00303250030040f241000c6030344603016000c00e100400c00304840c0e0620b00944003007800d02c0c0d014034001c000071443d00f87d00403070054a95802e0250450800400c41111000c40b0169a40d5100d603941ca0701c20507032207100078458040000ca000c404a00184400d40c1d0b190b0103420750090005501920714042420341e00c0075030040e503d8940c0828407000720007041c07010584007a00e00c0091440e004141300405c40001c0d182d00c0c40e859056020804100b0000880502c4000c0c2010101b10321140da0740d24001000b03040004d24242c00054122400b4a601030180299800340c11a91108a0300c0341c80c010007152180c200c01c0c40c40f900440142c510803c60703134901042c40e0280c600700c5c403100e81c0c40d810514020300d0841c004104901a40054503800041a0300d01403090561b4640d00d041070f41c600720815003101034003401e4001c0380703103510304000c1150030009514140c100c078040405000010000200540c11101c0343c0f202940c010300c070b038000140042c1855108100b800c0c41000c6410442441401075945000d050f0030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200047500 1250 200046250 200046313
    0x1b050a030f09081005060a0501090501050d0f091703072c090703020f070c15090b071101020a02040c0c020306060609011d03120a02060f0606031012020111010515130c0504050111 78
    0x1030040c1d0303040408451f0301805003130820404c0d09190a0008000740301c0c60a08225599880f1000000f8402503001020025004102400c2520040544020940c003c3d140300002c502111445000755000b00c00d100c03a200704020a0110000b8800c0900007400c2f40201000201a07003040f150700d0300521900503041c2d89001d059480c0b4040c3c10441d00604a0500c13880b03600a1107018041044603c5c5558116810384da0b00c50101203541e0004e00041c0c0c60000c0842c0025445030070049031002c03040d4418020319032207000b10115a41511040180140d520030f908089002550740a0808078036801c2004030150070401604681c041c500540d80c0c1050b0382c03c42c030007490058200c07505100d10401c1030f8965a4210ba8101d450f245942000c1143d440d229405100d48441a50b214241d5805d42e07006640c60f0b0501103481c00248a1468100d44181c2d0500c044036102c2c1c0300303030600300c40f070400c400451091034900c07075250320744600e81420140150340300c0100011b02040c41c442c000c60361100c510b2210b02c0c641e4a0300182c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200048750 1250 200047500 200047511
    0x1090506130308090f070605130e070e090a0603170901021501060203040e0708010503031602030a02130f060617041112010906020a0e01110d050f0f0315011b050a030f090810 76
    0x1c2c000b05107410181002d111070340250385050030344c000811504100e901c1400d01c1e0307a503841403000c0c24030114501c0d031040180d14102010040c90a8000011034803075074044514420540d602070380042161464040a0400700072a9000d1340340c40e8507c0c004040c11001401200c807082c526142c0c3c0b08008209030130480040c0c00c0406c080005480b005480707900484a401c01141960500f0301182d0f82e03008051700f03000340d480c000448405546060284180c80b035000b410305c001d680902c8032498080e00c1c40c00b1180000b6490b01c5000202e60b40700740c0f802003545114148840d810307100e03602d030031410400030050942c0c400410075082c10b0b203540910485040310f203d0000942c40364a00302014040d42d40c0ca00501d03041c0060160b1a0070600e00101e0340e207615000900301161600502a0803c031103024191036840c1d000000401d010249885100720440c84509a0b81c018118200301c0503a11007801050009005074007808010b40001c0c018034034800110034038540a01103a54401e0481d1400100c02d040c0b6221079680c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200050000 1250 200048750 200048753
    0x8070812070206150405040804080307050d08060102070e0c0306030f100504050115290c01020a020a0204050105180112050c1f08061504060318060504030f180303050a030507020109050613 82
    0x944550003092800540890b1601410308444d95094418640c82170b07613140005400c0164079820784024210300000c80f0b8070342585181c0283d98451400030a0007040d400300008050750320015140d0263380cbd805501030b0050300c422030030711480e030030241c00c40703038980a1100007503950070381084210a1410507000c0414941441c0c04c2c02d600715950050034105405041c0303000c1c00b546041c0001040010441c81e0070701f0016815010404450240c0080c004a550000500b000c5040d030006910304018001c603020440b40e640d400801c0544a041d8082903003001c128401004140c405124118845000d40c045d628104400f0000941c00804004d03400740e1854401e40d0444880d6000d80590741c042d006850703607101c4a00c5c101d240c02041c001c602c0780c141050340300c44814018100d08881c0c2014160b00620a007c0750400d880c014101d078500451f0f0000040c03590142c0801440b0f840d400e14202c0760103858051401c20b0303070b4008078050040280480c06540d05d90306000e00060040020328030070b00403002403461030f203842d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200051250 1250 200050000 200050027
    0x90408070606091107110301110c0703140601080705120a0b01090603060b0f030c1207030204050a0606020610030b040201030506041803050901020c0f100c0c15020106210c0302060c030403080708 85
    0x9400503c2d0040c9032010b0300c9a622062411104800d401a401c94031240b11040000c2c050118554111030400010a0040441e00000749640584e0300ca60303101603c074501030300c8050303036458248182c255035070060008002909042030011a43d0f00303a00242e8204100685511032150001e80c403820751250f03181d0080080c0f1002c0c0c0700b4420700801c00c46000920841c940c0019a80300f02c444042e911480380c46900151842c5c080000c1e00003154050001e129915195181d5001403c05100e900c000d40035140020761b0190041000d00281d913130001d00d01c50240c40c0c0c2d0f00110001c1c000107084c950010b655001c0c03031403841848210a03115074881c0c1c2d202a514409500020f00346032019a2032400f400040032554616030f200d4a40c110144c10514041031b0100c520309003910700c200964003010302c0d00c4452180c16142541074000030250b40d50310b14604c40803503201004041b4103940c0000504245e1611a00340b0040c5001300040030380b00007103022242800c1c1c694071180c0d010391010f541101c40030b00001e080c240402c0d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200052500 1250 200051250 200051261
    0xf010c0503162004020a09090b04020c120408060601021603060f02070f0c05030d03090803041101020114010e011e0e060904031103040605030609101211061314030f0706020c0402180904080706 84
    0x1000e813425030611114800c0a429401c882c020000e4640c0c440303c0c4107d1503240c07a410340d000341c49204110794120030384110140b1340754040e000700001400b44030009030301c80d40001081013212080b50f4509034070074a143c4400380200b1080188121460b0200040c8020440301152001c0c4c46004612203041036103050101480c20300315031921028542445010300216400c4000e0360b502c25040031340540e00703079846c1004034010034481e0313078200584924100200e0141d0074403120b80d0582d03c80e03e208020f403802566809481400321310a8100180800002440c1c5051005489030041c0c420f040050205856403000d5088d600700d82c101000281c404010018185030070101e154114200614050703016050043c1d900c540f0440001c00f4040034a000110082915080d08440214428400c0e603c41161202900c580d1420181000c07803092245056424401d400410048100c1d489034001300320243c0c4030018080070303402500c0e8980241c00310f03244100c41a05d03121a20b5202c3c92287e5a990786e1610b107494180115070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200053750 1250 200052500 200052563
    0x10021501091e050615030408190e1e0102070807151812081b0d050903011b081603150b030105010906030c050a0503042301020307030b0f0f010c050316 66
    0x40c1400300318916080742c5600c1400206050b00c01280c10750319500460441c041c00150340d1103a4000004200c1030000f444060316004008000d143d52505c07114408451000000381c01035800300c203001c10308420b56161b0b8114141c510060054407403030341d601c1440074101100307a8041e41d82d408190084c4202240d100b18414007070442c20034035800300d60600b00070f140c4c01840003a008006240003d90204c00e814000c200c0100703010b40c4030480301c26005000d030040c5681c2061503154001c0d0b00b003500c07901c0c0c5120800121000508195030b074281542c1d41009001c0c60740540c012080605596108a480c003540540352031010303001868180d562540741c00001040303560103510400c201498250860403e991200c1281c51074130040c901503881e0b88450a1030b0f014120a01d038a2002480308820030580306606401841c800e504c651020403ca0440c0010b001d25000c02c004005d6101c60a00c0d10b4680c0c070341c042d40794803540b280241c088a0820790700001e0340c8203616426801340e490501100c2c2c00d1011150203d82840c483c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200055000 1250 200053750 200053769
    0x120604230a08040e090703140714040b0d03140705030c0a0b010506070c06050901050903010509060703060915030209040609241116030f050c070f03020307060e01080a020a020c10021501 81
    0x800c40e03501c0b1141180918018680200038070008200442802c1141038051904840448558001017510f950f40341001c0c80303408105003101283c803256160038841d004103410701606070010202559030880d080c0c1040d1070140b015040c184031b00804a8030400140840760b441c031004001035405802d000001c1c40050307100328030031002003110600040c48445c0e0b0034104d59007801c065850310321450041e40c180c00b40a4134150950301e000100b10400031300040f280c0c0150040d480421039540c03140c603003a099911140300c0d80c140c1d0450800800060078840d14890f4854000d003c00103100c1e0440e81c07542a0310144440218025000d954820700c1c00d1014451207419080e0014440c1ca440f040c504940700a203140c42018040c0b2a0f12080051054003c1e421201408212030954410039140d00d040c2c000e5144501040c1e000e8840c640c00442ca103400b8803003828103100141c442c0b00c400da96a00c032940c040e600050400085005039403d00070103171078518804064010303640150840542c01c410b1902030340b005a0007003c1d031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200056250 1250 200055000 200055013
    0x103020f06090a090504020d12030209041a0d02130905030a170f07080105010c05070b04080109051203060d02061e0a050901110c0f01110106050d03031401080d0e06030612060423 78
    0x1280d440900d06800c4911345800442d6690f590b0001401c2112100b0018040341041c4408000540d4164003d080401e0126003c010a001e840441c05a5486810942d9082440076207680054504080031850126a1b400040b50690180c0d03500c42c01c0d0381210b804c410200d02881118108082d600180550011800040300414607020380024100362040c07088a0500403006a40c00c00e1010a128082c0500148250f90341c6e990740e503114560080c800558240c41c0e034003480c4140750035200c1c3c02c811603001d04e0b002071148482c18119000c1108990018401d0003000d14482d00090145403d50060f220040541c0c60707842d29040313810005050400600b80d00d62140c0c10521840c0070b903903903003070342c0c0d21080e40c0a18008039040034215800340144102d4209a81c00a000d000e01c0003015071541041c4a070000f940140921642e0b589101303691240b80404540c0802d851003143e604a0911401656115100074040c0d55810411400c0c00d0a02c6415107054900507044100c90110894030359905180724402c031f000300380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200057500 1250 200056250 200056267
    0x3030f04091e020903031603020a02100f120203090c01051308060a0614040c0906050d0f0603050705030f030c070b071e0c09060815130303150806040302061003110405062202030103020f06 82
    0x7120302c00d14047c0355440d260b407a003140500d8420802e603103407a5405081200580ca14040140015034036444400000724612000000c0c40781d0780c001e0301d014032a06001004102c4c1c00300015280d9030000e00d0803500040003250005106081040f40078050f401402000501301c2c144542801c0380440350038021b0149080c00c2200c41d101d544132101e94101c64292a06544400f044243d18001e044030780b080c01c3c0807508004021043c08000308000003158400c408032641c0b4954103282c540c503801101c40180142d004503200b00300074013501d0010100b041c41034107400035030441200340c0030154004400607142c0740c0c13840c841445444468494040a000d040b0f0042c81c030515081c1070740407401e1004003007030804040c1c0e900310402c15001e0740168003156050f0082070301298403820307280c3d13840c40116030650040c0f041c00c010034031003540031803c01b0540380c1102625a12140c01c0081c0009080e01800070b9801541e0045686010343c100b20340a52442040d55001d60740754910b00400c585141e041c0d03440f5200314001c000144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200058750 1250 200057500 200057503
    0x14040b0f011b03030609060303030608010c110d080907030b130c06020f0c061b060c180d0803010639060b03030f0412060f09030503090f0a0c0b0903030f04091e020903 73
    0x3003141070440c04040034000f85021005481954001092207080c280301004054041d01310100b9103100000800c00d180342080e049404000c0701da128410303600312003807a009143c442c03a043d0350710502d103100300ca40e855500e60b941f5007034860488901002c03801c82e000c03040c104403c030714100005040510003070060300b01c0341594a072100c44544000703215050000b1010300307000c406513014550f80e0410007a02d00c01d14105d00200b10546c00959400d512500c08041051549401c00d96400d000350010911760444c2e090801c05e442c8442c00e0310b40010ba000107401c2c0c0108036100d40307000505800341421081441001450310b0380603140d0f0500381c50703c40e03001400b0040b0a11041d0083d1411900e04070002130300b0315040d003081d000809102e03140b0500a0b00346048071040c140c0100c01140520600001c0340d10000c2e42c600c45c5903c400c0c244400070000224944200002d90000c009000b8001e001070a480c5400c124420002542e401980204130031501c65601c103400d684454442406080da04000790f15041c1c2d2180001e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200060000 1250 200058750 200058767
    0x60e1006020d1d0907020a0318030f1e30020c060f09060c1207120f020a020127030b0a0507050a020706080709050d06050a05070309053414040b0f01 65
    0x440400c080c00b94803584982c40f4600d100340c0000b0240c06180d040c100307201c2c0251034541058040d4080f80d107480c03100040118503482041160703000310012028442039900c1c4811540e01c0603001c1e00c032035042c0e450000401c904440601c0c0d03810220303203080d50041c0243e042200e4011201010429900495084134442e02e42d841103c41a480c0c1c2c541e42981c4480720000903469026103070345038442e84503036014100c01540c03d00040c413441d402000b42143c0102440300072207076148500840001a040560004015402484124030420b00b06146102000107010b07094085041e41c2d00c19120900a1820b020700c0d00390740d00c940360300702516241041c85d0071100e00000c2d52395100b43c4640c0040011200c0019078045c4515000009000c004003120000301d0142401d00c041d083c00d44210f4019454500031860440c001c0c400e040d003565016000e48a00081184140302e5110182d800322040070340d5441314a2851076490100c40600702c95240200204011000e0200f00c0e03011501e0300b40a4802c3e003851110981e0020b01c103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200061250 1250 200060000 200060023
    0x31e030902120703050712140f0d02011b0f230d0f0f05040302030a050f091309020312180402090a050409030206040b07180b1804020408070e0c04051011010209060d060e100602 77
    0x2e40000411841e2a950225a0700742614840c001c904d52707800039210104903070240700070503030003801509c83c130b104003c1d91105c1c140c08a1011400f0210001c0c2118040d440b0710713800000c0c0845c0c002880d02c41c16146000c90781b1420081f01e0780c9680c1c1c150079150210038484c418030400c0d9544100b08618066401039920301c6144041c07014040c0124501c04458003c1080741c03840e090191140807402d107041040009040c0c0071808a00c603008080c1c0416054205000b5071320501003030100860208050828031000b903000c41500d80c0c11400c1c80c00085403685a42c05034181e498400d40c010b002c20329141c14041210075000c1e26142c20070508409406040307002c16900000d40c1c502241c0d26940b040d4070341c040c0d81c0103a0380741203258105d40040350009110038003040140c00c403503019600a0b481ea8507054007405038801d5000b4a640031218060021a0603c01c1c1240300380301144200051800f684107000441c50742000c105428466100c034000c0c000700a02948050b0490161002c9440b6141411030103034031500708585 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200062500 1250 200061250 200061269
    0x18020102030f0d090f030509040f140c090d05011d0d0806030c04020d090c0e1b0c120f1c0204140405040c050f01050405091e070c120309031e0309021207030507 70
    0x70701038140d083c180d1080700d50702c2e4080015031070100c55250140441e0446c8100368843e500c3c0c01003600c4450294000c4d00e070b89061107008092940e0724104502d8081d0000007610340c009100a00c1ca80001d0720911502c085a00c01d100030440c400414207031103261074601494502086100c90a100c0b258600103800700d81010121b40c00360311034410024070401484081c1c0042e0040703a050800280401c801144d10b8002c0b00428180214050990b20416580c4202c6c0c00030440d541c0580c81c4d1690a00304880076021000b910300e4410301e04010300342090f1f07400003a0124650116400a0100507006800d010050a88401d071802d00031031405481d5034150503c64800c0b10b006100c0c1d11340c07030109a0300c144201e40140100404c001002c0c200032030500c041c00c85600301044d10a000c0c0020800a0303000d03452003280d4a51112a120b18485c1151044001e0008524120b00b80100300440800c0d42a40c260061071071002d030340d80050928071600400504078034000d010b006d1a0440c68041c40417a1012544000303441074a003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200063750 1250 200062500 200062507
    0x1b0a0807050d0b0d060507030f09110415051906030b100e090408040914091e0d050c0106030609050c0f0406080304030204020f070f030206010e0a14060405070207090c1218020102030f 80
    0x40ba40014100b1001a142e020011400400400c0201d9021300e018034042c0c0c1e030404c04106802c0304542103401541001d400d03ca40d480c00e0100d94505604903880c00c03146500b0302c51000313a4443c08583d28211808ac10020662110340a224041c0c0c9845026400c00d0125603900740806820800b41000c140305002a02528203000010103001100c41280c00604540604011074454450500c0b002c0006481b1005180203103001d81000242140383c103180325503000054181002282c0c0d06a0300d07580040d210780ca05540314900000821042c0c03090a0b80140100050702e030100084042041c00550602180d118600d003241c144203008dc00000c1c0c8050781d50540c1c00690301c9034034102110b0b181c010544010000920026100b080542c0880c01d2412036000c6110162240c0b60b21421000340c1c1d90344440901604100000100f6a00d0b003030300302d46d401414a0040c0c84c511500c40340d00100b662404411000418546003d40b071554860384212008085090681c0c1e10840d041d600007034580c403410814500700c21010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200065000 1250 200063750 200063767
    0xc09050d060608061302030615060306010507110607080403060507030606021e2d0d0c1a0c1201060908070807031104110d06060c1202370803010e1b0a080705 69
    0x42d07100c04094070600c0102c0d1501d14243c0000800500d102c00100d00a000e0407006c20003000060b80d00b2036141000604190071603031400e00440300d680010000f40d803a480c1107140c004640c0c03140c10060030782d64040e0031820382d00c600b181012401d40e18090040d10400d0b00d00b54003080026404204010b0040e00b88083c000c10030b041d501c0552501e403400414801a40303035864030008600440ca14226051500d00c00d0322801d241508082d5800703031301c203c1c014090600d07004e00864030140440c0d1807540014410a45401c00607125445841c0b00c81c242c201d4070200c0e4114a043c01010301c200140030042c6004c100034200309046644203001102d08020b054003660f16510b0086400a102003501c1882d103108400b000155a41c1c035005001c1e0350217044c180c80c5181352020001620b032000c12203d01500c42c681a169289860042108142c15450300d0240b80b034815520310301c002010b0500450007400307014803203100f5003008244042035411036002c035011002e0402000c4159a00451115446246401d1154454480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200066250 1250 200065000 200065013
    0x140f0406020a030f15050102010606050403030512100b07140106080d0903061107080c0309011209120804050f03161a040b0c1c0f1a032e0e010606080a0c02010c09050d 73
    0x78000c240e2002030402e1741203500e0810382d048520841da000d81c000c1c0101030b40d6030402d80d003500c42c601015001480400070010311110500c075007500a00d058020b421841c0d5a8207000a26070000441101e8500200030008814182402500c000e814840060021070380464809800303d00700f840003c007100e448010b40b40e81c141c0302e00140d8a0194002d180c0391740e1203208203412038480e0b0080d400305000c101c3c07680c1030003041040c6105103088241e0107800c030616290480270036140d6840c0248200e81c42d01c00c40f40714212016041c009001c2e0118004844080c000061403c006040000c000c40c00496400008100108142402c070311780050700d1005150380c86502400d80d482241d0b25000049006050802e1139108148c00d9100002c508541d03907040c0c02e08904070040540f110341001440c04840ea0405041d0050f180b2280320002e8003a0048000691000340000c0c0d6003580c409910032000700380c004041060b015440c1c01041c5d1401913601c020040503181c2c001c054010340c070700e00581e0300903042025a0020401d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200067500 1250 200066250 200066261
    0x5031b010c14070e010603060f030807080904150b09041404081911011a040506030d020c1504090c02070305061f0b0a020a0611040617010b0f03041e0302030d140f0406020a03 76
    0x8510007955242c030707114070700b58107104c0c82840f0740c50021f4070304100003424003409a4180c05890344480d01720328100c455164a6003131b40103201525882560b43c80059141d40e54041c540b0014040c00140c251640054000c00003100c034105038240e4241d04503002c0100080110044074021050120f10500601e5411402c680e0081a055012065842c2000d00148158400c0c90500b0840d0221070030b1000307603143d50031300d1340f030b500b42c0f410110250740b00c034040e82418500304204210000d008410b9600b41983c8025010990300d428030b1b103d000d6001038a05006002051090950002021312143c40f2602003a0340445209000d2044952a440100c1c0701e80c0322070300c280640c0c4081c0380c00078414082d078404003c1c041c5041e4454070403d0080b4501241c07500011500000b958100c4428001e40780c00c01e01c50350801003040c4d0000300101c072000a01d822080b00c5400e80004081c045000703600640c1c175061203c604d9021681c0586000544215030420070004440600302c4c01d40c0300d60300100c00750b2101004130040e0702425 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200068750 1250 200067500 200067533
    0x1508060f040e030f030a14090c130b0d020414090c010801030b0a020a0c0b1f0f0609090209030a1e0303110306030c010c03030b18060907030510031b050604030609020a05031b010c 78
    0x135000420b100c2d126649404c14050711001b01013084c031036101c510300190340351100120980c0108800b600401090b146501a00100c01c01a0030003621005076400202140d00d1107081b800354005190510006010800119107040d1080c200310800d541940ca8070700b40c8002c02801205243d40014042001a10a80c480300419a1001c041c0c500380c14010b0007011281028036000c1030829100d00005004c00ea074420340001c94045440d0a070300d41c0e0030100c1c40c1000e50b000c0b941c044c0e054418001003c000070743c10513076183c4001d040c1c0c0c0e8641c0301c0e542c1442d0040c01d0711030100907040311010074414001c0c80d96021609818508003402d00c80301041d068074064024114a85400d40d100c440f940603500c01e055451a407500ca13410842e003808081c0e0303446000f81d00b11142501c2e00300c5240e2000c1130500016194090040245202c2002d8118540e9280c0004150b640580c10440e8056100d0b0030032411424031141400280000300c000d05081e80d405003101081e5000c000c40c0d18104030709542864140090110008070f1700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200070000 1250 200068750 200068777
    0xb060a090905150a0c0504120c24090f0e0f1302031902010e03010501080a12050705100c1205012706051008060328020607060b0310061508060f040e03 66
    0x1070005080064036200094404099181c48100080b0394103003920920351011030300d8540303c1c102414801d000c11a4107244200301c4140c40c0c00ba03004280030820707200c00301d003065036162601c0019030f00140080160184ad031158001c08038440d024008601c4440d48950301000c203242d41040c03607885c0103070219403005550002c3d404d07000f041f0f0401500d45902e05a4200030b4001c0c0ca801d815040300406040c00c80d0401d01c41c072455a0405070345000040c024000000310000d103854180d080016a8880905000c0d010168102036982ca0301c0c010034854001d55240f803581c008150070042c3e0361400c00103851005a10003c480c0d0030140003202d84040300507902c00c0c8041c0c1005800c80001e03498010014204400945446129200d58408400c4060000405034401682083d20014401c0e080d030030301519402c0458129034460310340c02c0b1205a40c030b0030001c05554050180011402030701e44084070350040320b0f2004803401c20406004202031303500c80c42442509000700340d500003401052940c2032400d5016100c1d0680c0711 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200071250 1250 200070000 200070011
    0xa0e0f04140115090806010e090a15060e010b0720030a060608101103010b071101120c02150c0c0604020d02150720060c0a020f03010e100524030a0b060a09 68
    0x981c441120107043e15256664004040084031059a00d0380f21813180c0700e05940400014003080640381038541c3c0100c0c441d0120b03002101640d540c0d88819481030580f045e26513403403800308040c144840c149801007e04124075440c144035901e549400551041003020141100c000e440403903101004030151043c2c019408016080c0c49544140e201c0440160034000c4900b080c48410b6006011001c0303d0403160401d4085280440559442c03071603601583c3c1c0030b411f1103441c009054880f1128081c8540f03500c001c0d406032000a41034100c406d0b8481025000c40c4032240c003440381d850710319800039005404c60740403220a424000d46100240005140c4013810482140118508003008810000b01080740804448040b200d10803000b03004550044a91400d5180c1c0305600b58009411b0100703031404111720140001c182200c0310100107180800200e045000d040e0340e5010070100d8140799070070034004d003580800b001e1500783d40000a559040444800340800d10a03001082e13007959800e00c4203000380b0742c0400c00d101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200072500 1250 200071250 200071271
    0x20a1e020c04230105010302040b0403030311040504020325110a0f05030408010e0a0309091404020103050405010f0204120311160b0d020921010e01050c19050f030a06051c02060a0e0f04 81
    0x40c3c484250803c0b40856686100106241d0301a009580690f44418441410180346440880244c03030015444d03413030591b08100115072a12580000c5102c0c0e02c04802c03003140301081a621181e49485a201003007040030040418660050104560b541d40b50800026100c16445091103401c40c41164040c03070082d0300e040c01948070300c0c1d000306251156500075120019100c0e950744c44003060710741c11101e86c184414200002001076000c0d500c40340d0050f000300000901c99503d00318a00072640981c0012141d10203c940e4582015840104800c903034211300c025111100700301c000707100d40c01c6d468003408050403004a4a864112900c0c2d05032250800024502c0c083c1040025443d102004090b29070341455013803604400310f40505018035409101c042c400c0307510f090100c0040d00032107880102e032a81004401c0000d0541500b904001d94001c8140040004059103804208030394500802c6c1c0d981c3c4071388046802200582e0b02d183c10740310040b0203402c050302030615200c0001e29140c5406020b42d4041e141000515 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200073750 1250 200072500 200072531
    0x10e0d030b030706020109030e010c1109070e04150e0103030302070f0501050c0301171507120605090406050f0105090712150b0a11010c090522060b07050307030201050a020a1e020c04 80
    0x1003600c48264250f894494482400b20300b41da00c0f030701014011a0206042c1c501d0b41d4403c04000250358020b0702010100460100003c2007a030090704c0c40310000d034034000850320524151040c2c0307036994000c0e40b240001500c2c064200713482e184148809824103a001c03d0500501c03011101d000d50301540407008002d13a2a041071601c2c01500207014036235a44285e800384400040c4000340004c0c00255a110309038660b5241c410032214420903036204011962540c600284a45035800001c3c0903e01c2120042020301e0b0007000400035440503072001d4852601d482c01c0c0f0009541000403c003a45400301300102d83c10008080204180d25140d2082298690010711040081e5204640a10485c0440e00030321515200b00c034104e443d18528020150b11046840555203084407840c103103510740b4240031010910558440c00303143c01360400201502c1541000405100b090350a04c111684865840030450500c0b24403d00209005009082403958000841e8031210b614020400c0d140980c03001007081c072540c1c845401c141d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200075000 1250 200073750 200073761
    0x30e070b070f0f0c08060709050f210f010e0f0304030201120203060f0901030f0506011e050405040c0801060b0a0306060305010e0103082b0204031703010608071b0807030e1c02130c02010e0d03 84
    0x2500c0340c0a644041f401d078520138200b51017140d9000380900d800405000c00c02c05e040e1500b101c1803181e501d41800188910500340f00c441007840320000000b4040d2840c401641c2428030003c1000d541d9001008148010f0ba00b1100b181e900c03403080032006803240c2d902c0004c5206078072500780041c0c1c0290101c000000b0040c10b1105104114403031025194140da1719020301c50340c00003000480d1030485103004c0c00d0206040681c0080d500501a0040c2450569a1a0020308561307098004010902000403640740075501402184000c00340c0f450104046d626160705156000c6040c000103020300c100168804074a9481134540b2007030702c80d2000c0185455080900d91000794800d110844503280c003a01c04402c2d448004041d01d040710741c10388484c1c000d655041c40480312711403000b4503500440c2c2c01400d01d6002c00c02c00405005064443e0711043e5100c00f946d0100540c4059260548808442e00d540410043e100c00d0103c80080b100d05c0310120f0205101401030b0301600d546070700c04c40c00d440f1b04140440d640381d040c2c01c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200076250 1250 200075000 200075009
    0x321030608011109120a022d04060b040501090e0105060406030f020c060712060504020c100518030d1a030f120901020a0b090a030f11031207090302060309160501030e070b070f0f0c 79
    0x4000165000b064a0300c0d03148504010350f108803030014070391089004511414100d8000140802e6008c84407000900f11001c60304981024100400c081c0640e5800070100b4010f4040650071801d55803400300043c0051080740900c10805440300c51a050b81c3e01603405480c603101064003910500e1030250070041141c0c5070314410120303c03420000005100e080a02c02c940000c107032000600f0a5002041e1180c018000c05001b41c008600081001c106200e8140054050030800c0c1c000410080300801e5440f601a01c800031480c4071f5001050410107024000800700580c0301d100200c1519203e10a006030304203200300b48064501c441140c10800c0480003c604580317118131a44881d4401c41400f80204c0ba0010b5003101d10026503c03c00601a82d202d403c00050351107040c3d03103020000c2d26200d9001c0380b0581c0069070200395075030100145500414a0055032030240900b13280c1088400a00180159078682d20b220341d0750744650024074070041c00042c01c0060b803c81e80003d0711081610040c42e202c02480641d118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200077500 1250 200076250 200076259
    0x1b0914070f11070e1305030d09030909060e181618050115050f070602041502030d0e060c040b0c0f0319090902070804050603250309110a0321030608011109 68
    0x202450382500462000b0382ca01c054100400d180d03401c10402500402d00601000e82c2c00c1088049a00052810030060003401d50210020410210300d20300900314101c0c980103403034220304108051190702c04440c01e40c0d500054003503c111031002c0d980c0d0080e061101807809101041410800421203c00848151411017240701c0c007001142c0c0e0b80c15904030300c0340c2d00007958000520100408482445034034040c00c285030048000501d8542d5601b4064101d800c0c02820f2405a00046a00140d000841c440d0f4003010304e082000c1c05540c50010103080e200c1c840c90040711540f210208099108090800c5610140e03600d0f1011030343c0d1a0403d2192000c2910920b81202c0010f00003440400d640b0058000e44440d02c2e409007400381000d003880e0030008144c000410448000700ea90005065001004842281c0c608558070002202c01e414104800032010b4000d0003401410b65160400004100049100070340f4041c14a44c2c040c1401c0c40030440c05880c050307011420541c00c00075000c41207e40c910041207802c0701180e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200078750 1250 200077500 200077517
    0x10030507060f080a0c08040311010b04060e090f0a0210030c020f0a0302071a0c0d03022d0408190206070209060307120317130c03081602040603120201050708131b091407 74
    0x80c080c00170741d078100c0c01c2c81d0009010480403c000030301071a014088018802c00100340541c1220100b002ca0740d10303500622810101d2070900c400e0032014000301d9450b6215a000d408445031507000310380c03101000481d6000305a50b032803031159101c2c401d200c807001600743c0e103090b1940c00d202400d00a541d00710701d008220131824030146407040c210000307048405a6a048000e0401d41607000c000340c0094100d400003402c1149140112041c418041441c401102540c1c6100c0707445609029003245043e1020524404a2280101c51005680d48209030760000c0d904441d000b585603501c101290a241e2503a11110861021200e0201019000bea10980418110a1020711503840081100c0c0d9007808140160820445550600c0482c440304014003074050703a8008240790702c80d6a8042011101158001d584411800c0c0c40c8202d401e034280186904a01c50b850b0111260a20100c0200406131010300280200a4a6200c840455250341880014450004100004020903d68458198007151031300e00049955 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200080000 1250 200078750 200078761
    0x305030c0a0201110d17040602121003060608010902010806060a05040b0c070509060d08030a0b120706080a0f0e0d030b011e0806090603010203090d050f04050411180901150810030507060f08 83
    0x400d00070602050380c85002d5203051000800c206c031030242041c0c80c0103408201c01d1410b45480c124407400344c095060028006407940c01c10300119403490304101e45690500e201400541e074845600c2d6000074040f1021660341d28903c0c0251201e11455002e48440d0802042d4029a0100441d50078100c0344203458001d841da4441c000c01c444034950a80c01000c0340c1c2d0030301c049840084950b00c106401c02010344600050040407109602d4405141d100000240099007041440b51542c0140401d214001c20f0610800070340300780803902c030203501210b01d080603900d061510040c0e02ca169512502640199010b08a0b100107500030000d5500b2501d4501505081011071081d0a05108407031054180303070054061b10070403610407103240c0d020b42009003120f0028440407505075101e2144495130342404c14550744d40c54400c4010000e80c0d00924000b07100b0401900100482c040c0d940041031005201d04e040c514543c0c0710b1048002c40220340e04050028411400c002c80d0030754101e859848040344a80700c0c5885d50b0b455 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200081250 1250 200080000 200080003
    0x504080f072105010b060417010605060903030f031009050c19020a050d030c050c01060b03010f0609050a050108041509060e161d0709080f01020304020a060f0806190305030c0a020111 80
    0x441c030480c0d58101c108000110300c4500202c145807500c3c480c03000410002c500d0400180d03d0342140d0032038807881c0d6141e0501c3e02444d10074440d200050900361f4000d070406980a00107902c900541425038a000f00001c001007283c071041402e80041c1002c041d041010342080e18540503a0740001d15121002e180070507800c0d41c5207000003000010541d00c800140200740090070118003818100b000300c4144003040c01502c0e0500002e02451018205502c1611340341d40c5460801c00e114101980084282308440005000355114900d888095500a003405040c4d62502e240c1080c0d0304400110b4610701c6454007807003208000e49504010440580c0300200c92140c00111100c1121240500c04c00040884200980310300d40040508140d01c50401d041c1940c20303036940c00d150760505044040100b1940d500004001c210310700052208081d14443c075144445804550000d05002406410148120100504260012040c40310744015682c0b100640ea2550b480002003941c1d00c0c00014100d002c146000b00200c010300c0e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200082500 1250 200081250 200081263
    0xb0303090901091109130b03281112031b010501090605031c1115220b060d11040903050414030a0c03080307030209040614010311030903040329070504080f 68
    0x40100007054a03460b002e0f915000301082c14641c00c40e54000e000030140c0c1d40c1c070404060028445a1004140400483e080600741000700c3d0011200c04c081d624903c40e1340c1c101030248101140e0008090b15483c1001b40001c000b108403013a8030410340300010300700550310203289003041d445c03034004000c0c0138690300c0d40c100c501510b05a0080d00d4250b40008d50a05400011207064400740925080000e460800b06107403a0810450005041e01b03400030b0001e11141588070000d4201a2020069040c03902c40f556903040802e80f000b40c40c851041038044601e400f4049070791000080030f18010b00800c0b84a11614010b05990454440c844040d8290006100070b4107001c41c40610581c2c0c802c00001d549401c0d9a6044640e80002d003407001015424000703030000780ca0740d00c12440030709006412054040e480400040640d48114000315540c01c0074014859030305000030507101500d606c040c0411200720300c03030910360381e410050201e8004110404180038103a0780020062080c0c40210050314803002600e0a026035900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200083750 1250 200082500 200082517
    0xf1e03031a15031b0304081c150509150301060f0608101203050d090605040c0302041506020c0d06020708040947040207060507020d020c010305060607020108041407030609060b0303 79
    0x1c00d940142da0054201500455000002e00e440e0b0290003000b03052802160411101150700a0300012000c13401c0702500b240845041d0384050900ca2140c600740b0307111109103a445098042c1c8610004076030425410354940d030940c135002e4000c110141d5548809041d2104a105400100c1c440c6000706c1c8154545120010a581510b010710444500c1c641d1300300c40680c0080e9180c10965580e000302c400040c901c1c00b0b0240100d01600d55043c0d142e0075801044129184800c0b018205028614100300303140d0003148000c1207220031140c0541541e0381e400c01a000e48a061030003090b0f40340004000c1104006948a81d525140700b2414500000c51242d040195180d0082c0c3c550100c540303054048402c480030344400490050190001d410400135649070310540780b0035284103025800001064000c3c6904102070840a01e0900e0300f800b0505181001ca803203442020000b90400c031034000080c0c2406805ca1995107540740d04e80445900699a050000080451842c215600760611103c19070901c2c000080c0e44014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200085000 1250 200083750 200083759
    0x9051605010c0c2d18050a0b0d0b0a1d0703030207060504061409120a0501271a0a02160302150a0e0606010e040609111b0321040f1e03031a 61
    0x290800b01d0040320451a400d00c0c0c1c6190300da4513804204444541004030040c410100b041090052000d408800e9400080004103e0307440d0554403030701c0d07688003c030742c09000750418441358040e00e0f0308017140701511461906240c03400544585203201170000a5034022680a03900317541c3d1941c0c8401086425104510404000450f80e4a6022403108013200811000c01c0c01002c00403440d84a407101418582d80503010354aa9549052010348218071800b1240d03920b5001e003102e49001c440c1e5444c243d10480c0d001c105c0320051a0940090728076440c40c0e0454541c1c0c0b51030307c10880442180d24009550340014000c04061034044000300d1082c0c80c00d40600030070448010058040d550340c0500441d510340000740c1c0d0942c01522a540010206040e01c0b074601c0c2e2b08901c8000f2070390380d01101c103c4145070180c9910803c140e402001845120380c2c112000c50301d039a152003100301d81511035040c005052800c4500181240125215480d540f52a26090b0801c0718800c0d03e00380010440c0b0b20303680d480914085c401d035420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200086250 1250 200085000 200085023
    0x80f0312041101020a0f030e03061008031606060b032401020607080c0a0201110d020406090f0807050607050102040e0f0402010f0206040320031303030309051c0c020f011209051605010c 81
    0x1440b9000d9a20b1100010702c1280c40c10001c0d5103031407010740074100060740495140c2c0d00d07500e01070a05110843c2e00800c100c1040c18990b16001f071541c0d591041c01400d43c503c0d07500500e80002c00c00c994000c48014048141c11039142c3c28400c51244040c50780c4040c0c002c1d005c17010801500d03954008508031384602c9164984020300e03035907861a00a035610440e001340031550b030b82101268021f0420302401c05003064680040e1038078100100604441c5181e00181605504160304000d258800a501010b8480a584043c1c076200189005c4c0e01a001755000a804240e04104100f450940000510b00c40d80c000d1382c1703043d145010721000341d0700c600041d9000f41c0042c0d40d25440c9502d94892040a9012a14110442c0d03d882c12030000c0141d0300c0c1c2e0301e40003240041d42740d080507003e0280030400c0750500140095a550441503441c4003400c42ca02c1c00070024000c00222808101d580e000b6124500f114001038401e021b80c200916145803141d0460005456246010f0f60100d41544070b680c0c0d0194070395000014290 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200087500 1250 200086250 200086253
    0x60f02070f0e040f0201021515031917131706070e04200307020307050a080c010615120f0603050303190f020903030f07050708030a030606020601060e010215072007080f031204 77
    0x4105a0040c040e410b500c1940c0c00000c1001452010320700c6180202e403649c0402c02d0b20750805051103202c8a000e400b220304c0c1441500406c40b0640400424020744003242d80c1e47e10001840d0907008559840301c440100d4454034404410380114030948a8426a5508415003a00e041007004070707040b401a0b0006540c0801c481c1400340d444000858014075540110b038100050703607442da4a070008540d411107420502150740070310340380b00740244809004c01c0340640d10b81a6003a00020460b881c000802c040071a12040c1c3e0b080c80c000b1325030180307010b55007120580fa0303286884552510410fa0208150800d10b281000c0140706001d14403e4840c0d4000c001d01551506010305100c8000781c000307080942d640e0040520025140b84200010815524a51400708141d841c00c10081e007012016071154040c04803071507401c0101e0f80c0c0130410645900030343e00b241070b941c0c950b2003044559a010701c00e81040c80c900c1007002802000c0004d03141c0101c80130b9104445d80180c08508054030ba0107140240c0c0a80d100c0d4401150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200088750 1250 200087500 200087513
    0x106050409153203010f14060103020a08361c02060106050a0525050a03020705041503080c150703060f0812120a020d0c05091014030a18020a060f02070f0e04 69
    0x168203c070380c50b040b00b242c0081000034210786118000c5808640c0c2d81403111034028542c004a13034829001d003030840c106143c2c004082c0c400c15002f030000061104107007244d0402d4042c4044801c051001401c4d4080c5c3e19605180d00d540c0740408100400314840b80214110a00e200181ca981070b034003c0d0780c4079800e0071403901c801d03155a040f805c01021403403082020b2502140030070212519490085d001840ca01101c1d05001c2d04000c11600818015800c0c501d500050348101e2411504a80d0f014a0180d501e85500d01a603017003a03845410940c0e841034140a219007650300d40c0210301a1440819804051950b91007466600c2203690b41c40108441c080c028006803000198225501140098001d440d02e180c1d10810f80459107503041201c003050b0042034044a41c10f000f404101c265a15080c41000c0b006d6810300c94103076000041c91a104603403a41c00c03095010407080441c0050a5018101544280c1c0320103010b0516502401e071800103105107032000403151024007180089483e450180605911103840d00d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200090000 1250 200088750 200088809
    0x606050d09060204030816021302070c05130b040e0f010c03020309070b090a080a030c1208310209040b0a05130f030c110904110901050612240603010605040915 70
    0x54420b40c2c1c2c24030002010131002c60042510130401803d00408108510420210b050084840b000861040c024900022886e442003415110101c0345920050104008000500364030358809402ca402d01c03005080001002600390600d50f6000c00030300c0040e379502c00032012400200d65902c02da9000102c200101c1123011300400d00c2c41000b801150141d516040554070f0030718401c0c81140041c0a0040c100148181460014215900307131500e0070480c101200ba50510050002c64040b03000a12020f031143d00c600340c00c1c207c80159000d80300004070302e41350400001c00d001c129004078101d0b06200000c1c03251100205000245644003007003119644298800b00c6440161800c129606403c001594180e640c42e01c1d500740c4142d01c81e03103805190490300000d0201a600603803001d40214828003082c070f04448440100740e840740c80c030031410034425141560003404075100100f0b9030700400e0010001c148281d000c4004e0054450768403050014602800301d00d21030380c100e4420004ac0c00b00704220703480c3d45180800da0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200091250 1250 200090000 200090003
    0xf0911010c030c0f0309270606500d0513050304090c090e012601020f0d050c07080c060a0501080a02010c0602090f03070909170906040513110a0908100606050d09 71
    0x12070081d107e50f00c401c04103020160214a001c50704001a030303441111302444000d0029450170315849104400d4401c03203d01e1401d024070340c0c0107440151024044000f662205001c0490040300482a4910312913540c0f5071041c042c0d1440c0c01c0c2054001590060706810864080354054019031034103190045030700007800b5100e07510081103100c2c0b000042048000e0012030103407511501c103081540345120080e1000e2403551148815034018050030840c1765014050b15070241d280c41001c6800c0d510803040c0b000910900c3c0006288210105081001000c0000c1e064454400d030702003000b0380d98868501c5562254a6000240000c01e900340c0740b4001005a0060511140c02078034002000c0d40110000b402c1c4015030300300400c0c255440752284240309440003101e01e03100d020303012145071090038000700f521489103000b00350081580046134403060b007859016400c0610400c000035212600c91310001c21195462240103501d114001664501001904c0380c54200c07011a181c29160201d4100000301800e41d4400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200092500 1250 200091250 200091257
    0x21e0c060606071a070f030e12041205030408030708071b23031906020a021501030f02090903121311180403081e0103120206071d01080a020d0f0911010c030c0f03 71
    0x44c0c40403403581c441c02d040d01404d541d4682414107002c0c004020104c0c0c00c500d5548134154440b060030005020b00070100d409954290321412281c5481c0d0501a04e180f10f82d80c0511150301c0001500c90031f0110002c042c00c0e078241706404d00341070140300d130107811900401401041d509205130381c1d9405001d059001c0c490000040038090701c8000c45011050310380d400c0070f80c005071a1660001068800d1907818003903448100c0d04007007854195410754881e50841c1c550864024003482000e400b10700d0490040050301c0c18048c14101261413031410040d9450a220209021111003035490f0000e400d903c1d1000f4555001400d4140845245d03445440031104510302500103031940f0340390b0650700396401c0f10407100e81c00780d401110304800f80c0d100c0842c001d03d492001402c2900308003a11300c15041d81e0480c99aa6a41c020007460b002c1c0d002c0d1a100e41e00d20080c0300d062000300c2c22500c1c1c480140300280361a0004c110060040b4910322040540c140107580090390340c00020006020554010001203803540c4043c1054020314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200093750 1250 200092500 200092523
    0x601060813020a03061b020c0a03110907140d0f063804080a0303060302330f04050a060804020103050721020d0b100c050f030403120807020c060d021e0c06060607 71
    0xc4a605c121040d00182c400243c1d036141d0900d100030b8040201c03007010b45007a241000c00c03074510f469492031803809060041c0b1400120700171601035845003034069441d088205d1501c1c2d0720103400024900804100c0e034a515102d0514100145800700c094030441001c140010308005007489001d207103400c0c41c0000340c44000d0601070002003210382003001804c1c0818400d4800041340d0b8203600401482d03410f40c0d22198070110385210140c2d01440d99141e060509076100d903540341c41d130080d508c0126144c00750b0380003e40c026030542000210700f40d2002c1440d001d5030003a20100203e45901008a400004401d2190040c040c1c1d82119090b40489500030201200d00c0f50b000179098058200141041100c50014000298001c1c0c0300c07c203002c401d01404250790807080c0194580351a42c0c0e221404d8402e01509801400203050001c4c0c01c460091100d1040705000801c0e135030781e401e03101c6a06402504620030415040c0510321004410081c008110b0300661012801042c943d0754800030003440c0e034400034084a9020251 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200095000 1250 200093750 200093753
    0x1b0d0f0803150f04060302060901080a0e1c080f10050d0606030b1e09060709091107020a080303010f0b041a070311030324011d0906150309060115020601060813020a03 73
    0x50155000b80260200c0c0c0c84402c2205041204039040121280c2c8614906982000181e960004540880a0a0a002c1c00964400340c1141c002c19550380b1b0003009020300b18808900003844a5076071a842419180c00c03c85442310920856a036034102c40d200030004070740c0c409001c145004040103004500c07a01000c2902c545a07620070308110029a0f100b4000b002652031904400c403070741e40c0b281d40018410000d107441d24000800034820440c91040417049035803039001000c0d112405007251211a00a055002e01540d030b5680b043d52903009100c3c01240c4041fa42000c40c00c0308208007190112040450100500c00b02c04501c100240d0003600210700340700b01d542070300d0700661091010b14890f4030b154003642110401107402441c00c0d1012001c80341080710068885401e009280540c590219041d1100b02095807030710f01055240318401100c120448011041201c6100c0004050b816180744512004d003042019a05a07910f21080c012300000c2014600058200420030f416000703980d000074002d15280b5903d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200096250 1250 200095000 200095013
    0x31205090c03010e010b12150114060702030a120813080d0506040e0a06020315180703090503090a0906140a030507120203010b06180a0510020d030b061902030301080601081b0d0f 78
    0x40c61400313001c40e5180c0c03c0c1030074640760000180301d08480b50b801030003400e902c8185003509918140504000d000410703a0414054079180142e68089601134200c4d00d40a40c1c608080008034203a40d40c200000340d42070300049101d030b0880030b031002d015480002207052000c5440d182001e0400100401d400a41d9104000c4041e4010800390244c1400b9150040e501e081000d049481400c404000c0f0b030095000c50042c08145840e0390b40381d40d00105c82c4c07a00040d1090686042c609522610b22400d0303012100203000300d04404650301c0340040710b1500401c034444540440c00d20600044605c001b07043c1c1d4100720f900700040280c240c044441c0d42e1006000050000e0818006070054102c00401d050101d94100080d000c0c0c1081c02e81d0703070042d10b82101d0101d68140110002582c03010311140e40d100301900c41815840c9a2203507000e4450701d840310356034400c2141c00800001c1d80c0780c2092043c80d6440c0728003400000c1d00040030908204000d1745e2402008540c107810288408400030800840b03516102603401c102040e003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200097500 1250 200096250 200096261
    0xa0f030e01230a0b010203030705042c0c2709071103160b0601080a0e03090402090f0604120302060705090d0b090a230106060e03060f04080c07140406060c031205090c0301 75
    0x5295465040d2424032010030022130b49030161590641d401001070000741d54001082e10304854448040004416515181e090b9600001c038559200c2000303501489279003c22800a0048045400e1014004602c4d00003400340004503c401039420400b2003012a0200307110340900c03181d42c9001c0302240e24040503c40680c0e081100c2010079201d207804001440111340e40102c1040c2c008464083c140090040140a0f070345034494101890701c141c1d8000340840c415200e5031180f88000c00010501900d8907921030748140014000b104c100d006000c4c00000408250080c401d4600c040c002801e042015409580c40143c40f540241c0b45603e244280081ca40002e140012800e6403485403103404580030368101c6940d401c2d2180340d0000c4003403141f008100d880319100021101d078003100c3c52640175050b40b690709010703126201e010031007040c03402024408541400704070801085c1040a507410011142e40744000c9419851440c001000628440761258142c20203410103500807020000303854000e9422400a800c490 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200098750 1250 200097500 200097551
    0xb0304030801050907210c12110c0106050603010b0d331511120a09050303030f0712050405060402040f0608071e061112070c12140606010201020a0f030e01 68
    0x58a4000501641c2407071803802c1c0d0440a00d091603c80002070362030544e26101b035000b203e103120b50b5481c421301c0c2491003042401880c10a00000304901881c105c2418010b9000201d0401650f09214000880c2c0c01e209040b24102e4215901a41c144001110140d01902c451004003000a00280000000201c017014140c150b010b105200300509142c03521061404400c00c2e02d80050003080d424010303c4000116040ca04d641c07000030350075030780e0303c80d140b064a071100c0540140ba0588000700c10801b14009514406000350083e4858440510300d6403904400e80c0c00884000340f094000002103401030910750048c004d060600e26001c80d0f515110b40340d60b407504803141d01403505440311140d2074540e075098030400405401035207854140e0785102c00324a5038401854000c84d42c1d1920018650091018008500b0080d00842404104000c182c0c2020030610428090b4201c0901510000c24009c0d1b005208039010042d6a0b280c0d45130440d18454280c00a1085840f01c40c1c480d52603552482141d00c4491080e880d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200100000 1250 200098750 200098757
    0xa1b020a030b0c0a030c0e01020304050f12030a0810080703030e061806030a1409061006050f070501020a03020703020c0409030e040908071401090506071b0f050c132403020607080a02070b030403 85
    0x41644c1c000090542ea03d100d240c5042c01030300845810306c0d90b03001c0121416608140c901e201a011003102285590001907214201c1c2d020204014619643c00000742c0d0043c00c000c407000551a8a031010588c588a0510006011038000d5440b09664205500036100015040030134120410702840032072135a91003102ca281581d40c2c1c522030965a070019412043d0011440303001070403645040d00d51011444601c4c040e220601802062280300e807c0440d0840c3d4800341d0110003951280041c0304041c0c041e410200085002d03000e12400d5540a050912071a8034060b016503981409003462014000100001001940c0442c0c0800008002c102564001e60f040074010000207220810381c109581030a80c054441da013003150820411504418901c0799407540f640029140340704c81d0080c94024503003040101c00503000242c511203e2082c0040b54011452900c5005400b01c44005100f22110000f082d800001e44c0b00340b05100c0d41d000b00f030207030307028181c48901401150003954940e0201036864100300e5048000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 200101250 1250 200100000 200100007
    0x20d080408070b0708030402010c1b0e0610020312071202070209090a0c17030304060c03060909050c130e03040b07020d0c090b0a0f050915031213080f030a1b020a030b0c 74
    0x340d8000300440b0000340a10707220306041c9129541c500c0300902c400f40c0302a0401002d240d00a05100302c18006a41c00341520a460318036070b03542c0030111051031007151201c0c4542e09242c0c80c00c5001e800842140c003a10003004104150341e450003000e0722199221004140415400d202e46001601c4a107002c40c0164041c40c000c00240e810f5280601d0100303800d40000c80505000c0c24911442c080c0007054903005a88414017043c200b0110000710014a01940b20385281307030600a00e24203121020511110350b80b01036806010340005864501c080d51540c1c40e0b030304880d600800003089078074561009409410702c0201040f403109410340307401c080c20a45030031580134150b13503605041c22450002102c000422116888100746803038580015003c1d10000d124401c080c8032490202882d03a801d0004c1c1c80d401e209a072485403500781d200d40d0710101e19000e009004440c0304071614803000c41000000e4821500c550340d14050001c514a42d490704d17803042544120307004020413802100044100d6601ca10070703100c50140a46 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 200102500 1250 200101250 200101259
    0x80415170606121b0d02030c0a17070e1c1406160305010e04141515090a0b0306130c0b191206030228030602070b0106020d090e0f070c020d0804 63
    0x40341800039040e80c0c400c140c20440020269003050380c0d2603100303007120b03150191524030b03100082d1948101070015562610002c100545602c2d110094440b01003141e446a400c400700411701c03107804100707507400004540890440076036442e142d69030601e46a101c012a1070501d0883ea80c040c01c0301040b0f40b01c50f0040d04101d0401c030000c030704c0e40140c940d20300d098a424001540340400040182c00c01a0019040c901507115016440030b0420030284042c3c03e40300765803503910f000c5c42e4a030b5220380440d440c1d62280e107005000c90440d01c142d0280282e0844c0050203000313283c41d0b00008400d10501420103d03005800040700084440d4500c1c040c00703c0107000b61040900250414005000c010105141803c03d85020800d00141e03c50522203001d00c83c21880000100a180c00d00c4030029040c0c0c0d2000301884e00008000082009a444c141d04a64281e0202d80a200400c102628515a13a0080c0c10600000e0000242e1205c60501d440d0780165072800c000380082d129801240001c034402c1c20540b0703580e400003000c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 200103750 1250 200102500 200102537
    0x4140d020303040e0717040c0e0405010207020a0e0714090a050d1407061e02060f06100203070807080c06160c020f0424030b0703020406020a020f0604360504050316080415 75
    0x1800c1e84014103e05c005490070342d4690034288d031f550003075406003c411800a01080400d40c111130301c42d034004000500c0c0c4ca80e2005003044400c400c564150004500b4070711030303440703a0301c1c0c3c400d0311509117000b850b50380084e0410041c005000c8031102c003618003071456810f5220881c0d0602480024200340d81d030f52566070012951950b100303240b40c041c5408640c0000100041c0424200754160031202c111147c0c0d19610f08884101d08d5401804005001e4040014001d000c100b415002400c3c80038081003501d540390b0b00d0b015004035038900080d070400440da0100740c0b4001480c20f0850034290603002440050b00385890030b150002c402c811002207186902c11f0500303000b8050304001c5070360310919034030341503141a0030701c1002500d801c0042d0000b40948907603104114241c0d22a13003034074050b01d040b440c4c0d04440100c858070b401d180d0000840701408140301640740720003001c85004043c49075030024015864901081c0785881c822200b12810340703034803405200100b0703e01c1408036140729081c440c0e070369108080f81424090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 200105000 1250 200103750 200103767
    0x81315030b010507112806091503021e03040203100f0b040b03010b060904091a19050c030709170a171803060f010e090106030503040308181504140d020303040e07 71
    0xc2d06000c000e009040008030342d007581e144003400c00d84000c00f848014242c41007100402d031018540002c1c2c1240d0115030f46030300c08105021180c3d1a814246441e4841400341c0482c0720b40800c00024500c2c12854050b403220010045400a10143c01c0b100441e8905c0440750407540e4041c0e04070b000301d031a210078900c580b8280c01042c1c010316045008008044403180003820300d2058200c2d0a005940b174090100a2114040c01c445080c1c140c03403c4099907191190000d4289010400701009407841c0c0400318040444d10b0050b2482000242c4805804504112680701d144014060200031485028035003000542d02d0714800124403483d0355025103450390300b8181c0003040c110b014a14080c0d4070070410009000004106541100d9191049002c6500c60109444c05884d843c3c001400500c0001000000c0000050091400b401310300238610b00c21b01c407041008003030004000c8071598040c3c103100a010604510180981e1000000d108004040280d4040303404c6800c40d9024854000c210f0382008400c6e60810700c1c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 200106250 1250 200105000 200105021
    0xf1a03010608062212020304030203070906080c040f0e1b0310050f040f02010c0c0f0e0f091c021005100e010605070302030313030903060f0b03010e0106060c060908131503 75
    0x38081d0034204845a0742d1031400078142004c48985000342d03205100401000d25189070090b404140c07200035110301079504d60083c44224042d20036008001028605445424107a51809026003d80c01e1000100006840f031102050704195031f40c030b000c18010307404000041c4001e4428500d00030400c540c108250801600203038001000b410a0100a00c0040ca8050281d01903481000c14020307006030300048840d0032255600408200c5803500c081000551f51030940f0890b440204d90750350a540d020b07800055000c05171000711a80d441165141c464580f500c1d2a600c40594030f02c111018104a040c05105485080c0c0c0c4000c42c01c8105041440311030003180c0542c0c050041030030300905d0329886070b030300954a120042292545148018801c01018842c8181c01c0c003c50308000c0901080c50107170140e00c010469031050500c03961034440040f600c480103020b05803c490a907103400103507450948800003c0c180c0c2c3c0c0d000300c4200004200c144408406140c144010300030210a200481102410103400c458803c000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 200107500 1250 200106250 200106253
    0x703060512070e04170705070608040210170406111c0905010501050102060c0f030a020d0507110705030705010c03050d0f09030c031b0f0303020a12020c0d1e1e02030702040f1a03 78
    0x30b05000301c04000da0350a802c1644801c028010304102d10300d61100340150500100140034048000414942c8060340b0b50181c0d00031540c8403c00c601c414425500c01030707100d0f02c04c4480c008a800160100f111540080080350305000204c4c903001003000528128880c0c000d4942d14ac0d03584010080522009110310b9016000038001031080e800c011852170002d000b44001250312403000000120b400600e501542e001008005003400796003030021018040320040807130307a0701c1482541ea0011f002d00c5e00241040c1107a0044c0c48400340c00d00701e501d04550507400801004881d42d180c000710f0b0400f403008d00c0380300ba146010b96910400d015661038001d00c03011516031040aa14040d50442010800725404030510300d0740b60800580d074000401c030655614902c0901c040f00715101087c40c2c0042440031a20300c0144156544008a00c00402090404802103d0180c0000f03041c626000305800e0801880205014641c0101c078103100071680050300399403841d0000c005094444507985840400115a20b14001d000c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 200108750 1250 200107500 200107513
    0x10801060b0702190801020304060905010f0c050a110c0a0b070318050f0409060b09010801050105010f02010e031608040e010f0f0803091e040216061b091a0703170703060512 76
    0xe001c036900a04002900c15009145806044012030210b50010105c844c000d5490b890f007803c140c0010030308901700f90b640d5400d094107c0f00006052086410403416512400c0c1402c41da01012101d07021544c0000d501845460350080c5c080d90ac0905500040025082c070a6880300c42c0e18008003001f8020800304a84420054203014594868080b801250000d0341d00050b02080790401002070030340340d1841600000c4081c0007040b0321806403c514113841c0d003070300c420910b1842c24500f02d080b070b41c16400003402a0070034018101c403184902c499101950080c82c086040c640c071450b0a000c82c3c002a448070400a031700d03110130840307403071040c12050041c003055014600301481440405c01c002c40300b05440405415281950403d556503905948171464080700e800c252950628002c002406181406486039450440b40c0d110140b050796070b00c3c00d40d1140001101c0c4d01c000500040c001da004007500b2401c0c054807403064a030301d006140752144542071550340481c3e89403801050045490301c441c65025141c1080d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 200110000 1250 200108750 200108759
    0xf08090a06142b1a0102060c0a080c0313080c01020d05070c15271118010f0b07050a060c080f06100e010e0a09060308030a0e0c010806060307090e07120501080106 71
    0x11000e440c1c01c003501802806254220042e9402e40d0f40c25228101c010902c0d008040450248000000340361070b0007030302260b83c5515812101c0b020350003180281d03000503810200280410f00304078059a00500e424105030310760101c0c4d03950b121094100c2030f003c02036a907010900c0301c2c00072210f019030f50300101c0714208131242100d0b90b120646482656014011076545511030050040042c0200392441000404122108100c0c1c0c5400114035a8101441d0b101d0020401013001c06800741c9501750494160350569070b041d51070010341c5840c81d044902c09460070302070302145201160860051607040b055565500089107822541840c80100c080c1100703020f00202001c15649a4000103d03001d001400d00b041d0040c02903a000144450a094108031012810004000708101741d42c806503008060514084c00100302d0310609a56a2140c1c11460b40001c0103000403d03586d09000d002107412042528200e003289860f1418000c4511701511158000b4540584080400368148101800740054200034402d19280 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 200111250 1250 200110000 200110037
    0x120c0b101505090307030206030a0204030302160b0a081302060331031d130207060507021b0d020105070303021201080304140f03070302100c05010e060105040b0f0a03140a0f08090a06 80
    0x74507026420701c0301c005112021942c0c1044040b00544d4000d004c5a80d0b89040c00c01c1002039040761008901600c906422810b07031400c7c01c2e035000265003410003d02d0501c2070541c012184400041d02d4080014402a42e41025072141c000440c815402c8603031075070101890310b8080240f03030003981140d1403904c0b91815001c0021703800038601910300d000111313030040003840b1340c0080e003000c4000c43c0c402c0885200107120700c100440c40e00060311610541e001c0e42c0c8403055014514800400e01030282d54456405010240190700420287c441c0600034a8014200010302c4200d02400400b80c01103469540007040400602c103146181491b210010781c4e601c4641c000b12000320b6640c045a0100a1140e01e01d041c4d40030b03250f84900451079406070030600030b00c01042140ca200d41c486c034086c0500c0c0e02550401040d05282d0502000e41091600043c0622104900e5a100c1e111041e12a10032407800d40a810b5450700402c4003403210060140c092080c0ae43d440440004010182c003e070341c81101840410451802034680 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 200112500 1250 200111250 200111279
    0x111090a080120090a0e0a0e0105010e0f010b0307031803030e12090f091302030a0c0503150705030612031c0b120105060a030f11090106020a05010f020309070311030a120c0b10 77
    0x4500f507203544800c0c2c0381001400542c1c1940020000000c0ea208010098000790410791502d0405c000800c01070762145503030081008120b50040700440c0c2d01004102038a40d00000b1341c1e010f100c5107000a000015100720b144111244001500026210710031300041e41c4007441001130034004101c905280280f140085600e4800c04044580b16481d2180091444151341c0c40140c11198014203858121040c3e02c0c0c01003503440305004803400781c42440c0c000750805108081c614060b10440d00d945007175540ea281000004020f14004820f1800180240c0150390240307880140100301c07102011501d0350544084c0109404c170f19000c0c22041c1e0400050044980707c0021030410740f0b2b003203a09131a034105607003441c81540f01691015500304140400010390f0690109480c02110306c6180284004511100d08900ba808103858003c0140c000090400018100144d6a001c042c805004d40303090759180c0c4c844200310a150514800456803488941c030400c0b07804030046512401ca030460030741c401c0c10013101007038640 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 200113750 1250 200112500 200112551
    0x509060f040b0a050402040e1803030f01051c050d2001140408071b060c03030f0b0f060a1206090b100201050411040908070210181a03040201030213080111090a0801 72
    0x542c2c1c0d00c0000826203524651001030310010b0415965a5030f644c60070400348404070360400c00420038580e0705d01140c401004503805001c2d00001c0d40700507400c1c00100701c03c20b000c84000c0c1080ca58842c51500001d01c003400350a01e445080c3e213819204a1904e02c284401036801c1440d2001649000801d000030304419070201d070400c0e001843e86444010741c0c41c040000d08406d1842424112200000140080e4859003c0c4612031082c1d8048c041d14200002c00001c0e0703461056030035400100309440e12080e0030040b000c2c0c00448414500b603074100860780d4a41080300d856800c5182c1241d1100780c2c00206040c140500341604810381f00810a5152640792400030320340718580c440c41240c80341c07000f100703125003034007a1100160010060191402e04000181c481100f840f000f914500c3d0901d00041d030f81582c0e080c20207100010b040002d01d1561140c1c0118025404074032aa20040200700001c41d800c04244030b100310003144d1407009651000c80da802c000d034074102c5078031150140e03040c00704100022010190742007880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 200115000 1250 200113750 200113759
    0x2031f150c2919061d041e0f050604020a0e160806010c06150302090601111506010c05030307080411030d05030a020703090806010b04060306090209060a030f06080d0504030c050f030d05070303150b0c01060509060f 93
    0x103140c4802500c10346031f0241e02034075400f1210002c02c1401404a9010b010794822110030040c69070700c08440d05000001ca1307070140c0da04181c11000703d509000300d0856078010014034050301c140c121a5500c41c11070382c11190701c62040c1c4003c0024401c6082c40824039400050908145008101040d8013a58036009070000d01c6450341014081104c03a4010804902910b41c0030381501d07164900950000e10700001283c0a459504903003002150030f007004911100d041f501943c6003071840e5120700d21800a035014080840c200020801c1c00586908103000c1f0a0181c0f0700292400d41e603510b0000000d0a03501da0703412070301d18a8810016504160f4400003195034203c9103043c08180b400c0740308095001000c103a0b00000e0140600c5880d42030555014005000352071040c0c0c0102e074120b80703c00601030302d1001902007940507480f0045112940d40140041d028481c420300c1d0100ba220810412401d0300c594586c04441143e03404200b440700084280038520261405951510840c0745c0300c40024501548407901310700a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 200116250 1250 200115000 200115023
    0x140604031b050604080610140604031b0506030403051b0c01080f06010c0b01090903140307080c1b031206090a05040b07030905010f02031f150c2919061d04 68
    0x10100c6400c0c00c0380080c440184000d4840e031765010f10b9034481d0800c0701c00003001c80c1151004103004004c41e0500005a0001e80f40c50700b803038155540d01c205022031700c9440c690b81d10b014400140542d540c1000b984075034802d40c0c6164440c41d81d240c0c2e00400480c1ca074000345043d040300101c814207076804a607c0381d0200c1142c07210345641e151480141c540740460b14010780400842ca001046a0806402124820b44207582b8800c03551246001d4110354003041c0c9075440004c0d44503000c2030348140740d24060100c00d1101c003a186000c004c40c0f082107280d0740c4101c0c000842d003201c160412515280c001100e9a000790915028042c038585581c5400c1c442d1402801c00c006e055949003e0010300800350300483c904000e000045559027846003402c0700303621404418800221102c903000c180042d080c2072903401d54040d40c941e21407030141c0e6510b0410f402036121a888510440c1003c010310140c101110b0750050740030044103074145103150701c0356041c0e54503a00400f0500428040062100400d036171042d40c0103030043c405c49103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 200117500 1250 200116250 200116283
    0x307170606010c1b230d0b010b090102030f040311011101050403020c060a02030d1505041d120906070f0b010302040f0b010c02040e071d070e040e19330614060403 71
    0x102440c1000350003e02c2c6480c01c2c01103000210110074003420391544a000c2c410500034420009506e05102005203030f02c0c2d008004000140030340010707004401c0140140c03802d0030360388440c51a0039000b0341d000b66130b144c44102e80a07041d56000003418010006d020024000392500e508c02960380d6001d00c119178005c1c2ca00040e80070140b442401070b658110f410610a110390102000c038160410700034020745105034a03007258845003000400701031044019a0300941542c581e0080c2c681d016421000300a43c2000d01048818006003032203800d141214402e40081d056541180140001c8445980e01c001900b0f00d445e038104556a0070074020354a49504880c04500d4595002c00282003034100da009000c9080002c84500301c5681c020703041071240405540700800040e40d2020401507640488070f13444c3c0360700f0030310303406601140c1610038896003401036110300d40200d9214404100001840171100600d29060200d8501403e9809504002c001403100610101090000500360b4402c901c0020a1940100001c19 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 200118750 1250 200117500 200117513
    0x1107050309011202091201140f010608070e0102100c180b03060a0915050d051f060b0a0c030207051905030c040c080105060d06030f0b010e0609011a13080f0c0307170606010c 76
    0x4141c40c10240c00403115040f0070030600e01a100c401e1180842c071169000052850510b800c103e13042f0398085d44d5900305520f0700e40099400002041440703045009201110303805203c1c0380121000c007000f0b95a00314440d00d000030a200c0a4100740c2140a401000f0010b0054596520540c0400d84050050000d802e0041040b0000d2520b02035010503080a01c4600d000180040803952611402030321441c000e03400549200c0c482150040c1c060421300440a02a0f03403002442209101c10280c0311780101c0e1074564a940010307040c180b520803c01078600301c01109020382d00742803111403076501058500344100c0800041c06072001405003c1e00740a43d10104400c40d0319aa203802a000840d001001140000424145800000003d00424024042e2000440d015040c580c001030704a07400e146101040d40695010b84080b603014550b03040e450416001c01042c00c2a0034010796002e881c00c00020800348003800305050815506078401000c502e424507420684001c0440c415601c01000d2a0490798007040d440c211 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 200120000 1250 200118750 200118757
    0x611061f14063a140a050403020c040e1606020c0604062d030b04270210090b031801060608220317040f031439060406020405041107050309011202 64
    0x2002042840075a2100103409444400302c22481c4082043d070303a00c1c0c807480807003a900d4030b0703201100c0d15040d1350000ba58081540e0200c2e80240c401d1054505078141000001c0540355452804006038100e080281146040385600c10020640b60025080b910120000200540540d22405003070041d039900b10b0350b8074083d88138a21410344507281c0400b401132030950024001c24200094a0040307140071440c00008022400c805000248091412001c0c0701d59401d019400001c29502000d100c11b9120128150002102840c41503860065051984007180852825520103a011505001c0c0380420701050021100035810490700c11428144d01c987e503460211100180d5030b40e0030800031034100c2848108011050700000c00390081c2d88000002e139100004400c1031017070101021002d00410080300a000d06da000200f00d003029408007031520b02200c041e003070500d40210f404507111540000c050000e480d103442685aa4040e2045c501c0c244611540d0b015900e1185000c032074148150040034986103aa650100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 200121250 1250 200120000 200120017
    0x105070903020a2903070305010305010b1c0201110f0a0503030402041a0108070302070c0f0602010c0201050c03010b04092f040608070216140a050406090b03060c1303030503180105010611061f1406 86
    0x31145d4918002c0e100400812080c04101c500394203213103034491076240c51410070f0783c0e0420720511113100003010360044d103c1c414030100480641c0520aa00e05043c2000d0040c0c01030a4040d802466403454244104000c6407446080d015004012405101c603503640010080e078002c00500300141d0f143c0c0b03103090207030501d40c4076804403c43c5291000c010840c2035042d0440c40c0b1b0f10185030003d0085844a04180510f40024003500c3e00ca407001b070004104641954000e07500c000103080801101f1521101d85980443d082c0d00d00410703800000504000481e44680015800301c258030184c034840c00713001702500c1c4100051141c1da1048030b07034022407045640c8000d80c1c9001004014410003e01d0f59507111100035105e080a024800e008007000100c0c00c500075001c50342210705440010a049045070f5003030f1032a401c042e0415450301034070040c80b408558240b0503623020b400d05d510b41c5400c00000c12001860170f1402818004522107407210080d880c40d030610800c0c207540d01d40c4020042d0380d0308580443c05034010382a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 200122500 1250 200121250 200121329
    0xb0f03070c0f080a030c0e1c0305040b1201180501080307030c060e0a0501050a140108031b160f050901140a091d0a110f03032704061d0601020105070903020a 69
    0xa00b0020807501c0d00013040c50034819101070040080382070003580d0110300c140301c040d00001241003014400c1302c030544d81c0e4181c5e4420304295047c1034a4007400a0304e42c02180a0001e0040407800501400100c421190070180003480700740841e606040d50542c5030b0045410080621220380c940508102c490380040d07006585c5241200e0b45090741c3d041050107800705840e0a101d10740342001004030807411300304044c11b1f9043c81c0c3c0110301e0720312102c1c005c0000d1000000407540c140245a0408c2c1d03441d40d56075510004150a290080c1498100020050340701c1040e44503411188246594011030307124905091700712040340c04005a90400c6481e0500034045c8106280c480740136041c407800400481c006482020707181a1418074160364004103155592055017400000081c54540440e03c612083c0000b002e1140042c10109205a4502c18800155440c42079921140206002c004070381d41d0910603168407242600d8188070791442c60700400c443c50b489000f80d14465a14841014000703015000c0506007402980 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 200123750 1250 200122500 200122523
    0x3190b1e0a050601080601030903050304080a0908030406021b010c02090f040303021e03090f0a020315280203090c011d06030a14010e011815050127060207030201080906010b0f03070c 80
    0x210381c88010002200c009011691642c046180755202e0310500b070440b035064642c5032a5480f69114000c0c0ca400c028190010001003c1e0045030060090000d0300003001190000c05080315259903640891440c080c0c1581040742c06140400542d8920343c0d10342e0001c03040800d580c01500c60b401d00b14042d2064000e103c1056244000031407504a200004512450300c0310280c40b804c402032058141c8600c08103402030760540c8411403121005100e040096004a00c0d41102103c60b40400e540e0303da544241102040c0c2c15a021003080030300030f81400100204442488c18015a00160785191410500d040d01c840c0650070220020b640313110b943d44030f41000040c4d40d01031440c56a40349484441003038240911031100e4070200b5400301180da0780c010b908009101d02c451140141c205001110307601041c10409058604000882184855000a16018060f580c0c040c0003485c1c2036000140c0000741c00780c0304502c0d5034030010040000104140940300f501e48502c800f156241c40c0c111080b0790040300000068031082101c1e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 200125000 1250 200123750 200123761
    0x3010606050c0f0118080a03060e04030305040b10060909091104090501060810110301140f0d08091c110f0d0c090c080c0a08150303120c040602070503190b1e 69
    0xd001c0c0c10898109821600741200448155082e26818000192805c41040040c3d0008003404003500300d940d090324000444a580c1d0407240c0305810300390340035404a65204240004c2c406402c241c694080200410032000ca4074020008042002c148200600507030380e40d208508008070380d51001c8109034014010321454600b8200315000700994400d820f0a0303c21250480040d4185000b9a405405109085411a842d04001c400c0040e2618040c9601c80130b082050801d507a01d60601d80104c1d8050070055072600001000c0c02080d0800006044000184901034000a095982d02940144090714084050602040419409048043c0c02000703020b00d0480450301e01c07100c2d8071000403126207a40d05180350700c91580e550307030350b115645100c40003400a00c001941e5268280f6001211030010b011607180100070000b800411806550804075030b18006010861164104025000352030704401411140405202c801c00103100040c0003843c1e200850f0000320400001c04180e20380c0154200d5946961034172 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 200126250 1250 200125000 200125007
    0xc01061503140c0f0714150403080112050604060209010903120c1208132301140f0108060f070807030f1a090f0106020a030806030a0c081f0c051803070503010606 71
    0x315100c2500091401e9652035001c1403400358940102d0280031500d140414100522905621100e0b06a521481400303103900c1b9040200441245031585181900d041d09091074010907004060340209803000c050a507a8001c2440807645e10380065010b00010ba5615501c801070b6002092984041c04004881e80882c445039001960741c0a180c0c41100d40e149005140c00003034a400c05c041e10400a0303801719040c40e00002c0c400300170480e0090210080450001022011107007516041c2809006143c2100180455007140300e0a090250201101505075480c00300c610110400700140b0300000c10036101d02003409140a6030009486815050081c440b400b050390301c195140c003541c084c003402844d8500000380500003904a090680381c003a40074000300c5031070b9142205c074840081c1c03a044d0705028a5403da000074041c102042d008054110142040302c0b5200380c030410508a04074041455400e1040c0101c0301644002242c2c060390200c008440801003480c0403e14051450b0400e030f800d50300c0c207580031031079980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 200127500 1250 200126250 200126279
    0x120d090b0711071a090405090109080309030a020f0f1c09050603010f1401090b03060607060605270a02041214010e100b0f0307030b1b37020a05070e0c0c0106 69
    0x10b40300c1283c08081d6141500324503106903181c82c0700c1c885014412039803903103056003000c0d4108071942c0000c01c0a4401d42c4034100c11b50b205946072480b0340d10000d61107210302e80503c802c41940078a08050084586105091912000c01007102c804c0d82000640710803025000b07540b608041c25010348680d8885da162070900402107043c0c000c54000741d0038000743c4059584541203a0302500c0d12100124155141c407020b04c80103030005001200d20648521000c503040e1140468001e45240c06986410402d088150521010101404864240340108000d104002264401da4074841e41300b100c0c01818070010700c0c45801411a2040c90b00c0034002c5031042001180c2c903400482586608940b03c6156060324070400d03603550003501c40204141c0b0313200d00280080c4120a0881e6054240b40c4502d0300d0804070640a46038064040c544290001c024a045500c1c0180301007090049078440c001016210704580712990341e41003c1c414801c55500d24400552a400c03044282c4180d942010020301c507150305e0f03011564808a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 200128750 1250 200127500 200127527
    0x31203050f090619050601030605042a110c010f0509090a151512020304080c060f0103150c0e0409050705030703050a150510060e01170109050a0c02070503120d090b07 73
    0x9501070040740072210081103c6001c1c2d949104002076441e41c0301551406041d00500300d0b41070594401000542d41c450380140e004214158160505564042c0740040d034648208010100b00300d074014504101880018031480c4070780007400d0080c1000e0980c401180c1c68460140481c0d001b00131201401084d81031500a0004103030704203591400b00b903e50b10414044480c040c0303624001009644070300c4681400b41c1c011034000340034100040ca80211400500c0c900003094404d0040b80500000400510451000e4440150700c017800620507490030781c60003880d46160301041032145a5079411801040810406030700248000b8081d10a15952418299184d1140750000d64568180142e0204030000030304c40c20341700d0040c221045840e5801d29804941440c40754a40b00e05029045002c007401e94510181c02d4003c15200c04089a00d00d0224042c00a5440a109040075544200814091541c01203010341070168000302c0c0c00e841d42080f803801d102800000e0070103402c0c01c445a00344281d06600c041c4080066 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 200130000 1250 200128750 200128771
    0xa18090f0b04050d08191806020309100b0301090b150409050708010b01181a0c0f030f0301141005031b12040305070209090c060301090e100e01060f05010e1e0a03120305 74
    0x1a00003507000d0b501e0800c229042150040052540c4206c589968800b0101d00c1181c0600015004242e0b2360001320b07801500c9045841d480784845803c0d00d4128003a001146100350000d02110407103951702d8507109000361608500100a4010302c4150f11682e001801d515004012102803a0355030301e1560013050351070103090009280c4e03500d80e021a0741d08000c040845609980c401001c0c50044134840454101000600d01401008043d4680d44c00810245c0b0744580d040700d00300e90300c2d4174100c0345a903c01c50000d00540500c15410032a1817043c0c000b01602d0f8401c110361202101350344605c15059551080102c008100c0c0c040d042071205056210010700030340ba10a4614050720b48a1a84143d55403412041603075125400704018046c0d80d4180e08021101c1441342d0443e0140741401d103d8109403954040c51a04c2a99101000c019050723010910f4170040c4800c1c00c0002e403030407905010134420031030840d543d4045a000301c0051865141c400d0140300447c1c20024118501220141c0100500020369101810b03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 200131250 1250 200130000 200130013
    0x501030c0806090a05091005090c130e150a0608030403080304023c040209040e060a050c0906180604050303030a20030c12040201031d010e010c0e0a18090f0b0405 71
    0x2000e01840c04540202c0005182511583c1e90380142009040c000f0601a0180242c4600202e14001402001d024880c8a009415140c501c0380610103c0004c03180448825400c1144070071280c90081003104038004603a1124080d541d80d40340d254050310362a0b10803200d92100007800000d111094010310302540c4200d60056402d10038180603052100150340f9824166011582400c4a00a40741c14a0401c0b40240c009424004843d00041c1143c0e0f40d0f10380c03040300750020001c02014649030303c0351035030041940d4030260030204802e02066840c000e07a200110404443d24010f0010394651060750b000f841c000f012659a8501030749024041c0c801d42c00100340c0f40202504540f0700500e00e009582c4185407045000d41400010100003641060140c801d0741850754a549407010510110651107800d04018001308024800315801400c55244101a030100f140c1e0704440c40c0f2540d201c3c140001110b2118820300081e0b0203050010008100800700241480100321510041082c1041c000344500d0051065070403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 200132500 1250 200131250 200131271
    0x60a030506031932060106030902042306012c0906191707080c01050a0302030a060801180b060a05030a020d03120906140906010608060d061b020303161b060231050103 73
    0x401d802c00113070280c8103800140c0103100b200d00c01c0c0d0160751120b00060000c0780d2054400b680d0039040504504c0c440f41c2d802c05008000c0741d560080765812000034800e51840c440b8941c0ca100c01c225031880717141c0600c2a01e0a42c080365072692012541d03484402c0c140c080c0c1604980d02e80e001c022401c24204403130040e00407a0320001c0d1018000c03901d81c0e001e98041c1c58031440d00c648900110000d40c40100311101d096038a00004c100b43c04244501270707040031301403408130000c0001d00b0841c16200009089034440c000c015000d0200b41c80201d20702e03910700e505460034007544100c0d00c1c095401c88130404810442a2500c2841d00c21302003150081520149520050910f584801c4070300b90712034109015030000700f00c1d8239001c55128140f0a0017507c500c1e0207081e0006000c8503a2080d0200030b102c894491005038008402e2000c40219100601d800302124241603101d550b00380c03202c040303014000070090940b075808030705141003825109840d1007100480441d030108840840801c00d032400070740981c0c2d0000c2c4c03030321f044040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 200133750 1250 200132500 200132573
    0x21f0f0f1119140d09050a050d02130e0703050a0b04030305010605091f0c0c0b030a050c071104090c0b03090105070801060302210408090d0507030b0a0b060a0305060319 74
    0xd8100c581540504001c10107140322200421011204460210003803115568007801808807000002d01170341c58030f603030a01d0001000003803021078016922468407000c5010040c1d440060f6500c0e042d00702c01c0007060440b03072010001c1c100902ca9102a0583c05681c1c10030080107007541401e846588a91420440780c0d88800089600d0f0091441c480c0c2c20041d806902030f901c9074111040c501074039151802c034889040d542d1715688094a0350f405565800400310620078038800034000c295220f20413000950038070404e5201d100070180d02107402130007541d80b074001d079060040d080704034405400940220b40e40c90501c40c0c403060003030500300c0341c00340001c0c3c19000200700f061007802162407100c07084884c1032009221b000c0200139207401a10440d1660805c0003c0e81d03181d119aaa490b035001e004101030110a461420810324451000303103040d4a2502d040c402c080656250f0064581000f2107280c0060f05580b008003003807600300c03400201201003c59003040b44c01c0054030716051400228440034203030130600050042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 200135000 1250 200133750 200133767
    0x71104050f16080903040f080f120a02070303051c02070f2010200706051207090303140d06030204050a091119180b04110c0615060a0c021f0f0f 63
    0x4504012408010102c000e03c2a2541c641048220040e46c0c80d15942d010840c0410007260320403c2107070048596403c0500050000e51151409200f480d460202c0080d0000c0d1164841e020040a11402244404040945080131a18208216000c658408141c00c0c90a518962506d00701c0c0c0000300c9142000c807010218200403454030018040c140045615281074078420000f0400c000004041604442c404004002e07920017800d240d10307825507410086207142d203101802059003042c001b080004000090340001c042400100260001c0d44542c9090300103c042d260300e50000e036102f402d000c05e010881d071040e07000001e503e22a0800c0c0f14002c22040501076200c0300706070700054a208281e4100500744555600a400d1f010b0a04001584440800014225031090a0344040340c03002140d900000103040080c0350304a004401194641c2c0d480300c0c0020140d114000040b01088141c9040d2811511100303c03518104030910070b01003010f01c1208006015500c4108940002030408038500d04050242008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 200136250 1250 200135000 200135011
    0x1612051e090a110d051c0c2a03140307020d030306080705040b1e0d21120b03070504150b07050a0303050c0313030f0e04050a0b1e01120c05040b071104050f 68
    0x814511143c008208030345a8010300c01510b080c041d4050440c140704d02410361006594454030707154070380743e80c1d410701e6080304802051410b070b441d00003c0b05050180380c9000010440e907102000b91160310f0401e641c0c5046001e40721000390403000131700c44641010b0305031b000035054030801c804a61445640380100300c241d4000e20596030f00200743c210402002c03690884405042d610180c9021a410000e503650000c480c80c0d00310010042110070510135003154040ca2008401d038032042d0501c004070b00c1c0300003c0d440d42c0c054860701d440f0b107556400780d40218028104510042c58071802d001e03211001c84c1031168540c1400714003100020b1034880082d8000c4001c4040d40d00408000f121f115200c101c0b682c0a8600c507500f4694401845103d40803440c0c565a40d00031144502e0079420007041101e0400280302100100c950381078040250b8801160682c3d130f00003190303500b641c541d00e4081506071354684141d42d41d106680105070385001c0000c501c024088400002c102074041554108450ba5030640094030082081e00c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 200137500 1250 200136250 200136263
    0xc050a0e090a140a0902040b010309030203310803180301020a1b031407030527060708090a080a08120705070803010303050703110f2d061612051e090a 66
    0x4841060341440c01d03480e540000e1030759000407030215a80e80d10040c0302e4111030424041d52640c6109045050601444140c10000c0c2414400c01c2c641d50381c069140e0080e2003c0380b507042315101703c440b0710054903403064074603a284241d500505501c400580e038880c1c0c041e02c030391f1003800f43c00495060380c0e00b0144215400910306565011414000f9500c86c141d12004e030f00c0c00d50400c4801448209045800401854043d119844441d03942200140c902c003040082c03520200600c54642c01aa1301e5180c00c9c2c111048540d000b0030b81c0c1d540c5d804100c00185441c009411064040c4a4000440d00300b00c541d00c02420003010320013811450b5581d40204590381c0c840d500c002043c11000b070004100103030180d0702130880305d8424104881c4c032000c0310010354600030300702140209a90000d0a5074414002c00303d0241d04095148401c141c101100c10141030317071080c0c05441030310b0810100542c112650712030141c40744bc084a28105100c02d0a021300740c0e1060800240406861b10010303400704103807940004035542040e60152 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 200138750 1250 200137500 200137517
    0x507051b06151002010902040204120209090120130806040803010602060f0606040501030b030a141f230711010c0215060d030905010e0103060b07050a1703041a07140d050105040c050a 80
    0x60034000c8400e89100c0800643d0340320740c1b50100580c0e035030029002800d9450f0f401880f65426004002400d400a40050013a03407410310410303070a2409100c00c2c54812500020703240d4508040180304400c82035a4450142406010240020001d00c0b000850403038084c0d500310713560fa8039021b88604402c2e00590302280c0c40300e000c010401541d40039800540d0354000041c00c2c2e604020264850a4602030103800d840c00d01d07003103d04c88142c11499a400005100f8041404200484a1340d01c0b047d4140102c00001c981d4002031000941d109104903020416410b40e0002030028007041c080c00380d69400000c0310841c10044500c0014014107146881807a810b405642d07030b00081d458080195001030b0740c41101810076031a1080840da0030070090082030f41d94440d00060507600043e040150134005480d800d407441c48020018440401c0d42c3c45a4001c80c0722007100d01280c0341c0c48910042d0f9440d28802d03074107000306c2d1022030201e8022100d9405030f0f040b01c0007524140907864114100316968407840c0304540110300e655 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 200140000 1250 200138750 200138791
    0x2030702042c01090204050a060e06090408190210060b160b090c03031605060106031104030303020a020a0c0e0601080105030622020604090207080d0e160e060102100507051b06 77
    0x390004412810842d001c1c26403405000c1062446680407085085560f444d002083c003141064070901c0c2c0d2003034071980200f101d0343c108a4544000940a44514800c503118804a000d20010071300326900b4030030350444038500d0004800082c0d200c00c0c10350060708001c1d252031400180005103408503040f1809244940004008030b90328043d000380e0241210010748203580c00310105072000c02c003e2414920400040000355501c5c50b200345400c805030000410141042444603902c4040e1080c0d0302501ea01d41805a00c80d91241e004a00d00040c0280c0648042808407001a1100d04150102d0081c0300c02c0c1d80e4002541e80307400504d540d13040b0544c0c080c1c103081c20020b8215040d9a0100d4403400302031000342180d00d41030303035a0a01003d03a0441c02003556800f80001e100c1ca014640c51040440d4070042c20040d10b606813004041c10401d074040d20502d000001c204000400b540e10a00c00950030500703208080149040880c0010240c0e00a1491814001d08000c01400030190001c3c1e10b510a1017080848241e60743c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 200141250 1250 200140000 200140009
    0x50f100504060509041202070f08010e011505030309010c11090112110111100b0a030606060e21030a0302070305070f08030714191b0b090a1a15011b0501060b0c0c1002030702 76
    0x5100e010b411405612404152109c2d13201503900200342d0a4004101070314038002c2d150840718100c1a00f00140c00070801009140c5012040d50840142402c1106c51691a801c0c6101000054007205a21680030000454010710080c90a5010381c05400b103d4004800d450054070750b0045a428010785600c001d1103c007002074103404c040250340000c0d00800083d070740c9540300011f4450682151012460703060506a5a04107003007019500d403a20460303050b45100c802d58064481c03281e02640c40400d50000383c42005e15020b2002c43d081e81c1d030b000b540c1c1a040b8046042200140d00140d60704d20000d80d402400118094505065950240380420315220101c150041910559031205070310100d00c411055071030100b0a5821840c3c4551049400350000312070034030708500181d0802e102d0301910614002031161a08142400c00e268144c02c1c2048080c001c4581d200341c80700c02801c0c100a1466007041c070701088102d44c1601038211210710000310f0304108043c00030010745000020801e070060b070051100740c016180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 200142500 1250 200141250 200141273
    0x80403140904020d0203090106060311040f0e060a120c0f09060f1211090901050402010e060c0d030509070b0703021e21090604030f0302060702060711072601050f10050406050904 78
    0x28010b2006140c05081d64141c0183c0e0401c5419860750f9564a82c1045042d0f0103006a010100001040e40d00c1c050401d4498405070100d8002c18041c14200c0d4001410358450080703000280140300c0c1c0c100049105440e0280b0f00202602410030503001c07030240000c1c40405801030310107a40826450220945c100000007421200464054820301340791001e11399a900d0b4010031500450a0034004105031426000140c40c1100c1c804070307a4014641004242100c66003c644444403c0e11890081615101d0034403092130529250031140d41a400024160205600080c413041201e0880303c08044c00080521015206c0410725000111150030752940207150150000804054900810381820180c403a21512032060b1455400c0700581d12040134003c003150104000c5522a815140451841e18000b8070ba07500c5041500c00c14440da003554143c500c0e0386640000d9001d10b0380d08030b4020031042ca03201380e11414010f002e4032407104400380680b0100f0719080c58040c810036140040c0c524440c030340744e40c0d07240050103c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 200143750 1250 200142500 200142517
    0x313050924060708040b030a0501050108041104050403110d05040e0a110702060a051e0a020f06061012060b0309070f0e101406160809120604050c0907050c030d091208040314 76
    0x82d0412044002a000d070010308003400d00c1c410025100e1401c0e4250340126141078111505000c0e8103400c110024001031010303202d003c0d00b90b5000c5050303219840d0544018815480304880c80c08ac008000804580c42000742046548082450819403a0060040101c841141101c0e01c142800c00c540340240c24030900030070000086161043c0f808080303041c0821560200404451030002c0041e0f40403d13075604000039100c6612403005010282048030000e00318072403542e150824040781030800c00850340c00c2c0e8803410081c0344e021200382c2d40c0e04c2d200000f6601c8580c1d034041e0701480041d140c00880c440e414080d02d94403603d201e01140c1e06c0181064030f409082c41da00400c00d54856010081180400d003075615103070340d039445941c00e107448061820400681d481d641d104040c9036804401000040350b00020000381700070054411040c03e80380d04404464501c96020340f0015032100140017402c0d000180c2c40783d00114006c500980c1e959482c6801260540c00584011700003c155410030040f00121000500200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 200145000 1250 200143750 200143759
    0x12060114150f040f24141b0c01080f09030901050d0b0301090f14030703020613020a03050a0f0c1406030727060e1002031204030e0a030b04050313050924 67
    0x5146140101249502c1403080709642d14000c80c0800003140e980070801c014024204005a000b40d40e144000142003d454030001080105084034404542e00310803142d400880d0b01c0e02100c104507110b50680d4914400078401e00248031403000445c0d89007291862401440c0b00e030084d600c0c0283c00070045406030000743da41600180c1d102510385a5580900ca42440389110399032500d0740480b14100302d00100e044203003100381c81d0070030401c00c40000c0d40403440ca6403021049a946a08035054004600d40e2083c0350401000c070700c00c21043c3c0090080b00709110580c0b41c454003070007840d1600d03900c0c070311003000c10003009981161050001c02c018074003500020309140c4550b00d4410b403c084410362201d801402d0340c402c00104000085e8200a0b05140d480720b02010882d000942c0741c01d003685402c09208030700400c0901002091080040c55030b40d1250404000c6401c00038083d1a410207080c49600c0c7d03400300c5c1c0483da41c0c0300321050000d910704005c00c960703214003080850b08101c81e0842d60400d4801c4091544207912 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 200146250 1250 200145000 200145019
    0x51b0102030d09140c0102031309021803030a020601080115030209010e0402010c0606120302070b04060e091305011d01050f0106020709020d0204050603040f0512280c05010c1d12060114 81
    0x482d4288203d2a80030302440700c14a02d1038100c0e0b0080d0904440d02c3c4218110b40081080009100310032041404683c18401d0040c2da40e058806003200c40c0d4510843d465040c0000100103c802c0d41c0003841e90305a07172505000300094030b09050481003080307840c4030080d04500040d00401605c2d0f0801c40311684540181070271070344103090784d40d004200c07202074000e110f140c55075049200502d58108841c4014025001c00702e86404c1c20898050020351444060500c1844000300180100e0407000244400d294044001c3c00030300c600340e41c15200301e0030100c05441550300c0c00000401504080781258121200358024291790350811842c1c40c0658820140600f80d150200720010b110344440740110b101d10f004824100324501245401d80c07d10340b0000a156004005000c10916042080050394034801031741d1304000c0c1111909010340f00ea0303643c9600076055518181c0c444d07100c1604651415465514204d03902e86c002d0001040041c107811041001c2955072000005000289800d50386240903540144031151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 200147500 1250 200146250 200146267
    0x80106030209180924150603010e06120307080f0315041b080c091c06050708012709020d030908160b070b0601090e0103060c030c05030c092b0c14010c051b010203 71
    0x34441303034522070505e0b03403d40c03c04111310103500ca404500082c0342210070714a03652510454170100e40000e00001d10941d07034003400f1144c0d1041003048418035176000c0c408540712084c5c2c00c117088c240d4200300c1d100280b803c0d10a52801080c6818850903070080005c1f0803d4080c5281007170111b0741030200500b20b81091500f08504502991011105200c030f003d88140b40401c080180b41443c1520405890b0f041800b03901e41c0103100d0071942d2000c1c103451000d182e610103202c2120440010152205060194200c4400303503d06040c1a80400d0b4030090b00c00550454043c210000250412204184a8951101702c1403185400150b82100f0035504070b0814500100c2d890b0311543c048d42d0702a8203074001c45102d40c0c0c4060400c0d640d80c15001e1461140c800d401d0103421890040e40c0c4100510a03030640b40d10400d40300032100071443c080c026010400581580702c40501000c0c1c82c0581403e005d50044440d85030410040c003d00d2f40c03003035030ee69006543c003c025100c0d101c0c141e48055420001130078500c1c15800103018050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 200148750 1250 200147500 200147533
    0x50d15090f1b0804030c0b06010201090602220506040803090d0f0204060e0708090105010b0a0c03030f0e030711060a090302060d06080a12110a03050301170102070203010213060801060302091809 85
    0x41c0c46010000000e0480101241010000412008601480740c400104400310350442056000c2d0358020516403070a545200c0100d00404c04000000c2a43d880071880801800c107480c00310000d02d0001030208034a603203910401804d0700452003500003130b500800c10314603e03051000000c400c86e481600480026001d943c0002c080d0b0b00f09402584100024904004800da4407c01894002c010400204025410101621181c0c41081c400c1e806012001862504251181c0e000000701001c0e481c0070403610300c040502c291254851101a01d1020050540c85014134002003101c001a185498003440c203455a0300f0712545400064441100c69500d10001030469010b021200d0340386c2c40340d0400b0240b0044064007404c00e414503014030303080c0d0303002e1030b600c00000ea003241c2100c3c1500c10740c8010305210f80411031102d001e4854044000e400d540041403c500e03500e405001c200c19111981ca5120181c3e80341c030000c400300e02489003101d40c0403034103035845400181e200707038419000600281a00c40301c034007165020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 200150000 1250 200148750 200148761
    0xc0102120421050a11210a02010305071206060f030c05040e0610051303080409050a020313020103050a0905070e041211070e040f1b0509060f0d1106090a0803030a0c0f050d1509 77
    0x303a814000760a45485e9601c0d000c990b9012000300060180010100700b9140c035642c003091080281450f6444c0041003d80780030707860841903040316038400d00901c1d880704070080000c41c82c80d0055006c2400c207100d20f5801400390050310141e1b002203240302c1c0c00d551203c080290310302a401c900d00a001c020009425480300c951303462805035000b25259039440b842c002c1c045d41101c2004122045403803040c4240200c04a89202c600c01d81a024070300402e0300c0d114024202c0c02418400c5001700184558003000507031005a8458911071402090301c100c0b40440550280d4540469048a03e082d42100c02d043c401c215001c181513800034029052180005c0207030b902c8518a100407070100002901c000010040c1e07103080c0380721a0b401902a100c245c1c041d42600040707038451040450060203000052607140d11a183e400030b48031113420007400700550300d940300754445c0c4903441a10707958043c038205422400c0740c600a110000d15040740d0703901c0502e8400f210302c0550040c9020b000070341c00200044c400044200081c06107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 200151250 1250 200150000 200150003
    0x14030106050a09050409021c0c090f0504110d0f150605090a0207060e1b04050903091801170601030b0103080c0f030a050d060e010f030f24050103050c0102120421050a 73
    0x18156100442d40d00079202000b82c0d0300052085003411060b00060302d5280602ca10310509450360301800c2c2492510718403078052500b002c2e8002d458513069840761022900300300e0099000d0310901c10000304107011f10001956402002d00340460207070903100001ca00f14a0081c201da5001c80000c2c039180c59900043c07900300e0544290307210940124141d42440460302c00c0380e514020103001000c2d242c1034080c0da940c140a941100500c42c40e17640d000510030f500140304071081c980300100b000d55042d086085000c0c6107842070150300b01e148a14200040c14503000192903050760b8000b816044e180c0c3c82c554a40c4815400b00100804601681720382c0500d01c50108040c00320f1000790707191070f1303211304488407248100c60b01075100c160a146000010401c1903003800d40401aa5080707600e850081d80141484e00d1b900c240b10200d5814140b0950007240c1168140c0e202c07905036841401503880841c2d0100049079a14445600700c803000c0410041000070000c009102c5078103801e40e200e1174640885ca42c403058140b0800c07000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 200152500 1250 200151250 200151257
    0x50f0d05150907020705031b030102070b01030303021b120d0c0c0b07030204081501140105030c04030c0b04090c05210702120c0d0906110a02060a050403200102240609040314030106 79
    0x62190891a00e6402c90354070558a00c000e0120074545400280c2e01c0b032032450700000b03030b040c9011824500c2e24203404482a076600002c80d0b503a156940c1c94020020340c0280300c0000640704114030300042460214000010304822a400c5041451201011380202011100b0304140b08011150034006081c544034540b0a48175501c0041e1210310f0001c42c142000a65914449c41c00c420400501c0f0140d85401c070210425000c2c60312544950352150f81e0b0405100318cc0015011120941d0001055020705004206a8603201402d00030040201000e03200c43c010802c80702400d400321060725016410031840c1590001c05441200c0041400c5181024581e0001904820760780118402c42c120039000300203c0c005200d03e10f0314840942ca40000c0d0ad44400c00e102009204400000b00f201100707101314149e0f07000c0c40d0004c450240d1480743e45121000d155840d1042409400b803c204008101d00701d06051980b0000c0042401d065641c1c2c10400c0080704005004409004060400703072940c201c02400b640c00b030f000644 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 200153750 1250 200152500 200152531
    0x706090810050612150a0b010c031403180a0c0810020405010e0409020616060e070b0405030601030b13080f0307020105150a03021224070e040903090e1510050a0809030a050406050f0d05 81
    0x15414041c2d1f0b00d0060210b040c8a801c0ba003180000340e21080080c41d80000d12101c039101d455041e01280480000340e0f50940c1c0348941c031a460141b1000c0801a000c0b5800b4004076a00d810411548501364001c601c00d0a0120305008880b00e50740c1040c0c0c210900352407000b4070481c60801c412212450f14a0b16500a50b801039840200201d8034804100c143c0181001e81195414146000f002a594138014040288a50703003400104142500b070240001c030041d40302030780c0f685507044040c00b00910b40089514500546c00c000c081120780ea29038240060366a40070381003088a90550b02032020f4010f4400001401784a10207a0940310030030900a0035009a856142260900741440001c04001e80c6800041c401c6260140244c0080d400868140841b8459455480c0075907079034201c50003030b07404144d0441d0008070700c202018070a036000e0300815a15510f07480c0c00c14142c1711054200d0792409100b4004020503c204010703c00d0f44e010750702404c03076403490052083c6001c600c01001c40c15204152500514117031540b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 200155000 1250 200153750 200153761
    0xb1005040e01020414010f03060e040f21023d0923030301050f03030706060602010c031515031512060501090b040b0306010e0601020f030f0903070609081005061215 72
    0x6001d00c40804202500960415050491418038428903160960500450300071844000380241c000c900100068121440c541c031305420080c00f0051140d0b4116040540025003885e11100283e00c0c0340d82da40b440d402001c00b415050134880852a00e00e4842c030f0400b05049981c0480000041c1034200045c40e40b1022035020440d02d0702c11020030490740640c1810703291241c40302103a0f03000000c0e00c0c1181d40482d40764954012000200f4207620900001030480c605061010604540540210143c481c0e20fa83c00c101018001802100b16019070282c0c000002e0b40440c2440214403d82200c140307088440b84000e000d59485076804000722602104440723850300d80e0010001d5010500c0741c440c00000941d0144524a4a07800090700c0e041c05004142e1045106004175086034400c104404e4500d4210341169541c08410618424940120650a10074455040049000c62143c030380d400031110440002c109900c4285c2c5034601820000380801c0c1c01c000c09280441c0d0001c01040381c82c0d10281c000780400500c1c10503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 200156250 1250 200155000 200155009
    0x30a0806060a050f070204060306050901150f0e010902130b0406020c03100501030f020112180c032105040611190b100f0b07030503100e0f070809061902070f0b1005 72
    0x8003200e100340010320140640c5900a012039038070410190352a0ba0b10328103440080e00800e0541c001415003458001081824101580402410700400c0809407829031307101c0d500d0780011002d02440307501d0b4007890010080405030790050480ca203040c0d9250385c402a1a160301211941055001d0001a40403805500342420207002006404000030010301c00e640c107644a40000c00a04000207041200882130340354414080d522101803850301d491400d84444841c01c005045082900098903034210f501440c0c0f40c1d8102d0040d84d0004c4000d1500c0d4a070416117020000d484031000010200c80c5402001d110f284840045290b090186110742008425810690215150035155404c80a03040c01310180134400204104291030401e981031410690780da44030320210340100802c1d409401e40400301c01c140404040900149449408160f55003071207070340d030902565510703001540d811a07036114607200700401e0740310b03500203180250046290010502003030b543d840c41c2100c00c940b025042c0e0b491030b01c01d0050746003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 200157500 1250 200156250 200156267
    0x308070c0609060e01140a0e091e010503030a080f0c0c030316080a0606050d0b060d02030408030106020d050909011203050c1e1212011205121912090c062001060305030a 74
    0x25a1404441c0c8010300130010b03002d20b07010128040c442c040881e55000d018850442210b0002d005041100707142003052100941c14111903c81c00c1c4582807400218a5050000c195101e940036650303411043c0d291001151441c81e80035007844e8080c0d00811616415000030001140a01e9121036486843d4009a4008000c1c03000030700000416030814604021180d803040039282c204180c814009284c80e1104005100791280c003102c0401103001100b00b00c180303c0c0c86c002450486001e40c082c0c2d40813000d00c03001141c0c1c03403241f20f60403940000b501d1700622800d45606121a14148a828414500504110191720b003541d1038940e11030070f07210300c444402d009005106622107094080c84035814000c101c81d8030800d01344140245100d984030894540b080c0202048100300085904501e10703640c01c9403d4086400c180120b48280c04a11343d00403084100400d4821904c2154101e501c100e40b0f1401d210f000c603103400700400044914855001d05c109007103c20700c6450001d5200d14001c50303076078403600d03406040da40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 200158750 1250 200157500 200157509
    0x3101203051b03130915030c03050a0201020c0901080d0f110604051b1503130302030405060c010501140a06020604061a040e0313090b030703030c051903210608250308070c0609 77
    0x402c148130310307000000480d07003aa041d0340998401141e440400e01020b0800e070010350001e03105c098908000414010040b4500074014000c0e030954112500030024445079007000e124260150307100100500340e0b0b0303200d0740010807004094600364106c421906170140c0f4044094405498a070803410000a05010301905443ca9040030784000c25101c12810618040340070007007002d000c0c5901040c114081510901c1140c001d0080141403d0300c1d21034069045002b04024001c01c242e0b80c2d01c00807440a01d00d040301c03c580803a14154001d11080e5266910b05c2e01801010944186006410030000415501e601136581c13007000501c011615202542e0404442e001c2550044010030b00c0d1420b02039150324003190042c1504e4140c200100b401c030071464110b00d004a10400c19240c1d0741d42c20303c0e80c0105076110624101c0000c3e40640d4581c5440c10a039804110f034413034442c910042c0d0200040d1915800f000580c400c00548001d51819044d9498441c4504e070341c040768003160310042e00b42c1e05001090304101c2c01030140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 200160000 1250 200158750 200158753
    0xb041e05010f05160212010914010b01020a020901050d020f040f0b01270e07090806150f01020c0a060c0602040803040605070b07080601050715020904060b0a02010e060c03040803101203051b 83
    0x401021016101380309029007107603071900c0d80d941c43e0150340310001d0022886c4030100081120700020f0810010b040c10b00101075103e5428101c458019610004510a446400800248180c0d20306801c000c0454980359080380c0044400c0c2d003d008646d540d100c0e148881450f06400b00380110403000050076614031841d500d11000c00c100d40c0000c0444860001e0050341c808240401064803186800d071820b040542c0540c40b140b03c1c0008208a05a8507902c00362082c1d0151602407094880c0d000590b21086220041c44c0c07c01c6024108100080c031955080311814050305c001841c1c562142e06045c2507604c240c04c00301c04144000307503c408100c1308415640e844805460605002e08201000034614450190301810b01036081440680500050303049803003045d0010030802040e41e40310030045480c1c20401040003d5407901c2080d15440401160a512403c1001d080034070703654859032804a40c1d0405800e041c43c4410424011a2440c401400414028082c0d110141c03203405041104009040c41002c00086 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 200161250 1250 200160000 200160017
    0x92d0f060e0405100903050c0d02011d010c080c0901050906031609050303190c0c09051501020f030c0304051212031503010c09031a2203180504090312090303060b041e0501 75
    0x100380d010503a404c40810343d07a40850070841c14141200c031805510000b41e003034000c01010400c8950150712003031955800b4400c4400008504050760308072002c0714010008202c450700091a599100c1c0f000308031114050403e2402c14403403034040744103078100b00c503400019402c60a038000400d0700308c00c10200410302180118a00f14180031012900c1480c0c0580d202485034140051003000072104000b805032101c00130411242c944491281c1c4901c0900c2c1c0301f03502600400c02d6240038140048121998407618400851900e898241840101d0303040511244440c002c003a000c50070348400f10029806102078242c20184102000c08145c00c544c40c584281d0280b000c4400300300001a400380b4501f152620201903858940e80d211403000c130400c036400c402d040c90800403400e4020190000c222001402c141e0107221129601e0b4414081101d1940a024003ca81401c001e540c0c481c0c9203410070900d1900c070b8030380844c1041c1e8036051915640c10a420240c4060711044181d290120b00081c0080208024130b80400c1e03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 200162500 1250 200161250 200161253
    0x90e0105191808071a0702100b0102030a0c17070503040602071805070e0111010b0402190206060a080a12030f060f06170c0f07080c1005100b0301060801092d0f060e04 73
    0x2ca0503180c0350040001d034010803039800707221083c81ca0303032040c91062400d40140e1801100007911092807941118903d4688005900317554400000e03520107010a890b001d145030b80603260240844503034048115602020081c583c0021030071f00c00380000b403945400805095040002a4a0441d07071421541111803030601002607a5601001c40444900f0a0810360017008400c10014090290711088035003082c000a00c04a6a0300c0031808816560010303402d803001034449104012008105206410490740020002c00c04140c4403080c102d00c50b411030800081c080107524411080c0e03030542d4030404082d001030304200001e9410074505da5080e226003040000e0ba140148602045000740003801c2d1224a01064100821072624111202600300504550003600007903060006000210788c418940010604000390700701c82141503a058407803580f690105030b030a00092000400c041c00000016442c9000a0341e048007444141214626200d1404a00340030f9411030101a02d8032513210681e0300b02e91104120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 200163750 1250 200162500 200162531
    0xc060a110723040b19030c050414010e061c0f050601060338040b130501080d0f050d02030a06030f140607020f031e1308030c0606040e0c09060604090e010519 69
    0x10320030601103c0003c2e4520180000c501c014401c4660760740b800d818258040f00340b01600f1522400c54104803024080814034480a1b020414288210070191803481e011410b98a4501c038002c048424a00c45964409180e8545021005c5c18080c02c0d10f154218000500440da0b050007480350100d00107421065068450351032128281c1850505001441003608500c000c0d55180c01204d41c10301d0040501c0c40d121030400b1000000c000a2159405910071450074000c0300c3d0098242021107403268442d141010003660005019500c02010040242d03a680c0c800310008a08805c5009072601940303040341d04a0301001030f6441e01502405120955001c54440540a900001101e0318604000f8510041c144150500741060041300041d209280700000049081c000000150003078289110803284292900e100b840101d601012840d40c00d40c20002500e2064180100150b400403001f4244c01e2410fa0344c0c10310700049424200d1081c2850b5118014020f800c008080a2402850092003c0001a001c8180380 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 200165000 1250 200163750 200163809
    0x90312051e12330a080f0303010f0905090d0503040f0609050a06150b0d150807080d02010f020f0f070f06050a020a0e03030a0f080a11040308030601080f04051e0c060a1107 75
    0x411820001240c0e41280c1315501404005d192210445102e04910301805403650402d008000c81070071800c80000d070000d803c1c00340c03901410191000c0e041c4079030095070445882c3d00041c001d030380d0b4107400303265000011007030300c11052106d0040c0c0c09002501300515254041e00c602d02860900e080c0284820702030000b51108071400c6d0316000c40d00040447c04000341c80c040fa61160700c00b2030103001c3d10000080304040800d10111040c610b500801c40242c01c1501d5400f05c0c0594852802c25220a0050030700601c2000000d20003940209814491402c441d91040155441100c0d0800e5454007c2414003400c0d800229200341c3c148218095800c05010072401428075482500180400001401103412201583e12a20307101000a48255403141c0346c2c00c280c401a40140c03800d500080760b61000a01c080c0e814504a80590f612801802409645581d543c0d003400503629094114021211080d03030a5480000401e49a981611906031010144003034500b0042584e0000c8801c40b444201e1002184694101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 200166250 1250 200165000 200165071
    0x180f060a27020604140f040507050306032103070c06090501050406020915090603060907140424030b010207051917060106020105072a080c0a0c0905060d03090312051e12 74
    0x40c042c5c140700d480003440026510f030303500f9042841c0109000d45258803070700551181e10140e0440b0b0255040140c810303035845030303003040d058492002d1003c66840c0c2c0c0300c0ca01d00c92180c0e000e148003007951226519002d00712030060b141101c444d0380c001502011070516802188003076443d400c041d410008410f0110340e85200c0200707070074490301c60100040c607114045c00c41d25220b02a1940c0590310745444141c0441c082c659441c0e0500b203a0f44d64a41c481d0910700c45e00031000480c5041e40605504c3d85481e051007070309032000c4000200d1007000407000c207000030004440c807003036030b0b070f5000078440c95143c4000642120005800c01c81000750141d40c00001102049842c10800d20440d25060741c01c4290070200c04500030041302500c1406070303850900600c91008444000d840b11940c0401030b94441404200c50324a00d5200240468a240003c00200300c1841d6035107800025420090302e1300b0b81c0e500701c25401c2e00040e40c1d51906424085001819514030094080e40455404000100710482280446007030186040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 200167500 1250 200166250 200166269
    0x807030602220306020903060f01181a030331030b040803040203031e03070314070903080309010209060c0a060b0d0c03080c1608071404090b180f060a27020604 70
    0x510b604040c41c2c90700c052416051404501680580340e10303102e80a07511400398140301303200c1d04010031907850407000514101d6402c1c100c040380e00155101d4950282c800c144180b2104a0041190030f0310751800c1c0000e0000400280441070100c910002d007103402c1e1000758201d0105245154140000780854100a41098100b4503441d1a5621440002d16500c01c0d030304c40b20b009000c02c0c0088460351943d000914043c03032a070f840030311000da42280e201c0025181250443e0001d41c01c60f6040001c100700e41c0041d600072005000240c138000c030010100e1030740e038001000c010301070703202040040600603e4403404d840e03450200c07543e0059900f070341c8903412020920300010344400b13000505802d840741c00f0004041d5200382899403201307041c0e80e9045a40c54075282d00c2290038003e000390f906800d81c5054030880d400c480e8804030400306901c402508450f083d00da54841030580c130a007070008000c0141002481c1c80343c4611a0301082c2c410002c890b02940c0510416041c4a40c01d0240405005030707241010380d000d1700c082ca41d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 200168750 1250 200167500 200167507
    0x150203030103030c0c08010f0207050d020109052d03030c19090f180f1e060b1213081c0510140907080c070204020d140c03010305070303120e0d02010f0b0303040807030602 75
    0x281a4070f008811ba2184203250f2800800341100c0801da0042c02d429030160054941d10700350741d2801e03800e880b5052030060a5410045a040e541124440c5a11022240885d030070104190941e005107180e00c16076900461603008035240b4407043c055080b14680200c6480d204544a1501c80c0c0341d1142d250500846000d000c588050901e111020380c01845001c499140c10b100d41c1840c1d001c00b4104108112a1680c00d600303140002c0f40d0014000300711a0128030140c44404240e407400103d85190404100444541c0c00800c0203019101c0741a0042400070840c500002d418100b40050b0b60748604141d1100000e04500030703411b081590b4040c07074140c0c0b210890502603030682d107291581f203c0c2d10075520001d51145c030104413040103c01c1940416055892408100c0e069201c0f03002e01c031058002484014402d5000c00001e0000901c100d034420050000550041111030910035001d04000307181003443c0040c0e654011410454010340203a500800050780034510b89420a50041c0d240c59442c00041e02c0790750000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 200170000 1250 200168750 200168753
    0x70f0b04180e060403120c03020a081501051902151506180f040f020c060a0203060307231309050709020406140c03070804030b040b0a06050f04090228030b01150203030103030c 77
    0x542204500c040200c00791415031509160240482000c4181b0342c840900d021699541340e4024821104803c40c1070311040150365410520008281a42101d28104030040c0301c5200c0c0c92024544102100348141c0151800f003840340040710702900000c02c1c14000d503102030301254450704d0b12821104800c00300c10344c2c0341e00902d4410120b00005148894540c0192500414075404001d5901501116180406540d41d0f91075055040c0c040c5c2c0015596158160401030301085100390154072a42c00c91a0110301d0100040d10500158451651885a0b1500703500d60ba03022003002000d001c81409012024000c505050904900030542c1007110b0414184400000b03d070044108100183d40d03803240d01091542d0744a8591406260300e24040c1c50884451681d08045200344619000d56010340c2d8000d413040c00e0300d0740800d041101070308415000342d0b001403038000c001d0342044071741d0708503c0500c06000c00c802c0c400e807030341c40c1c0300c88400d105a010f9021054410000443d803a03003c0200d03411070740c041c40c3c0300591040b0b5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 200171250 1250 200170000 200170049
    0xd0318082a1005010e07021509010b15090111010c0917100905011e0e0d0f0c020a060806100503040b0105010e062511060703020d11010204090509060603070f0b04 71
    0x910340007860714058000024490007000680b180580e0302a2428441da0343d803202d00c0c6a8105094602c0c1c400342c0c000d0924840d46e41702d5544081d80c8a103200d0b0010907407481040c00304854125585000c4005400041e20b03200c1540c2109681401c9000d502c001c04c0300c0b0607800c41c014a108024000d50078811040402491400020054002991700106042042c0c00c1c5070300d407480c000c00420280c000c2d0610500e4030380840034018401d400d484451640a015802d81c621411500300000314010400e200e0f000350280096180e401e034030409401e468645132071605009040141610303c2c1100201044810000c2200007040108454110b40003030901000b0070358140002002401014400c400b05104050252816a0030444001c070081c0070758440c40d4022070002c00d008451092010140240c1e0145820040c002d105160044141d104030000604040d16a100801035880a50f0f0b10b40c0d60b54400018032007145030500075040100034004491900d60b1510381d00c40101e00841c03050410002c180d800c1c2d2a0207144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 200172500 1250 200171250 200171287
    0xd06050901060512010219230f1c050403020c0d020d02040e0a120306050a050901081e0708010218040b03010501121713060c12021209040230090d031808 67
    0x14840c041c40000781080034007d402000c00b1045416004862a8205000e629140d0401400843e44028145102106e040c2070b8040104ca010a034004c020444584c103881454552948140d0380214040c141404c0c0245018401070203548611802e0746800c005903500c4400711310036981514042049010702512500b022030103a000350240318a601c15901d40d0794550b0201041d20002c07900b2801c1c40f522071003440075600090080b4129580034031085000d5401c41071079070400b0070040007290b423172544031890582681c0040340ca28010812920354143c081c6864010940e0440066002700042c1d032405075102440c10002501506410040400300c041c0d1009400300c0e486c07410100508840c103550743d08010010b640186c0103680a43c004211004418800b241541408682d844902e0600c000c80341000025844004046188040210704101e9210f5481b01c0f041d40325540546024130f454580e040c0d0341052403002d030780340416150400d80d07246084c2c810301407d00d854000d070615481e4032540c4691100040d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 200173750 1250 200172500 200172509
    0xa110a06051303020706031802040504020a031b0f05060a08010612060905010312030507030903082214010207030207080102030405060c180405040b07030e01090c06050a051204080a08010e04020d0605090106 90
    0x1400d1508200c000d1031211403102082d8402e508445545036100380c11411201070341c01000404202030f000720054038082e00305942050004140d0141a6505e5584c2c4016903044000e010351102180b0082111420800d40030009000c181c1e001403074038280d841c3c01408040140510002e1090341d840f244d106071055072200004d0800454108010f5849040210b040e128010440c4000790902000600b085d100c1e000741001c0c1d952545a200341602e44042d5000c8989042460b21001c021805d40306000c90b20710f20803c040103180e00001070b911102414024113100c5503404c81582680100180800544001045940001c1643c0c04503107030641d0804400c2c0700c40366980703515405410102030105210311080c249020700140d840c100144003490030030b5030076144002c901406040d01d14404100190003000105581d40c420b280141c0742241c41e451440100e48103507801e4130b219030046440d206c2c554025400901400046241c100700b884c1c00da0000e0042c00050500500403507c950100d000c51100750810006007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 200175000 1250 200173750 200173763
    0x30509030f0403060501090b060c120a030e0a06090b0906370f060e130b010506160c0602071a040806060409052a0301150503030a05090d120f081b0a110a 67
    0xe43d03403070414074050702083c05840940c13454540140c40a2074020100c2d0008001500900750040f0f40701c00320185500403404070310a258580301a160b01020a0000c1c542480c45268005018400740c20001ea01c2c07500104840300a501840600924007500e04e500301020382400074294080d54405c1d0700c001003021304458100018141180c54200c1c50300303a000341c0107071600c0701c0150070103035103100240b98410070314000038041c0340304030006100e103040c010000d218200400b0105002e148042d030340d40046540707561007003005800c81e120611104116800c5030504010300d008240c00d0605200226484240c040e00c2248110360b181e041030200711081c4444c0c01c041c1c1c0c8000918400c0294038190642119a03041c54900c40d52074580e143c0700200c80341c0614025a28050029400c12a0041c02941c03650301a07484583d00c007a80384440d80000340c8048204103108500d9031b81000c00c001c80f40c006000c080010701240c07021803581c0c04c110b842c00074010985800d4441407408000c0c0000103041c040c103180d100480904003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 200176250 1250 200175000 200175007
    0x6050d030219050330060109050d02061303080f0a0e041401061809020307020a030306090207050a0b0c16060914010605030303131403030103050a0b0f0f1801140f10080c03030a030509030f 82
    0x800c95442500c207841620b141941d045550307080c00462300d040301d50107500c1c1e11100c45889203001d414200017510303404448c1c40903481920f80b00e444120440e0808c100c3d600002d4400682c880032103600a1102d001b60006840510207000340d81068156944140942e50802a0b03041080380304d4030700c00c000c1000902021104564905241d00d009444aa2240c000d6021074203091000842085902c00c490002c1d03041405856843d05982d1010307420306001d0180c13107524400b844030031510801743d074040c0d880d14400c2d9000200c0381081c0c07405911800b00c280d08840f5a0740760000401072518040100d07644070544601ca00101000d924280c40c0c58011400004940d10012001104021000458a100501607070400e0550f40c2c0d1024030305003101003140d000070509542e4002c510341416030312002054500c10800400c0284140c10034260035082102e00d003920420a001344030001d4401c5030101c02805056018100303504410020960324400d28a084040641d0351002440d803000c18000e69103170203000080541d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 200177500 1250 200176250 200176297
    0x6090609060c0e0316030c0603020a0504030606090c0e0d0201080a05090a050a0b01030219140607020f060d050a0f0b01020c0603060a1203080406050c0c1908090d060f06050d0302190503 81
    0x7900e01c4510f0304601030b102e146420301341803140f0240181100c0d4400310b007560117800c00c0f00c201c000e500a41c01761014010140000700004034a030162001800c4110000281548058401000c440020410718050411000d4800141c0d90094410380d004100c1e40c0c0201c4d494840ba440c0754070701000001c000d4042d00a030b003121800c200c2c500d540b0b603040740e00840d10484018101500004102024418003200741d401c00c900d07910f9400c1200c06040f40c1d60008080d1344807018600081182540403041d140e101943d1401000320080051048138000c07240d41c4020080c07003001302c0010b5615880d00b848507124880c00310008595507103074401c4101411801d004459010750f14540940702c142c013030300c0c100c54440c204000101603a00603410384609800040041c200010280a003410130307480c8910a0390f901074100a40701d11038603a03000c6900c880b84074040000d822140150204103e405036086140b24041d40115540425400103440020200403202e00c143d105092800701d142d0310800c803144801000000e810360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 200178750 1250 200177500 200177507
    0x120607080622050603010c030506031c02070b12060112050903040b07020a1203080f1509070c14030a0e040b100c08031003060906050103211409010207080f061b0c06010306090609060c 80
    0xf030113000c0640c001c0c07019844101003030f02035600499855405071302c9a00000340042000e103e10b004000300d80140d84446440c2e8520344603030b520000903036131480007100a000725135074000750120040c1d07205981000030303046c1010070348e84921440c4103000e040c120104a490955541851520080282001d6124003062a01e0050404c410131101305207a000b1050004a400040040390401000010224805035a90110a071040740b841241a140e40d40721103210074507010708000030100c601094543c02444403001c0204401d60711800000c80c0078850701804c1d0780301c2503000b150341c010b0107038820446034036540c802900d02911207880d03001a221034180b510398014441c41d0752101e81a80c0c002c0c02c0754601012880c1c805600c0403070442400c4000b502e4a401103a200c031841002d00024881441076a00b000c0d92020b1540c41d14080c180801c030107800c40b4043c03000e401104035905c400080080d01c01030404101ca83c4054031464140301c050001610740b45454100422035120400c1254007070b1003080100f080f110003c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200179856 1106 200178750 200178761
    0x8100203040516030c180b09041112070e0f0901020702010206070f020a02130509061b0403020f0604181a030f06061c020d060e0705120607080622 64
    0x1003d07249880d028050080d0300600002042034280110703520352500c4004160345c11071601205420b43d4039102c3c8030765806a0400c107240c500e0b401180210b08246004003081905004010010840841e6140c0f1240a0741c900100c412003a91500a010b080b4400d0702000b0303026a00010000d440140b01e240500c901a0091041c0c40c070350345569000c030f0300350b80420740101c1d00d440c0c0b11020404213000410645510104001c4c200c910010495810001841280006130084905481c0140a5143d0b03004480040502510940b181d1000424040003480b141d2450603401459007084291864001145e280303800c02d040250241c1e44071b000800c0b2010080c40102580305122262440140c7c0e0740742d0460017400d0141d1000709580c042020910b00300340160300890712238420390300c100100c1c510004404c0d0380951581440e19850320b0340b43c0010309081c4440002944842d0191152100d006181c004 = true := by decide +kernel

theorem cover : BRFrame.Cov 200000000 200179856 := by
  have h0 := BRFrame.cov_init 200000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200000000 ≤ n) (h2 : n < 200179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
