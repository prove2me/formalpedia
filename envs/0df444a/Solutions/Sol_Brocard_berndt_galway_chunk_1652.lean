-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1652
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:03:52.102909+00:00
-- url     : https://prove2.me/submissions/f6a64297-6bcb-4f51-a6d7-29f1bfe45e6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296942446 ≤ n < 297122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296943696 1250 296942446 296942453
    0x1d06031c030b040b0904140f0c030a0320060f06180103020307030204421202032e06090605010212030f01030f020109090903030605040e1609020f091801090b06030f04 73
    0x186441001c20f5006038581c2c00d035240d69140e250010340104d2094038407030009200c8210a038501048458081c005900801d4055500e4901185141a007034251501e6094900980203100000c2c0c2c40510080441c0304007002c11129158600040b8041d48046a641d06400920005514000000e020181d415000f00e0420001860541e000041d48401d05141c00c545800e10300200705400d0500300403c000d0201d011340a01003550b03507403401000e04400510003900c0400354020950b103a0354074100241c240c6103080000101031002d503581c03145126218060000e940c0790040e080107415503202e191701600c41c0041201645800d80d0640e48109070300070801c0426880d54031945101c8113842005c1c3d041c000d100d4000b1610381894000c80310030070700a44000c59220326100600c07003214940030812910750000f40420004240748c0c0074207021607525000261312000c2204041d00f041c4114070328513500c03240346540c1d80807014440c021a41200c408d03800170403052400000b404003d2204550101c0e0300f544500008000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296944946 1250 296943696 296943701
    0xc0206010b031314060103030e041a0409050f07080330070e04090602120f010503030f16051c021b06040312120b060c1f0b06072004061d06031c03 64
    0x2824012407058850319221130841030540384c0340d80307590740280d030041c010305411044554180400366002c11010591032950090b01d1403401780c0790322881d1107400240034003200300803c0d0850707007900081d075940568a541c03050f52540f016810391680c4503010318214201750020311505403006001d040d2290303950307821002c4910405d0704000952003550741c2d00b41d07400b14070284098001c13034141040c4144681070110303088074a08816030015200e03a05c1040008031055088d0166104001d5a281d409a020450304c0c00ca0308107201c0b01c4040e549401c40c1d840d108072480e8001140300c0607501e69a81c80e0050000c52041c4542886030307000c0980710349115081c14641d0340c464000c0c28210b050004000680482c1d640000d1003d07800301214104c0369204c0e141d000710145c414210503c0742c0011500400001081c180421554090004040d207240c05102540885038456200446400700040082020701d0322904502c03910201c51035590703614001c48000880b24140015040444180001c603c41d5401462104901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296946196 1250 296944946 296944951
    0x3031b09120f1e03020f0f030d020c0a060207050114100303050f031f03060b0a082a0105070b1f060c0309090f0905030403080a02011413150b0310051008010c0206010b03 74
    0xc002d03280d04644404030310780e0381503500c208080c2c401800301c0100707505000f440d1070740106043c1495048103040c0c22032003070000304684501421400243e02c0300013003001642010500714003c3d0240b4000260750003041410343c00b058818a400983c41b420340c4484481c190340862900000340454010018000d055075500007a5074409440451101c0e02c50303444c032040c503684030b541d44104c40840e101c10310342c2010f00e04889240c015140c0003008001500c1503a51a040310149103420404803000c150b009841648a00225a54250895500d061905100d076518000040c0d450480c40200520080440c1451103090b0320300100b81c15654404516007030083d250004c0003240c5503004140c0c0c2d64001d88000980510150000314015400da0344c503448108030207401c2d94034141c05080804142000c1010302c00c1510b0500d58410f401201c00008440003000c002c1c024428021101c0d494402d441200076803280d5038000600c503820f62000d0860701d0380c7d20b850f25401c1e256086450000f42c1c000f03034014804069880081d59 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296947446 1250 296946196 296946203
    0x6041d0d1803121701061110020703020114070e0405010509090a020f0a050d0c0e010501020303010819060f02030a0509011b09031e02040603080d0b060a0c0f02040b0301061203031b0912 81
    0x80d8607660703952102d0a060b190f03038001000c181103501108038401c1040c440e6004100c941810385800843d1180103444401401c40c10503216800306038241814800d6100c0d1034682204143c211640c10660300117445046d101c01401c0c0f2503030400001145070300b040035140b401080250020090b101c500c0c0e00700054060021200b07500100201000541c0e69a142c100c2c844081c041d440b515007280c10051314640000c416007125041d94070400040101000006031402210503d024a502108181c5401c8002c3d0050300c0030407000702c1c008400e2080090640d0300c02130161403004001c01228103040700100001054101010110b101288100041074500c95410750741d84220404480a00440d80000c2c110380103a04191803040000c100c40e015449c040c8544c4a044004a0315075003407140021000b40001800701d0000c0c540150320030b10748210346075a0803546503c080100280070003038481009030020b82000406030b00090810002d50308004c0b03040f1006c0c50703000c91565200306082c02e00c4c4082020301e40f2f540044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296948696 1250 296947446 296947487
    0x4050a061b05011e05060a060806220c21150b180301020a05070b091f0e190b0a0c0302120103060207050f031201030c1509140609120606041d0d 63
    0x80091804c1c0f01c0e8500c00c01d003100c2c1c3e502d0611086107010b07041303842c020b055030302034103a000341032010307580112819600080c12601e0301c08590b2810a20307117001d44500d001c001141e0601004a00302900f0241c580b0024804102c0c0e584000c00344035440003560300c52100c491241c4005071041c006054003030003c0c910b40e640d40d240380e0390114200010070b003241c0c49540080002440420742c98100301c002c40d8150b070007413030400041030710400180c401145490004030790542150b4400e254210000e080c45503c1d106040a909402d00305424107260880314002c0791140c02c42071600292a0f8168040c3c07007130b07654a0b00c0c02e0f6114001a821599400002c1d480114151201c1c031074100028404281040206090000203040d15000c2d451850040c1c102c543c203810101d4841c144c258040d01c0c0c2c5500c40300e10811140d000c20500b000400c08008200644a81d0841a4100c006180088102e60000402d980589010340d01080003005025050403401507440840106822419004803014820303103c41d08554005202d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296949946 1250 296948696 296948747
    0x13150518190b192301020a2d02030d0807080a02041a0702030106030804090b0a1a030601030519020a05090a08070302221404030c062a080903070803090f1204050a06 72
    0x84150f000741d00808076110715548403a25400040c100c2c004907035080c0005c00d40c1c05199510a02da440d05690b003d040b000300003041d800410661002c8091a6401a09032034003003030310010003048070200729500804110b0317800114011441500c200c400300d4001c5142030041040c0c0040300c0ca003580c0180e03c1680c1c550749401010022030a0300d00104020551982c000600314202c2080c802d09201c00c0d400110744403023441114003018900001c40740e001c00246400201c954420741108250421074604d604014400301d040030071143c1000080184003400c80d4003420095543d1503050b500c00c1d41d800300940204642e0403070410243c149140300628910b0000210703100b03191202000e03050308221010b4002a101c1c559000034031010744142da0140030360082480c800481d40350705080c02c4256204983c10820b04a0000b0702e040400e000b03642d05103a115140b180c0c0c03402d2812b07045a85561035100d01117a805040040740d0007120081c216000c550740030303210901c050300c0c0004c01c0d5008011650001c0080781c03043c48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296951196 1250 296949946 296949979
    0x50409050c04080f030c0105010501050304110904030c1506050901050a06021c02121305041812050a052203172b1b081b07050a0f0213150518190b 64
    0xc4d1440303030131188001c5880301d112242480c00e5803010303030000e41070210405c184004203a50616415411205443c0501f07035444501d404c40e0040e84001c00902020300360341c8c0d619072031202ca800c072204585d001c6030300100b0342e40c80790100003128880d4403030040907070300c0014402000c08030103d01c014038500c00e0041c0d4440144040c810701d503940c004a00340030454003100341800310b0b1130140f2404140c1041c3d62400d00507850f403a40c9280301d59000564800a000c4007148103545c45d44920101c0b4442e00c0480300f4904041c0b0049504195000036020032200e0326002c42034846e680c02d0b50700980c0c4901e03c500c0300740358000b40407a40c80c02d144d25510ba00000e04d140c8032400785000e410b00c010080600300955885180c40e1030000030300c100c14100102d202c42102410468040400d40000e401340703a50340c00501c1c06650044505c0014100c2050003030032580c003414030700c00d500300003908140d101c100c440c190786941c424030f100c01e8508261b40c4104c030010318130030240611801206070b65100002842000c0c2260304c00207a10304 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296952446 1250 296951196 296951203
    0x15010f17040302060118180b1314150105010804030903170f030f01090c09061403071b0503030109050f040b1b0c0106090b0a0807050603010b0c0a02150c01060f06050409050c0408 78
    0x110260051380c096001044030741d03540c0d241c1e2a00b100e00c444040002d50010444107090b50032607a000341c0029207100108028140248514011780e0780a1080d400544400722060f48580f100e41440d008190888000980381d402410814406c55040d6185503a441c107680d1a0001c280303459000401079803050024002c8038100b107000b140034501141600c1c885614282c01c00341520784000704001001055482000045e0308407072100450400300000d20b490360350b11041101c800c5000b03a014800450701e04100b4050100110081d410f8071113000060040e80e42d800070000d81045c00340c2e8000c0442e00031000045842846028400141080711582d81c0381c0714603202c0307442c04e45200707800c0380c41c0fa5680c507440d284903442c01e422004010200d24001d411180e1502d4000f0700c00340014452400b0b088400100584402000d0081200031607008200785040641002c03c0a0590000045450310351b103040c10104098000c03541c04230480748240c0d10189080c0c140f00303070714010b0712015000e40d9503d030050001003007407417050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296953696 1250 296952446 296952451
    0x90405070302090f030c060703110307020303070c0e0703060e040206071a091b0a030503091e04020403080403061505030c010f0203070b010b0c150c0a03020c100c03020306031515010f17 81
    0x641d000368680c1d8030b1a04000e02c40d020066003c0c8294014200a00c140c3c4600041e1400b8581605003c000000c8002802c0d055220780c0300000c1d4180000600d0300104501c134510201611170702000c181c2c0c1741d40c40890035421110b075030041024202ca1071000600626000d8000c00401c0d2003240b45500740512201c0e4a010716005076030000294000c403070395070308414048030703106d8190300c5c01c80c2c030151000c1c03031030721055128850a01d02c3c90140d1070408031710300720300030300302e000c9014402c0030340115a2140c4c4d0b420042d18030780240c00200c450608003818921107410400f42441500c40040150a210070341c4801503652030101d044000941c00309101c1075002c40c00e041c91150003402c200e00e0300ba607105c2d40c00c00c1c2c45082400c140510ba0100c0962400d1180109a10050700c004100600f40180d03200d40116549280800c15003601c1c0400c0d050030200c2100590580145000d61816000c40f00007150409800010340c004940e200f0f80d04401d290b00b20425881080c1140441c0c041c7d04165804180c0c0014069551404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296954946 1250 296953696 296953711
    0xa03200a09051608060904022b060c09060c171305040f0b0306091915061e05011101090503030c030c0f070605040510111b070902070f05061501080a11090405 69
    0x440c2d0030030100004030240001c081007140340c01d0f0268501807000a055800160001e030207040d07203070607441c50743d030942030181c40c8540c402c0e540803450051440d00002401c4007040e06800909294000942c143c02a40c0e4110059844a040803003081d5440040e210f80d00003d0441c0301854010030002116140d500c24240c210107003480c045210401039003070500d0580c010f81142c9095003e41040500144081e001d001e801d075000c62030303a2421240d4244200036000540140e07400c1000d040c015419a12010220001c491003030722000c0026403940301c0e9500700c40a840c009001e0303410810000e0300d42c1c985d0304002c55001c0900704c0841c0c24920703452182d61050700404c0d02103034040d949000b0311083c080f0070040d1200480c0c030128203000140c52018a40c0450050200402c14607d2002d10074460b0305081c020400a002d83c04011074481c115424007906040001c1d0055409000d580b02194042058010036028954189c40c0c4d8003d540700c4400c10b500505100c80c882c41000d000b4044060a90f8803801b81c1d600501c4c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296956196 1250 296954946 296954951
    0xd141e090406081b0f1008071206091b08010f050603100308031f08070b04090f06030b07050a090806060f010c0c03020316180b150c0111040e04150203060a03200a09 72
    0x540c2c401c04c0d0782e00000a000a0300c100380c031100d08900b03560f41e180240110701e90343ca030060490300c1e01841910120117844a08000710b0030144003003442c0e240d0750710070719500c2c6400c5080e00c100d101c52a02901c8880080c01400022003107114144020305003a802150000d950203106c996441e40c85d00d030404142c000b41c400064003d00c0407081802403010010030000380c10220041c12185140220800982c4610711558035100c1d240e00f40c11864050640c40383d0015a004a4030343c1c050b02e0141002807955001e14980001704001420100300c4e81c200082071845984080c0198507462100001950541c800e4201101c2d1105a0300000c03005071402d0104054045e80300482881d0141045000520711003170103101c44209190004294260782c60010b1549095040d41103296030701c09454010340540120b0400507540380340010300040781e15045040d28400c6016a041403109030200c9514401d0f0300c4292130465114034a404c1c2070020403140c2d141ca1785031415205808d8201c0001e8404070341561502d601c854401139 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296957446 1250 296956196 296956213
    0x20c060d05010e0c040e0a052703090411041d06030f01020a0c0309050402160201051305031f05100b031b190e09010812030a0203060307170f0d141e09040608 69
    0x8004030203c0d03810410401003141040d0400750390400022004141c0320046441d400828020015001520200380e030200081d070707480c83c1c121901ca07a26405542041d0159240c1401403240740300080960302034a5246015141c0d640707a0701d050440400024282c1036150154010100e00c081091006103080e240d65152600a0300315420050a190320300c0e031099004600411000e01001d02e041140c2020343d0342400c03c00c0c0c0307030a0710140f184881d06a07900035076054400c3e161201a516104248105411000b0000740202c2da07400380490380d40c0c01244510003a10a0620105810170801d840350b07810100700e840c142e0300b06184265000070144c41200e0348400705400d07064030719181c2040400c03540584246401003e40b090340d0354050019110003450342070b1055021010074036607602809030380001e00b00a04040411684044c2ea01d88a00c4004c03480c8c0c07130354032550700800d4809026428030741d42c0074543d0f068182045c541000c0c0004040c08489101055072040160080d580d0729485082c1c085c141300c200401224 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296958696 1250 296957446 296957459
    0xb01030b070906080a0e120a080f060f030303070c062a11010e073003051207090518040c05061306030b03030c0d12140408070b0a0510060e01020c060d0501 68
    0x110000342a607802c204614070203004080d008007809401c18101d40000440f400c4085a582c00c2211440c0000d03941c0b00b000400800d010380c004d002c3c900803c0c1503004c2074000d4503480d00b00080400c0180c403480c2c154000b40300084c1b2443c041e50b842d95526008540109600030701b4964220112998040c49030140400c2c20075044e2284c1c000c014481004c3d107403008202c0c2c6482000810358995a600c11002c00000701c51925010745605c0020b03010300440458040741103481450301419640240b85200c4000720102d0005461520940c8064100e03900a0005220b00c07103419852094100c00402c1a1050800444009220b8941e40f0090407410b0501413180308039820b180c0b004083d244030080d414400d9000348500701d0105004958001c0f041441d083c0861098a85000711000c0d100300250380c0348a8116604010901503440c0c02400f80c0c44c4103503501042da0380c59a00c0001186d10a0381d071921a004021024444a07014151805a45070140100e40c1031160440020345554803162002e0b44542d212401040034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296959946 1250 296958696 296958713
    0x3060e09010606091206020c0d2303070c03031d07171e060711070b03090c0108010b1309020d0f02130503010c020a03080c1605012d091e020303090603040b0103 70
    0x40e40001e0054a28006004001c02810702a80c08150064030065040007800c6d4110340034482c107203042d1601c0641c0c0700d002808900d0f4441d441c14590000740c0c9800b60070003405086a10407003a545901c05250310948045004000d00c45d42d110701e03600001d00c6400f0102040101400034000c80c00c01241d0406480b0840d0305154041c0c000000e148450b0307440380c51518011a10b203600140714070700010700701c04655201c0c1c03a01740c40b944a00c2004c00000140452140089001002d025003078a82140b16683c03500d29400714802d5005260101304111028040741c0b01076002085001102c04000c524407034042d0040c422603000c545540e00c00c013414001007000d401e081c060900000014005070012811680b8003800383c0c0002014030080e000700090340450002001640504c2640210082211031498015950b52a508585051600d00c142d1104081040c06000d084490f540c041c0d9440d000c418a080c40b11008042090102d03811300051120300d12544030303040514403031030003401210039a500d5404c0140340b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296961196 1250 296959946 296959951
    0xa0902040605030d02031b1e03030604060b031302130b03030d0618060308031f0b1c0f0e0a02010806030a170a080702030a0503010303110a0b0a0e0609010902011403070302070c0603060e 81
    0x1030307040313850803451058001c0143c580160403803005034140d40d02e040c009401c242c46100280300307503a900d5143c42604000080030b503204107016030742000f0141c0c480c120f6052501084440d5020880c22130300803001810070042c424042d20075004085882004040040e0441d0022511240303d036660340d800f04210286c40e41c005440d990012001c00c011400c6807540a030038880200700d54415070f12031201407440c00c0000c4202005019604405407221500c4034002145403c600050034050705111041d03002c0c041c1403082015403121580140107120a030b5006665a10000704420751500844000d07102260003801d01c0701c0a015401d546036603941410002400641c0068608800c5500034030480b64190b030060205c90650380c250600c409208980e000340781c80c0c9840510001c0094413488107100c0488419080344c9000420a000d5401c95a20088410700b01c94181070041c1c002882e040c3d40510f4001c2d01001141c1151a904e0b0140c0385c80c585440302104944581e000700c0000c2c0d625401000085914200a078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296962446 1250 296961196 296961199
    0xe0114030a0b070c030c0c150909020301060f11161d0702060601050405130213060c0c0f0501050304060528020306010e15030c030603030415180b21070509130b0a050d120305041403030a0902040605 86
    0x1801d41d41423b4004000001c0768040d036049c0107000341c000d45081810020500c548904211402e14580c59441c540c403d0050184400e0f02e00310110b000ca501c00303001207240d82c4030340d4041e51442d00340342c0307014104036203207030020101c1100070f40c2081840828103da402803030291416071034440c403940b05407500703540a404590040c0c10441803400180b2040e070b48142100c3d040364000c1d00228180c0c41d48180008950442c03142100e2000710708003e05803180c043e802070f5105690036281c0000c2c0001207001d000041c90441c810008542007000050600940300e005160444070103401c5904154440c11030140e008201203201000c50580700070203c400d00482e00c80400307805075458003405d02054288244200f455900c114a03000005000181480d00ca4030644141410081c80ba01b40c8060a0480340024801024018002c00d9030341c10104071803c2c400d017120300d0140e1049208010360b4010030124000c2001038021984903842142198402104101560040f1481e26000036800b030944100400c617030342680700300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296963696 1250 296962446 296962451
    0xd06030c0812040e0a020d0e03030a060f1403030d050403260a0c0c0305090103090303231006020a0305070f050a0c030501050604050115170406060f0e0114030a0b070c030c0c150909 79
    0x9004c10a1249501c641043c2000409a11030751055101c0c405403032031503082c03101c3e44004410059458a55003010301250280381e14041c0c2e041d04c0c0c3d41c889036031107080d012807a00b6510800489030452100d41c0074507402400303440c0c01040c85440c1c030314000c82d482440d90704000e46d02966082c088a45918800e0841000007401d01100d14041d603900074050340900b040240c18035030f8540c035410516004c0c1e000745285060b0211100c040a14885011400160036520240842007004001c1006400001e45c200c0b0310344c16494050030054903a0b50000e0000f141780c1c2c01c0781c0900940c100f0600003940e40b240c20014500ca1000030607280b03442024802103850584c0100d2210060410121350701d500714070700440c010940c00c0e0f04c2d002c0d42e54505203040502110360101540d142b1080c0700040c0c003081c0714801810783c3e10390040c002e100351094003010358407035100c00040c00b502c81c20404030304803034010624141c9052285c00d042045440c01e40310440781d034150340d021a481004440041a4890780021050b004d801c128604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296964946 1250 296963696 296963699
    0x60f0a020d030b01170c0703090503070f080c0604051807020319080708160f030c0507020a0e040c0f0b270a03030305090f010204140603190e0106031707050606010e060d06030c081204 80
    0x1100e04103001404055007081c001406509040c803440d127400c040c4c00060304070344480d9602e82d120368820304a031007000058050329030200c1d0ba602c0c003a021142118002451140040000406208501405020941584801c1251b91414a1490f450166440e0507446280340340c900380728080c2c000c0d107000708002051703181400c18003941600250403140c0307078055140020703501c0010340d000d6440d84a0300201a50040e800c40d000103001c010301c0340703007032080e88120614506d0681c0c40d5500503008007103000b0042d107404107000c4007903568219a4403000341041c0c041010780c5101c110300401d51310b14842d00f00344c0c0080c1d1138408011081d07000300024041d0300040c80c000c615052a10104021f444c5518146a02c6280000042980b000903412001c0d03801d074100d40c1c20803d010014a816000313021602c41200d40540842c9003070451a920003d03521865003040c0503000350707510713000111100d81c040040b1650082c024412666015854810503020b548182014260f4a081092407441d110400300b8401c10706004010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296966196 1250 296964946 296964977
    0x709020403150c02280c031b06050a0f0f090e0a050105040c1404050d03050909180c1e010f2c120c031207060204091b030e1c080402060f0a020d030b01 66
    0x88512140d485d019060450310b07a1000160f5254a10102c090038002e4910004024031141802041e0006548241c44e12034507903540c016035841c02400c81050218a5640c0480e410718003404400912400910700f0700d4499403203600d402c042d031405a0307e04030f055076204018405801d017407142c070504c5400703410301d07000143d4400b501210b0741c0300703034058940104040480d080c01c0600a50954811010040915000d1b14050724400c8940180c100004603a04c40c000d10b00d40c00c1d0500840d01c07200802144142e4404600c108015140c00b145411381104120f160821a0308642850845124003a200104d40300c1740400e60081214181004200f00320a4001201510866400007149484980c02004076621461942004802800b5960009030f40703904000b0154200c0d0410010358040b9030340c9403001c01580b00c0c141c50241e0b94904101c41018075003800c2000400e00c07402a05401c0d880b030f02c01040b540c0390500340814004075800c0301c008007015038000c49a036080e00ea09400f51581c2d0a400b8600440086071100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296967446 1250 296966196 296966203
    0xc060f020304170d03111312050c0904030f030507091d0613020a021605040b030622020303042c04050d051602030109062a050a0c150507051b070f0312110709020403150c02 75
    0xc07414103901c00c0440f241c0200403060202b0b2841c0380000b031511242d46001e0a005d01905051b003943c0300000e1904001600182c044c905440664100006c40c07114042608000302040710050300d083d038801e1500500c5140507030103000800d503060362640905129079640c203202194000a8125610450521609500c076840020700740354080001c2294038001c42e0404542c1d001240c000101035014000003d010404030229070030400b005503e504803950b040c00340c00d0401c22409060ba0000c100d0380100381540c4082e4410009080d00038400001344240d81055070001c0d0844060031001c90700c03142c40f81744100c04400f03c202d13801c050b000c24285542e02050408001451840740c0c0170264141700031421000700b40441e01c840c0c207040e0701c4002020051414042c034042c00c2c54009000d0028441071801c01408040d5000c6000000c40e10b41410303084202e41540e031341e4031075508400c3c01c010030400284e182a46e05c0c10304000080040130203442c01a030700d608505001042e00c0034940680c1c03203d428240620300065000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296968696 1250 296967446 296967449
    0x5011a0405011a0a050f0c06060112140402040b011b0c050108010f12080f04050904050c09060303041a16080d091e1a060f04020f0309070608040c060f020304170d031113 74
    0x20080c0640c1c0d8800c01806485c42d0049903c90032009a020454100c807500005a150003000240c0303c1d001481080c0395000e00f501d0a071082080300741050404603005040982280710444070505020309000c0075441b040b0b904118104041d142c0c2d110f8240204002c0d40c004a40c1030140c44003480c02400e01c1d080428400320014540350080c100c02c0c0001c2d84442c600d8810040d0742c0a030000602548890500d400d2090781c0d4000c3c0001d813407284a41c080840d10500e00001140c00f02c440140c0003000500b4280c007aa42d03aa00991141c000d100400c00103d000104064020b0443d400382081c0011914050300b480015280181c0c90b1f80f490309002c0d801c2c1004201c1140704c0540b442118407011401d5610304d00499545c0075200c0c01242c219002040525030406c2136409140315407001c0c0100d420031070b500c4408459103501070ba0041c0000480d1f110921038980718400407040551a070040300d00c2c15595480b88405070f250161014a550440302129010079410b01440c45101c4100b03000a013000c07850605820300c00103d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296969946 1250 296968696 296968739
    0xc2803060513050f094309050402010e0f210307060912090f031e060e010501080c090903130308070c1e080f06390313020907050304110d0f020d05011a040501 69
    0xc0e0003151b5000300340703100d20307284c019101d5090040c4e040da20208003014001c02d8400f20302045143d60400041e090001024500c1800200100910701e01a90044682252041a1003060200300704420100e41c0b1400b5005429110380811404c13a42440b00092010382c080e08080b0310340400c8001000864020904818a0078036080c0d080d40c10003c1e0724011000300030290034402c95500f010b000140d0000082001d01081505407440030881e0b540030840da440384608040f004c030580e250482800031030f882da0040c0801c940316540b1138000645480c40e80e801a8403e0b80d94184a950300345051290206c284550384880c40c0383c4001340404d041181424005c480744c00d641d203d04d0945d1010300c5058010f00d80ba10104c0401111074250717282058140d0500d51000c00400740c1c003880c880d40100c0c100350322540417a4480c5d50442c042451040300f08082185108580609407064001d224041340075a6894416508a0b07216900000380e482000007611001072003000e420744114038040040001e9180c114140b04c50317200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296971196 1250 296969946 296970013
    0x3022506030c020307050105040309050f0102030f031f090f0f0e0a020f060a03140f090d17070810030203030d0f1b05041505040b070501020405090c2803060513050f09 73
    0x210040b0803451401541d0000d0065800d04041c0014150403220740c2d4103a41003610354840404071003005903940c1c850220a01603e04041001444c00d119400c2008000410102201d04541c2e8544da594155884600309205c00c1e075a03002210100802d0f4404d4a8048c1034100280582442540000314000c0041e0640ea000b500005040d510741d9219900241601a4079400340b070700f504008213080300c1402d040b6001d04c4030348a4405850340481c020015002d103400740c148040401c4c1d451300d0013110800740c043c4c884001441102c0c0040016541440035142c5c0303800c1c0307901c005440c500c500280019039200c3c0300100300c500550035007c58070390340c0002120309403020f80190901e4402803c00c1255107100d1035100d100a030b0800700f02c200801c601034000340120391003242d6244160f111881411650b108444a000000c66000503580100c0c0b0300c01882c8001c81d409040c00580184d4500c00304420180448903e00b07405c2e518420000820080550185c2110480307004003c01c91616180a203400d08014102a0225 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296972446 1250 296971196 296971211
    0xc0a0f02030d092001090b04120602070c0303020c0a0504020c0d0503060d12080406050901110405190506040605120f01080a0221030409090303141014040b06070b01030302250603 78
    0x600030021500848001c1c00b00700f15480702d034140041e00c000f5050103143c80601c00c000d015420b41c450700b1200d0030341e90810101031505103440039160170000407030700464510b0380038071183c0082004001c00707500a5010f600900058a80c1500700419008a600070920451060014441002c0009441507030301c45581403195407074403103400103140c040e182c07400200508043c444034503501744d1000306140598401c01c1d0034481501c07003001d003a0a0f80c4403400c00b855400010b00040007180380c41005c0c40d084000307801c0c110314003070385450224405600a801c4140810000181043c68840c60fa0140341e100c142c0311f0a4490950509401c80e895000000000e407140b50b014100d01260203e8100404129042000302d95903144e451440704041c01741ea850580102e850103081356031401014071228400d03602d1005501c21542441c0101040100501c0120740069452200300c42c079880e514000c1203268000c03480c0078082d614500d0020700e41107420901030b96004180c5000007443e008081c0c0b24007506c0c3e080c00c01040c0c11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296973696 1250 296972446 296972477
    0x1107060207230d050109051203010e04020603042907091202030c0108090304090207030c02010e0111060402010320032406070f0f0f0b07170705040b18010c12090501020c090c0a 77
    0x100c0e109020903600c8003c481c000002c000056000b0a42144a08140c5109401c034162990350744c0401d214511107410140002001031410030011030b8010305c114003a912241c07482140500170900c6c0050b868901c51110240a12aa0000000802006068502c0d61011000e6000c0703600c41c4c20707070480e9505005801c0c02040c8088400d00550300500410702c411502d440903824002d0003100329041c00d901148284c42600003a512448203484607904041c02088261101e900440082c11a07a0f80c000c00c6200440c4200000004d203001940101980d2900249910280384080d0340c0d410f003946018070a183c00c11030b00000600c001b070b001c035449030040290035000d411130801c0c0110030038040006000035106000c002c65150440ea20489152a603501c552160b076a0020684170f0344658000ca400f0200d081c0071401b640e83e4860744a005140041c94100e166543e0b0743e4901041c100c0396110b1034041001c04405121742d503410060030088820485400d00c103405c00c0400900d00c0e00c14201e000080140c1c0c5502d5041d103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296974946 1250 296973696 296973749
    0xd1704170c03040509010902030f0f1503070f051503070801230a0603021e0c1e070f080601231e01090323011802061611030a060209011107060207 64
    0x1001664109079a4104610a60303450782e206016541c0f284021800110f0320b450140300b5203225080c0f0808003401e80d2102c404c01c2e41800001441d0840c041540b0b00124156102032107004001c0030708040c2c00001c0e60904040200d0340c08064001d0001306405d200300500b5650001949044607030001c5a0b0a1404203e01d4004c205051604a140c2100d40490002040c40e810340c001c098400e0300f180c10250350070790b1100590301c43c490000100c48582c8030000c4003c102d42071b812240c120782c00c500d0481e4403141d41d500200358514525403005c1d140d50030120042100c403000c00f840700c042200d407516414a48030702000240700c1600d82054091010a40c03090419180d0040385a00702139a0421281c081c441d1f0310301511500108861984103455003065884160380c4e5600c8881d10440d54000c5c2000c0c10310040c989103600400c0c84c00001c0d0742c040c007854421880703601c0905c43da1032424040c41015980d040c400e0000760a00c2d040341803003501580f1040741044210ba0100d2400300780c880440080f103c00e003092154100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296976196 1250 296974946 296974973
    0x4140a050d0503011401031a011b0b0702010c0f02010b0d03050a0203120a0f060e04020913031205041209050102160e19020c030705010b09100e13120801050a080d1704 73
    0x398819040000740480e000800b842c100c0d00520158500d03154500c1c011010f40303540c02c84840300e0b45c0c1c000b0500c030030a40c011100342d10a0f0484260030a144032240e04e0306500f000003030300d000300580d64401c02c8100e1198840c088803801686400207101505006000c00c968005500b005400c2010205652035000e1003401200e41c0480c007019018014141190060700901000d40210400e61034105c001542eaa800358500303100741e400070080d511f035a07034200140c8520341301c001c0b04038104580b2000064980d03c2c6440b4150250b0b00818106000410184001d080b0881a0704460b0642d400000740300001c5405c400d00c9010348201a0f9124096295800110845035100400000090010903d080c108400001a048090060009000340038440050001246003a2820107072951060010b2241d40c002c1c01074150000d01c212800c2c10402510f4490921100741d082c44200003444803c0100518544030b20343c90b02034070307400e03000c0c1510390418440500711052508002c08248920400141406202e401c1c114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296977446 1250 296976196 296976203
    0x8070c050909060708090c03030f0c010608060a0905070504050603060402041d0304090f06050a060f03050408040f0803030f01062f030c011506181424040603022107020604140a 77
    0x40e42070204100b0f0f140c220495407840051070703000000d09150800200004000c40c0503028524000c08c40501440c154172125881d1010341d00c1d000001424002040f00070b06c40c1c8005440021031100314641a406c041c1c540d07000074403460030401841083c0e580818803541190381100e0010f0003108101700080c6e015500141e4602c0b0307000100c2c000030402c810350481049118480c0c0300300711442d01c980c01c000f82c8000d1400740c0000038240000c807039107030350090340a90380050117042494101940c94003070403425641c03a0045201500f000c001c1c0b1096001c030110769400b5040c1c40c241080305440110424104815180f9001203004440752440d08803c014002c83c0c000300080c600030310065010180c00003450159100d001c0c0003d10000d0002000c0450388452801d9804402c2d5186c0c0c0e4a241d4410044445228403500d03181b144128209500221388000400003003403142c03009a11051080d60318030544c0c150003216690b141018041007a11076010400b45d921a41c0035544591425222110f5883c1000300c68005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296978696 1250 296977446 296977459
    0x5010501090c0201050906010f03140c04060306090203100c0e06070317040303140f070207030b06040221090d05041a250b180d020c041d070308090f09070c08070c05 72
    0x81500c10030703600300310b40000c002d80080c00540c0b5061100c035600d50007481100745018505100b0b000107090880c0d520680c5a00c0c0b41241d5900b4030f9000050102c40280d4021689250b84491401c11810144140c995059030742da070808c0f401c280701e00042c242c014400c1800703120b110001489000c05000b0060604184040b150510162034079107405402003076142d1256107402161300004010114040c8020f00c00e03480c0307071f02800440785144d444040c041c0002c1c1584d58807a03001c0c01004000a8515284807442902e0078040800381402121b0a04103082c0d410134404001042206014002c0c0400e0820050030402c40c415543d5044031040c400c0b410641400d4440450000c2d0b144014072040c80500e6005150740c841c900c1c12051800c0d501590f82040072007000142c3c0080200603842e00c0c1c140d000b00c04880911084a80803500d00c041682850b41c0760f041210b4032103000c1010382c2c1609004a460050040a6440780c019060011010b0180c502d11070005047c0400055507a04020040104200070034010704038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296979946 1250 296978696 296978699
    0x311040f020324030d05120604060816090b030a080909040c0e040f0c0509091c021e060901050a0e030301030b040f0b0c0a0305220b0a2d0b010f0e010c020d05010501 72
    0x8852000c403682c92030001c079082200503c0c034a10300400c42c580900100d498040c501a070300408444410030041c420b0b580541e0743e060002d800d51090001004905110504c1d002050811020100311031402139014000c0d484001c50b54001103d0a04903001c10304d08a8074040c00c5c3d9210300d8003400900803504512081c40840c41488204101c07141d0515006114260b511400b076120028040316134001c8510702000d038040c05001000110360f4130300000781001403040c0ca441100c560004000e640707000075103407030581c8800c0801001810030b1083c0750308101030f102c0038854050b01d84c030345550360300040c0806412586190041010407194820030410f1503444000705489180440041d2400d40000003400d01090030000016800031040d0340020140101240c0d841804c9200d403984031001c40028500000d06540b02c0c88500f410b1844007a485603910040d0002524610500041c001e81c0d00c81c51105051041030910400d000b0b40011520840303035820b01e40b41201d1149400042c0b0500e10f940005401541f07060f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296981196 1250 296979946 296979961
    0x1c06091d070b13030209060f04020a090e010b0c0303071d15030f1509010b0708070b10030302071211130b100206061903110d080706051009060b0901090311040f0203 72
    0xc1516098108416030300400d41d1019540000d1280541c01c81040300b035a5001d1005150440f842904240b001d855800096a04004502243e022b0640c100118410100800103080c0b0001124090f0024200c0503082a07038440f0400c3d42ca00021b00344a0900100d03125000007003c00003407443d4500b130010944001842c0b40844808194410384400b40d25988403800240d00e0f1384104404c01c100b10b0050140d003210307031801181600e140c021b1441104c0400c01004600045140116914004c1d0007600c1c8201001e459442d0282c0303010500ea2252400c120f0303001703074400840e0555080c10030585040d035164400580002e00135004020054065038042d03a403001011200b54000b40a920400c006d590610001c00742e402e50540e01c1c02c007072000500401103060b182c411401d28400c3c618400384602c55041c00c1040702c0d95101c3c169241261118515081d00c042000301c1080d41c01618000c2c40c1c070412440c544400040020400c818a000281002c0da000d0602c440c80c0e200d940c802d04140448070011901c034100707031030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296982446 1250 296981196 296981231
    0xc1002250b1b0a0e060a140c15130308011e0801020a0908060109060b030103021c0510020306040f0605100e031e031b0309010507060b061306020303090714061c0609 72
    0x542c010700c07240d54948451085400b1030112080d100e1540c40e011360300800d82d010400030340e211111210420086032580c1d4150443c803000350040b00202c001500c3d41407010720620400c030030700070701c404070171001c1c403180d01d003c41c0e00003400c141907550512104c07100186180c4010402900da600c8002a584000343d4901d0599202503d4019900c1010940307450341da0303070114802500d506000e00040100b082004000618110b0303040c42d050b9600f0980f80d0400410f41e100c540c18464014a4030a007960000300700705403482c140c4548480b89401860030011241850042009074003420840c0c420312a203c41c070040c0b071365410081c803805200c14540d004501440600b00b142c42c0c3e0000818200c0c4902043c988020419020040c0c58540e1410394896051103010b07110900170349207001d00c40b5000312003000404642c100790414030000c1c000319001180d40f410440c00c8517160244a610450b820002c02c80c1d41d03050b650310001150105244400e8008481d041210b2060050070982d000e040d03110f140c08a44a00c0c880400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296983696 1250 296982446 296982451
    0x314030a09060503390a0507030306061805010f020f010507020109020906060304080a0c06060b03040c060809060906190227010206011d011703070c060810050103020c1002250b 77
    0x240e4a54040c955281401e8406000c15a05e51705440007050010909a0443c44c201614140ca60801282d016008450749a150702030b2441034001203000480300d0905405010364402001685046860340003103200807008145103001301410000309032042c0c50841c0c0301304510144908098020403c504103458003900074000c0d00303400c82c007039a8282e0014555280520903a4810b6812400c181d00c2e240d1010800c440806a8403c00c07290742e5981c0308041094550b00000d181314500c20f6240300001414114003038994400180191440d0b4003800c20005640c41c04118150404000c1020101040c5030a1264029000e2050703214005801040d118050b2a510740309148040740a030207071101642c0368850103065903010115031960540503001002902d0128404021b204244420740e814481c081da101c24090704241d001d20000f641e000d090090710803540c803d0030000c1409003800c61800806510103911981c0790000781034240e6001c2010104034240104840312114000718005107206ea5280001e800c8406 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296984946 1250 296983696 296983717
    0x1e01080610090b09011a21270a03030518010516080f01030314030402131d010c05180d060b060403050f0d0309030203190306170a0b0f0105010507061104031403 70
    0x58980060b0725001c0d4402c0b0040118050f2a5040d04d03820906846030f9036034500c0300080700c0f00e810021030f6040311103602c0c9603000b9a8030070204095428044802012814a0142400100c48808040021010001e5545606a81070a001c2100d680d0b01015024001001c401c1104035401c00c02002280d004070f030030b0054240b4035521203441c90340704c2c80c0000c0c04548090000401203011050a004001c24850103160b2140c4000c09070030f00514003030081002d0301c0b1503c0303a8280d05a44200d5040c20a1000e0150300b1f48450180382c41ca091900300d900d4404481449004035020340440c180d21401d02c400c40c0c0043c10614000b901003555242d492412a54450102d64201071900403208a40d41140c80380c00f410350200d0701940214140315180c08104002612082c0540c18580d60f20400155221440c01040e4000720800c00313407030125401d082684d520781000305800c0381603142c04011300c0a60b0300030054803460b80e002140082c20245651859010748140e81010b01140940c0b1800300303140d10700100801071b2404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296986196 1250 296984946 296984971
    0x204050a09051303031a04020a171612051b030906042a0605160606060e01140313031b0c0306091b0302060d021e0f04061b050a03081e010806 62
    0x15180d901e2000c40304103550301c0c0b408181045005001ca40700f90451503030008940603005080c042040003070101d0384008903003808100c9400014885080501141e03601c90f9a44150b001c00c00740440d4020310201e0508000d003246a0384d0804070706060249900806c441000c582e4841d0341c2d050206000d9030f00c0100702d40403915240a00768240c40350354107421500240d5210340c80c40c40d0541c245002640d0f00e802901781111100f01818492010440d5402500d0051019455109034220201e00041c880d01c0d9245038580c01e1078007001845400510000501c0010342c05240903420241070000c980c210404c8041c1c09803501e18481c90200902c445a0300c2003d10314030800a1340d02c186c8a8070054501e2204501c400b81d0701c80801d03c08040e00b1142d40c0c0090480000b580801c2180c1500d80340501a42e411400c0029640600840c050009903040000c0c94205030a02e12800031255056071003503a02c0048240040803c40c8100200d2003101910720f5a807183c07a01d6200a0715039686600301660344080440714204c500a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296987446 1250 296986196 296986199
    0x90c081603061a160204050a0b010e090609011a0c0f03041502010e060a1518050f10081225030c03030b190b13080f0703060b061204060c05040b07060204050a 69
    0xd000c0d202d0402200c000031502152008400c3c2030b003001d6000a08114244600c0c00c44200041e5a14420b042c8620954600004e29003003010005060400e002e0320701c0c0c0911000d0040c030019903540c964850448421018540429107a80b80c2c840741d038000c034100c00c0e00c00e1240241040c5c50500100251064900c031103c048400e07485414120700340c40c0818540321300c0e41c00441c082000d141c2c1b0b6420420851701034400b06c1d21205d6450400c01822003984860741415640c44d0140510400564003640c0c00c00e1070a18900c000034103166449488110a038035034507040d4000184403600002d1420737400c4004890200c0c042c01c101c1c1b907080142c0303028038030302c41103001074544400310f07180349405819103500c5540c00705408007240c100118000c2503403005c060f44268840350140014692820041c1e82c80100408002e05131b243c0c5149480801d4400d40d0800620070301e4284100342c800c1d20480d04d100c0d406a0400300c080390450001f2004d507058403942c0c00a0b04c1d484800aa200203001554004208503801a5107110391039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296988696 1250 296987446 296987491
    0x30b0a02120a0c020304081213080106060f0e030709050903070203070905011512020909070513092901030e030c01091a060105040315020f03011502010b3007090c08 72
    0x9100d4000190200035241d40441c840d24110740c000080d03e0203070700489140c5500d0b2a0320502e8043e034402036400c08000000c1d41d011a4955142c1103005101c1007000380700c42410500d0280c078030340d1600c00c6e031010001c003150a100c0d6a50108030610047c0310fa40020842800d0621a40b6240c1e400700710264028403070114009240d071414071403c1d0403200840c80f0b15408070054041140d150314442c1604600c650280040403103a982c282c1003500a03c641d460f416540d66640d120440640103d40c05039642d0b40c03500511801000200710891446507030070200140b007121500043c1d00402d0b4800c0300800901c0f000c100740c10415815400000001d0040710200c2007c040704401450800c02120380900040d1f042c0400c00000b0b140011075a4a10201e200150410f011003030500b04035002684450340300e001c00114540096028403e207610f10005907050a14030002ca050742c080c0c542c141000388062460344103a003580001c1800303450082c06030309a080c4900060703024000d0072070409440c1c101300b11225108080c040d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296989946 1250 296988696 296988701
    0x140a0309020907020f0601050d05070b0f041707050303090904060e06091b030a0c0e0c1e180d020a05060904200403020f0109120611073513030204020717040609030b0a 73
    0x1176a000c20000c01c010f82c01c040c18400030703001c1d00d41d0886a40c800c9680100d5000138850140520340c1c2d4001001d82c440d85041c1c1085044903100c075914016402030502031103076440101c11107000f004155a0b00b000344d2520702c3c1110081c0b1f14101d00000314042c80007031160700c071400301d46c801210081103050110350380e40c9030425490b8104620010000c100100782002140d640401980e400100d0000c0319062400510180c200240c4454110900328000038034004000051410403100510940313142c070740e044041d40400d656642f90b0161345d00c20030300403887c1d802940d903e400150a180740c04500768840301140a01801c40d070440d000480c0b00300a110907501c05540b051041c4800c854202d10005066451038507010000c145060456010400805c00320b0701052541ca0000d100c80c41c0c804134800070310344004400030340501c0340c41f04001c481d604005c925521800e0501400999804640050340c0d04660b141c104000042c1c80304010742d50202003400903446030070080d030008407030055400142c02d94400104004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296991196 1250 296989946 296989963
    0x307050705131a0d0f0c1403073005191a28020a0c0c0b0a03061a070b0915090307030215060a03110a081b03010b03010c0f0f140a030902090702 63
    0x700781e00b0711480a00b510307050795a84d94441c001c00742208800c005480d28042192540c0050080585060164101d400c080003400002c024252004a40e002d0301020080c0b10b1804009040200c013181d0007880030700900b03115804140c0d10301451102c24011900e041028844007000004082d0407540015001c0b130710015502d10141d0180804606003154035a8403402500b19148402c1001030071140e032070001d02802d00c00b20203800d019071005e807564414817000301660080d8001d0406100a010f059100d0f440c1c0d001540e503000d6220031681c140d507072a02a1141f82c0168940d00507081a0000b00b031100b00350010009001240c00707a800c0c0c4800b90b10110f48a070051100313648080c3c200c50305000402c08518425501c04000310000e1031075a8040c0d6800041c0d180000d0317002c0c1442c002c0e2004642c0109890240304c1c10301420029002030105410744180503100a055500c850180401002182c4c0900c0c482c12059054017031030005151100d40c414070040040c0b030349890407401000c89070085151627000058007036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296992446 1250 296991196 296991221
    0x203010f0504020609090a060e0f060f03120f1b03030c0408100606120c03090b0403110d090b0a030c0c0f031e0e0307050f01020c060d0b01021509030426030705070513 73
    0x28641405c440c11300220280003480c10001d6039907000d0111380142c05100c024014004418404c215081c114208840f1651008083e03210351f22101c43c0c54000041c0d4800d075087d4410049510762101d080000310101101140c441c00460702000003000341d8049000050310580d005c440440350048049e46c05c4004480c0b2500404002c9543c0354040e4401d0029038010301009040d9140c0454011301c9580c0703429500b0010f5400300c02003501c2c600d00000c0e5000401c201ca40000c00b03171400201c5140380401d81840c5101d0f5100c942c00309074541840c6452240511f0b03a04440560128090030824000c4c10010410a1118100300d400e2400007060a861403050440c00c0c45004000d001d02185890801005418858194080d0540c064580c40f0380d1556207110143c429803141c000d0200d50500d2200009060003542d5500481c0300c040c0e50244075606c07078000103a4040d00d00080c01852981407110308044240300300380d4003564500c0002740d1201000004180f010440b00103881c0300400640c3d00400f003003994079240303860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296993696 1250 296992446 296992459
    0x10b040b16030c1e052a040203042a03050d050f0909040606050a090b030705060a02071203020a020604080d030608030a0e1309080712020c0402030f06010c0203100c0c0203010f050402 80
    0x2820528850311403141030302c1c42810701e21040b1060f40d0b01c0413000425400180801c140500842d801e10400341310300e8203094170b041c0d10070714402040c401e0f1410018401d00510f010344d03130200c001070030009255001034694903d812101c06124008044880205190004031064081d00480301007860256040d1380c9884041c1c5502810012254144120444024016540c1c9503e032000011941c8400210030302820f4001c00200f100a040381c107041ca0001c199101500900b020070a910788640c0c0414060251100d2801d80c817612011428100d00e420801c420103540900002400a40804006580e403072030070703080c0c405010b260398841c0f1541d100d000b0110070501003814580020b403540380001811700c480710300c284001456090382c3c49021039038021031000c07244131200e1034001461603010000c001c1d1040046500750f00d50315000340c01d42d4015001805180c11711900c506890f0441d40e05000d8600b5401c4420010009091076000080c44ca190000c0203a00075441c2100c195885802802403500c169000703000b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296994946 1250 296993696 296993707
    0x803070c0501030902011b0c0515041403070e010b0d1b0806120d0203030a02090120010603020108010e010f05040b04020c0105092404080307081914010513051b030601020c1f08010b040b 81
    0x2103101018002c4212908c1d40a40004070349030383d0300d0707220440074007010302c0840d116400e00c000c50340682240405507100c1d6011280070004040028141d42c1035400c00000d080d2614005413039135014050b84100c40d10945140e88070712046690000e0708500c20041152001540143c08206a445a141185210050b08108005981401650020041c403071040c580100d6091107001d21115204102c2d0f01e10310540d4490f035041042d507074030180c403a024000c452a500282e5140041d40d507201c0c4205d104080c0615105c0c074000d0031603580c036810394811110943c024441490700b5410076880d0711325082c0a6480200c4405100748800390014054412607000c98040d19644038402c0580c0c069900902007511101c0c01c1d11055040c200900640c0d010500c1c21f4442c06c919414501000703d09000350b9200f504481c034100820107400741c0d01301d000241c1d00d284c0c110280e0f2500ca0f980102d05180f40d180c10180c00191007042030031404400510b481c9002c80640c4c48042690700c8406403070444c0700350303c102c0d45015814040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296996196 1250 296994946 296994977
    0x5040b0a0e0c10021e010203011508101e05180a0e0a02010e090c04120303151203020c0103090206160503090f04020903060103330b10110706080912040803070c050103090201 76
    0x410b4807030080303d80100c0380410b1512043c01c4503040d10750041c41140e50040010400b664501741d481c100015241030074a00d40c0750100d05c03090527000c41d00c80ca0000800040c0d003c000304000b03100002c0600000342c950284420b0a0304410502c11080e80c51982c124549405c0c414140390209107070004a50595030301d4090103001080089800c006801140c1010f0b0401000032002c103c80c041100c6580700b91404101c08158180b8100c0700740301503026551030560854140d0020b0f50104101c0c0e001d0009003400a4100c00f00d00200b001030083c4158a00f0441c000750f03844050000001c06410403540c101d03040c8100c050b0301700c1888142e00401c00c41c290141d1100006000003100341c440990b070701d0241c00300741c4184c0b081e2082170214025282c04d9003110541d10038043c2081c1c10004040e001c101400d0501121060682c661203560350114815001041090707808213008110a00544104032104150541c9403500c80010310b80740e510130a004c072a84400c042000401f5402400f13603000c855016164070181c0d001d08034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296997446 1250 296996196 296996209
    0x140f010b0f030919030c03020f07060c1e0c080c03070b07020d0b0702030d020301030609020906030a0309290a08060117040c1403030c010c0e011d060703030209060d020d05040b0a0e0c 80
    0x409683ca54014003006104401400480b140418002d0b40ea0900070212414040d007810410184e1010607000100c040c4850398109030310001860707120f540400c1036064180f0325184000c40140044c080c03440d01000140454000070824103110b8114151028684ea4103411103242c030422200070b401205002810b80071076a420010340d8000901d0069900e0006e803903005000b2a030090b00211400c50760780c0e4840081d0300b00401c441342d00460a07001070a40310780d03d40b80a4007a12492003007d40d074010010201d42055222603400740d074483e0100c1d02c2d5413540904400501849000c072031141c0080d4041070a92001104280c40743d000700d8101c0208074150b81010700303580d00e0b80c1c4501500c5416100c10002c900342004244180c1581c1c0c103640e50351050f4400c040000410903042400c0e02e070429000001a41156a103060841d4102c1d03038503080041c0c0c0d4001d0f060104480340503400c0d800501c244003158404014804e90006232156120b442c1246890f6a0300d002c202c12214243c592010a9124a40088241c103220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296998696 1250 296997446 296997451
    0x30120507020d0606030b041e260904060906050114190c0809180a050a0b090624030903040302040f05010806060d0c0b160605070c0201020330070201140f010b0f03 71
    0x34003030580d00c502c5501c84005032144e6902c1102d01c1002041004248584002600490402000400701c2d20980d9114aa0140086502206c0d010070039240c100d40c00d62000c00311039090b2400740c01440426502c0f0301d900d0040c0a1840346e41d0108007503020840c2882e581404580800c0725064400e018444045400c44034004100d408030b9242100700400c401d0380e0f98801007000d2140c00e5421402c20703031030001080d100b92000508400380c15810b00407603502d51350b40e034040c0d5540400140c40500d00f03803441c2d01070301c44400c141c0d01c071a40860b01d001050007640d00011006105407030080d03078148017604090005030100c0341d007403049a400e41c0244000c01c2d0249000c01c5a4151a402104450b803050740f41c3d201c200241e4442c1c1c03425603081a40754080802c00000340100c035031103001c9003484c00711004240c0020f926031064180c420043c1d500340065002c400307c1c0100c0140010070341101c2140600e0180d80180c000c01070044100004068100064401c2c201346131528140c42c00c051a2074109011150881d2068201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296999946 1250 296998696 296998699
    0xd0809040f020711010f0504301b1a1905090f04050703091b050102030307050a0c0501113705090114030c070c0603140609040501153012050702 63
    0x310840320451141c14006450f0042c040c801030088591401d0024120907290000303c81401418082001042009100454906001483c1c9420051480d4220b1008610040c0003440c52105410708203d24200031411410b030b40d0807a05201a81c4442d1030070501500442d52601c1452032200e122030f0849218a014004440703014084200d0303d80004002410b41c0c1044038048000b03503544940c4418040308540d441c0c140d10b00b8110311102c440c20000002d4032840014102000c0c41030008945016034803d03055007401c240c218008119110003000e038010954010140c6070400c402e46454820300e56082980760000714440086d01d14100500b40040e61540c2150600905200d511003000c0f0f0003113082e070b0085102e03202c01142c10b5542c120324a0b10074172004180d0840d02c00c1520380b1004401c40816505090740019080f9600d5456903220328002d801342103000c1900c2c40050942000090105121041c1d20030700d06070f480004c518005800b0390b1045490513400107002041426807004009015400030420380e0b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297001196 1250 296999946 296999951
    0x29070c0206090d05030a0f051c09170a051218060106120905060a0b010912080901030504020a03061811031b040515060a1106060904030c020f01030b2206140d080904 72
    0x1c6030004030f1210146106840d80d41001615010301a400b05d00f2040010351030504506003003000c0070340c0326010b058890200e125950f803040802403000a840c1c00c881c1d244500c030a103980e0020185d008103190040d0002d1601022400041100b0000c1c03080c06100200408006090a1303103041f8080311554030700040e41015668511034200410b00030f018651151410400105441d40300300001070441c001a4008510030402402c0c1000040191040b40d49202091801003120348032750000407070600c042d5100400b4189407180e425030380b0f0041111440d0050007070003460749000701c51052649503504882801c0254110244940544c58142d206640140c0000500c0040709401404120650720a054580109081c040401c8083c0010002240d022200f55074242c80c0381826600a8600c890600000344600d44240d03000e20140d10a80c00841e09500041400c203011448070080e040004803104071300d50300c07418208046441c5c0c0c411142021540d0001e41400390014880d201c00e00705802803070201340c1c0141c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297002446 1250 297001196 297001207
    0x605090a1113141503010f0605090103060e070804140609190c08060906040c0b04060509040f0e06011e14010f0c0f050703080307030b010c0804050d0c0504050108010929070c0206 78
    0xc00b6140c40c1c01821800030703003c0200146500300301c801c143e41820385580310301c10001071144003c840b0014048919a04040e0f40360040a030041e00070b400390f504038180381401d00382003141065002500f13600079402810030340c210700e03c2030021350789400342240d03162600e901c24980d04c0d110400380c00071039400f5030080302c02039241c640780c3c622141401d00549032285264400e00a000900c0042a00036005000c00d1007001d10746440d007440a407050007150b2402e48500d81d01c401922851460b1f402a0746c00400c03490a450056171154081142a2100040f081401408900100d00c41c018a0200d0b040104142c6a00b031005151800848144646ca05c0c00c0301c13001941d08400001981c2080060003961040b01c1090300d0340b07004140103040301c2c0c0e0840050304025956000c007021034004811a01915400c2e5a83d184000c15130070712030599001c0d6031049400c58640000000c0300001035001d80078003480f8001d81811740c5e450004600d41291820080a010b550400101c3e004c03a0040c0c030b42c2c032001e03032024202d0341c00c11703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297003696 1250 297002446 297002467
    0xb070819020303090f030405210115170d0305090714031e0309100f080403110111030c090307050a030c0e220c081903082e06030603050c01030605090a11 67
    0x4520500d260350240c0d1000c8280400984244020f1101d4904000114203042c6001c0003e4003a000c01f270030507004807584000403c081482034002110100360000031100590307450951503181c40d03030003100a10b10b0088580d281c40c904d00c41d00881e801054000d0060244a08041074680040c00414a0a605d80f10350f01070070004c00d918040c1c5e4400359200501030740d21024280c8c1480529100300c0c50140800c98102060035541e43c0003941076810a0f098540482d019540c01d29140c010aa103d0003640d032010007004000c02010f026009001510701581920140d90b0b554040c080c4200703103800000d1039546900030500043c10307850500c076401b000e00640821000342d480224221603135440c0d000c2e0b414040c000d03400c2c841401d0030040d03c0c03990701b03601402e65030030586920001d191080190000000c4338804003512900d1845189514a0703540d041003401010340e9412000e001001076200483d02030180101c556040c0d0b00a100354012900e015140c80d9043d920540c822008124041c1c55440c0b0b541c1c28070001c0e009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297004946 1250 297003696 297003727
    0x1140604180510021c0b010c0303050a0e120903010c080f01150c0204020d0213081f05040c050a060f0e04050c0403021002100f060807090903020d08100b12180c0a0b0708 74
    0x30003d5020050b518600c2c0156201401e41d40030003031840a0030042608140d0764021980300f2556014640043e00b616508c060380b016044000540109214207030b41400100c5a8000900305a602140208481d0300202800c0d0f5080c0c008a48100f0f07486920030042124060300410849690100d00d85620640704640c00a022a040590480d034030682c04200600082c280b07141c1c01010f8003c20008114115110b0050442041d030318821000440d02c42c0c0c00320f010806800c101c071000d800020b018030010b5444040c01072000c2040c41040d00054a070000c40d80140c1403d204a50245445060303003864141541c007402521007034201c0c1c0340111f02c600102c8028624051103840459412500c7c08102203103810b4500e803800f141c0303403c40c44c44c0d985031105000c0007036000250b4219034242030030b002500c0c0e40e982d0300386450302e64281e201122004000400403420698465844d10605407003261420f00a8028004c59440c080049a240c01c03032000181030000c03c4030500a003450750300c140d40d81307403820310103800011a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297006196 1250 297004946 297004963
    0xb040b0301180e03090d08040b19090e0103050a081b0a1b050114040e071214180303040b0109020c030c011a10050712050904091b030b060102011406041805 68
    0x80501000520507101500307001c2108801c064014404800c24000c00c9031a486204c424900c100c80b40b1117198100b040c088240c0d001020309035203e070380382c0308090300000301c00f02801140e10001c0d14180c03000c284038a45100d014140c070341000044c01c0321469030792094030711350182c600d0b030078582040b0401c0180200704001641c4854800c000078121080107182d0704007042c02c250829414402d404c40842d40501c103110540c1d0032112414a111041d440750b2030291580a00d18102540841c1070220341d0700d0703000f800c00c2201d0080410844210300041e420700b10588901081d20b0003840e1400e10340c010032000c1402e4000d41030b02c0001c4003d4034076040c0d81584040c00c441c070165480c51292480358601846203401d0410700e038085280d0403c070340361100b1580c1c2e40c02840301c1c0d00034410038403a002c01c4040041d111a4419401c5a03400010090044182d030b51036102c5440c9484202c8160b083c40340060000c0d441809580d41c0c00c901201c518019451703000c200005810000020703982c41030014419404158204106003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297007446 1250 297006196 297006209
    0xc02040237030c02070e040206070212030708091c2102011803021b0603091507091205150606190c050a08071208090106030309060f0908010e0c03190f0f0503040b04 72
    0x48003122407400c0542036499242491095411503d010002645c40e2000554800c1d0b044425507541c2c1e10a10000326101302c031910019452001245a81c100074804004103d8150116074841040c00020f403440c41e80d10f61034100030301c1c41844541410302111082c051040c6458140004075603d04100c0c83c48000610f0140d00342c0c0142d00c511001e180c2c80c0d845280f000c07070460041c0c54852540c0340509040b561820400b10b041400000b14001500040c490980c0b400603090440342c848961038581001380d51044500380000c440812035000c80d07141c1ca095001c80390f2040d00c950b10080c1112403150155542501c960040e5a03070f01a000c0c800001901d607900a01c00907100340c180100c0f800f030030b0324001c1684500804020027a0326102047c008a038024500341d007220244d00c5c0c60300c10841021404c882c007aa2a5111038959803c2841c402a0580702042200b2034010035400c46101d001a100303005180c9140da4809004002e1182410780460703c4c1c3e80c800c26030a8041c00449241c0750780c45010710100d6025a0040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297008696 1250 297007446 297007537
    0x140a050732100608071401051804110a0f02010c1d0402041d0405060108060903040b0a051303061b0e0a0608090a0f06050115030504050d0509041404080a0306080d0c020402 75
    0x1e02d000d00d1103100e0b0b40b0150440740c0003491010b0a10610341c01080780e0182940c14014049007040003090b4000d107403400320002034401c2c0451085107030100d060750000c03a0078001040300c0d03190654032140f05120b1103d085c9400d03a1152242020f45051107070035506c10130343c141c000e03408100104903c80c0703407a4514501615040690700900d0301e411309500b4404182c0103503c198000300280101001c00006035419501c1d9280880c3e9585142030040ea52840b6146034521841e4034601e002040c02110780c448400100c013030604039180c00c2c60b010216400105981025844100c0b0345040c01618400c41119500a240d003085948400068031248940d44405404032007440e1a00300600c40c1003410b0440c0c00007a0010306080c046814aa0745084c0c440d80482a001d040100c003184803141965950171011b400c022050340e001c01400c090030030380301c10b074001c100c0b0901003070504600242010740010300e040316903a155280900c1c0000340d801c000103984031107841c5401504201014004422a00c012141440107190380d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297009946 1250 297008696 297008713
    0x10e0606130603231606050306011b1407080c0d021c051609020c10020702010804110a05060705061b0703080f10090606021b0102030438120403140a050732 68
    0x24103150042901404170750440009042102c240c201e810b4030341282007420310b45006001d081709a186510700100191a048154111401250002c40c2140c1030360b400300180c9518280c46000c1c440305d4a85c5000086d0001d031001d80090f188a100c000e041d00040c4514151030001a440720b5511202000d074101d90401540021048241d5204002115003444481015810f002103900040d0845100820203440c0418111841d8040d5407004000006071200a090680302c141509129075111003c9910704151404440c40303640d40f4071000d0540b042e0aa06560b40d11456440c2852600481c001410240b5078115640c0d02107550344940c01081e000d820030394014956010440c8800c20004407244c901c505542040200340041c084110141510030425114454a007102c10f0048020703082100340c03020006c0c00440c0d102e5058034a0003117039018034020f68442e82c00c20041644414280720b10001c5401044040003444006048440c00301c4114203000800310351a110003120b1003d038082d00c00c0469140e00300c070701c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297011196 1250 297009946 297010013
    0x2d0d09080c0904030504050f180c04051513031e06060b0a17041106070f020402041401200d110f01110901140c0d050c1c02071502010e0606130603 64
    0x103038541c11804588206140c102600c015107948a00d00869008800d0780c0c009170400e858180c1041d03101e11603d000c0c60290b15200c0d100140940090160300d02c209080840001503000c5002a01c0840903c084010240751540c2c0d070b04451010801c100390300c1900300c40c2030100402e9640c41240010454000d215554a8005c40014034210405040c3d9140d1385c480c0040c0000308130000c2003180340c0d100c01d449043e5505800e04203207191394a00000258000d00000300850f00d48124024064041c400313880350150303086130186410a40018402c1c3d01e105900900350101c0380ca20a01000f070021016a054841040701e07070840900b990118000304a0120b40018500c1d51964001200108060300c0103c0904002c00c1c591241d4036480f0f0a20b95008001010500010102c810b00000008108100d00d2440e01101c0210113915950a8424040d2509914014841d030074010b004500c4000d1300c00780030b01178a0391404c00300003818050003c4090f0f0150b6480011001a0050b80d6600202d401402d900910f2120440e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297012446 1250 297011196 297011203
    0x90305030301230102061b0307020102040b040311010f0507050303070c14100608100905102c01050103050d03050405060708071202310b03070c020607080301090506040c0206092d0d0908 81
    0x14030f000c0c1154041010041c080000d10b0065060981544100e0368940362490100c4c0a03000310740090941410004002040101411445d60038510a07200c440102c00400420703a00e60090003400f81584d0820000241043d1246c01507000c0706202c0e00f04a0a03444141941514041e00c034030032401865900c4900f4802c408042241c5102d10f4840c240c184a540029520a525488081c0b00400c00071f4441c9a844200f4084804900c01e44031000c0d96901626400581140680020320098455010b0f080c4234079041c9100340900c2e0701c00c07a0000010a480d4803656800c1750400c0c1d00400c00310800084030400300f0201d4090004020411040c071503a00341e842012050302d0b010b205016010910103102200300042c881d0a001c0c1ca030300290a003000007810b2140d0001c5505481220300040041000000104602490780e2200b409100292820015490541c4042e40e075405d003540d43e0112a0300010b06540120701081c003421440e001202400d42001c400c8200074602222569144045012003000340b00c180800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297013696 1250 297012446 297012509
    0x60e01090506160504060302131706100603060e0103020906130204080a05070b0304030813050c030a08040915030203031903140705120a0c050d180c06120b01090308030f07090305030301 81
    0xb0100c3d00104102944050820301c55485001c0c103050300424014107031030580745c010f8024403100e034000c0c50710070005a116480301011902442800f43d0000c010036100d21912445040c4d4803901a821100d2b420f5400b0031a0b02c40c2d0040401c1d500ca00d42c43d807240b01c2404607001810003015420700410814009252050501c2e00540084440741400d004110100717500910702d540200d11781016020351005800c155040c80d07101c6011035050300c2001280010400381c84018011200003803010007107480500b540c01c00c81101880302960560003030100c8108051104202c080d410350324100080c0b00041c00582a0900808940080100f100806c210040640702152682d1200c120721040092040300b00018000d80078041464107e10341c0c4a0141e4110017460f0420001181c01200c02030074103a407507100418051f00b0010441010b820445414a90750055030070000b035a42c080c81d42c904503519640c0c01405401c006224000700803500c03400101080c4140025400f80c070f1364850280a000c01c07080c0701117451072413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297014946 1250 297013696 297013711
    0x50a1a150d0203060402040b0a03080a200f070303030b060921010b0303130e040312020d0c030f1a040f15090c26071d0a1d072a050a060e01090506 64
    0x1080c0d07480181d601042665005a045400017150301c041e40c045916511942c10050020300006100d10f0304640040c1905180c54010b102d8810901900300300d142c4a5849407500c0906521000702400000d00a400040c607406c1c000d03101c681071403429000168000b00d98060b0080302c0d03030800480401013000380105600000290001c524040d103002025421101911170000003060101c042000c040c03140380704264660550200790345800000c8000310051000c50000d20200f4074110018007088d0080c090300000d9070006006039044000e490a000141600d100c00c250b00c0741c1d840d03012205040e46012094040c01e0488000560b07035000c1c002c041e000d001c0078400c1e0f480450001d48404281005081c01a511114a10340751000d4609082c07812400d4ac1c030040010b80c0300d03600c40c901040e00f00803000340041904500c040e0b912030382c55200d02503800e6001e450780c26031844440348a0392586803030a000300c4c0409114108980000c1100e80380d100c1140c159403083c14460f51559411005d02200300100381d040042c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297016196 1250 297014946 297014959
    0x3010b090405120c0c0406060e09060406080c060d0f0213090b030604020f0103090507080636060610090302060708030a0c020718090212060c041508090d0507050a1a15 73
    0x30726407262030f03440e1074215070f546a8035000160350403240c0c42070007190241c060281080c840356855040203001580d500700401d00400c144400160107241601544003112000009001c6400d041c10a00107950301c51115031500c0e030b8980c0c84280c0d4081c1188000e041d401c81000303038900305a062408103404d40320601c2c032441c80baa000401303000c0540c1c0c0c6e44680000c1c850090800289882c890b1500764100600c980c4058414041c110800915420030060000c180240404841d4102c403e40868000c0d101110882c2d01a03078055800503000d070901d2460610342801500304031043c1e5540b540021303503580c031040044801e8003012061103038920960207800071020392030001d8207141e41040301116843c1c18400741d5074040d58803204e0740700c20b43d00c61643c40d2120f406e100090b41d503540b400001c04241ca40c041d10401201c025020908840b1a125003810780c021403800024122900e01c0000841e4280c00c10b01003510345014400c0c0030070007d582c502c03107054029100301115820345864000c80348100d03140d4008600406 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297017446 1250 297016196 297016201
    0x2031602011104051315091d03040e0c03060315070905011205091b04020d0e01020910080f070f1707030f0f11030c07060605030f1506220b01030216080903010b09 71
    0x1442003043c0d4040d510305481d110082d03401400c020018041c02c0c1a101d0a0898220001c164106150400d03594000310501c5c251151680d0706250b40d59204500c42c120008980e000420401c040c00d030011500400024125450b06c140d000341501c070310000303503000008240c2c03030b000410031941c0200851100940c1800d00b041203180c5064500d13140d12126121803d081d01040300300303080b99a960b044d1049140001c43c20442c1030b8600640c14002d520804210317201c3d080c4aa074481d0325030701c51029944a0340200d0080c50013a1510071050b2551102c98801c41c080c000c000a141c12580c070030118252107800301c0d03a0085888441504450100d50385800c080524500740201c150620b049802100d0300130a496070005d55070034050401c60014042900459454020a0b0045542d550300098040c103060800701c204c61180c84030030410840e10b5500c1009038030300308000c9681400e6000340d400901e01c6030b03043c14090700c1c00705013074440c29031541000c604607030503400440c0014050a09101c1c41e4527840064600b4904d03030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297018696 1250 297017446 297017471
    0x20c010e12100b030708071d06030303040c0b131d0a0e010501080703030e06040503010c090e07080609040204090221010c080c03100b0a02240106020d0c0809040b010207050901090203160201 83
    0x145058142c03100703441c0c0c4a00c0f002d081501e040081c4070003811303000b0079109541c0e100c1540f940d41e0b510318002c04d0000ba1203207000c07580d6403902008490280d135010030703a8218240f8104c035007a040c1e0480d000d845145d9a8801c2c00184141c00d66002d140c0d032603198103280c1e400746800003c14007247e00015a4155030783c90840180030030040014030b4000d494060914148105d00c61001030f14500c2141c100c1078042d42024818101180c001081c0003d496041d56004102c0d034036210111804441194290b5003c411403010a0240c1400d9024144844c00949003103100041c210000c0c26108001540d4807090f07546104100d0159444007003d5003000803032840d070b4514100184040709805140c02030075091080010382c0700c0da8034003c00400c4001c0c0c00d010140d24095201011041c5440424030400016000e032036903000c071040c0b1a141442c0b05030350208110b400e0090100920000705213030007030b06055119114010031031f9560080514000e2001450141e646d00d0302c2c540c488002540701c54030a042d6810104544540d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297019946 1250 297018696 297018703
    0x60c050607020631150b01023d0b040507020d17090c06030c0417030406031112010902130b16170a050a1b0807110108010f1d0402040912020c010e12 65
    0x3d140107001d613040490b541d04000751441007030002c110001d980091602801680c00c8199040c0d000d80958080042052012001c9502c0150380d0304440d04403103299a2081e80e6a04050108143c00d000080004214011500301c0d48151100b00151740131100d10034205034080b8030101c042d00400c00f140c6075810400781c41669196049206446058080001101005114103440081550b1160360002c90301d10ba50381600c030b038064001e200c006401c22031001c8503a484842110401c685c2c10001c1c05513a864448030034003e4000b05504080c2a03c100c4001542107400005402c11020703045440c0313801c590510301003220700707070350314801030540001d0150750b14a42d00720064a102c0d03191810700c82401c0d1403200d06120821406d58004200c6c030004200d43c3d082c0210a80030403240c0300283c0351312071545d807110b204142c0280c0320311a50014016019540000c040503500707072500300748007410101e4420910364800b10804030058100300117903c62810801d1a681c848000d0811031026210100081000340c3c1d410385 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297021196 1250 297019946 297019981
    0x90213150804020f0d050303222003010f060b03060d0206190816140706020a0201091a0717010803090f06070b010b031501140712090e010b0a1404060906210501060c0506070206 77
    0x49c40040810310340340180519020200d05070301a2a0240c00c44c241500d05064551030100140658604000c4409910951052505484d40e9244250031603403205c04200c6401c80f4040b00300e0b00b1603010312900d000c00c5103448800a1250040d140d1405926124240000303085420b07842c8020040d40100501000c003c4a0455501382c1c0c0007038025070303114440c44080e400340c001000020032900d003030700700341400c601c6006095000301c009039500c6c0325102408094009408080c01200c0c441e810800c4800440d2030292500315980c1c42c0940b44034140038440e101c0441d8a0000d80c45a0110322000003002070b8211440401d40d083c0d8000d0038140c54030b40c4c1c00c0240000354001c2602c014403458001c00000340307260188814400400c14038251608a43e150304414049800c08074018020541788421888020b2101094505032080340d91403507001ca01d0544200c5969074054003030040c0c180c00d400c6154010701e84d402014040c1c941502d40480410051a01c146025002020082150041824800a10300483da00c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297022446 1250 297021196 297021211
    0x1703040e0c0f090d120e0414012607060201091205161205190905030d02030405030d051b1002180105180909030d06090902010206090d09090213150804020f0d050303 72
    0x10744031802e803445220940f19900d00300b070703101541c80050010440c040700340540d88501d5580360410b000b209814002594003010b0640e582d201c2110051004c41311100c00c1e410486048a002400100381e1707011541014400c2c1c02000060751150340603000e100c1c030034072843e80c0d610882c60000c0c0b0b88480010b80300400c2c22005001000528070900541d94103108600b81e4188006030780d8403101c0340c40d000c0400340070b99000780b040c40e029005203205040e0060011069408590010300580390b42e1a14003822100d5621030120303071400e101501d040c000d61550401102c284003841c00ca0042e51410210444a0300a60300d010305810001c003003001d03402030341c001107103100382e5007058034500500d07205e074000d450550090b014810758003031500b000010f500c4010707040248114000e0b000d56503640c440060703080e02d0351409060000072504060080010b0003240d40242508001d0f0301c41401c155444401451a0441d0050400c00054850062100354540003414012000c4216400b03100d007100d45e40d420380c41c1d000061114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297023696 1250 297022446 297022471
    0x9011532070309181407020a050a020d0201110f01021e030105030c040c140f040f05040203071b330501060e01020a0f0602040f06050318190b06130c091703040e 70
    0x904160168480350301501c1c1c030203138902c030b5a203007410b590000f01151801e503012000484085450580003090748600190024050b220b807001da03400348070908158810490401170380078010729402109002d40c1011980440000da510050911002c000760174000d010300c000ca03020001000251f800082000620f501036074041381c1e039515140281c690304003820b400c42401d500042e100c510f44030000010810344070400c0207000283c1d00c070400d0008030b0000b00c0d4500041540000d421100c4580b0701c504103402c9100b50704160110344140b603074400c02407081c80107941045c00e00e01c5484042c04030f402070a000d4015894005d450301038000000795165001d0348060030f0590421460428403d442d0126405480d8100c01210002c0d035400c0001c105030b00c201c0e10107030740400a82c03003424404404110301e1291030040c00500509281d9450f0003940346030103001103a020f0401e890080c804103a6000380b410103400c40d01c2e030700c00c542d1400c04505100385070f07145070448070303001013006002e0f2000000019801c18800d0003403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297024946 1250 297023696 297023707
    0xa05060702040c20010f05090604031b082503020c030c0a140a031403040e071407030503060303210709080a051b03100608010207060f0e07050906040b09011532 70
    0xa1381c100302c0881912045090166070b091501805401862840d03c1c000d200304041e80d40d203c412522a101550000d00007900d6030381040c1030303480b010018409075000c0c40c0d03a1850310303207180c0c2444200d58040034001c08070300603646c030b403c107040c1c05001d030100d003200c00c0d0060f116507070354500004c0640d51507004403004298038608880c119142da6400350042e543c0540380580c000c40355401e0568a81091003854440c1d00c00d40b0000e03540620402c003000d20505004101810300030a0744d001c1c1c0b07298100900598140c0b02c10b110fa510051141e80c01c020382400018800541c500308002c1c02844424281c000d07640c2640900300000c001200020782010018960340c000300c0b030000b4540001c0c1045600c01c0261911401c0c120042895603065004102143c41769004011214403d4001000d5441000d0141100d40003901c003006070b4106018050341c00360740104006411080709000448009080c0c0190401060700c0c005000071a40110040c101444c100c1c1c200c002c41c002034079220300801070a40407004a00701c0401c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297026196 1250 297024946 297024971
    0x20a0e2a031302041a0909100b010507150b010e0d0c06080c0a0c0f02060c07080d020105011203170c090409031d010306030f080901021006150e0603060109030204020c031603050c06060a0506070204 86
    0x105030505c0c0a000748030300b00310b0400585460f62002d40b840c084405524080802c0c07090f40c014811175050a6002c503009003440300c041c2d003080003407c00341c00a0b41840190f03042d59040780d1300d14803102c4c0c403544100c8044c0c03580350401c0380040015200800400882d8020494030300350701e8000303001d81d48c3c086c1c0c49090803015080340d00c0450280d00070039810075041e1040300d10101c2c086601048260301440346070b000b00800d1fa0b0390034642d10717403000255000e00446c400102092000980c204255403251441318200d242c1100040810100c43d0340e6481038001400304160320220a694000d0700103c4802482c4c14060203080d83c40311006032000e480020f010713500026541c101079009026990f03c0e060801c034204411641e84460440c981b0300051810300041e18520302040e1031400d0b40a4a020f01810394841d00303042d046074203001c000e60020244202130700c0140061500c180300e00f06000c0100c0e2181d82c0e4552982d40310400300b403915401502042c4502144c4174140516210802507505064040740c0220302c403501100e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297027446 1250 297026196 297026231
    0x206090307080115170c060307050a020c03030a030f060905010302090c07030c081602030d031a1306091a1e0d020d300908010b0607030c020a0e2a03130204 68
    0x240b101d4560b50030410501d0301c2c0104140c0c080120f580251506405000c00000c2d192100c40740000c10381c0c484c00c00e02c003080980384114003401d40c1e600c5a0040319250349003100042c0c51904110a507900180c2c403a0307081da044d0200c03801a07000403c0d06003814809035045a00241d00000300a211141018000c01d41009042c4100080002c1035040307626183d403400001e400103081c0e03280107400d90080c0700740c03c0b41100b540d01c40d22a4a1103940d008c094a101810b0803070410511640c402d0001140341c0d00d404010411182c1e900c00e80607401c0c0c100c20305000c000400010300211100744805c12a000412114a0000d612203c0340c61120780d504070340011003403195182503070f004011040d101401c0d8000b044205074000e06010701280385455501c85010280e9540d0034503007079800350b0014a400240600c50040028000d07680451120303c0280340604054445d030078440202011141c00100d901c0100180d0b0000003200d98280301c0c0304883c90502c3c0b4600c0d14451030f040322a0b050b2070090080e030365120b400ea241c0003581c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297028696 1250 297027446 297027449
    0xa12090f051027080102211303030e100f0203010609081b0405060a0329060a0303021b0402040b0d09020a14061b0132090a0f03120609020403060f15120206090307 71
    0x14040000c10f6900c0320704d4030b03000f504060fa8052102c00e0358078803008062541c8001911070300c80c1c0b0051180310a034541c1d045002d80540300c50800329103d9541040c445041d54060b0185940c5208030040e240d41c500764000344400c55640c416001038211384000c810220070040c8190045000f6034000c181915084003180c12a1450751000d45040c0c06030004a41d842588044c880008801141450164954408004400794140700040143c3e000c00c440c03070310f20b02d4289000c502c3c000c0014170042c206555113055045ca9400b21050285036656505030400f1032034980c2003000580641e65415002d9041e07240400c501344031b110b0580d80200f001c100b02c0c80890009400100140701a520680c80141d605800515a1b032000a18000240100c00020b001030500044c200d000a17004020700001003001c1c1c03001e0306c041d00340f503000c3c41c038060f140d040206d418802130009000842c03050f0b00000305225600084c608480c0008042c4900c0c0c03140860400c52a030710004200078041c0c046800300e541e0108100001d2408034507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297029946 1250 297028696 297028757
    0x6010c030507060216080a0c0501141006120f05040c0807060c0b0a2f070218070f0f0507320c0102101104081b030d0306032001030b030a12090f0510 65
    0x81600f800d070b0344180c8d2005a9441040240000c1c0708500c161b090040003200c189054842c2210208180c40c4a240702c4108848454000230761405030300e6242042d500115415203c12900c5901005030742e008000440003001140340c20111420580d5039111030010150031190b0180d2140c01480d808812401d1041080c200700c8050f121000c582103011290303401480050388500300381043c00d2205900f09104c14800c144c181e80701c0300400781014080d100610b9208a1508000050214034002039803c82903242d4050440314100e8401c50903c0f00317814280f500c040103604c6400c81d1342c00c42e6040c0d030001000c2c50340c0d80c880c03c00440d4154040075003825601559100f1040791041b100f00891031400d20304404401c0c0816004d0f1001421006826802c1d02d440d803000900f021a4403101e220031904460940d1680b40c0149808a00d100064001a1420010201c10b85900c071955142e082c6464100000c1001007840c04c0e16202060700c0c2c400011440041c080c082e006105200e01e00c0c04194001d0400c43e28049038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297031196 1250 297029946 297029963
    0x60806030606010e27060f0f030631050303160c02030a110d0c260a150209040b090a1509060f090c0905030f070504050c0f27030307110906010c030507060216 69
    0x1c00c0d05e140784203c2c0042d220389000704c0319440414814180321004241013440540240583e4071480d0040b1290b046940c04101050134003000c5a044085903240c910340d0324000d100075a12810001805c2c0c0a08440b44681c070700307110150b07804000580f0041904010a5004090744640507108000704071408481d4a004050035040440400c990a5044102c40240070402d149030880802a80c903a644810458025142c0c3d80b5204200f94615115001466a10030251012850b01d030350320040b84040005484031900c4580f2004802c1d510b1807a01300c00f1005010200c814014145042c0c0d40c40e40c0000c440c003603072040c40d88800f0308001050240d403a0b1801064080c0c11900903c2c0410700c0c9070b403100c0803802590b101f142400c001c00d124400c0d4000792441c1c0c1502d80401460f1600b03030f480c021424149100d0104138800c00d8440c0715050756040c0080c190460089030703111004074011040103c000c200408079818080c00e41c1900001c40c0d448000d81d032079150300c0003005a40f00e0200b40004940600d072a001001d628 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297032446 1250 297031196 297031249
    0x4080106140a0602061801020f07080d050a050723091210200f090a080115090b0607050d0c060b0a030f0303051803181302040e040c060806030606010e 66
    0x144154000021030312507401400e4801c00c844204410b2628038400c1c480142d02c4040841c00c00c4800308000103001e5100703030006117081080d00c2c3c1250580c0120f14169155840400c040c0c0044c80d090003003551003841040100704c2c600e0003400143c10b0401c0d824041a103000600800e103c0060340c40100d90198400070820398080107910050b0380d541e510042c0c100019400c0100078081d10045408002000001103aa1420003651106201d42c1d40c110381a1594049a940000500603000f0320503002c80030103c141d201d038414100311542054600e182c1c2c016010708000c104c240082840032030103c103020102c1c40c1c02041c03000a800c0c00000b8001840b01d043d489001100300004002503a41c01108031442a10140819a200f064039100d01e10b9001039589160010414100e4038810041541c041c550f0042000d0141103030f0400b0740c800c07138000750084c00c6070180140c00e0006006810082c5401400c0c140707000a210318200f40441c0e1902c4028084d1814481d001d51100d040e555800c1502202d002090901130380e13035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297033696 1250 297032446 297032459
    0xe0a05130b242e110c01051615021305190303030b03030f0a03051504090506040627060207020a0506040b1204110603070306061416080a11030a09050f0a03051b030f0304 74
    0x961200820203039a5900a80c2d02070f62070f01404000380042d00381806010842c0d001e40c01034500d588295145d004030350021885e000001c01c480410915040030140050301c48401c40461040050305410031b074840c4810590303140300c0c0003c07040f04d070083d00e074940b078041201010100420300d54040c1f010a50030f0a00040780038414203600d640b1140c45502e219000c5401001c0c2d56051200303c96204802509a030031580010b00441c0e00b07a0421040006200360350002100c50384c1148401c0c1d1401075080750700700d4001914034198607211010300c020b031104650281c601891702e081c101141c0300b03905a048d042d6585100080601944c00c122020609000d002c042e0b44e403920600040060026000d00340110b80101341d980a40602c0a080d11584e03071400242e841004003e1b11803100c1504050032070000c0042003086d4508040092024014a8560b500c03440036483c100010040c45101002805028041c410000c00104100180301109461020824007110540078082401c2510608101115100001c1c000881 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297034946 1250 297033696 297033739
    0x3050304020f09060913050c040c09081608071208040e0a02030a0c03020c2a0307150305060411042904080d030f05041a070c0501060e0a05130b24 64
    0xa64802c80d29010700e103010348104414400150382058110255400003a041d9509003c1c21401c903002e40d040b034115a41c0c0400050942e02c03901030550004244800800000000b00700c10b00c1c200000f21003001920341032890090756034100d440390440d04009460078009102c2400704542c058011844561080e02c3d0003c1400007941c4207643c9410103624107446464042d12034425500d030310032450090a5100714040303080703c140408007d0954001d2242e0f560800035541040000014003003804141c02c1102034074030240407070f07500a144a004505201c0c100340703c80401030880d410b0301e212040d440149441125840e0311b201c00201902071245c00060302083c01d410001c0d00480400703c943e01440a80c50b441c6074502954010b844c020806204200340b030407d2907c1e848a203030321111604d0070400c143e0060722403d0949409900415111031003005000340d41f0503600406521100712451450480c0c0e481e81c1c1c2d0401c000b0300809001d40d00742c06020310f2040780d1540003a1008110010300e00603604203008040c859 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297036196 1250 297034946 297034951
    0x4120e031b04181101080408040320240a2708010b0a0e07020706050a02010b1011010b03070f050409170f0a090506120a1a0d080918090601180b0904030216090e0c130608060103030503 80
    0x1240320b800c400d00031107040c00c032141c133000c0324101509810a034000b81c3c1030b2008401d11810002c1d0208148480c0140040004c1300c50040c00404004599120144140000502c0b10307008801c0000d130000801c00f655800207003140031640945407140d950451010200d0040985184d070981c85280000410000c5510010a11181e80304200030080082d422042507a100450300c00e1114030800b4032020070036407610394400006030303015620001006c042c4820500c1c580e07000d11200204800046079a2618541c8440600007038401036a0091622552104106910350000c040a03406c549940041405d4405101c40c680d941201603c080891256450555000d070800312809010b50004441c25024290781d284c500e006e188000058030a590812000380740701401080c0c1d110f40d40782c03905d040407800e483d244107051040740660701400100c000201ca8100c0303500c0c0ea0380300b000128141030002c0d56100020800500072001269080c1c00c0d080e4802901000e01012350209219029170b4000006240d0408010351 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297037446 1250 297036196 297036199
    0x501050108030a0c0602180306010b070b0f01030803062e2d170703022808010902090a1e05060c0f0708030f0304120e031b04181101080408040320 64
    0x256a00d580009a0364081c6002000008a1002e115004202a0f500824004607031040c0e40698100b2540403034944102a4088801420f001a60b1020300142a8080c0d802c084840d0381c04500394034580381e800301800041c0001d849075a0704902c1d010568481c1c41114038807440300d25040192803030f410010b8050303020241481b18140d00041c4000b030040200719190007a444070f440c0e114000300751007a0121000d40c01003010301030550800c500021440500b5403a00441c0fa1140e8250102d4288440100029011780c811160980113120803482990340ba101a01628450714030011200c466180000348001c0607400742d030b040711000039800300800c0041660403075003400904403405a42d4a1041a41e83c0c032817125158801030040c40420b000030a002c0c1155000340c40352500e400c0102061000a0401d511235021803401411a2070032001424940540c60111403004904d0031801c400c0c0e01c0d074150f00b03850841c0c09030420100200207003c0001060070346000c0d60304400c14010100040340401400500c0c0d03440c0c503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297038696 1250 297037446 297037451
    0x909090a2a0f0f0315060f09091203050f1308070210090503071d07031d1c020709090206030103020d1a0a05100801020a1706040f0905061f06050a0c030302070b130501 73
    0x441c410051000c14402c4901d03e5112000251454403020b50192090741443d101d42c0d241c0c82c001840c81080405071025108030b0500190b40702c564901000000b242d03c80d02000e16090038200300461405645156001070040081340c40c02e6105d2822023001d2058820081d03100780280b407070f51a5150300c5648042507c030154115568a500c4200403405500412008040214500009001140b10f80c010b4554188070380e1180d4882c00702001924140804000091081ca94021740c800c040c1d641040541c008000c0d03500d040291040e60740100c0c81511050101034000e0310102062020040000165292180000d81d030720510700b0a0603030740006c2c00d0160303010b01c00d0003030f040c1000c920720006200b12103403001191554920703074910f40f01040101000420070f503071080d40d800300c42840e12250300a1014951003a4041d0400749801640c64400d070010454603480e800b9400d03000d01031103401c03004445100016080850440d410f52804501a20440000903e1081400207002e45c0d000b8410b03114848500c45c9009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297039946 1250 297038696 297038699
    0x1710030506091c030c03061d04110d0302030906090f060301030c030b0601050c0a030818160503101103150a0b0a02060411100e0120120307030c02060403050909090a2a 73
    0x4203940d03c5072203080940e50100710700c14074543d600951080101c01118140401c3c0386940e42d5000c0030560725452035850359800c800c10030042111070426001c1c503a2040f83c0d0900d803c4c2040d00c00a58a014484030700e40036007000100b05105554400c015900d0f07003401011945c0d250f84a241074070351180c2500c0201d4083c80c0304008109a903000f0700079642403070303d828002c10304030900b600c045641e0940681912686016240e031485650400d0120050307610b1104200b00e0744500d40780506d85030400043e515900d0314174240320800032507030700c40c112508400403025041c101c14800340029513400c40380c0d20504030003c0c005000f0702c1203030b00402d0151203076020391001d0140001d56403d012020320b2210021000074219000d280c034942c0500d028002c809100c0c1c0c66075410703e401c0036520385002480c5030500c0e401c0801208001e43e1540c10700a03890302070071a1014124608045d90007a0070f81c050000501e01c00c142c10320008081c01e1041040001c03030303a001002c002c1000d65450380040300c1c04a403c2d803594106030a070030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297041196 1250 297039946 297039961
    0x602070608190207061b021506030c01020319030e031207031505030304091109060d0518160918150501091409060402010f0c0b0c0910022b1710030506 66
    0x1d080c420291061103400301001100894000d500c080c50403540c10740e50340c1d0500c0303195003006041051103ca5800400056103000403440c4856001005603109505c40c2c89900c5250340e01000b40e07a605420034180300271036006000d05038003420281c0400f00c0740d40b00101d5040b40000d050090a0300461042d2400c10444031040d0582d241001a4000c46406600401c400c100b00c03095503021694104042840c50306003079880b00000c1d159030040381030400290300c2d0300a100c480c418039001c96944000300002013503801c3c0d6003680c2d07418404551141c2440950784c1c003c40c02e030f1941c42c1204203010650041d0000300d8590300640c1c4000410080c0182e410b600c0c0b0b00010b000102c205800c14034007c0601100602a41d03840780d00440b140038110400008010348110104009660b1050450042503d4502e594860340c0311028042e44448075403c007800c552001e5011013200e008200ea045c1a070070301c9115107103684000a4240c403c026111468107030304d19032008205920042c425003009491241e401d841c500d86410300c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297042446 1250 297041196 297041207
    0x150106080603191b0302130203010311120d030b13050901051014030c090c0403050303040f121d1011070f090f0204030c170c0a0b120105091b07140a0c06020706 70
    0x10300b81d81001c110004024085900454200041c000650b44d0600c85500ca5011856860200b80c052420300e8010005000304222042281a03101c0d05850750560840c4400380030303075074404000ca038509040d41c0f4039412001d80c076074046403101d1800c5031105100a0400441c150b008010440300c820405807141400f0450003511401141d070054010002c00901d95804100b002568020b040c4802c9000108400000147c05202440c0300b0303801250100078140150034800300e06011401c42008001440151045079400c00f100c1142c81c013400d07104000092a20501640c0d055413941c5030701058803640c000040c090307600c0403042c016600140018841c0013401103001e41a8022030200400740c403401e04d400e025403041c03644802d42408003901140d00a1019001203503202c1d410f0b4210908158000503811901075081c9038060052400395911055803403c0c1c500002d070108000c0d0345456a00c4001004801d000004030444401e1000e84161050b68040d8502214068154841d02001d40920140001c0c03441c05172 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297043696 1250 297042446 297042463
    0x10201051b0a08090102090a060c05011a0a0b210126061e0a0609050403030c20070603090303021e0319050106080c0a031e050105211518150106080603 66
    0x501c1c40742050715080c0280c0d82e031200109100c50a642c00d204200d055030b5540c0701c480c001e204980344d030080324640e400d000e800d55426001801c4c014402e8842c1d200e250700c45504540880324080e10641d01c84003080d541c00c000e00703010000300303020050040001c40d1f43c500b611030f44090703c05802011103184a0044074180c54100c204c40c04049007000103203001c40c80b50381803a0550700024890001401c4d030703140d8003070a04688040d0703020307000665901c01d080d480d42d0300b101d0904c2c010508522010a0b0002258a050341c80396203020300002c240d180c1c001581058000e805441c041070368041e410910b0080525240c94030f030004c503074500c1c200b401002192009942407003014165034056039040c49559402c012105941d200c0d40100d4209940d41c00503003e00c00e01e001101203441e4040d000400c56515141c20000e03c0100e0100000301503907101c602c022801c0c00041e000d6009203050340d005880742e8680490b501703404a007600070001800b8544243c1c80c0f4000c056040d0741a1038094035400310986441c8140740d541c2c03840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297044946 1250 297043696 297043741
    0x4080c010e0609100c0c120203090f031c050d0603020603010806060427021c05030c0105040c060e01270f061e0309080304030c0503040b0d060801050903160b07051603020c01020105 79
    0x20f8080d4880210130750308001c09000c0a0b040070801c40c50301d55607104048a2031071030b000041e0000305805203146446501d007018900214010440907441640e03080e52003088050310002c0c00b01c009007000c0da0344110b8000303800540d0000d180700e8480d03070b503001e025440d220b003100d56900c036502c5c00c4003401164041085044500030000c1e4038038111001c9038207100006208560050a1151048400c0c0001d0410402000311440f09000482c050502d840c0c114042e4401d90020f8043c40344c00c2d4160a21641d00041e0446d0b014101c8101415400074000394012030441c980041f003800b030342d07a24045030498009030221031103040169541c0312081c4040c411005c4500c01c1c203005040700410400316000c24030442c0c200300c1035401002540c0c030b007541e0b81c6030001da19840b8481c0540141e450b0174040001130002e204065010341402c0c051454110b20070703e0801ca45000300002051814148040f4800e00d1141050300d034804007070b0880c84001242c50401a507661410000c041c0158200340006201c3c94118854441140c3d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297046196 1250 297044946 297044953
    0x2070507030b1021210e12010c0f03020d1401080a0309080705150a021e0c0102240601050a02030c010f0b040f0c050904091703010303091a130b0313020904080c010e0609 74
    0x1258804c03401d4000c0c00120035100140030601109442d44e4411294000c00c50f25240c41040700708800610601d003c0740c18040415900d858040032313a0f6030304140341081c0340d00e03680341c0142d0364001103904200401200701652280c620310400483c0e68040002d9941515000e9105c4810081c3d031654042c0c0e5851045c001e440d0001c0c03162801030002c414070000307032000101c01e00640c0c0040951840d9a10200e600040f207851a52155810141d51350301440241500c04a100d48211081240c01510050400103803e0b01c0c1001310000303030140b0f4284284207032010421000003e10100003110402c001030003402c250320f4032442c035200c100c1c00720944d02d220b80d00301c074071140d1030304e070f05010200e0b0820000704070003082a00c44441c0c0390503080756101c03988001c3d03028510030b0b201c00000350704000d5070310b08031a1000c10300000408104625004490400300e01012110700d940e0299581d621b040d603040c0801040c00f0000d4006905a05102c00c20028501400c24440810000c001c26a40103842660310074051300d00601d80e80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297047446 1250 297046196 297046229
    0x10b040f03020402030408070506070f0e04060806010b0703140c0105061305060109061407050703120305070903080d09210e01140702090a050a090b1f0e071d01090902070507030b10 79
    0x1000c4d005141c1c000d0107558842e04001041c0c490f40e0428004035500000154000340004003580c0007140b4131409403040d83c003002800c1c106111140e89090600420b0800780001c1006820944150000d0395040f490000181c0c9a44003007190a010740801c1c0d5030240f203043c0386018070b1000c05180c45100e00c2641c050b502ca0302514038041c0c013519103c070140358061406a08028080c0422820007042005501c6003c003c080c0490003507005007200c8003d81200108061140d040003c240044150745240d201080c00189880c10f43ca4100d8003140300400035070307401038104000312107243c0250140ca85403100780c03a0000421b0302000341d64281e200310b0300025481200032010644100700e552066600c00301c0e00500103408030741511200c4aa0108442041c60b98001e00c2d80c607802e00364107020b0000200b204590702c855600300450042c00411019084210301c181c0c004141c1c40c0740c0e220f034140000408212004660b40c8040d82001500d1302034a0005a400c00444c0700840e050120500e421011600116400701450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297048696 1250 297047446 297047449
    0xb03070e010c0c08240c070203060a0203190606050307180b0d020705010f05040b0109060b0708070213060b030c1206030a050705120c040612110f100f0516060c0206010b040f0302 78
    0x200c0b40c04068030044442d407404140c40c48200003140e01203030f01170f9551075480180c1d42d04000001c4001c00456000307170f0034170003c0300613240041c2c402e821800c55000561a40c1c1c6515807080c0e010208440d450010317040020008035150804000c5000b00044e030b44e5043d0500d0390310209071280c10544200f00307540e8420000c10040000c9640500300e00c0d0320460021914074000080c2c04d0650300c1c1a0340503a0704000000041200b11800d00c640780081c1140c035011820036046403100101c2e07005940c0c1c06409095901c40d0711a802ca019400380b4050030305010b0313032600c070304202000030001d4015141c24000e28038102d000c691280740004d004060b1035407003002030281500381400c1c840101c0344041c0d41081407140d0010302c00a07940c1d500a800c003401801040200c01f1509007004054090382c00c446a0080c1030b071901b031140c4c40c1c681c015200c0d00c203089030601103d072510000d422902481106501228403000c0d80d21602003203081e0300b02c1c1100e58040c0c5d003101c42607600c6004000141c49948500c40d26061240c4040005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297049946 1250 297048696 297048707
    0x703180c050613080102040806010521030405010305090c0901030b07230306150d0903021b010c02090402041112040804060f02070f03031d06072a0e040b0a111908010b03070e01 77
    0x4911848400c00140740d0350f90a030609a80142e023200e481500600014002800e02c08a49030703012440d031403402c0303d81480352074150b04e03440340340140340c10940c44600180f1603440422054002d1000603016182640c0c0d2070a003688021401d50b21803001030581000300050440c0c00b03a244e0001030308031018503d107071140d80803c40f819006051003541100d00b4009002649094410780002d14002d402601c00701c143c14401101080b10501e005040c03201590005000d070b12980d4099600960640b000605078040d00710350400360186c406440d00350f0b42d13031030104010000c1c07400141c030440b04507880d000c105e000d0100d8140d1300c41c480790042c03900104d001c04042010a00c03450100c050581d10060030300400c19500c1c0401c40700d500401c030950702c15080d140c2e03002e43d801c1240390b034920b440e180714121071030b0030300301001040c0f820300c040d00c0a00700c0a2a0000f1406810503580804400f051480d506030b42c0e40f402c0e5150480040017220102c0100300794100000714000c0c3c07482101d109012765039034408602d00d85801500c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297051196 1250 297049946 297049957
    0x5030115020a020d0b010801050c25020102030c031c05010e060603040b0402010311190e0f010c0204091703011203020d1812240204080105090f0703030f05091005030703180c0506 78
    0x841c442c0062031805600d59030014400c0030300441d40e441c84c2e90304044580b420764002030440b28601004110111442c1c1d01046049505181944460840f160600041b03181d4010400f000005010015110848241459940448500c6d401e8107102980c0d0b207650000d0034010880718190413580030000200000c070301d1940e96501c50701c14100044c441c03050302c4882c2d1003a041a121138010310300c1603019800058118001c80318410046030b0165100541c03400090190545c072000900460b1034020000401003c03800d480008640034411544940e503ea04a07104035013081000d50260280500444003688500c0c0d215129600070000300391a1707440d03e4a8076004819000c001e9607c0101038104000b1844083c0f030b000744407107030b1180242e00c81e8207006180b42142c0c0302404650055001132110070b0f00c0f00002c24000300326038140c10940e90407400e0840c00d4076a84144005503900240481505800c2c075080030186001d80d00c80d5804020500c4010508444420b8600000c2d00296401400f0041803410500810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297052446 1250 297051196 297051239
    0x405010c051203280e1c0905060a180803041409061c0305251a09030408010c120b0f09040809010c051518060c04090b010504080607031505030d050301 66
    0x28028000c2c140c00d0704032030700140c48040c0c40300e8100e80f503003405284d0324000c1e8400e8581c0781c104200802540d0505991003285040459007002040405001c2c0b501075201d000c000c0002070601942c8080c0260010030111400c40700d030301c120300d1144000c40c9407000007090f81c050340d104d0301c02a610042e40000b001400c0d24000e100307982c092401c0000ac4110700d84801e45205062294407429200c24800c10014005900c550f07448445801ca001c0e8040452159140d8481801d032400f101641520f80518035401c40c070454103c062150700307007600005820780c4401404d0204c2c458840802c112402e44081111542948080c29031000d410310101e00031405403070013040340050504180d40f20b6000381d601c60f800c00c181d000d103480c02030001800b00036003012809425a0b10040300806130005251903905825030717028500481ca510b950b550761210280e4002c8080790003070078140301120241d2410202c01005048071400c51900302024000016050800141d4000700b040d903500c842c2e00310707800e10303140001c000090441c40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297053696 1250 297052446 297052453
    0xd051b01091505090d05090d1b0303020321070c0201030507120e0703021206041e15020301091b0302130e0c0f070b150d11011101060e1008190203030405010c05 70
    0x41141440034401c07059258801c0380b481c0c548040b028100c40450300d0041c4000300c960002c0d08841c802961146c03c48a000383c003107805034945aa51300b40182c41d000c010a0818600760712250110505d50008090a8038100a660110b80d803c441e182c0200511002c0c1c955a020a41d2806a0030056010741c0045a0000c100c2c41c09240301426100d004041c0c600300d0031080c2143c0c000f4402402035003020400103411080210007000035052079503a01040404c40d50090080d070307078440e07802c004000c251a082608110f480c14150749a5840d0304012004042d607020300038003190881c040508182c007074000c0d0b4001c010001602d14000780740035120915040c005010090701c031000c100d90884030700344c000900020b03030203402812020720f410b40080c0c12000c034a44072a803140703100c039000e04001010409411b850b9002840c04030582c880402e9101d01402154100b0103010700d8000130000200103220402c0c00b1144881c00700d4510000101d0310000c81c441e404406074168100b000309000741d50040c0c1c0b0500742d131880b40049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297054946 1250 297053696 297053737
    0xc12030806060a030f021b0610051f02010e010f1406010e032802060f040312090503060403031d0a120905060c03030a020a05040b030403030f110a0c06150503120903010c020d020d05 79
    0x204c008a90018541c8542d940804004031003001f000c002d601d03800700300c00c005450100c3c1000300003108612000d04030b10981400041811505100b0341003c4004580c0c04001e0040c0603e0700717810009015003900744008229030200042c99580706140d944542c0c0e4024002e000004040424103080d201c0351074407011344020050389980180c031410000d251804100c0500d50b00c550440ca88220b002500c07408000421807c200140241c1d074001c10501e4010b503150500003080b510804080503a1001c400d0403101c103009140c0c590082c041c4c1c290160989100742d54403407454684440400c82d01c1e0144014044441c3e00502c0003403600c101c558001c059500007030030003508060340c0d126840b48540c000c9070220000303504e0f100c010781700c880a4011500b03071032200750308039080000341034004000c001800c3c1c01400c4030b525140b401241090304031311003000d0200681a240302c00304e001078104242c0c0c4481c01d03a034000d40ca4121452049480031a03412036211003503002e08803e07030240c00121015000b0000700c0d4809000d4840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297056196 1250 297054946 297054971
    0x311031902100c0c0306060e010b040f0605030a0609021804180c0510020c06030117060601050c03093601031208070813050102040b1207020c040501151b0f050a0c12030806060a03 78
    0x34040103501c03d040114505d03041190010230f070300d03043e4442140c0b00c1c018042444a64440d5400d5800c1da0802d00c0c0098480c1d643e0300d03540020740920741c0400c01491001402c041101080711501c18a20800e403418081009014084114002000b4024051a000d1803090285250445041a074003d0134812101002502d03c00104c140c1d0081e84884c403030100750120071811420038042540d03c0b03082400c008d42480640222140c4900c5205940e5100300e0002001e64220b02d034001411681c0e0f461103884085600d0080b0505040360400c0c0000e81c1c4600c0740c1c11140d00c400b44943c0c1418480c450b2039556800c5611060b4604489081d48134040324a95028080810b0036218540600701901c1b4050016500d810040350207030500e5a555101c9010b58185070062000b42100040f00f0109081450400700110300100d403c0884d49491f030380204070302c03007a80c1c261090110024102c0512800303200c40c1d039407180e69400c800b031580403074000003000b0440c0b150000340c02e441c1400c01307001d81050030305010400d00c0d28440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297057446 1250 297056196 297056213
    0x3031c020705070911070501050f100b22060203070203060a020316110c0607060c110601030c06110a0506070323010f0308180907050a090b090a05040b0303071b0311031902100c 77
    0x540c0742a00032990105000b424009c01e6009107c00c01e0159a40c28184082000c040441c001c0c102c060340000345104010f1141c9100d841030780d038502c8024500c5074485200949075405030406a00c00d1007132034007203204040d251088a009a10105003c50301c241d00860507076609044201000c07030b6000d441c183c0308054980d90000c003481d40c0700e0380c00004c149260703c0024100003500900c0c030099520400c010300016000c078131030f0b0054805a007000d899000b1562609803404010540040c514080c0505002d82203130190095000350f01c1070300c00c0d03440301800c10501503040c1809100c6c00c059100c040d1002c0001c14040c10003003615411043d00c600003681d40d5800b050f0003140a885040000b00001810450540e10042000190030300300181c514217403078080010462000350050300d109031750314001d80b0510794041080302e80d050b80c40b6800c0c4082c103001c2d00b059108003042d44410b548010007501c00c10120300e00840c0c110100c44150715144484001c03034092020b0051190a5102400103010840022401c1070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297058696 1250 297057446 297057461
    0x150909060f0501140a050f0609060f0c060106050c030304061a060a02060103150e0c12030c0f0c010207061e08040c0f08010b040f091208040305040902160506010503031c0207050709 79
    0xe0502180900015458070110b400c164042c0c030aa808881124090703680f903514410031a101184c503002034008160010f0601d114143c2c103142c0c04000050752070a4910500701400e08000c005094030758a84e654581901d8912480d05541d0143c1c02c100001000a00b081e0b00440203154804594001100d00101241c0740790320a80d403000142c1c2c001c4004208104180c020301d03030548004501440f0394030b410b40100d0395a81c0e0403004503104118102108291000c100700781c078070380d9280500300c546002d80c810300340703480f8801240028014040c030400800e869014400480320701074400c0320707001a415401400c80b03c0355000340c004c88107240ca00314000740d541c25041c0f492024003818000010354540030000c01c03088a00003005420a03604000381103011440c090090600d8820a060595a07540c40c1c0c07034220795a100e0b640000066a101007610300c04581d10f01020803041e8400d0046548690701c88003016540e000c0c45840100c801c0e0700500004040401e9006495403034440e400311840746884240c4001a5500c0c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297059946 1250 297058696 297058703
    0x906090506090106030605132328020a12050907090509010c08010f050315070912030804032601090903030b091f06050a020c0103020c2104080f06090a0204150909 71
    0x990061103150b24110300079500602003410100405490324000c00c06905803000c80c0c0c0c6000b03954103042e40c5127804401041c078038080380c500b59411500c0c11140c010319a2001200d450146440e007080c3e201940c001c0d101710307a502c0300c554a41c082e8440300c031015140640002090541c03640035484000421120a024080c0030b88021000820030090041005001d004d05030f21100000c00686c00c200015200461038680460805910100340e0b900c50b641a151445294005100342d40c0c400d0b811300a06511030a001e00a41c030955441d41524141a0702000340b181311107003c6c0c441d00c41d80740100720240c0b8a0f8403c51906109080204040000c01e0001310700c84002c071080300d0088007040c80c140744c07862403040c1070015010300d00b413260400300700c1741009558400f42501c090500d07500017200340701004104400d0400e1844610251256203002c18616002e40081c440c444071881034016040c00820007040192143c0500c00c004d00c0c0e074030311540130000640072294044900c0c003556000030a40c40e41500070390184a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297061196 1250 297059946 297059951
    0x1e06090a0605180a0302181f030f170a020c010e011107090606030b090103260c2b024c02090f0a120b0603030d0c080103020a051009031704090609 64
    0x918407044041000b080e40c0d03602c41c2d5004c4005200594030785940034280781c1c90345507190070b5a441c041400c1e440048005000c4000d1200b840002c00c01400d1502c00800c144182c445c2c140481003007520018602440406502507002050308440075441a801c031500020b051510f220080400d84ca09404c00c0704540102c1d01c296111502170050903018000c05956a60986a0001070361443d200d00d810007110002e40c100c4d503c1d98064070303070a41040740182c49000c8012001d40d80c1203041c40d8030760840c50f07203941413218401d00b41050340204180046801d01c07100a004000140d4910070290034880c203500054080314030b041c95468880240c440368021000000e500c000141e43c2c5558204000c07220700200c8106200e041d60040c00e0042508d450500d004043d8003004c07800c0240c490200003811030041c03c80d292106854001a00d04242e40075040f241220b0017078074480482e6886005115005008048000102d40c807400204006500e04031000e941d4400b4102c0e40d03040c55103c1c4030b80310540e1201d5001086094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297062446 1250 297061196 297061207
    0xc0c01080c0d090c0312020609060a0209010c0204020f12090f0d030e011d0d020114070e1306050910030b24060a020f07092415110a020a08060f01090b1e06090a0605 72
    0x7407401b010b1502d0b014a0008000b40d282c91480b0f1039543d0710041403400c15a030003060a02650340240d42040d20b49600401c29901c40461240c1103036a80c01605807401000c4000b000f16480b00000314101042c0706051001c0d080c558407489003580604844000192650b41e944240c05035a5128003a180d9900f011101070185480c540d41c009080d1380d0017071214000c131a040f005002c0b81c180c2004481c0b041901c1624400002d0501214440007802c80360700198001c003440c8204058034001a81074015240300381c0c1d081c00740c1e0b15102f0707560319803200d0000401c6510410000c90005890210094400d9009500c111250f450381403144c2d80c00c01120f903002e01d0100d40c440544d2814203022605103e03e2900740c070031896045141c001c2c0210b49a000030a45c1040c000300325500c50909206118284c0340d03540260a6851090361400416034809088943c464103c039183c00204010400380600d02040d00008c04014007014490005006040c0900c251580b00d0000c001c10b030056110341092070020300b042d854640c0c950 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297063696 1250 297062446 297062453
    0xd0804030b010509090c0108010509190c050c150105063f040614130305030a061a09041b050304080a170718060c0807060b0a0503031b070603020c0c01080c0d090c03 72
    0x104007178001076498001900d0803000740d92217800303a0304560b403c075074104036912034901035441c50407480d601b40b0b035127030074540b0390600301b40c00c0340041882c50420011256440c41c0c0036010710418000303008003548210204106806049103200b1303061040200301c03220341c2e100f0b0b80b00052801410100d807088000340c0c2d607030100014861941300c2c401d03030303056212540b1000f842c0c5103c0c10007039034945200040c03e101c40031012075184001940588042d00036400d00c1514003108020000440c0c00400e00700d8401c50412007020346d8413261080c0251094255164242940ca40d60745141490f08680310840400c003850850803201a03110703410741c1c09031601d074030382c3c07954601c18000c10110045650441020b0001d8043c4a5000444c2c03070085841c40d642102c400144080500d000885003e05540403070ba240c400815003040e10f020010b14500300641d9401204c95032070703540300254144e0043c5d8400c0d03801e0380c00c5900c110415500506015620103900581c03035182446003007441c000c0f80c07004001540e042095620502c02c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297064946 1250 297063696 297063709
    0x6030218090604020409081303031205010b0406050f0c0c09040b09060105010203040810020304051c050a17070f03090c030804090c112b021903121505100e0d0804030b0105 75
    0x410245100c0c484615007101d0569442402034030007809251345e0100c000030b1220710000d44188901c1005401807103a0380c1d08009145106114a95103c2c500d0040000356542044c012242194001c0d03c60720b00303115600c0301100d115080230480805031b0181c81300da00034a60b40c1568151243c2d04c01d115104050074144111031402d0016040355041d54030030403080c01405400100a14144005000503940e942d65107011803c1c40910441c2010800d09811700899080d000070207045944080c1d601c03182041c0824a089814000541c2c0d00c40200320200c1494a0152181c0c010351a504e02510300240c1c025500e5030b90441d81d510590040d2403c0303a403540248180c91380242c142c00c6010300070000f231401c00c3c044035082440010320309103000480c4207014600134482c024803074100e01000c1d8181101c0306506606028140170700c0340f107211081c50301d0440340900781e0944428803003d607031000e810403c03041011101074900c2c50130f41c1c1480f94020444d508110004510b1300c000c0014602c107403031194055242006002c034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297066196 1250 297064946 297064969
    0x130b0301060809010b03010504150e010209090f040201110d0807030504140601141801030c120f061b0906050a02101a03100c090f210212240601180b031b0a03060302 72
    0xb21f0303414030b801d02c40442c80511100403540c446c9540012080c45189400d4024481ca081507500903242800300a180c40c01640c4040c4036038002e807100d0101e42c210400ca1178a500f44a66194045140d00c8042440c07a842540105e52040c4280700720122584903080392444c040e000d900c84020f4034102026400c90b800d1032140c1130010300d0500c10a030095411580c030628254070341d0003501501c2d03e104145206006c0f0b0943c03103018903604200100410a01c1380c031920811844107400381d010801c00d402c0040d00d07034454030031910518010b0f40600074420310444440098002145000c000a03007010074504035640a001d42c050041c0710020001d0b020302c0071840909071070900c0c2d1064a039090725440800c6000d82c21005007804001e2608000c0107100c403440021107004000e80c80841501c1a0b111140b0500e00c81012104186645448401c940d0b03501001105d5820b414130802c2201081100c1c00c001e40d00805002d5a008030f0b5100c0f240e000e641d6215641c5d51035400c482c10070000280c40300410002d600f05030b082c516 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297067446 1250 297066196 297066199
    0x6180f0c03060406090f0b04080315060a0507020907021e0f100603020d080904110301080a06050c090a030b09030702030109080a03050106020d080402090403090807060509190317130b0301060809010b 87
    0x519046034000003074a902c4000c102400031525415201c00f0010800c01030b6591070307440400c0c040182070034105a9102d80045400121031108911a20180c1c5008010794412000e0fa5440c60300d050115420310131442c0c00900a20705510032a4115422041003018031418030041000030102540c140042c545014004114000c2031840e04c2d5040c405a200c2031030b030300d00070340d0008a0903650b190400042002481e40190303882c0d43c2c20005c00080340124004c508400c40d41d00540d814409900c60307944400d00c1c1e04ca040011139110a11500410014003440316266005914500b23480c18149682c001c02d00751000c0000486821030002a104900e64241c425107014102a200400c0b02c40c4039181e0203020f6a030702030800b0b849014000000b800b05031043c035541d800b0b0b008081c10394400540d111005440c40d00196240f511802001007006807403800414103408507504603011740c01d04640b008002c4a25401030406000c5081c9007140401c1d07103203410008500174100d940d203400891400001a5086546014825 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297068696 1250 297067446 297067453
    0x1002030901031a0330031003060b030c0901091a10050a080106021c2d080105040b011b0b0601020a05010204030302062212050d1e05071709100b0105090306180f 70
    0x100441e200020301e40c0f04100001c2c00c0105e4038100f0420480c2842c6410301e01d0958440000070840d03400d000302180f008403403141d40305000368403035a0101a202c1c4050001ca50b04545488010070000c44190012070003c6294038041e242008200c3c0401c81d82d401103503d503000300310005034144001e40c4c459586ca00603d52880a0109101e80e61a480040d070221510a41003240c0c036400c15051160744040041e495502d01c0030015800300710040900454001d1054500c51494003601681c19400755600c81c0c6003613803154081c560900b1660b100c01c03141c0c40141c010360441c45610010800110244014005180a60028007040ca0008940d8507050000d0b40324002100302c0c0e00080c0001003c2000b010301c0d4002138202a61502c418001c2000140b901407001049812024041d000b041d5895200d45d0140e0815902c1e041300040000c1d140e8600d034020f869040050b400800b031107107084d0f40c960101030746013414502685010801c000003031400c0d000746c2d042e96500c4000000c0745040c1c60100000c000301c6009001a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297069946 1250 297068696 297068741
    0x190b072105030411060315030a060903031a0303040506131e050915030316050c0301060914060f010929030a050711010b10080c0403120906030b0306010f12020d02100203090103 77
    0x803581c14844d40c510741c038041c00340800800e900362a1000ca13105904805400ca44014042d81400b0020f001182d0056000c2450001640c1c1c04240300c140d60b0418440c040c1c02075281501d080705014840d8401ba5240040b404051808a02481000012024541210510441107081c00d00b0083c0410001d8040d1001d0310755040a000103440110036640f10396010701d20003c130610036003003240c00c040c0003001d1580e06510380040070174824a141d000707150103800c20300440180d503158024040e00c0d04041075405d000c00d0015a082068078201d50304580d008001e1007500b040122889010703d816041904c2e81840f641e00c2d5001c00a00b41d42c0144880a0911200d009002a910100204054041c60020401000407447c001280d11845604440055610103180501143c058400801c0b8414500401c1c001a0900300803101c14940040d0160503140101519420340e403910310303900e070450a4020121303007049000c6896000759035007078142284020150040d6540e02d915030300050440351120100441568075208 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297071196 1250 297069946 297069953
    0xc0d0e0603071d0a05040c022107020303121009021308240105062203030e030706081b0d0e070612111c0902180103050d0305150f190b0721050304 64
    0x50f0340320b10000581410038120b00f00f00129044a03295003105030020b0401c55a5208564009140013142c1c84071400d40c68031012040500c14035100e8801c0196045e401130101507007104a00d011260001890310880c480d0603543c000c55001c0c0d03003050b0740c1001da80000810801010406100d99040b02003c03056498840c2c401030403100707681c42e06004240c010800406d41c4c9941707840c0702c10808195407951080416040d6645002003801c441c45100d18040d0180c0c4800150181c01000c8090090501c480015406a950031411109070002c0380b8111180340c86480414440340e06000c00000f500840c0c1d40c22254130000810a020340d0190310042d000c554003004101d100c40d4241c612040049100c00d00425807101c6800003880c446c141418540c4034003516000002045000540a581d401203504d0900c8140c1c1d0b40000380c0084426050b103550040305420141d451443d10000e0081c1c450700400420030065200d4007074034019004004100c81c1012000340c2c4404465528044020360209450021300c0c1d0719041d44c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297072446 1250 297071196 297071207
    0x31a090a1106040e013b13020a031202010c0f02030c0615011103040b090f0904020f01210c0309060e0708100902040b0409080d060f06050708030a020903030c0d0e060307 74
    0xc00280100351400e098807019034501040f903005010541d407460955844102e51382c007004544407074214a1910b0107100301c50035440c3c03104454401c00c80c070583c4500e943e48038074540842031851040364090740502c03003c0f0010705460107002d442c140941c000261151b1080000d0300b0000e20364212415980207005038007a05070002803a41e84944264078001004020781300594421203920036a2100d400049008603451140b0343c007074015840c00711031440c0e400741c08205201c0d0018040d10042d4001158141040e039550182100c10303421101028040e10800c52080b45c07800305c1d5101020880042c0c0c03210b06d910b061000f10701500c1c180c50940787c00f038040a89085000c03550748482244204c2e0b85070f240c1640b5810355030f59501c075901010010341b0a000c81d946c05c0c6005401a8801e0b0100c0e00ca0600d0824003044020320035042a00b51b4006480f034038517100c1d040d11401c07000c0e0402880784008135001c010506031743d02c043c00070303100010100c8000c2004400c500c40140030300403c241e10601800e8103000300002e00358000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297073696 1250 297072446 297072463
    0x201050c04051e0307080703050a0606050d080301050d14060a1505150a0c080f040e0711011103070c05030d0e030405090109050906150402071b1409011409180a030504031a09 76
    0x3040c200d1410f01ca090040790800c102548501624040d8540000074804040746401c0e4a52150300d040240e540c85004202a13200c0031071010304118010f00041c0f02c030713043c00e00000001c00d0058150190195820240b04d1070a101100e41c6540d05440b000e03004541d2850481e0680509400c46410303000800b15500254540100d04a00003008a01c000302c0084c00320044c203c072507445401015540c0d50752150b541802c2030340700b590030000040800d4260a00004103200d000b092107100e5812070f10b1620351060440d104200350030261103c0c0000c00090008105900c02c04001c44150300103107403150700d40f8003080003607035050707211003002030908040002c0c10401240140d0311041200440b00306c0080c00e00880c1c024065200001e05803001840d08070440840008107a04540707864030020740100c4002c2c2130040e081c0080c440c000d481440e21110b1385040c644002d2550307001c0403880701c04d803105200386c06c0c007860070380b401c1c40907408110005000c7c024000598059214501e07a41813182090601948603a91010074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297074946 1250 297073696 297073729
    0x6070f02011803050d0f110a030801260a14061608010b0d060312030b040c17010902033105060105150304030c1b09060906060c0b01140105040e0708070201050c0405 72
    0x40030a1240d9591034034a0b524041e54102c03080b01c1d202e4010382d1015080c0280301183c0008a40440701051140c0c1c80003600c4c041156255860500c20b034a041c0b06540240c0e24054640320346030015001714514841080842c82860107908111700c5814070502c4039081c144080c03c000c1c032300064007800300b02c5150000c410034112801c8070b083d5961451002000b034010911504020031144c80032551050440d4143c000c08191001103c00b0058001096410b1381c0f036102103905022503281c440e00412403009507074003860740420289009400356140180700f42d11924041c4002c00421b0043d07403650144481008264007401040d9850522100780c918100e2440c08010401020004c0405041040010201000c1da103500c0b250002d0300c44646411100001e003056014030340d5454038103e80002c241c0d108166650b00180c000600c2c05c4d00d43d01300000300180c2d5060000040c103001081200041d0584400402d0b849031043d41c0e03c41200d8140000000c2c2500d0000d0040e020142041c40240095076580c1a02c0110200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297076196 1250 297074946 297074957
    0xb0418060c0c121209140c03060702011505090c0706050112060e010606170604090c060906081b030606070c03051906050f07020316061404050319080106020c090403020a0b0a0b04060506070f0201 85
    0x2480c200c1100613001c1c05d0401040380c4082008450000381c00900f500c07080408905844260f52429012803c903121140300098524003074500304090300f040074400f0380100c140303c001860094a178072200306a039004c0c5e0003111b5041150101a0034045240b20710080e140b940030080c0241c41c94000d0052504588070300d440c80d49006c4102194096485610030407180364485004080c19945110103031600599104240219501000040c030341c3c0203803ca20040d91a8030141e150554441606003c0203402c107a40858607100c5095011000c0b51041040740031081281d0740b241d8112040c0d2405074192a800391501c550400e0b4541401100c6402009403010300c81c4c02240744074881080d09025000c0c10400d1402003003864182e013404180500400204440340c0e0007580b080c1405150001160a1402407151900680004044030780c946454038280360041c0c002c1c41200c41d106415203840c82117000a94520500a903600900e2040d400c10f40501c43c01007800711001800c2c011543c83d114075610184034001e04100c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297077446 1250 297076196 297076217
    0x304050a0f050a0b0a05070f11030f06040f240515130504020901031b0f03060e070501020a03020c011d0418060c0504050904170c0f0d0311030103050d030b01030b0418060c0c12 77
    0x103104a0030340f800e07c1c2c0c016248280403895414003401d4020f41d030601d14064000c41d05050b1607a440014014043c5a008502ca2281d01c0366850700481510200200314180305541c0d240011141e4030701441c0e005904c144456000c07442100e0810a000708112a04400c00d400c1c202048056915000e4241c1100e810a215031003e0100c415900e100003003640040d21160314410022080c40f015500c80c892070f41c0503c0c12550207644400c01a640c90700410300040059001c030003034034259440381c20510b5444110340c5404241c1400440024181d8403c020f00c4101d41200c9001d45080c031000e401107e80c0003c081c20a50b241900b0030011841000e8018400b130841c1c00c04014903881c031070004040720306068492041d68004078000b40322070b8440600484141c0080d08203207100042d8107040d004c0b0b9049903070200040c4004d08c00703108182d010307151540c1c80034103040d81c0d4029007070580c5460048a0005071401601c00e601840e40ca4100c0c12901c1c11040401004080c030301c040d00243e0507000d0a94a01d400f401e203c100e02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297078696 1250 297077446 297077467
    0x141c1d03120703030b0a05030601030f0f02042013090507020d0c0203030c0d0c061a0f01030b0301200d051f0501120906090606061b051b0d05030403050304050a0f050a0b 74
    0x10501d0318150040100181500c24560b240d84200c02c6041c003120114603c41c1d54000f0503503236410070300028000c090f41e50074000c0010540c0320340e60b580ba4400340c0007042105003600c440c031a101070850301c0d6651a6000400f610039150003070b46030300030b480c512100300b0050401d10402035850100744103120500c03105100c030000755a004c0003070f074580070110811603440c2d040218004143d00c0313804100f00c441c1c0d801c100c00a03d40d4146510803100703101018000c55400b03401c0c1001140907110011400380c15540c1e4a04a0312900701c00c0e1900c50200c00f56000450350f54903007082d19402c40b90f0042902c41a02d105a4030304540008011034082220024a04852800e070660100c000a0011941c0108185d181c4150142041301c6034110307808541ca540c690400161400a440e560b200104000402c80d422081c0110496210003150421080d005020b6403110320a543e9994959442034009175503d50011404208600d04004900050000a041d00308071510b4100031a1115041d800345000f0aa00410b405100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297079946 1250 297078696 297078703
    0x130c170102041802040305070905040302101d0a230a0c03060c050f0406020d0e09072114040605012606040b0601120c080403021b0d02060304051207141c1d03 69
    0x1603c00480d0046440c07064402150003903200340f000f1901030046050001d46c0d00c080c1e2046510a9405401804013500071058003c02080740052654801c2c1c122640910076020811000d4512407040e05c5d0307110f96260709900e00c2000c858028800e00a54071504032100000c1c103018802c0110380d40144049140c428240c3d05860b24001c0c650314081c2140d0115000801540c00610001000400d03140e0455050741c00081c01016030086808401195018918100c203881c4070344a154180e001090000300010150365180c840f09095070300362191a06e400c0140301131805440c108401001c800c807448807a03003a80f4816a200c00c1c000b0301c081c0c0030088100004905034002e02020400c4586c445080258500c1c20300301034445c10060f41c0070b4006100e041420f003548030704142440903081c4020321013255024140c1c20411070f81e00041044a850003005281220a180c4074050206030340700740401803040f00010b0b961450081c0425955058000200305250b0302900034405001001c038800c0100121084040030925 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297081196 1250 297079946 297079949
    0xc1b020d0b090f15190608210c030d0b040606020309031e12040e040308060103020f070f060209061612020a0c060f1701060f031a01080c030403260a05130c17010204 72
    0x229016204c0c000e0300540b00140c0c0d00303201d42110100100321184a103201001c9504d9401a40c120b40d020701c0d0f0800f402c142c030004841121440d0000c180c54003e06c2e8100d1070550b000080c3e28014107444441c20003452505002d07400141c4810301c01507081405131000642d0b120103281c04018a41b0194881d019810018007007900c01402c4010340554070341d82c1300440c0e09042e204907030aa00040c1e1030302c046541036100e40222400c1c1d86103403401d0b80c104041601c540d0660080f0360300456003641d0800104070252580406132171117200c0b04802c1c10021003581041407282c1640340e03c041c1190811090040081d860f00c08403016101c451910b0750541c0c01070030b4150340703840300310708050500c0c14508000190240e2003d00301880e82100d030740c24841480e0440c5101ca005800719009404203100200203030000183c6005150300c513020340340104031124220050000c1000c140d1980c00c420180c001000a400554010079400441d041202d406610181c0c032130701401d059600904032440b02001d55001444002d4040e41d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297082446 1250 297081196 297081223
    0xf04090c05190e0a06030e0c09010609170307030c0609030509041a120a0b01030b1f08030d0c1b0602030c0d060f06020d050408031c0e0f010c1b020d0b09 67
    0xc09240510007414507000754040490541420b01010b603014403410380000c800001411061419003010000e44c05000001342085162251810b5003034079030b48412400340200060344803240164100742116010701e1001c0300700c0101c6e5004014210010744d02500c01e040e82904400700290b04c210714a02100c1340e10a207640300e640241000d609030081500c0c00004100d440c003c803487d00418805440003900c1c0c0381130850140048075680300402c08a140404910b034080e9103448908141c00b20110a0310f6034a00d69004114280e101180b990028400c91046800c00121410b001d600d03181940d1a041f0001411600102415000310200d02c41030f441c3c1d4199562003440728814440b0540b82c0d03010416040e8903100d41c600500c00e03502800308090240080310103503000b08024510709020020f03070f90030124071117a40140705640c46270004446c80c800d001c0c1d4000b590001c0c0020175a02107014000b03041030192008062100d646643c00030040c0d5804800c00d0718241c0c45520720140382d5480002030b0525040c43c0445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297083696 1250 297082446 297082451
    0xa0f050d110c01140405030105190e070515090414011707050a0b07030c0303020d09050606242b050a0b0f010e0a030f0204090f0b041415060925030b0406120c05060f0409 74
    0x2092800e140b501816521103c642b0810481d038841704542d65911580c81a1900424000f58400130302c4844001041080030241020035550606030003205600740c26409221928114501d66904507030501078140204030440c0c00280150506500c81c3d03080c81108002424410300021501c20075000f601a98800e1a06110400803011141003940d10340c1c2044a16500c12000d03001192141e8001a21500c85080610f0104c1d0030404540740f01e100b44030000c94503540c45036801c038180c41c0c2d0040074000c0c2481080501d001084802c1c03400203000125014112580c14802d40d241c0012194036003101c0781049982100600300c0300982800860300528082102410381e20340c501910050040d0030240300e01483c80b4950f42c02c44140307204106900c4160703d07082800e6030410500410041e24001c540c29800c0140c23300803001001e180b2240844840840480b030003c02c3d1a00e04505091a0034410307a0020401c2c0800e0700d8400c1c80c19581c2e0640481c041c02020321800d40803d692010488070801d403009001401c1c1b08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297084946 1250 297083696 297083701
    0x1308030406020a0515131e050109030302040e1005032104050d03030e06010909080414040e010e06070906030e15280b0a05030d02070b03070c050a0f050d110c01140405030105 76
    0xc1d100c00f100c0e0029103441c40303148000811061030000c818880d40103400c01c005010310f02d94a100e900c02c1c0101da0100d80003441c640d00d002041c028071819120031320a071401a40c641c5005a40000100300800401252040000422064902040c00700f103580c480b2001d4407180c0c000401a03000780c012030f040a6007240503500240d0401d90164407101c0703180f089608513882c5a0740c07183c40038282c0ba5144030082010708184401c006c1c0200310303410100ca07100001c2002c2006100e19007201e0842d4014030041c5d8290707100406000306940c000801c40c1c0a05031a280c1488050045030030b46954010301c4213041d0810305440300040c10501741203480802c5c0600095200e10090b4220345001c060318070032003090301c666884540007640e8600040c1c80000d224294014040c5289045190fa030700c1c0d00020010024490450311040c001a030602241d00814442d004035101102070f81046898540d1954503041404000390329a13030314807000205000007a0091802c4e0301b04058108800d0014041c5038000c45d05582400c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297086196 1250 297084946 297084959
    0x4030f0224090f16140a0b0705010f06210f1410050106031a13050c040801020f0301030b0601050406140a0216080609010f021c0504050102040b030705070516050f01030213080304 78
    0xc001c2d0240c01081d0440b142c60001d064040e4881000408519a840d0540c104000c0c040d104080c03040c034410005e03e00b41c881c60383d41c158072107654004201150640d54031074003c00c00800c2c62082e00054082d01d040d80105400041340503850385000c280181c402c0401000040401c40f01604000d1101251401d94404125564414015000c02e019440101e41881c20000d650490315000800d40c00c0001c141d2070340c1c1e0310100200d1000340750113842e806401e8030070080895108801d0004040c12081c00c800740c0c3e80c035855803d00d200c918402510071030421908020401230b1700d83c04a01241e0740394102d100d8660310507010030143c1c544008601c66142ca200380c42e4000407030031004500540b1034444003000380410820811000c00301c0c030944001c0742100e840364400d486200c4041d0f014950161240000501e05a120941d64070603400c00c40d800030000e00c0000308901081003d10580290021600850010328202400904061356210710070341010b501080c0000e1085d40c1c1c10014000700031240c20380e90f44944030300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297087446 1250 297086196 297086263
    0xa0212060106080f0615030a0b0a0b0a0e0f0d021c0204050f01082103070c02030703170403140606060403020d060b0a0303021e070e010b0c0f070f0e0c070201020604030f02 75
    0x840e49010810f0600041c0d182544c000070188190f800410301b1075031048050902d00c180c0c04c0500005100b5a54061071402c6072600c10602c000703031004e02442da80780d41c8c81c420000c00c90b201c00790046014940c0090b100c83c95845207010401241c3e4121030b4104003c18240720207081444c0d0050103540301b130800d41404400c0700e00200d00c606030340911041e54500c001c244008040d90b6000203418148050420014103990321410041a0851004065451403903998030307841000c007186c0003007000d41d090000b000c00403c20681d099020440e410f6000d13145514151002a50350b0140b8403010740a820407800034010032080b98807040714000c0091102c1a0980c42c1c1c20000d542c0e450506404071089070380c0c481e00900c0e94000031550110307150702054103956801e007066281e058111072038091481c03140d9850141c10a2044c81307804046d01c0346003842e8080d80d02d030082006c00c02e44042c00c2b043c040e0808220b4680542d80c081910b82c4c2c89070301414240300301c44048400320310740b201c480c50a441c0140181d096040002081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297088696 1250 297087446 297087449
    0x10050a06030b01060203120a1808040306020909060a1503051b0307030608010b120c0d08040f0b0a09120302030318070f0e09010b04182009040f060c0f090b0c0a02120601 74
    0x70030078a09940e884910684c0daa101f06485251800161070019050441075002481c088403490380c1c004034120280d075182c1e401e400a41007102c4031900031402c4501400c1c1540f025501150413180d5208070b5140045441510300b00794281002c05840d00700185403c1e100350040b640140126240d10766a01d4848402002407251b0f00400066500f800b40007659440d0040345609194003400241940340da918040084d1020152411160080e00740400912007034400031400040c00d4840120f9965a2050f07030080440c94240c1203510141b200800750000702c1d0740002941c1c0d1011143c803241f4030b9101000002850005560b00c2240b003c0c141100c045044440c4101c200e001f901c1c060001d000380c3d4604020030064800c100031012030110603d004038086154440f00c1c04403a907000c1c0d410780c0011000c0002c81d10b80c041c1101c00307459070144200088200443c81c4151480440b00c5e18080380e0140007074030f000b49215040c0c4030340100c41e04003068424400d142070016072425940201411b0080c80c940080c1601c920b0309 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297089946 1250 297088696 297088703
    0x10504260c010503090c1e100c0c08030403080a0e041e0f050105030307021008070302070b04032c0918030d0c11070803030c0304021c021306150504080a02090910050a0603 75
    0x141d80940e1502c1d40640c3c1502e00070003e20001c0c050113071400301848507070600b4012012000303400b4122615140c0390703000030559000141da02c02c8081d502c00c0c20400c0880c40300d036101e008c441c0d00800041000c11000350680740c1142c0240b400d103c611544000040c050704c11210741510b01000c04800d004104c40710b9010320910030702c130303003041c000e903a651002c140d124020761001030b400001d0102400d4401e842640001c2c3c0c49461400c1c01410300d016a100ccc0031103100f0445045011030004025613107102101c2c2d182002c203440e0240544090501c4a0108110784401b070319015003940020201c07421903400f4803d4600c03034494500108000f03084840005c0ca202a0401403400341e0260100125081c1e0010084034400e03d060300015285444983c00d0000012004081c012a1402602a0350042e40d230482e201044c08014800402c43c98207040034090180c807a00304034014008108000c0115250103d0740581654045078058020703501c00000506112441107034140d0b0300d141404114000c407036940b110094902 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297091196 1250 297089946 297089953
    0x13111207050d0b12120a2303040b060402180f1503090307110a0608060d08041d18070e060409050309030607030906140c120601020c190816121101050426 67
    0x100d003080c8000044c0f42c0486a21a800c68410010404100002028900d1031480d060889079036280046081ca0300e191110300d801c44d000400e000c24820300c0260150040c804580441c80d1090729180c2d81c9480c54050201c41c06090140f000910075a01d4249003540f60144121b010340d2840c040c030b20242c40754880101251100503880403400d440c03c088015005a815580780c00c2104d0300ea00b802c002d403400b103c000807103800c4410880800d50007841c0e0403078610390210307640442c0c1c41c0c00c0c85c240c0d0049070310702d035000d1b91000c1d4000c00b000c110303c5c5201715503903810503019100083c6411481c1089404c1d03124040010b0381500c0340700d0600044540c0356216080d000e0140d041004050214190000344102c00e44410140d10030030301c10210400b0104507500e42001c0e050041340c0510f06c1100100d40004042e0180078945a4406010004d84e2418090441e8034070300b4451602d007181c14020f010108843c0d540d806402266042c482c04510390103030040714060002c60760706150b10001900c44140b03644603a00c80c00050301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297092446 1250 297091196 297091211
    0xf151d09030c0f07033809030403060c02011505150a05030a140c03010305071a0a0f2f07090203090a14070e010f080f07240903020a0905040302120913111207050d 71
    0x80a0b2a03411806240303a12030101d403540320306c3c0861800c4101030300343d92450108001c0080081e0047c403802c00c802c00c0d241c002290041585140c3c568a200f01d500042c0200041c0d80344d0890036a80ca012220000c0f120305209441e074076800180e40041c2980390fa842240c042c0e81e0103001d00720607001d028604072481401117442c0b20791107402c001e100d5200e0320496659800103115400c2d456002e00b00c0444150000d140074a162240c0c00d01a404410989070742e94a6036069541c013070307031b0300034248245800f81c50b04a00541ca5404c110503410b035140a0481c000e42110301d50170100d00410001e000c94001081c221210150958403800c844105c00c40901c0b554405124800c0d4540d100c00011900030200e5210401003480152550a080d1126299804d92010480d44410220061b07480c0c0c070812000d003040c40f00c002468900b0b0300d0080c3c6010742c12000140c03d200180f00c0c825a03030b92104401058031100c4080801c4400ba8100c0590b03460194102c0480003002440410245580c40740c050002510007000a00001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297093696 1250 297092446 297092483
    0x5011b022803020f06010906140f0a090e24062d010809010b031207030905060301030b010b0702040b040c0c021f080a1d0307060f151d09030c0f0703 65
    0x4240300200c0700c2519084044084981c0031000c0c044014a02a005a03400034140800d4a030802c0e0f0240c010a404599503030b424414404c03d1066115070304403d58000118582020000e04003034107610640b50038645a01c8040350700d48050090341c1d0b43c10b03000c1c6070b10503e25408440d8a000400300321540c2d8001ca180710200c24007800741000340c0e0104020910185101221000115070100005100c2c041640d01c50012092944042000c10341d40368158201c69215030580c50000d001e20455070081d0b20840c828001803010450120707078507045989100304280c4d070b00c03410b2022501619051800541c018541a841c1810580007002140594421a0b4100315030032210070074102a40741241210018405500145c260180b0368011600c242120038070580f090b40c4050b18a14690280350110bd055486007040d4010903a40e02400358806281c3c040b80381c4035400c0a80920038800307050740c2e403c0404603034004a5460703442031046a150003041e400b40c0307188009601d2050754a03141c45c8000c0781d194401d0505951350 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297094946 1250 297093696 297093703
    0x40204050c09060306040c09080f070513060506040b250b0f180a02061e071208161e0c171206030307050601030f08041e05040f150b070606030f05011b02 67
    0xa02c00041c8500c0c1180c40d400244002410258011000c0c0801c919020034144001c2002c0c42c0039010705002044007906040c18080c0441020380e8040259092440c244101d96424041c3da0684030104080d80c0c03101c1c485400305403252205903002000c60b00c404c2038402440781c6e0107220f80c402d90141d10846150b4a40b41ca1250701104569030103080d0344c00502e1404014030b0144014440b120b0b00040900c00080e85040224103039100910481c1d45d080a42c119228281d0000f145030380c086403800302c1c4c120500c1c0c0940b0250146144d2024000c000400410b1242d0450081c50200102c3d50400d10100009407840c2444130945c1c0040703628840e01c0c490038005401442e0000c121800f0941c1f04015002c686d20719034a407031741252860803c036100c51702880f0204940c200000000d5000b4580301c112070499103084c1c02d20088070040c000b03c2c141d46007428011075030301d4043c495680803100c0301c1002940c0c03aa0070313041c0b1500502da2900010101c16000d0081d40c18400c054010781c5602c503201900102100030f01d0750030780e503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297096196 1250 297094946 297094957
    0x60e0d020613020d0c060509030613051906020d0c0201060906050402070812090307080d141f1406040302060c0616230f1209010e0f070605122d040204050c 68
    0x5034085400a0b03080100d5140c0b1184191000e031803160a48480e0307403804403022061704201c0c0010004904000b45207820400c041d04043c014100000e8034005840b06601e036200c2a05000100a140664408015041c2c2c111000c40c0c1e00300d038040200c0e10b032219009000e8603d40c03207500c180310705120300403078546014401c41d020390b540800303010300d4400801d180840a44004001310003d000c02d00100d00031900c030400504540c51240c2e00042c4600c00401004d0310ba44029040c00c080850001592102c3d400e00900302060b503410211351151080100d00050841c40780e604025040722000c00d6411101600003002c038002c0444045440e131801030f4420856044034040101000c00500e0f0340111004003881c8000c019811004e400c0798034042d61800404800442030b20403000680d134503010188070308801d0081c000c0d65443c08010f010310624001c00208035015568017600503800300008104038004000041c2826005459003001e4a160280c004500700002c40c3c0590040d410580060403111a4004850 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297097446 1250 297096196 297096223
    0x10c0305160c0f0b04140d0203190303020d060e01230a0503100608060702030915030406090606150320071112070303020303010905010b040e070305041b0f030203010f1401030201050f130f03060e 85
    0x2050018004200001c0d042040350598060060312b0480c0004180b00001c40b102c14065103001d41c1d64103140070b11108988040d484041c000341c2140c014850ac01080c94008071012212101c840e01000c540c00140c5412500e91055515200e00011260100388540001c003c40781c0d994240c802d50ba07034804017a03881384076508419030701c44081902002101107000103075400c2030060038000345001c0141d80741b0040f41c501c0d0b00700362a1410240c000141d40e6a05004020550458144c00b24060885501c01207040c0600c502c020405110440360a0043c0c5410700010480c00300c40d01114903060752030901a45a900a0107542006810b11001041464038881250206c40d130041559859607070b2104100e000340000b6104450412451030a890540c0d40104c0000c003900340322400e40a000d2840c1f04040c03c48a813008040100c0d41450003c070010456140300c40d044079020b082c02a5165208480c141c001c0c81094803d01400122031000f14940040322290f13015240300380307001c010264285184c3c0d65134031140e603240c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297098696 1250 297097446 297097469
    0x106080604081305060a120f0605010909020d0e011401080f0303060a0b1c0e070503100b030303060f011101060305070302010e03030304051c0909020d02131505040302010c0305160c0f0b04 82
    0x900140342d1400900b200540304a00d00b02d000e0326080000c5d92640400d0313400c800501080c0128594100500c100794400c44a01c000b00403c070302d0036001910304441803140440f00c40d404204590180600d403c1140d0b00398100e802007110b40c840c60b001341000310b028081e100b02d5105071481c251790884008200d90040b80c0080468288528004840d28a40d2051114001c01442c11030641c950b0549406034030300c0c014241c0090520f20741010309061411401d002004009030130158004030f15200881101d80080c401c1d65000c0072041c0180044c2e6240d0300b8094095002d43c608000002408001f085080a99100366100d4290300030883c00c0560b06d010036100a0140d803c2a080e800c050380d03c070240490139158504025003516962034150081b6000100c0100605400040740d442c210840c076001c001070102240b034429903400d40c3c2001002400307240402810701102038111018903010703c054810020008404038402c886a240c003805900e0203105400b904a401003021400e44d124800780c6040e00e0b8060001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297099946 1250 297098696 297098701
    0x2241807060c380f07020a031d030a0b0f090c040902030d0806032e0501050a030803041113050c070210411b100c0504140a2303070801060806 62
    0x1028000c940b0060807014440504a41d02c0c940c1d100303000c44280020000360b030343e0110310b0301180d440c01c1440028141011904410343c1c420000c0e41241d0002c00103181920500000a0100007180c070b011044500901f801e10060100228171900b54038440c82a540141034412640000c4140410b8841c0ea0a000b0f41c59000000103400d81c40c812455144e0020005048070305c2454414126943c2480b20075404412000303611a40104000d6802510b00400c4169400b04100e481c6807617001c081c1c0405040102000d10241c0820b50a0b6600100010105c008030810421810080f0565266074404c120490040340802d0445560f14000c4184171f086050583c160303100081c1d9501441500c4071880d107120084400c48048450b80302a100150000c03000403040b12030603a1030144105c0c0350107400c01b6040c00341820140002c140960010a440c2140d0745102e51102c2341200000103420030207940c00c4098806090919605082c101452441c2144800d405403085941c44950741402da4003030b40036030b42d220b6000b0341c003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 297101196 1250 297099946 297099953
    0x50301030210140d0c18051012090510020c1605130b0105070506070c0309080a03050f0c0c0904150f0905070501050a02030c070e042d060c02241807060c 67
    0x40315102100d151803e00c2280f5071a0003042500e410a098001c5442d58505890b0016030f0068100804414045003030b05101d031078000090030004904030348000700302ca00d0307500d40707206962134000390036896000c82642d03960481e019184000f034002c051000243d10440c00c0c10000d00c20601a5202601c002800303035495981400d004ca009448a2291141002420414140800e40c10300c0058040d0401340ea503011729101c0c500f0002e001d142d003a000000143c0052400342c00107074000088820518421059a40780d01c1280001c500f0555540200d0740c000c000c070030810041000078404508032210b10340b01080221089603c203c11aa91144024416407015409000c01d43c001c0005e02103070803091044925040340ca0030500c1c203155166000c440640490b01c20b000401c42090034449180e5580102002d50817070006504c8c280f1802d882d4060b21a9548400f00240c4501c02c0c00782003074110201c0241038000e190a85400780c03c00302181c1c0220850004401610725030000305100c1c0032940543c2c3c484203000079544 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 297102446 1250 297101196 297101209
    0x31a09100303030e030906040323190b191406091005060d02130807091e020c1f0609021206030d02060c12060f040e010903031b14180306091605030105070503010302 72
    0x10341300e10380710501001d0107941d40d200c0204051071040200000108030703185844400e8501c02056981c0f500110301803041c1004510290060303503003100c1026110384460111400c000d051100c0101d01c2c50a044d004400c80601c0030a29000b0001910030652580c3c03080100c1400c42d03154042ca50b841001042120800b40d50358024040c803e048580e020304036035503940e4a03490040194416194141c07103038016103400c05002c04441c9041d85c2c2d1031040d89400004008035407246d43c131440d003070100703514061030300d075405100ea2040000c0c01011a04555803441c5548120459100b241d45502c60b10400e0001e40000b0b2001c999a8040d44610b02d842d4107005226801a0301d40e50003c080c5c1d07402000f083d10f82c030304d29070300c6005a0b00310740c14400001035641000c0c01d00800703071159aa943c0c2c01c080c01c51000205600c4e1b00c09010781791034004500198540d03560b10500b0b1340000811038015450b21420080c00360a510110b04104085400700c00d54150550f124149801c0c0c91040383d090b00491000d200410140c18000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 297103696 1250 297102446 297102461
    0x21809010f1a0f0c0703060f020405060d09030212040602011409121b19030801090f0606080606090307090905160f141c0b07111e0615030f0706031a0910030303 70
    0x542840f400d00704440400714094000f44180a555070005c1da0400500440780300d201e25076103000702c0035440c15040ca400f161807481a020f2000d1a40d03a180221006d240c1f0030b02402564102e0083d6680d5159074945009000e000e074503030321030400ca40d080c02069004600080703107500009c1d0518a58100b40e648054841a203505400070701150084403800410442031503850800a8480d854100040d41800c503401d0845a008003c041d0307042c074001060001e1504041e885521031002c582c280d50740c4402d072001c00e041c0006548101911820140042d04219010810b03043e00d00c078070043e2522107581c0d850140812000c030b00c51280403519401501c4024280401d0344031484412001040c844d210a035254000980111100340001c4d10340810240e05030320900591515024140426400e55010040b858407075401502407a000002c8a0301403102c1c0d20207100c1c4005104e2200c0036200b0540c0d8a001c0a030251400942c004040380c00240e44042c103250441c4000d000d50800c802030002181166011303070081995 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 297104946 1250 297103696 297103739
    0x501050309070504200f131401080f19090807030e0915010807090305030a020d0f0302090604090f110309010b013f020915040503070801020412110a05060c01021809010f 74
    0x440900013150916100103001b40460601d2880d61000340c100317541405c52842e00500f10707541c82200c640405070fa001030155041a100c185022542c1c5510080300001d40264441c0181c044c100401c180034020400c02800d0024001c1c3c4821400c002041c041188c0c04000312521200004803040c1c4560715407017a04082e034003000d1800d1503d003890312a103c4a2035500000c0381c0c000164040000e1001d460340c0000400156138041c01c096041907a18030004400f4042d074051310460607500c40250024101d560040383d00c0c80c051080c5c043e524100514a10b0203001e100700d40a0210354000ca18060800d00101c280341400a026102d034143c1d10701b501920601d100043c0e00001040c0c00340505070180c3e440c1c000203004003010a6102d41e50b2403611045c1030600029078003299082c0d205100c108403030030044140c43c200300d07401468110720301510000500400c203142c00c031a4014001250700a00140e055005003200b51000c00350440550181040001040b424081c0c2c9130180c10060041041100b612031481c0550f15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 297106196 1250 297104946 297104981
    0x307030b0714031f0506040b0f0c03091f110d0f18090501120201080f07080115170a0902120a110d0c05091312050301031a090a02040906020a090501050309070504 71
    0x180c4010554100303541309050440700344c0c9168500c0b030404080301c006000540b0210b08051070150084040e020b40201d0f503600b04400600c555041d04103100300c03603144100410041b01082c460421a42c40840800b4140208180c440088104d003000203448200c103465556480ca1141c4485c01219240b8003400c3c41c18900d0f0085402207640320013405403602070600441580380340300540c00010280000680702020b0402d024091050329070380100190705482c140e41c1d1215040c0a0b880084580440505440c500c100d003802c140311110804d600824002c50085a40c41801102072041c0754980c40c026100901e0000c1c2c0c011044901e040919038400b40b64003a811b511a41c1c0c0d40c3d0001b150100504480d41905500d900000004004590310894524a15403030310a08660460f41e410540069225000710380b401080c001580c01c41d02042460100740d030140061080146502d0100040c0d0402c031002c401281d5030000c00306c0c0300d5224105807445544928004d03c41585484240001894102e001001004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 297107446 1250 297106196 297106217
    0x204080d03020f160b090c1906080603100e07030201111501050121020d090302011d06010909082a0606010c0206030105060d021908070806012c01090906090501030b060901050307030b07 81
    0x1c107510b18039004140105c0c0f8841191134051a40e030b04224010002d0f500c5070500740f00c4209110747e00100c0740141c50107130519030130a44402c00040d18102c60804d007450140c1c100400a248000b0101c3c003842128400c2e00c0d00f125601d460310340039458408411585080642070001004198411031002c469440c5c222011101030f600c59801c90309a030320001000b55100d4440107001c04155091140035206c2c40c01c200f0840d540001c002004e40c4400043c4194060345480f03412050911180c83c0c115903000c248524402c500c140d04408500d075411903070300616954001c0c4000105554010151301e900d841c1c0c000c1040e031441e0f0030101002241c2e00a602848606035003440b181080300300034600c001d60080eaa4031010110316040600509180000303150382c0c10083c1d0300da507058ad117804a41c0c1c40320f0001c00040300000300300310800048030705110036808212014182200002c141c04c160f070240c0c2c145d0b4051007034104265508801e01499044c00c1c4542c90305580410000c0001c01d0040c4500e507001080d07403500030f8110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 297108696 1250 297107446 297107467
    0x50a02150a150905041709091815090a0605010801060f1701020d0507182405091504171002030702070e040305070b040c09050601020c010905040c0e04020d0608100204080d03020f 78
    0x140b45038100c2012035070750301c0500c0244118081e03a00d01c2c05600c800240c0c60001071602003812583c001c2c000010525031102c1a201240301401104403030116090424180d18003400542d40e241d4000c0b0b400d84040303103040300100307000c8c01c18020b03c1e0980d0f000044a0f00c0141c0380c20b60108060f136070615800b000355401c2c054101014154050103028030000c4d0350f624a0300303403841042c1e020103020307500034a540070110080c0d101c8005e020710b1940000c4045d0030550340300e0020f54081044441400401160701200050204851401c0130f0841c600d0030702c0304d044410512650f031822040b4401601c3d1000941d1040703104100001240344a907503c1446441c1840c1090b10507a039038554102c0032b48049032100701100d024041041544525540120248003c1c51401034400c0082c1a07150780f4080c4900a540720b079201c400d458041d0400d01807168001d401103583c0d6160305000710041801740207010840c01a441421030301da0090090f5400d442d0f405010300054101c00405030005d40c01810b500441c0341c81481082c064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 297109946 1250 297108696 297108731
    0x4020f0301090902011b030c02091305010e30070602070c0902040f0e07030911061803150702390a030602070c0f06090305031c0908070c0f06050a02150a 67
    0xd10042c0408151084148000343c920301a85482542c114051003443d004a0340c0120034214554050700e00442035116041c24070304200c405a009060b56080110101001d40002145004601c106a050005007800c00d55910000c103d1400d011021206001080114595a00800d142441414040241617481c282e40c0242d0301f25a1003100f0310401c1480801403031140b00c0100790301807418070b410080314141e07640e1141d0080452007003070700601020940c0700312018100d02d0044000d80090440745506104a0013080128045403034034010300031400b44903a400320380c03a500c884943c00c33808108818022150401610001c10408030760040351902d000021904503c01403094a0042d00034104c0b06051a08607241e00e000341d80302c2000c00c51003201c00c001241e004000d442003500e000c242d5007480c403013092820700a880c2c01800982011400142e000400103d015984112005100312003d40c03035840324207503120f0007110320f88030141c3c000f40003021000c203943c20200c2c0c2c130075500d4400040c01c1802c0c80b000300c2d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 297111196 1250 297109946 297109949
    0x70302120c090112020a120c120f02071101080f040809041d0f060114060405130209040e030c0d020615040b1f0905130207020607200d06050f10030b060f04020f0301 72
    0x10905400200b03819256400503001c1c1c2c044030300041c1985030480000d4014884a4140311081659580e0050303680c4042c030400c15020134042030041841030310300e03040b82c150003980030303450413035104007a04520403032540100c010f40d100d010b258403034000e01ea5454030340d6211984146d4015900c55503c500e104050007030040d16015100c1e03440c004042080004018030714202d0181c008520b14040b020020700d01da0b482e2000c88058a03c00d5034080c0f451031f2a40c4d0200040d000d0990550751050800102642d51900040a450450b011030200c0f03140c601c00c24401d0b0385880303042d0f90101039141030a00d02c4086060580140d040440082c01c14581103030b0010082420651410b10b403400120551010011481d00400e65103016860307000852602c1115030010340141b01d1078800605518030004a8070054507212250312541d00041c00312110443c00b880d001c1e0003041c0c21100c1000b000d00e0103000c214001d8088401d20f0641750f00610402158030340008100300f030402e104102d03501c260200850241d842c6500040c2d030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 297112446 1250 297111196 297111211
    0x6050717030f090105060406210305040b0c15100b09040e030714030a11071214030415050403060c0305090a02130b12010b21060703090804051f0e0d050606060307030212 74
    0xb52500300000c0c05800d4650181c80703035108600706a400e000ea42101c6000c00c09004446151120b01d11031071405445a0060303174010301e410180400e103c84003010102e0300c9080700140c09451401c9540309412010010407030701a089001c1c1c010b2244480c80e00b0035a0050102096410440c1e00b0506140d440c5a11204a00444815030300042440b5903029004100400e60100a03400781c011641400c1602c011001034410140401c3c103541c515002c480400d1048401400c141e8450302c1d104045c0f10409052030b0300504c0201c0700c1a18207801294154841c0c400d19000303454404c00341c0701c682c2494003080702c200314078005640000c0d80c8012448495031a142c0718071021904030004607104240384100610900c00f10381101030441d1f55811141504404140f096125a05040020b0194028100784816000b150401900140d01111120804e0301d5074000031040011540da0b800350607201c4080c0044a600d0039802861075108001040c40740c50104065a4050741500d00181840d1181c160310741c840704c05445c0380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 297113696 1250 297112446 297112471
    0x906040905130c08030c10021605030408010c0e010e100c0501230f0c0306060409111603050c07061b02060313060c1d030304030201090e130c1e0806010803040605071703 74
    0x82080152400b107903c001d0803140095400e03c5403180101d900ca4a2a20888003a00c3d0f0010789e25481296204481c14074a4200701125110750310307541c41a00a000044030f06c8003148070b10000302c100790b01c26040c0c07102072240640019160241002c0075620b00040100032607943d500d503025558096071042032500310b031045401440a90a0800c01d0f184a20405086154503034420000c01a898583c40111402c50b80b0714100041d1100074807811094900905240d2880074407200700807828140d00030050b04c0403170404002d0f03407075940e070307440c01610b1240e1000e00b003040350310800c0a86405072422402450707000e8850013441d01c450145580780350841e0080340040000c01c004119030345c00320010034403000b0403c000b580214581815a00041c04403881d42c420360394044071000004010381d0818005c0c000c4143c0c0700040c241c0072601c8016a03803640042c3c3d0301503080100607400000b0040e9000800034100c402e048003071441c1604000040740c00ba8005503080e1201141c600c002d511054403440114450300c240c0030303003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 297114946 1250 297113696 297113731
    0xb030303151804030915050705060f0108060f010501021c1206350c041a04052406120a09290a05090102120a0c170405030903060c031006050906040905 66
    0x8215041042d054800c4140015004110000782c21030210800c1d10310040041d1100c40380032804543e0f52043d0780004003240620b00074000d81c21070b9000e50505903a00d00050300c03607654416014a0140100b40b15003401603100901c1000380134035149101603406001d24141104400204404003a0b80540e88942c4010380401c584107020b109c111804041402075400c00540000070744c83d071701d0b0b4844220343c006205999501008506c40f90031003035035410840c040d01c14481e91800300300c44441c040b0340c41071098403520500910501440d0183c00c607a1440246003900f42c95450304c084110090032406000c841c03090340f082d22820360440c10f001c004001e00320080700b50594900446454155040034080c424107038010b120701c104007018500c491303500c140c40203c0011291550b0504131284074410200742080c0641100740418084080001d252403c3e041d01103400f50f8460040c0b400451000f16817130429640001d00034070071544100001c180d04d90380142042c0c1400e03180d40300c440417030f1415101d1000c0700810068 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 297116196 1250 297114946 297114949
    0x180e190209150a0e1e010b0a081009090c030b060d0812150901030506190e0a110a1805090d081006080606070618110910030602030603010603052d070612020d0b03030315 74
    0x580340c0d0f00c404007040c0c0b2081765261031f60041840c003503d40b40750144890720000602031000100d2801c0280071000c0c091014108900b4520b1008a403400280c40c0100c12800144050500d41d045054150f0320044062500f2646458100d801e000640200d800700c280299039421951441070303141c040d601403005055503040c8060708020184c1519181c103440750500d000c4440700e140106484515a802c02400032160821000081400000740c1042c01d003181e003c01c0541c00c000442e03011511901995049941c070001001c82a01e00000c210b500b40d8491403038141c18003095100d45005900044c000d401e145c00c141c0103507104410354000154004142110445002c148070101200f07071900380c410f8030088a141414a0294440c001c11b00000c1d01d401e03000404959a52070950141d0f0003503070403005842c0c04440101607544a10165960001c8410a40780580b4450b0b00125600088400039140c01e0200094110001c003e5007100034017020b1196210541c0c1c00b1a281400258400e00d1a08072a8440300b00040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 297117446 1250 297116196 297116221
    0x2040203060d1a01090b03070303201c0c020103050c120c0c1006150f030c2f011109090a14010e0604090203010e060115022113030507180e190209150a0e 67
    0x11031b51442640030403010008260408995402984c1091081d00304e018208401841c0890740c0000700002040304543c000000d80c02170700000c40b103100340e0f024003254442e4800c1822601905c6280c0e54038040c044082040010100300800320310b0940016540b400603e841a00c0884019901c441c140700c884014400700345a208120410226641c10104050104528010000340141e8540800e150382c9018089102c04002003107040050614000d204e030140e031900c1c1142c01c0c5c10590381c4034000c540c01e50229440882d203025181c072800003480d00a40580c44c03c00928118030025020075000b070b680300a2000961400e004100b01c8558100090260303502d13104044c058000d80603080070071900700d400d001c01c62900c000307010420410014032a40d1540c404803004d510510032071b40000d241e449802d100240d20032031350132104254000302c17404115603401c5010075915649002400d2a0091009203000010b250601070140c200c0500f40700d20509012140101754901030300d030045070403150307000b0400c0022420175 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 297118696 1250 297117446 297117461
    0xe090703140309041407230f070c15020a1502030703020c1c020c0a061d0a0e070201060915080a150b030102040902121302010f0c08090d0602070b07080705040302040203060d1a0109 79
    0x484061700e6071411040080000030189502a543c415150310030040300c01c4441990210803040c40203a0340c8501c00d29040300000d4281c03040b80350b600e44a0804040e118004a50800d403142c01034149040b00801c002030300003d40c0010990014554240070907102c1030801c02c07400ba0746070a102c40446e1003503544d4a010f1310381059900c1d0700d132250000c0d010a01a055203c50b0b40c118540803250315813a44048100018030440c0b541d000300c2c142400c403004014010303905400040440341400800c1000300b8400c071003a0780285d2180a001803550000744074000045501c10340e02031401170076070001351464064001a003a644181e21a0080720f401203070140c0b5055420059580161840c54a412000345541c0040c207004400544002032000c1c0803002028040104111103250000400340c0c02c4c65003c0c2c0c80c04200030740001c902541c0600c0b451000a034480c1c052075695000e02c90f161142401c051445e400c2002941c00200482c0d000180440b84200007001900310400c2e03040490241c603055030518900314129240c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 297119946 1250 297118696 297118721
    0x1140d0c170907051c020d39051e031b0f0306070c02060c01090b0f070f021b0d060f06061e030209060711040b0907080a0606180e09070314030904 64
    0x20900841e000b001550740221202610440454802c04040a1030a510008069000944541c01c40c04015043c0c3c100e280e4240a41140c05501032082c1740c1070586107108041c0c808040450909200c00d00d00121030309000000c14003040d480300381070400300f800d001c3c0040c91120002c0c0f5440d62613245192150740340b01422802c0d402172009203045100240544c1d800207000c0e01580c0b00080c000715180081d0825019079402501e4041c1e1810f2500000d020f10b001198481c0018229100106116102240040e010502c19065004000d1283d08104205160610449415a440201c2e0701106090301a8800600c01c0b501c81c2d10102c110062414022011035002000b054410011b644499940744c0170780310340303581180740e240356010000c02050042c8040b910352a031140785101040440750b448042180320344a0400709028241d501d072026114500e5201c1d18800341a1482d400380140d0100b114000c1c0d11070090030803a42c05583d40d0310389a0880401d602500016000069401024109401540c808028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 297121196 1250 297119946 297119987
    0x10c020307080d02160f2004021305130f1505040b060c0703170d0e1605040e0601050d0c05090408040e01050603040209060907030609110301230108040b0601140d0c 72
    0x39a8810b2070521400b00481c50340c0b580441c9826a56131507021150a003940b1000560906c612070818a644085003500780000001042c050001801c05000307680d820360340d5100a0360b0701400e004c100820719500300c0040d000950741e1303d02c03580710403030a006684408201122400040381050180020f84180503078081c0140b100700400d0020150018544040701d41260b902021352004040803490b620440d1891040e460405209241c110000315840c0f100890007031082c40700d180d4500922080c2e07004840541c6140d00424010089410300007071a59216102c0d140300001d49803140300094490200340c0d07040c4c82110001c2740601002d190340c002c55014180c00c850080c00c502c1c0990019a270a03500411503030080315004042503405003e0341150014000c4080c051201e140034030f1141c0d586420034400e00e12919141121030000102031003801ca160001a92100c07503613642c4d030f10b419505040c0034011504004401c01e408009010030b60103418041540d45000c2140c0c610b401c0000c2c2082c0500c102d0010080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 297122302 1106 297121196 297121207
    0x100c14030103031d04060605041a040f030506041502031501030902030c0604180609020f1926010305060906060307090f02091306061b020906040e0a020d050609010c0203 74
    0x10b240216131403440e00380d241008142c1783c9620a12000c103070700300014440d803158448021210748140d54910f00c0e1030390303660714615003a030340c1d61050f40d00741c10a00510081001c50006000010f04182e019401c6050440c0000c0000c15881d199078107042d610922942151401d0014101460004203030f1516165540a144082c2d0400441c007205240381c002d011603148030134401d8030b100c10600401c407410b00303100c20b540c011a98000e00070b00060110340c18541d450b81c85a400907104011102405030065451450014a0400d010f04920b656800c648100521920006618422105c0040001c1035414403810024001e220b2000041d030049803c40800b07111040607000f550403219140c0e515400c008540900010b45c9004507402036000042e940401e0407484c060301304000109995040e0b4089007920b500190710101340100803200b13504403030108540c0b40428850a00c00d20580c3c00554a480c = true := by decide +kernel

theorem cover : BRFrame.Cov 296942446 297122302 := by
  have h0 := BRFrame.cov_init 296942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296942446 ≤ n) (h2 : n < 297122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
