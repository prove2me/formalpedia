-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:38:03.388312+00:00
-- url     : https://prove2.me/submissions/d15140c8-71f7-4353-8739-6788f3b9a132

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 72302160 ≤ n < 72482016 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 72303410 1250 72302160 72302177
    0x2090a020903011d07031406040519080d0204030809040506010e1e060c0d08010e070c05070b031806040302030d1116082a070f0503010e062202090c090405060d1101050307050c01020c0a03 82
    0x87c218081019842690808082c1400c4034941103200d615070802041202d001d5820005102c05200610140011718014010381e511111028180030071510003170b1426040c8000107803550f010781e5a4422038041040802e6501000208003c0810190300404448403c940210030310707014102e0f80418564125402d0400300c1c0d181c6d45511030280c41001c082c81000d8156007001105110f8100407100440e040501d40100c19810300030356009030f04209050320201c0c010381001a040c4810300315801100d44405c080b804145c40c2130910010b08581448840d401410142d020900c466210f00000640b03410401000c0d4080d001c0d40881001c0d03032528903034000c00b0030f0050600400f19150905218030400580031600070309c041e40341c500d0402d03ca102e800c0d01c0342c10704a1002c54140c006880300400603010b40c07e075440e8103440e02c80040422003502d40080056020f10b0b00b5024010200700701790314041e9400d1003803c1c0141d0740d854501c800c0310244142500300b6015800020038514600d4001a80c0c403219000395151b00c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 72304660 1250 72303410 72303443
    0x4090809031203042105161b0f0e012312010e06010f06080f0c0f12060423040b07020304030c030b04140138090c0c0709060302090a020903011d0703 65
    0x616002c191006032042e26403002e010004101019905e50704c2100e410582c5c14444140c19407000000c80e082c0032140745071444d07103c00307107a20740c401d42c0809400e014130743c000d46a08000018000d814144501e104041448800b108818400d1064100340103024220b146441d010034549800780108941161461080c0000016030544a0f0028070a903001540e5150312612800d0721700700f0740e04014028550188040007100c4101c01a070740108070301e010481c0420840d01d4494100400c540103007904c07182c040041c00c011b074141c0c0078011072a54170991100f08510341b40c840b00000c07803440c012500010410001070601009200d08206524420741c0310705410316548541503480f5003038034100d4012003c00545a02e10070321042820600411130022801c600032800001300001d1162901518912264007000032402c9000e14180070140290110040900002c2e14550104404c000f0091280034955070105401c0f40c103540a400c00305403041d509145003003c80040081d035480d112107110480e82500307160303039400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 72305910 1250 72304660 72304693
    0x80606010302090d0b060a0509010f05040506040e07060c030507050d12051305071502030c100203011d100e06130504080d0c0809030406080403140301080d080106031a0411090409080903 81
    0x43d070482d0b001e414000e65103110350ba9070501c090080e01c810b41c091440785005c621b41d00e801600500174000320b900c9440841c50202800201d42015211500075803c00c818070701440b400107042c604443c1946411581d503010381c10100d4045c040c0040040c250302403410917008040d4000740001d02d03112100300030040c54680c1e07045000350b0035586a0003805074010020800202d00c60544032482460180180da1900c00c2c20410b041c18001500141d0301c0d4181e010005220b0520100303909102c0301030420403240c40d81404000c00c0b01c10311491161940c0c0107983c100003003490b1a0300f00704034032040040d40140440d040c02d1a04802c40d0704140b6034640c9513440d21000e0399180d40324010050054500b80f000e14036040c00c04500f00c52140d402041a0300380160740c450040c4403102000118000c10400010340400c801c0303403000400244041c2c0c0403404050400c00030141e074032014860b81c046003000b2500020aa18080d500b4559406040d100c10350041c900a130410a01c0003020081c24500001c50603922100752904680 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 72307160 1250 72305910 72305917
    0x1c090210050711090618010807060f090803041505090909100513030c02060c010b030a030e01091505090112060801090303020306040c0305071413031e0606060905060904022a07080606010302 83
    0x50700c0e0100041601c500ca09054100c160170500c090580c14902020461514609400707a014200c0ba9112100c1000b030383d5406621042080d4061502d5801c6c0e0b032800314034075980c0c0241d00a0140c20301e00c803d1607604180c09502100c01084000d04040e0081c41c08408098a8a4000c141d00318820f0910b030014030078140c41c00812484640c161a8411000855028002c03181c100b580d04554030b669891400301c0a6404000d0201690320907500d112030f041014000420881c819880301044100e102c1010000320340003419074801600a01e800d85c40c3c5241180320030064109948040c00c194a00701c210350a160b07068000f14400c28040d1030a21038590030f070004900b102c0007101c0040020b02ca10341c002040065240080032100c036410007100c01d2648030780380c0e1440b007000c83c1800b130764980314a050141082410300408005107440d0501007120b925000c0410514801e50801c070b48503c0d40000e82100e016101d0990080c47d0725034510013801000c00d100195920420350164150f00c3c400c8c4400101c640d80b283c002c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 72308410 1250 72307160 72307163
    0x10e0f19060f02090a180b01092102040f1b090f032415060c0203160e01060c0311070807060206090111090411090d051b01020f06070806061c0902100507 67
    0x3005049101900c89100501e00616003018441c0c080100540710344d1070460000c003405d14107080c02c00d46c1001e0350082049030720010020341440f0a42104016a180e8000101c86041c06d0784c0c0c1c00704266080c0e1000600501e40302c58801c0e1100d1130b10000c0701034aa0041c2e80c0f890007507102d072108041c00e5100c001d07881c8401664031004200c0c08003540000502121402250f807441c840c0c180c0460380c2c0202c8200f40b100750240c0e811800c0060030440c200030552400f001404402404050381401042c1001c0c03182d465a034050142c241801481204102014450343d03100441038196425140200c1c0c031003030710b1078459010388141c0c00180320301400f00740d0301704042c410346c000d5105455030545401ca409c0140005809040100031903084180001055134550302001c4000c0741c401ca014140c80310303001065161114044049904540c446000d108030000300041060300565a8140f010165591000050345e520540302d07500940459a05010510718064000420442c821500f044040281010844460140c400e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 72309660 1250 72308410 72308443
    0x70515031f031406101203020604020402090f1507030908030307050313030309080d050405060901060308070b0406060302130e01050c0f09090709091d0705190e0903040512010e0f 78
    0x8254619541403905007448007900850720019900e4480c1d00ca04802c526628042d078102008010284c0c54040140c0060403039a40f5176510200d045d10025610900140b000780a981c0c0000d42040c030f503594071003645c03500d440140700c001c07440d030b83d100400001d0300000c2c41100401e005200115800c500030040d00d200390456a1f903582107035a50381513205480524074007030b01407603611b84403840402c2003040103009480a0000c041501e0510b071030070301d10f005801460b00b0352591602005200180144013140c10198202045a869456500740b0320000c12095100950000f4036810030b0050b9102504084040303403810008001d140d603080d61101440c8219100440c000400f041510b11600d080700c16035811203ea85400080320344c4402041c0d00312100d004040c2c1c240d220200141c00601c00030052074010340019980c000d00a101d000c6840050000c80c0521444e0248080015110701c40c10000e6400411000f050546000040280341d4020001c016801282e80202445800b10b0080022501501d0030f220301d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 72310910 1250 72309660 72309667
    0x190f090b1002060402150706060b030a0903110706020a1103030c0304060c1a061807140a050403060f0b150d0f0c120509070b0f090112020403061b080f0f0a0b040501060908070515 78
    0x900711b00350307603001c400d08961085d5a1800400c001c004217003d14480d0812442c000b401036060700b00601584410821001a43d200c10001d01c400350b400302c1e40303d00f0940c5c0808c2c50700c400845200068114020b441400d41b0f64400441c000030001c0d480444002c0d000d0050141c042005820318004050510865186821200182c805a90032020b081090752110b4a4500405528a8802c2000c150740c00a46140300040c000304090050184601c03070213090f415008404c00024070743c68027045006403403d1200b40d2244c0c011403401c1c0b5030f1415030440d124014800340c0420686e1804107001c0c0001c0d92000d11444594501000508c00d01c00010b0000103a03000130030b40501340044502ca604969004416060400c0384100c0d40c01844543c9001407c05103109000200c0c01c2c51010002054040060101200700110300041c0010b200052160542080100c0342403030341582c4030080032001c5c1035410a410342240c58000001009a80507982400740c03034540c01034441c5c0303d90782c008025086121014110000e4001c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 72312160 1250 72310910 72310939
    0x90612060b1603051303050d030608060609040201050c03040305060406061505180907020c0a090f18110d0f0f05070e01050312091c0f030215060406080c190f090b1002060402 76
    0x5102400e542440f03890024640381707901c250207400404a80c000c640703070740c4100c8010304400e4141c040d5034058580301c80202082d2600c5800a0620580680064188040010304e00c0c40c44d581802140d020b1600413044810500345480c00c48000c00c01d9128041078121103a42c51079a40b40709008490449210015030400c0d803a8034030812041e034030f01911890640c8a4608045510b84410300024000e104101c00050428030b0040070000340c41d10030301c0c00c4140b101e13003002c1c0000007440b00c003989801d82e805648000c007814080c03400b1112a03e00640c0909148480988002008000960301d801d4440d0703c2c0649038140d9a500c2451790720714480c0ea00703251508044c00550014180001040248182c03451106400050740d12203903e0101201415001078100e001c1c0c40d07840020501085401120584080080524040c0c01c0750f200e111440c019480f0342c50740d503881002d80d814080046c0107402403201da0700ca5a83c0c7c03890f91000602e0b40302c10381b50040b01107400c114411800814042c4c45160050100780c4c02c424107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 72313410 1250 72312160 72312187
    0x3010501021b0a080706030516030c1e120501120302010c02190605090304030212151320041b05070516050919020c01470d0503040305030a090612060b 66
    0x6040c81c483d080002d80d00c000406a408016000043c29540c03000201400c19505d004c078800340e540e000400740b6040030744200419034409074003c82e0701b401c0012040101d01d110401c65282c650040c01c20300090600300082483c0c0c1e0f1200b2803209051280c0c00800c07080c1114181681c440842c505184060342002c01c1d07010203c0d0032a04010703132141c07605090342d06e4507840354000b400601502a609a903035120100d24042c020160300610b030030546035496038050307903400d030381d940fa820001a601c0505500303d00b210310080e866030340050340390b01c003000c107540010341904400038225086810160781034030420144000c804001c8681030f0a50b04e010b480d28003140d446810b10b01d400d030540c41061845681c00c101441c030b9264207106800c41c0d544043d80514031391003030048811919204125020182200b01e0900f200318034000030b8106584d106817800f048909a03810500c6c110300a940c00a0316038000080d440c02ea060340f040400068601ca0307218004040c00120b03000c0f0464109000e1407a24146c20402004040030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 72314660 1250 72313410 72313453
    0x52101081209061e070212010209030d121805011b030902060703050c190803010609090c08011505040b0f040e011d01120809040f06090507020313030b0405120a0503040303110301050102 81
    0x1000c0c0840c1e241000704480040510000c4c0c4122458041c045040c034110b10f005040101e403522042c00960030801c080300002c0d12011b0140071401400520800341d280c0e44607940045802d889084454a894142c2c0c0c2002070107005500c4401441545041c200c1080724003a00c03544540e5038010300314030708061580d58186c40a600031003100607036220310a5101c0c2000d1001081c0c7c2c004522a412a684951409801078801d2486030000b01c2e030141050490156250b00c030706418111100b503580c1c000610400d00080c3c40c940305039000001029000960486000340000052044403220300d00b41d0704903071381c0d01802c0c421403905003801e4494220b104010013500e600d01c121280a68000d00c0d0b494541a16040040d0440700c04910b0510159100c04042085031030b248608c6a10080714001b07075141140c960f900300740807012030100400380980d0802181c10b109040018181e401200070503207544088804000d0301a40086900320300180c240061206c0f161204801d0301d040302c906030000c24090215480748c142c4d410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 72315910 1250 72314660 72314677
    0x306090c0f180102060a02041d070e03100b0a08150703020a050d06030f0203060106180302060c0f010213030506060d0c060e01030902100309020f030d1b030e0a03030521010812 77
    0x424440c490740008407100400803540103024214a20410800180c1440c0005240e09030003481408208003281c0404280c0c580d03048080c0d000e00540d40c440c1400e50b034504040911b0794262042c00f409140000e81540710500d880d1044619540d03840ea0f48190b150307600c0500755a00140c03640c2901203642180a60094450b11079681081418a10f0913100f420444488e80c1c404e54110110f1000103041d818280300d000c0c094426490040203034006c12200c01c60103262880001d0140e03000141c1d48408100920100220060303950007590b0b90244500b81c50803c4003240010f4580b40903420100351241340085000304829446030110200030324004066480c1480340d90003034141a2100d0f1141e0060b0364025400b1a801d90b02d860009404540e0b0041c40341580c244c500e1203000740e010322208442143c2191003494201c02d20242680c2020492070125030010b40a160f1a81081c3c0e101e10200401d6000f5010b0001ca180124400000300114015450710345801e114810716031f04083d04010358041c1c0c100044c2060f1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 72317160 1250 72315910 72315931
    0xd080703060503030f03070314040309050f040f11030103050f0c09060904050a02090108030319020418020313050f0105070e0102010b0d030e0a0b030112030e0603091504020d0218071b0503030609 85
    0xc5941c0c0b800f09045901034a092414080f00104100002c0e4061240c0503454941018441640c98503a4000c0d069101034003031580729a690303020510480c2d5503900401d09600c0310358020b0010401003c0c00c620035800a010407100b13405210110898503000040340740316001c0c010081e00407a2908414400901006402a01c150085202d03000c00b585a0004407802018500300071613481c905290b07a01c02c40180014062a0a030041100b0400500d4410480712585500000140c0d03d4680c030121100c84a9002d100070b09030f01072003803086803404041d0301c0a4880c480c81d0322184044000788004a00726480070710301e1640200c0d08850035000c24820741c0292600b11015010542d05911070001251682007680003c400000440c00e00081550100030307a803500c102510b115056003028100644c8481c2704003a40c5040c0d03e04100024150340c2d490722504a119006002814003198460108020090454844c0081880c1c040404110350113010300c03501d40c42c1c20001860468980f5020460028030240c0301a851 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 72318410 1250 72317160 72317171
    0xf150405060a0e060a0c030206070f0801090507020a0f03081b0c03030a0b030c0d061b0f02070605030705040306060303030506120c1c0809090108060a05010911030103030507050f03131a030601020d080703 89
    0x2d888410041c042000c5d0ba40359a010a6594640245807420041500701000b10250400b241c0b00c0e080364810341074034003481c80800d0f60f9845142c12850302024030700c00751411803400c90400070305420500b280d0040b40701030240310380c0100d40030301c1c2c0f91103110300482c00301164001c00000303421a415500c0a03000f101c0c004c041c1c6000603000300c005061039942210565005903500380d0740d068818082260065403100b4185643c5c07500f142030300a074685085108142c1409400000125160300c100c2c00c4801559011404010043d22401c0040c0145811504103001e00c40400d40610800b600042c220a078503402440c6010145c0750310302168039210307100000caa80800611a04060340e03070300d01c80355010b032149100503d50b500d1300c0070b00794056a206130b000840300c1d4a0010098120400c01e42180d0540b40c03d8108a42d40341810303d00140f50540095410308030380004207540c250540c6803070003101160b0307600c4030314101350121184001043c441907582a001d640b1040000c9245406400b4a6070700c050103050000340c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 72319660 1250 72318410 72318437
    0x6180905090a020603090d02010e0a08090909070506031603200316030603080c0a120305040f23010510080c12030702150c0304030303020d050112030e120c030a08090f150405060a 78
    0x8107170001d5404c514590880c01c20200b100f5824424242c420081c40010b08884141e81c5452a1600c00c0c440c3e0180600044000a1810242008500002c0a01a00403940d910704400014041a106e498000c00681010504030099040711900b0b04010f03504e03c00b00349941c80c0c3c08420f605802d007040071581410749501c000400301e403115001d003820724105005000517440a181104540040700740e2001494540400d010100316003141d54203180d40d0041008810040c01c000ca03210001a030008000d0310360814040001902003080d2250840d513210040b1842a01c0300c0f070820050f01c18070f01e00c1002c1c13a03006019410151400740c0301041c8440880011503c0c0c8640050443d085034030903042900401c0d00010000001176061041a0040144102c241c2c511645658001d103940c001201c4288680c2282d214210340d100d0501c250480240c005080300c0d0039082c28901032110360441101d892140410034008021400c002d604c2060143c0310861040c41c4c5820401001902c4d04400c4d0f031041017205a0b1603205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 72320910 1250 72319660 72319669
    0x711120d02090a0f0f120f0506070c0209070201060b0d02070809030607050a0905040204080c0d0c090c0e0901090c050703141e0706051501020307140a02091008010606180905090a02 79
    0x1496002002000d07a0b2069010107000c1203032115880400c589615940c1042a54131980d01c5105581c115950600504214280104a50b40c2c50b54046d105000384c01c280030013160030030700801c0c20034420ba40b00e0f0980d83d1b85a000f6070072030303000340708a10003103804001d041d5100031543e006040c900e10541000d818100b00348023291400d039045441401003070000031040441c5030084120002060200d40c25450a8140710005444025000355107000e00d8400000308100120008220054416110204021401d40f0001010510f01c80302160041402d4070020076105440c0c080c55400028a4803424604206540c088031101030540c05074031240f0301031003c0005081d400e00d08840c0c00c0c582a5940b03427a80d110307040401c12039501500c071001c0d001a000780005140d0f008019290f0003030300030280041707010340c03003181c3d90a140d4aa54004d41c09107004e0200100801034215090995903007600030051107840300010780d41c14502d44495812000c80003c2001841011780081c1d0348444400180d079640c100c02e0380400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 72322160 1250 72320910 72320917
    0xf0106080d08010515070605070c060c020102040e09010606080408030403020708010609060602010f060e01062604030503040302280204020f1303120e012c010c0b0f040605010b0909071112 82
    0x9800c90307005500041d049542c40602580503040444d2840300066480c0c51391401d40c420303100b0042440362150700050029014404101240d9006241400b40b039400a000170700035441401440b85101e10100032405e1850148a500240e030103589070841141c9481d201d440f45900b00900c110210711510070f01160306003081c041c0000038010443c010407900e051175401fa0950380030a03014a011480d02d01c04014101681c1c840a04541a60801c00e420304410b200015800d50202d80b030382a080340f90b0060104243d8080c0c000c520450103a420f5a40070303400004020648041c0e0028082d000180e540302401629096000b00030b0641c0d542000f601c0c10007414003c400c0c4a00e00d41c016a54040c00018581d0902d400c90715032141e604e800d00c0c00468454800c4d1900311aa60031100600301c242800c034403079540c0d0340100100b203612174012031300c03003554a403e840b200b10f0444110340450b0f4075030078a0000120140c0360820f88804810003071101c440c0e0f03515540101c0d001c8500e4140000648207a4407144190f004c1380c03004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 72323410 1250 72322160 72322169
    0xf0b1309020d12030c080c130e0c041211090906090304090b0f04182904080703020c030712060c0c1a040c050a0605070606080c0a090506040609050c0a1403070e040e0f0106 75
    0x8504545c0d00c4d1806040c5000050201c01403081c04c00810190000c03084071007040d12407e005c80c600c1600c03403031442422405190014160141c2505405050042c90004441c414208595404003656100c83c40b5448150a603080e003004c0c2e00c00e00043c800e035201c40e040750f8070001022f42201c80c600003100010b001d0303940700900b88609504523104c810912182c00b08039a5003c83e02c0b000f031103ea842e4011600c40d01140107001078212a40801c05c0003c0620900640d01c2c5950020700720703402c4580320200e140c071461684104450940c80c0c104a40c48040c0260380400c80203402c00d1111203a5007440c071f230310318200b40020f01c00ca8201080100100b900d9071844481009000c2e02d695083d1542d4040c5080d1301241c1141d004040c456110744000700240d5102141c84095604007003000c41c1503110306000c18003402d0190081f5003164106001c00144401000103440258026640e0f00440a000d607000c00d011707c0240d81d2100000c1171080071246605241d00901c508074069801c0700c03a05550052954210340e500c0c1c20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 72324660 1250 72323410 72323417
    0x20613020d1e0b0c041a03130615080709050c090909010905010e03092827020f1801090f0b160b27071203030b0607140102030601030f0b1309020d12 65
    0x40b000a004414100360340c481001410185424104000d003000c0042c0105205604c2d00c0c00000660782c12003688445105551019003030040c5143c00300008609592030090350118454003400091200050188074010011000324524141c1440f003808140790004110300050340d2a000d1160000b031091060707034102144003000e542c540c00c03004100000d062400100e4180c0c405072440101240980d10b090350102c44403404040281c21224804001605181c040c0f0072900c0d101103107202410006000800199135045441d50320060000019500722040e4011000c1022143c5014000012142c0040c80701841018140c40450185d5031200c0400c0c0302201c200c448009800f0345c0580041c0d0604401400700c03250340151440d07505001c0100f10107804800080d0405032903038079443c032070b071140b404407511550003210b035440c0e14056a9006010b90300a0b195140041e00d00600080040d01c1c502c50318801f5103008001098103c4800b101038083c4c204488141da02c0040c110b5640001a4030860b42c1400b0f01003901d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 72325910 1250 72324660 72324713
    0x30c0a0506011707031505041e08071703070f030c050c011a0306010b040602061323010e0c040e03070b0417040f060305070509010206040b07050d0f1b03060501020613020d 75
    0x35010f0401c000b08842d504190300807081400050f8110201d04100d080d090400100c0ba034403810000d403e07403202c007000c02079450440490b40907c03040b8401441281d000707901024600050301320104882c4002c03218040024088181e500340244640c10000c1c2c0129a460442d0130a070320348980c00e00311000f6440d00071820104901c14034060034248819401412131030583c900707040ca440e030042c0d00c0383c1000301070310384132080341c2407460400802441060364080013503020b50214654a070402d00034000204803410912910111b0000d038907050140c601001c000c003000d035041403201e0b0717a001d030750700c1001d00b0481e0f00c200700c03e003401c0e0480102800351000b031600c10040c07400f00746001e401400700c0f5800740201d001c010381003141c0310090340c00244240c1c001d948032080305074a5980010494040c0294410340c040c4a0a18101d00d03001940f50700840c2c0300618440350643c0241a40a06604480b414030800740942c02030300000309012702e8400442074860000d00000c082188559455001c1412000170f2281c0c0190b03035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 72327160 1250 72325910 72325919
    0x904060f0609060302310e010f050a09060b0312040e0c0904020c07030606050303040b030606030a0b0603090c0a1509061107150809010518030f07170a11060a0c051209030c0a050601 79
    0x950702500c6020f1b8514891240d451103007009511002c8880380c424251030f20000c840b507020942c01241400602c803003c100c281811600360024000d05002070355000e09201d0302101d0b42c503010a0078100d14145020302c0c0d26251400c580d551007150010209041c0500031702406620344c4072400185640346044001e00b0209085103481e41c100e40701600300782c1c0640c0c402d000a000706003500b400c4a4200c8030454699450b503903600744070009000c0c18210150000e102006114002100254500912104680d00101030751941044c0100c500c409100c040003903a074460412469000c1d0405540105c2d005050750491034450341700491140324418180e0018ac030b0001000070510703083c0300e5180c1040802400302d80c000703055000165240121448440f4001000914008000d188020002d2401520380b00fa522840300c01405460356526000740c042600406d800a0180c44103445400100b4182e034950701d0400c1481c0c9141404000020540b001901c41080503d000314410031201c481d06118500504496052 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 72328410 1250 72327160 72327169
    0x403030906080c070f080705070603021908041a0403170106021e0606010e09130b01031115030f0f040c0e27070503060a0c090302061204110d0308060904060f0609060302 74
    0xe903100004012551080c031007460040000c40d000950014071200302c0540398280008a0f22554600405510a26100003801501500605442468890240c3c024945c5103025a0003890480300100740003000d25921503524005c842994201e4040c0c83e0a8000112f004065850102d0a8100c90702503032010a101021002c0c46070300188028025001d080e8034288480080c001c92103029485100c0d64100d400031350200c040c100d0b4500943d411800800391560359040800840090400c500e01540d10f4850b0040f03218400000c5030301410325a242461150b071013200341c1c05000009041204c00141078030000541c07044411081d809000c0702000e07552032485040460001f10032904074441d558101620401050354007194a59114541c110041a07401c1d46000c01c440c0107d031034100035485880801c004040c1701c0c000c91a40c1c400c0307104100b142d00b40d58141c1c0c02c1105411030b102004001428481c00100c0e5410300104043d00140f11f00400b141040581d06401c0c00e90786181c0001050503034952040007540b50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 72329660 1250 72328410 72328427
    0xb090105040912110f070906080c0f091303021906050601030e12040603180f0503040f0e011a0a0e03060115080a06140108040f06230a060506030a0b06041208040303 72
    0x2001c03202040b142e00e0a944410a600104a04a050001c8007158050240c0188610b102e031044000c151225a516019440300070a41e9005014151141050810302800e0403819180384c00c4005050803015501c10725035641a0180c842c4c100e0460180100c1010100c3c20240448001d81c4a01c50204140c42c2060006040b641400c422000302c1e844441c00035100d4021100312419140c10303240210b18240f003030081d8070104440d0f14000b01401500c01310b050070f105002c0058001c0d202c00381d80603140c0c942c0e242502810f100c020300448101c8a061660318800b0340481e0020060b091460425405000c240b00c0000e0900a090f40440e0030710081b00640ca10003030744803500c541e00c821520020400349061401e00c40c0c00040700100c4d1410310458501280a02959a00f4480050f60142c0b082c00b40c89a050400080c685c200300003052180c1020010501208890050b00241e40000e80603508541c4c0d03042d03401020b04141e40c00c0c0c6810003030800c008600ba812881952400500440043e50780d031f4034600d8000d000d40c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 72330910 1250 72329660 72329669
    0x405030d0c120f1d01030b0307080601060f0e0307051210050115030e01020309100903110a060c0e0609030c06090607050303010308040e090613120915030506011209020901030602030901020f0307030b0901 89
    0x143d09912030101390030070314081d9400031016088030f5420240300180c005000440942e981441640c3d80010240b000007076182c140c8900c0c0d034440c1c0d031015a075003090381d03800c80b26140d0316450741100209010900305a244800d512848204464481e01c00c950000304071075003a000051040c480c174903141142e942600130b208224103210021450351811800090b1070380d95800e05c4501960300d807602a8141482000090340c5d1500b4042511070004040c0380400050a90b290b101021486400581d0028a0101d007514049031010b8080c1c00c05154400402942c0e40c4601001d5a101100380300e500d004c18410000303140650311900c0181e5844e4140040c0e0096840000c4c40080381c0d5000404004408001c2100c0c900620307071100100320300310740c520000d55907030300b07150401c0840d080507254440c041a0305800c100d00804080c1c9600041404000400d001d03540240c0c00a90081c0032140100006100d503801150300800040c0018105403001e81c0900455100362105000a91116003050180c60006c1d0501d0040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 72332160 1250 72330910 72330917
    0x403020a05120f04090c140c060105010e0904020102061602010608030706050603071703070f02130507030c081006020c0609190303081801021e130302030f07090635030405030d0c12 79
    0x142c0d40c50294001032066028405c405a01d0745243c012030b5004116520000681d40051921a113920703800b0383c1c2e142c6003480b03254000360025030010341c030f4206000707814069a01a80a89400e80ea040540c038039080c442800300003190b5030340b18005800b92007440900707105032084e000404d0600b850002c151411100b0340009002188444400c81e180300004101ca0318260700403907610070300c440c034000204a44444801031040c14140fa08020185505500403030b031b601c805849500058480300c000105001490003401d0259015071085d84c810314051016100034900100043c4074040740c1c8850146082c866803089000c5203000c3c0070f208000113070800948444150310b000314144803051143ca2014100106a003405c01c0002030080000320202c10791741c0296030007508030f0f42c3c0280c1860880b6500d0500d44500690f651034010046031120701d10300d00b280f01c1070b81000a84030b14600014480c0400c01c4516100318644800c010004860300c06001701c00d24036a054032281c10380c405c01c0c00d02040054400d418a404c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 72333410 1250 72332160 72332167
    0xc030e0d021f0b0a0902090108090f07090b060f0c010b0a12120804080705150a0b0a0510200d0e040e03070c09230103060b01020d08070807080417030403020a0512 71
    0x80c5540090300c000301480c03040e800c0310029080200e0070b00410321140302ca07401042102d00070a00c0c07030407500180020007017aa50f101d0595501404181c859075254000129608400010032690034140c01c041c0641c20003c0c1035030300d44078071019400c0440c3d02400c83c16080740d46449081c0703094170b80708410400a00c44541550300b9800d52ba905d24a890100806020a104c42880441d09110000c0c00760341e004ca07407000454054000541500d0407035070084070b002401d103090042807107081c2004118281200c0c405440c2210560342c816084e10704e4588402c0000101b01c800700c1c0510748035800c01441151000e00e49844030504111000d010030340300b00740101d0440f82c6c810810000011004003956048400b03607000000c1c0424010202011b038802141440c246548890012050050560154411403026022160f00982004050301e450400300c403500080b40388031001604940c05091003d40c007a2003504c6202c030251401c0c20b101c4054106071380a50050b032042181000304201003082040306010300515505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 72334660 1250 72333410 72333433
    0x4050607050f0d0206010e0a050a060803070f060b1c0b04020102190b15040203011809020103110c030301170706170601230901080a02130b13090204030f0b0a0b06030c130302030d02010c030e 83
    0x1040c60303000e040c48c40015030351000244201e08030f40c805d0002e00700c15001d41c0da445085040024000c0400d45080d14014a071242006141c03400740c1c01951200d8204103800f00c480000e49440c404400001c1003039040d4010380c060340d00d0b48000094000403042c800d416080241c181304594404190307919410701d008a2040005010221001040305480301c004000071801298610040f07000d4450000c626461443c04a010846030001201440c16100624841c7c1c403200465208243c0ea12090310545002c00ca2100d00f4500c0611100410303540032006041007001298400d4490035080c2c0003100c60500d60304040b802c4152580e0094074190849156032046d4141a03400a0705004510503200d00050404001000b180394a002c114030401889040405c544032952400c250780302c4c4040c08402c0356006100e0300040c1c00c194051142040704140034101c0c509550b162158075040d5808401e8240320003000310400801039400f085161541a15039002040e40c0801c0000501522113a061303111040c1c1103248003a8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 72335910 1250 72334660 72334679
    0x50f18010e0a20121f06360303051b07060c03020f0c010e06070501060e0705070510050903030711100c0201022101150f11010501061d0904020901030605060604050607050f0d020601 79
    0x204122190f0600340059103561820300d48a0814200f8200d0f10340d098000001c100340c01c000840400400340c030a90000c0d80180310440d4500d91522903c2182ca415001f09101191081c4060705584c040010070300c4265050440040c82c20404e940900c001550074440d10003015030500007440858010001461260040d20000e8074505031580c0c05da008507008607104081c80070035008000240038820104515081c03c15000f8005d074085001a1024442c0c0100d1034103460303483c45501e00c0b80a07608091411900ca03e80121032051008910860078460382d003095211110a210707165100030940c000685d1240b10341c1c0381e00381006c182814100e61a610800400010750401c1e01c0001c01342c4a031400f014503203142c2038241d80024480940c0880c640c80e1400110300280c001c0404061075070700e90340c4104140845000c200002c0b0381158000d401c100000010000100795030819070300000c00030120307030034140c40d8404101d0940101c1000d0720264440716061041c0703001840301c6d000f01d10b418805802e0f00e43c10107907941d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 72337160 1250 72335910 72335917
    0xf0b0901030602030a1415101d0603041406191a0102030d050c041a030405070b0306010e0f03030d0c0503040c05030304060c080903011104120506060102030310050f18010e0a20 77
    0x14040030f030000006111420580d0221aa0074078640a10340740b030504c000304581210a4a819a0140311905400480540280c185291680000b0704240d0b110f4940d005000441d0006002140c0c038000c0c40a0f615001081882418131901400b003e2100307142500720854182c940c1c40c000d0580720605840c8440c081d9030302004442c180e0004480108160715000013000340351103558403050900408115880042c100040154090745c005c40c11180c51036210f1014107040d20007980c0329804280d43c07903040710b614180007a214140d0300000341034034141000d6a0300d1200740e40d400c518550005000004000401c0320882038580544015401541031505082d130140c000034582030094400180801d04821594003504996921400a031000303840b01c0c0d403a00c00701c030495400c0c681103805000d10000103005502c00000e07248101050001401303410702c0c00040c020840701101800e41c211512200c04400f1035010701c0d105000388005228020249002c1702180d0484646006e43c0440d1241e80c000e1544c0c140300e0303400340c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 72338410 1250 72337160 72337163
    0x6010212040b0d0b1f2102030115080405010912050a031506020c130915020a11060f06060a020c04060f030c090b0a030b090322090b09040f080c03040b0f04090f0b090103 74
    0xa800e0132080010b111030769a05441035504401000d030401c0154081c502c041055900340010802455030485001680800d01a5400c01c1c90081785804a09102e16401030300103000d00b00005200c1191740b03900641c490080848c1001c9400061940001c0798584584a5890011500d04805500301a80203449580c42c6158500c203000d48a80440900200c0d8801804a41c0c0b000e410400d08494044903406074016404801c0801c818032280303905440d000c00c46034482d1003c4018002c099480c42c0801c035440e004010079008511415484000c15181c3d442080080c03c0c52400790fa036494651b00d0500e421034015000f43c00e040d402cbc0442d0741d0807a03d17000c210500343e135030040c088011030380c5008107540740d80600581075503450321000c03022090104414400c01941c004030014400007080d1310920452005c1906d00810000c000310740200440d00483c0540800401082500e2500d591011a04010303000211000c052580008003001081d02c54400c031001d0a049003800d024803040640080e1400e28140300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 72339660 1250 72338410 72338437
    0x90b0109050405030408151509092806050f011502071202150d02070f020a08010c120b0102070803030a0509010f05060117040201180f0806010e1003200901060806010212040b 76
    0x10504100c01842175401a06150003162609281d0111803654960195020301e62150451151151410141c0b00c240c407480f4144024642e071000c2c0d00c14440841c2c44070840c511b400c000d441500740000d080b0300640e400341030148184e070050350410320780c00c01d0203901c0140e620956018980400c0300b4034140e807d1032186c54045810f04250900850f07982d0041c8180d2031071402041c40010403504000c0503000c080380c6140251003070300e000d60300c03090464200c48545c504000444c0c04c50715032000b84401d541010000300d1062050380c4840c2d960346134052460f041503030960000d43c0c4520400c280b81c14240301e8a82c046075a00e000384071a0401600290880f5901040101841d003a00300040540e400303010185106818400741c0c2482c165151802c105070780e01402000343c6030148100000d2564200ca00c0180140301c0318202e1151b0510310307a9155002600c69540310000c3e402140340071010303915800c08a000340700b5034480840c5494040700090811404101d00c11103008203200c240140b100440c00d84055050080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 72340910 1250 72339660 72339671
    0x11d1005060312090103060e01080d0306050102012d0b0924030d0e0d0501110d02070201110106060e19080303040602040302030c010807080a1109030a080a1d060d022214010e04090b0109 81
    0x100484c05007034160005103498023908000201c000380050946190f11080e9010010f07540c03194012801e880c6504885490300e80790245102da56600d0210303201d8050a175680c0080d850000c8008166141005c82d8058a009070121904000c503a44690b078100350303a0100e026080107800c400006e045031000402c1107000f00d507422030300d104000e000d41c40886222801d45446480702c512002d0324001c0d40c0202e40883c005856035603101c10308801405072005550007902c801410192410a11108903610080104182c52140002411709130a0004500442c003900d03025039114250700605251400c11480c40d0304104119041000305540400b43d142c02042c9094003003000700255400c582c0034003c0d0b491f0141e00d40154030070380042000304001801040419100c1ca0010403040101c0c02081c504034200580120040104120034107142d401443c40c040030402c1303004041c000301d0070080052016007100d0340311446c1840c01c00d810360f00608010104101141d050200f004e081da58500c4104041c4240d0010340c0d22003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 72342160 1250 72340910 72340927
    0x8040311041514100201050108030d24030308150306041109130206030115030501050111030f03060d08030a05040c050409081e0f0c070e0105010c030f0f030b03011d1005060312 77
    0x10b800a0052080700b01809030304a80f02c1c02091094103010030240d10801a03400a03542440c018002c5a04071200c1101031400d003070958484101912540c0c400c0c0e44d003149240c0001c6805140b82c5ca44038043d50213559001c03800e19101d04a0b5140c680600a80d44c8281c4c0900100400a000d1020500d9094026a00742c9507a07140d9803172010901c065284000e50020300840045420701c24070301c10101a543c1a5000c2c02180d07070f584010345461406079090f500c030b40c10030440c0b15118812000115088440130740303011200300780c940b5052566001510300500140d11201070205202034460408007808080f1000c008185030b0f5511041d5a2040703070405500d004281c40701074220b160034070541d1000040c02c40da8aa680c2180d914640e1141e60500a01c414141c00d0400410254410a00c020089605881d040301c0d18500074015548882051480e400301500c58220980c1e41c0c40078080c040e40071030b194010f480000400d02049007040300355a428217040c0d14180412040d0741c1e0010b6403078a00322080c1c880c140e65420f01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 72343410 1250 72342160 72342169
    0xf010c05190609020301060905010602030a0f0e0909010b030d02010209130b03010225061104050901090203090a050319080f06090f0a020c330c0316021c0302041a030408040311 77
    0x40803110400c89140810703a0600c02c99801c00e6004620840080012a4450702032100303e800a0040c40b0050340305200d4101c256001d000c008443c03241c5400d0804104001c0350000b18605001c94402e003442c0d4507a11004414241001284005803507400254180305a0b1008100380c0714036130000d003007000c0c2c075501d06d000980c0303080d411121300440c1c004c40600100e9000c0040c5142d1140307100700f1117080b881c02414410402c02c400542d81a114002d280120907460f0110b908042d4201901100c010701400e0320a07800110104001e100001d0301c941200c4144900c2c5001500c0003500800c01c5030b1303a40c01d01040000655541d418664407141d1900004490340783c1d01c1c4000000d0050b0340d401200f521403c141440e240c41d40954087c0b41e00d05200031040301100301040c4561524095a007100310103070903c04900c0a20f451000c01000c0c0c040c520445d03c481c41d00641d040420030300340203140040b940c0081c003842701c0c8080c62142100d500b1060041c500e076052039620344620b40300381d00c40540402807000c01b40310b8070b946 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 72344660 1250 72343410 72343423
    0x1030e010c0503091501051806010e0a03050106180204080703171c14060607030f14070204140105040b120a120905101106060d020319030309080301141c020f010c05 72
    0x45100070080c40c440d058018001d40e10594101c0340ea40300c0d21805055141036031044034140c0308042d160802060354070204100d228006080c090500400c0320030440181c0307445043c0b0000f5400340c00003250300c4d4540781301c0c031810301d105c040d41c1e044440c010402407040c1080052038200326603000d60303080008940310030090428010034200720b100e103045185140b03442410350882c2c210200c031100b5068460722100c0402c86180f0074041c0007400302d9813101030520301c0da0213803440b04412003548041a00e000314540c0040c044406107083c24a0316805a40144010308151140b05030044055031090f80c090f0240e0304042e5074980010f0700034210440d8402070b83d07400384500108401400060138000780c4d80c090881c0a00000b9450350b11490500c1004005219480c1605d4103032605030f006805001c0d0720300140b076810503d08116074282d00741038440345100005100540154004d0480e06c26a44048420741c0800130301c42c90a0b940036000805520030b203c052383d600490302d602c51809083c00c00d43c0e69840c5c50214100304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 72345910 1250 72344660 72344681
    0x1202031207060e072c060d02130b03100906050106080705070b06010e04020c0309240906310305070b0322020d0615030204060f06080105011407050105010b071202010b060d09020103 79
    0xa802e40018a400007042da0b41ca1341c44c1d28051390703201c0b88400c0003040e0716814104c86ca140d10070f0300044103a0241c140701e107140c00e4030701740308c1008550031141001180c42c8c800c0c05a5900c2c10942d4a5010a06010746c500c94603000d004245821190380c28030040c01401401740c06c01c040c0568101001280c400c0e8010070702303000840b078003600564071075150404207074898110350003203030084c0380880c06030301c0038081745000c1d007213401075082585c5c2003101c55021700c2501d4102c070540210f40c1403000090310703412001c1448200e48000c280960012503007949031003410b250503a48046c03c409414400d111080014100c0109514144051116258203d00010383c0e451980c20000c0c1220346024004598071890a503100c0a407030081d03a0500c48140d94003d5266103030f000f40f10301c0c0000b50000c00148210b43c0b01d40a40001c0d03044d03481d00740381044480d4841908440c000c0e8484c212000300001c9010030401540a144840d4605000070441c417140e900109619220304441d40c501d8039581c14401045a009510201c600c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 72347160 1250 72345910 72345913
    0xc1204030516020d0b0103110d0312020f040b04080a1a04030206061e0a0603050114030c030307060b0a031e060b01030b030d110f031303020a0f03030c030e04020c030c0c09011202031207060e 83
    0x1d04c1500f403180b8928001c0c0030035510341425400784d0781203080c81880340400070760660311455090141c14403400203400a00005110b198104400182410391801a0000d4540b44000c0c010403041854092030320080f00050115405501c410031020a4000c2070f15a800401520b071041c1105072132a110007104107840d682c0382d000041c0b08010400a906a203c141030346d0840352011900720b510010103a86080044040394150b02c2041800d001035801d40204462400c003800266030302d0384942d100c100308184213803c03000d9917494010b5441440f4150041e09982002030904100c0c80d01d030500400d484e1041c241c0c4d00001c0c00b424189004202c1002c200b10b031070f0881d0100035130761580d4000c0d0142e04603203084e200692040c00e400d500840e0340341070600035408072070b1b1503209c4446038030103603400392a4407151262440d801a4207102a5481d0b2805100600d660242c0001034252000d800701040456503040c1c00622101c10340782140c01c01a10001103041d4000b6941279540e4a030004d0740b6001020300340c1404c005505 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 72348410 1250 72347160 72347179
    0xa091e12060603150c020c01020c060d0b040b030d0e0102010515030307060c02250f0f1523030a050402090f0c041809050106060906020d0e060d0b0109090606170c120403051602 77
    0x600b07030340c5d200c21001c0803281e081e0f0740d24454500049075604e8900807010381c04a020404181d89481300da02020750900c000d0b101190002e64100001d00306240807101e03402054200c8140091581e080c0f2490b50b0114004003c40005449440401d40c1d078011460000c040351307541c1e074441103568020044a8080881c00311008642c580b10030f030044c80030101d8403400c8444c04c600390005c00c201c905600300b00181c5002e00d402c016101c601c4101100c421440030a140100c4017030000100c0710008940c019413080b502e10344045400c1c103091043c8650210b00138042040250088140841c0c00c0300801149c04603000e0f0900d000c2c0488107000b814005114042004109610300704000070510b030009a8a000c56446400347c48820490781010f0344c03d500425402907000c1402c00c1080507030312807580206480ea2041c0344c608005600c485000045484942103070380840d4040d048442b10181c14401d065002c460000030030701f0800078143c1c0c16004c6202500007070501c5808510491a8440090020b00c1c4070b400038404c2d88d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 72349660 1250 72348410 72348443
    0xe010c050a15020d050109140708100e010b040602061302150d1401030308060108090c0f06071506080708010e03190c080c030f13050d050c040e160801020a091e12060603 74
    0xd5105001302d41d462402c200c000183c2888500c42c04150342d00b48010031300765039a2003004031642c440007050241c980e10f6103500400d0a5944c400702901070001541c00f00c0da6242000c202a02c2c0c010010401880c812844030810010b84032030740300300e0020920700c030155210480d95262034090003c01b0031403041c0301e07601c400000c2132650280980f400b9074400c0e02c03400c2d0aa215480e4864491240000c02504141445114102c41c03d054000300020b5014144103005051001d40540654444e540a00882c0e8014003080c003c0740002c3c4120000c00302140021464100e100a41903804404080540300b8004088403600510481004692070400040b0541c1c4d581c059485052075603410180e0b50302003030032080d140403a003824040791300703010b582d0400018a1014080d0007004007510711810103e0040c051300300501848100080814080c06043c0e001603101c0c5004a0001c2c2440c52550000d08125000040f0340c4070b510045c0700c3c205c10346011030707410016665281032202c0606030700e91009000503a80082000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 72350910 1250 72349660 72349703
    0x2091201090204110711130e0607020105010f080d080a050402040204030203102c03180a05191508010e1506040e0c0309070609081e01060807230d030e010c050a 70
    0x100d041d40700700ea01300201e02c00e1400e51030340da000d4164014501d41e8802a00811132821100c140c001c0e003000d003030202d0480c01c0c0c1c3e0310a904000c000c0d180f00c0d0160391141d005024221480494101802c2c14000900208650303800003024104042c00050706160b6030001304003591250380495010b560082e0443d00f0811108542100801c1c150008405c2c01601c03284000381961250080341045034801d00660400c003040c030803444090214500180d20446900c4001510344030111099016409401003254262401007101c80840004030713a031082101903801402542006410150446041c4501240f81104c400108126100e0354202c46c0f005c206040c10804503442e0300c0b00442c07065078154141c0f11601d54445050350b004801d4055400d2a800100b101c800781200d540050304000a0f00d0300100d4081e503607000700c5040401caa041000c0038100c0d4541041d244640001d1101c40344804c0d10084240d040d1500c00a1036000300401843c100a61000504141b21082140e1410a900120203041c401300750349480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 72352160 1250 72350910 72350921
    0x20f2b1406040c09061505040303031e0501060504030317011d0705040305031b0c0103090b060f0f060a0507140d0f0807020102120a06080c191403030705010f0204140904050a080a0302091201 83
    0x107000c0f07506016000c9080329007506d40005855194071440d003030904568050f03001d4603506050686c10f805458000003030140c0d90080c14000c0c000f41e254155a2401c605000b4101c0c241d00005004165811004000f0003501071010b280d00081c04501d10002d468101003160340303100e00d40c030142440c4008100d420540040490240c9003c8607138040341c002d0045a0019425030b01c40c3c9101500b03d64a0000064060500040c07603036245c4801000ca054580841000581075005100c0100000b40b0102d00907040000c030241075070b0424003041c003d14290707039601801050b81c0002c3c11080304000081000c2004a8000d406903000c18548d40080b00c010f140c4400b40b030b0000c00451050804510684500c18551b00704a040482c1400c154103080c440a414080c0e04940f118814000c650035202c104080404100301b0704c5140390300005000090703034542c40e021202000800001c8403903c591020744c18480020000201210800d44c403c42141c1c440300b4088080d03000703010b40808203411015820300d07049445410b5111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 72353410 1250 72352160 72352169
    0x18010e060108090f1f060f03080702040b0d050c0103020a030207060507020f010c050f0301050f0102120f0712031a0405041e060f060f06091a0706090b04020f2b1406040c 74
    0x5515580e0340329000959034010041202d07070300e41c00c11008141c46a81821048070140b1141e178010800f40d0791100c01c1c50b550035141d4070540d15a40c1c00b158041c11441c15005100380c0c1d0500302c4512418038a1600c80c282c4522800c903d440c141580007034100c84060107074045c0c8000070707040742040080745080c6202035100d1507400c0c1c07406411b502c0c10342003103c020f00500680d00f0314030511400c14117507030810f418010b50030180b121107070640c81142240c43c2c015500c0c000801c0c65a41510042d61100d805140c45000e0724140000308040c10304080f0441000c82e070a40b00700d120060f044034040b641d6216420640b000301109810b00300305840c100c00043c00c0c0501504543c507080d43c010f408004007035545410150200d042c7c01007100103048131004000c69a100411141024031a04500e031920003070741c0e01c2200b110740700c030b4080315541c0e111410030040d46414016507110f503a09070b81003040d0103103c8654404201d00e4640f00c284016a034003c1e20280407000011158001903801101c64604041c28400040502d6114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 72354660 1250 72353410 72353417
    0x20d020a0314070215040501020415021c02061501030515040f09200604030b07020111280914040e030d0e0304170c0102280c03030e010e04151418010e0601 68
    0x1c0c8002c280315200c0c2c0799031141c641c0f40d000d032404860440e0007400e500006001a9507540d002c0c08080740344800442c0e8091017910540041c003041c50310340461880f400c180301d03665042d500036000304548010445010345281d0400d01e80007805070364000b4485004001c1c11007494000e45000e40c00c007103424aa40c40241500c2c01941c125828400358040e8042c448160020303641c20201c2480100002444008000e81200340da00011840702042e03050106650400302c0c0c0b80051040310702908171015502c20000701e4030603651074803003071860806101c074014610404045000f141c0c4e841148040d210144180d52481c2d07a5000d047c840c1c10002d11000c1c0d90f03500240a14424140d030b5a401c038403c200e000644840039281078010302031281a0020764010380e2061000c0707480c08030440e850720000030800d0b050300c000b85100345c80d400e02d235200d400001010b20a00703025070780c0a43d01e8507002d03260f40385001002804449817000c140580317103036000c0820303140750304210550350120070b820000c04d45d0251440050f20484082c0c1c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 72355910 1250 72354660 72354671
    0x20d03061a0a0f020a0f050a0605010b120601140c060f150d050d080a060b0d05090d052802070509011706070e0d1b120b06090a0e070b03040f06020d020a03 68
    0x40307800582040c10160004006810400642d5403805112500044001401a26044c100700d803148001c0c024140d001302c6290f0401c04109013081f49030b204031800342009540c0e06050400c0000d1042c0c80d103131f002d49403a05100004ca109101d07001214103e0703c10005c104180c1da00307410308c03000c0801046020f070b840c4c2049200c001c1d41c91805c1d0500580c2c00b0061078104000300041480c0030700a03030350f285010b0f0109101580360300e408159401c0000c020702c03148588ac00005000d280410b005030400014800c0007040000400c0084400c0301120310b00b0081c0c0c0c440d803202c1c0e00c440c1c541c102c0aa1074444a039110980200c0b564000007100519084006802280442600c1d80e07982ea0302001c8030001c0c2c40300c43d2a5406802c088016002c10b5040e20703030b12014081c6070300414410b51078113640ca8100d66007920440d10300300010100a0030b0306000306001c1d041103c142c03007400342c40c9000c2c0050351905820f020310020ba02000c07001406102200d440389141603009001155204030140c030343c0002c1c5d800350111802190814 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 72357160 1250 72355910 72355919
    0x3020a090b090406020306040213080c01020f07060903020103020c0102090d05070305010506181f08010e0c0102011b08040b0703110706050720030d0f020c0607020705100201020307080105041e050403020d0306 91
    0x9018912840200500ca10340c1982c0f26600e0000942001d01001d030095403e01020711009006034055019006e42c900410b10002407000080c0b91180800d1074015a420044040013015045200c01c4192642400c000d41c44810860038540207001e0690003039805a05070f4020014000c0104203c802d0341c3c02078009000f07955130801404035071b50700303009141110132256000610b180080c0d8156914140c4102d42400d490ba0344a0609003942d82c90302d12110980c0000346192403944c1c091041d03003103100641510302440d602c5407a0180110300300610240c126162540020b90705072003503000700d01250403440e5a039191009030420400508003120f04001140d03590044e1100300032340d10340304a4103d03100c1c4021440e2164003040c0001909a290701c840e520f940901501c04150f106010315403160a03d5401451b030136292508016491341003c08000c15a481042401142030f4441803c0d81500d82c159000f10786401c0c100201242501d800741d440301404e1400c03061204240d400b15442080901c0c50b40c06100343c039141c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 72358410 1250 72357160 72357179
    0xc0f06091a070602160f06020d140910020304020a0f0303020d0305060108040f110409021512061009060813060f0b040b0a0602032a1203010302090a0e0c0d0203010204150201050103020a 81
    0x50041c200711a020902c18400010140e80007009112802c204203024030b0102d50303d041001403e00c000706d840340d40105240b85040201d106a06005c404041002c0c2d280c10019205501d902e02c0f140c064912540020005003551030781c05114004100c1480d9000043d42d0b40d040081d1580300d0300700340c5d60010f030401e001710340158892401240a96000b0108920343c44259a51301c2d094002c241c0c0580c0c2290f01c481e40040540c2c0e80d1007200d8801c5c40301d0107180d075494900303000b103100000c00181400d00c1680e45010303071407141e0f40c04007006003035625500b0080800d031500c42410941a079200f00003010f0390300b0300321a488400d10035000f09140f594223a40074409200c01c00304100140c160303030041800581c811f206c8040c1000d8a0360500d000d40d40e101d02518400d10319207c000b0304050801c136020301c010000000400440c00d01b2400c44da40500ca107003080088480c80e400c0e6030b842c0c2040c2010b1504c100c0c0781c4032181095645c203504a5000b000c26403c0380120716544400a030103003c00744001d91051000320fa0002c1d45104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 72359660 1250 72358410 72358439
    0x30c070c0501080f07030f0b060a0905040c03060e0c1e0304110907091203050d020405030f030301030510110a0f110613050f0303010311010c03020c0d03092309070309030203070c0f0609 81
    0x141104d600c140343ea52208214007d0940400b02440c0c16224100e011164a9400081510720100e68070650000e0800c8140015038515012190030185000001c01140780f01d2084150400641604c4540e904100501000386284504204183c0c66002003800b04100a02c2151456600185c0b150040c0e0713070311004262040c00d00f038400d80c1e801c01c10014010300000d10800007400c440101e403100600309a2110040781c80c0680340c4807102a10b5000000600511104110454021004a9040c80b10364038070030442400e401114003003000e100f140e003c0054034a018005907029040948102c407094905052082ca001e16015420384050040521420302010b001c821641a03a80213100c128034042100011070300a402c032141501140142010910300303139a05640c212030369019603900030f6a6810440041c0c3c00c0319243c1c2004807410204484000c4a4450b40c2456500034100c2c180081c2d5107202c4d0a069055110765800240759480085010a600301901c075107000382c5140d0780e2540305054540301401d0513405c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72360910 1250 72359660 72359671
    0x120c0b07080f0c131206060303020601080705030d03020a020307060f0c0f0305060d0b0601110703060b0a170705040b040b0607060f110403050a0f0609140615010f05040e0a06050303030c070c050108 86
    0x42c00c403000030b440c24001c10040c0241c000b0901490842c641d503c045034505a0162821034000e41c484204105040e070402080303000d000d280c000b4103111454140040e594900a0034002e09050f00031a20440041c028000d50350300c150054014000c203401201c0e0700d0020410072000b81c0c0800d14100100c00300c01c1c031a22400e0f01c24400900223449140369501c2e1101010002407040d410010204000780c450442031003c08000c600c14100800c0202c9a001013080c5040039800c404031411201d8800c3c40040c80c0020380710121030040d60001244038031400404e015042050045401000000e4890100104d5034444c41144c2c110031020400d00c03800f11800c064501c500c0c44058410b40c81950b541c1d000ca52a10302c80701d8081e1040314000348a1151343e90f03166890600c8280c50700f4030f4004408100041301ca07000200e0880000b4a41503402c0001031102400b107000b00c0c025105c2c06407c07000012441e4000364414070250000400312516440d0441010041d50f00071001101d42d4114100006060f5004111150188 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72362160 1250 72360910 72360931
    0x318050f0d05040e011707120b04030f08090303150604050a062703020a0608090c100305040b101805060607020306010b0a0e03030f04140109170a061d06070507080403120c0b0708 78
    0x141d1802000c44a032900c1c440700014075005907000001c24140d10662344284611503541c0b00c2c0346151904010309039503001e040e04014400300204000e000c040100440c0d0b446040044d02481151354000440c0485c0a42e8006580261422101040c07040d040070903a8009407509002d410000c00000507c00711126505c0001d42002921030184007103802070046941c0612040115900b00d0a03410004690300c41e0400114003003659a030a020030300102c42e210652082c015111511106d241c0034442e04803a84031040c00f0451a030364804901242d540c202144e140c613400030105c0e151035844420410b21030f0300c00760f4a50041120448504503d050110642d10305500c40100c00c1d003442d01d400e411440000d81444414101324011034041740440301c440990f0341c40c0e003600004095190052922030308030b80b00743c0d4040000c0c402d0740140010518001454a0303010340d50b86030031620740a551501d40e039280a5900003c20f081c04c4000310407800f40d445034003444014080c0c58080e403191209801a03c021034161180342c8038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72363410 1250 72362160 72362189
    0x50109060b0f180604090603110405090304050d050c030607020c10030c050d020313150b011d0901050105090d0c060815061303030e0a03061103070228030309030318050f0d0504 77
    0x7911404090042e20307180000700112030803c42c000070440c0e44141c01c44146a07581d89000d00500070460790240110600f541e08100314200b024840c0d999000b140300f068815104a061030b0704000c028003d41050000c05001c41d8428100306d0406502c45101610090246805807188100b043c424096580d18800030703201d0518181d5880c4800c1c0280d0300c010700c46021840056080350026403042204100803280c1280080e12400d1035000400e00b107403446410200d06406194480c140d601d0383d244604548090a086683e0b648078404500d24049942c80039008040d80301000803203541244669204450f80c03900305040c400007508102283c0140141c4e0300c01c402003804248002809408404181c440041841040aa903a0384036410345400c085612807001c000302c00d2040c10b07501007160000000420340b0761139400080c00d807114070004030035902808041e2030b0a000000e060207070384214483c0e540001043c1c1800014105503623103d01013140754059200d4525000041445141581c003a1100880455203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72364660 1250 72363410 72363427
    0xb0301050606131a0702030a03020d0e01050f160218090610061d131d030909010801090209191b02030712080105010507020d1e0c09060b070f031101090b090f01050109060b 75
    0x9a03140c00495221030740c3d204001756000760703900700807000070725100340d001381a410940c0c000101031002d0310010318148201400511040c4444d081500c02c0701056001440500e411400010b859800036003286003203080d580280182c0304d4000c00d0651080c03070354540403841c8990303404003110948450b101c09030a004038101e009040e407400c0701d40b8a6208060340c0011440d0710800b370750f24803400d150390000c0b80355900c0040c21850350b0602c005514014030707107100200205209070300410034075400200510360008003040034080141d805d50100c0020030b404060b031810450481c0d0040e58941c00742c102694240745032081108403500c141c0708507058801c1a59041e041256550a01c00c01c54070340304003290300c256800310419201c0000c80c00c0c082800e000380003d5a505281c14800f4088130400d41180c00e02101c00c1015902080000021441c0c25515140204e280814045890300400045000070940556041400402c8800082c0b05c078803008100e0003001241d9880e4911000c4803070038460b00c04c0b40d40d402c2c4074500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72365910 1250 72364660 72364679
    0x607020c0a170c060a03060612330e0109051e1b07080705011503031403010303091206150305030a110f210f0c030a08010b1c0e010207060f0b030105060613 68
    0x290064419003111642c41080340040e0703907a000752070b03801c0006e995003c0401c0040da004004075540b0700e0031401002540021760100d195049444147c0c201900002803e19803031002c990110b004080c0100310200c1540c41d5810306001e41010344407802e1003c40340c008115141803000c40d55010b00b0382510742c100701030f40000c17a0210a8100d1002580c8a1000788040310104800380036900e4030040d040a1079150301d0031413802800061a9404803042c104c41400103100080d00018044103603003807941d07509161000c034600031020704100c00840c4010303489400c0c000200a4004060009201e058582130400041070465a584009008462520b0307480300300c0700390751014160504103141c0d110b00710441c50301c4000c7c1000307192030380264100c201580c4001440d180c10303a4003103204c2d40905801407400c2d140c0000841207101045002c18a502c8456850841008142c800d50407103107407503401442817150b000408103650041454080c2c150107542000001010362400308100c4481103c03150046142a0528800343c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72367160 1250 72365910 72365939
    0x306240a03050f0f0121020303070f02030f0607021b060d020c07090b0f130507020f07030507081b01020318040f090803180106081216170307090e01050303090f0406030602070c0303020607020c0a 85
    0x121b200e88822080303400360700d0900003002480e01404803c1c0642203c1d1060500d0f000c0c43c8540c0c01c1d22608143c092180740c0340e0210f03001c04c203803081458030348500300c100340024070621031106080c0140348001031007100140046040d900b03c0380100300401c01000084203008107036104d84070155001503e01c000c1404c41c1015032105400484610450340c4a41207010303094540304041d0819500e650240c00c080002007030800c52035001034461403c030030441d00020b0010b0744d280608a002034040c2c00348803e03060142c6903640710240c4042e10210901c5090100c0c204455640c0c8142d03801c01c20504920000300c140c400501600044543d200010828111424038502107500308500004d20302c103c022001c2e011614660500000e40d0b090036099a4900f0580005810012140d005080246030030004200b60b40e400b0040d160149000c0d105c442e00c846451000600a112581004004502c046814014440c04035a18016640b107034082351810b40310850160f03510032403c1000355200c08100000e0090465103102e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72368410 1250 72367160 72367199
    0x902040b0f0f0409021b0c03160b032e0303020f010207080a0c06140a0c0e01020c0907030f1b0e0307080a0b01150e10020102090301060f03020d06020306240a03050f0f01 74
    0x202d9041c2501c0d40b100809a910031003103292501c56148902107051800d00081c43c1c418021801068024400b11000d4000d1046100d2003242c80e4020000480742580c2c4190054001c941780c0302014031959013202800a20740901041d80140302c4c2c07444031001c0c0b84c1c0500c00c4602035078024513145d0501c10500c1f8111520912110201d4500341c0b81c0200141350500207100b103010700d480e000c0205074a55400d000820120010a8440c110741c407400750001030780c43d002c1c0304540042141c980403d5154041e0341080c0078090200d46c6020700300000b0000750320b15602c802c282e007007164102c2c15102600e59400210b03a881076003201c00740c103580c0180010880c0d8521101403d5000a5074205010388900800000341000100c041c904e000d42d400041c144043c1c9000e1080e00c0241049042e2041c00605580206492101d03c00d00106419400800f00d9000c3d600c061007004d4a9034100b005030220340b00c1d00e608420a0300400d0411001c2810030f808078000c498400351991003100d141c030004032984c1c642949101c0350503c1505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72369660 1250 72368410 72368437
    0xf1501090504020607080d061a160326010b090a270903031b03090618030206040f0303090209100305070609120b0406181b0518010905070e090a050a060902040b0f 71
    0x1807000981b4500c060900c49034182e5000130110300e488041a10421f00b129104030600042141600c0c010400189500494043c50325100181d8103141c0d040c00300400116850040e2421000000e000f0511002040039480540d01084425686c2e004c92000b126035001d41c045802070100d00120345050b50b408060664000d15000c64403501c4480003442145500c0c0a020000e92246034902c00e1051901131015004000c601e0b0000035240381c0c40007519900040d10062075850a05000024540320b41c00c18800c0c250001d1a600b202d04200035081c3d40302c1c00511080703405000d210320000313040b401801502c040b178254461640401140e41d80d0b203d6500e900400c02c882240da504982c2d501502c40529a0091030710410a4140940bc6060b03400c82c90203c43d408117105155880b242410b1000040255045540503040482c451f200e0000554528515002013038110343c4407010450000460340101c0c0c01840040c4e800c2164544544415050307106601400408440c20064034942d003040c0790081c21251048038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72370910 1250 72369660 72369667
    0xf08090a060204240810120212010e06070f020d0504051012020f0705010f050105060f0d111824220308130501180f0504020702010c02030d110f15010905040206 70
    0x156200e08070f0304142c000c07011048515029403240314980c4201032506020b428000c02c9441c0541e44200410f0940c040e109450303202c9a604011503c8241c079844508074014002e00032011405170003655920100d0b00c9030700060300301c10031402c440c0c000710710321411600644c0c8691406080009101641d41806540410408956921003440b0842d2020707101c0000c03100e01265450803281071603030075614035800c1005050315050042046030380b404110745c1d001c80800119030b110001c0700c10307440003800620b03134001c1046030000782c0c03084610030705440e003410b444200d64014502e198039002801d00380442c034075064010400c11200000185a08841800320b081320039661519441c0c2e52240d0090f04141c000300c040058908050055682044000380324560611031161064500003400b50061114460359004079400036401c01036903c20060300788501c1d001707030442da9440c101d141c00501c5141420189140d42c068101941030361100841c0241e240310b01c14504c81081c0e428030324850000c000160080364420b0f07082 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72372160 1250 72370910 72370913
    0x1090b0310060f0603060e060f010e01110102040b0915033105100615020307110f0a05091602060a0b060306040c180905150409050a03080a0b030a0f050c060304030f08090a 75
    0x2d004034006050710080041505180000150980e174103034011117121044102048083c0d100c3c0e4005d01170381d0000340f914242c040c0e518001a540070380050004800c1d03500014002ca0408503990080603100002e80d545146058000c0804d4564042510b11441c00040c1c43c035000c2891015041e141400040264000c013410740c01e80d034192401e01c030b400009440343d40303440d8100098030f602c80c4185041c0100340003440c80d000035540d400101d400403501c66485004101c8183c40c05d40c40d1103d0120240c840030b404080c080c10300a050210031021005c40340010322170940010300c010040d024010450001a00071411503c45030104400381005004150402000140030300350750b00300e004418004c4c10041c40c00605800d01520051208a545240a004505080070304002a800080311003241e501490045410303151240008040d110355408a0303814400d40701d120080c0007107000358003c0f4612580c1110360469003a800c0c4a001d0004036030240c0818421841c540d00035004004c0c0ca94003222400503550840c00c43e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72373410 1250 72372160 72372193
    0x30a03050a050f06030304032603040f050106080c0a12150908070314040501080f132001020105060409020307151b061b14041e080609010903090b0301080601090b03 72
    0x10145000080d224024450010854440e81e50000000c10031203071140703009404282c0d20710551100909087d40009442c0005807901040301d0900342c0c131440245d9034206400c04041208520005586552030040d0006851000103440c1072402006428020604d01d044100001380705807007015107440b194400005007484443c0300d013034107142c072440c4080d88814080c18001c01c0044180303845640d07148100414819a82c21582c003690080e41762021051698400e034105018603102c60005103e241240400d03544d01c14264a023504040c400e81c000c0060b59a8502040186c801c03925000c0c0d01a0040c0c4401d00c1100d00d9500000411003241c01c018401404e00300180c41d4041c90640c003540c54940c2c50402d594002c4800c5c0c215a410582032034409007a5903001c0c0c91126500c203c1c410b443c40698000c14416209a0b058122002825100c0a030b41c1039143c02015680604480c607422000242c41a00102e54202ca9200780ca060350340d104020300c10b81e0b007031140100c000c02204240c580e052054042c1c507445040e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72374660 1250 72373410 72373417
    0xa020c07080a080408061501050304080c0f1c020d0207050a03030804020d2001090b070b010e07090b04150e0105180d08072001080a0e0c0906190b0913020702061e0c03 73
    0x104203d0700d60350302e01d86403029081c40400740c10726015002d2011303c110183c1c1e2000c166904181c21103191f0b982c460b0608215031400b10391407032404142c022804102603980280d240034600710016000d840011030303403000803038a40e24603002c1c2c00e501c07080058050002c00d214020440e400361016040105160f090b0f12010241114908081c102040f04c86551b00c055901203044030040940507185410040382e992030302c010321750500443c0d69420500c07002410045c03081603048c006044408103965541e483e152184040601840c0d0440071414030480f001c50f55204030210b4800c1c2d48a90018041000c1d000d040010358203404d00144e03070382281404400c0109080d4101c0b41114a000003c806c2e81c82d071407400144c4080d200a003145c03070302880e004182121010104140035200382c11510b102580e0380700c1001a91105094090001000c1c40380b0000c181d81c40e14100500040400700c1d0301510200b4a031803800182d20410300025017054082c0310101440c0d00c1760f882c0084401c0c592201c00e0070071a105c1d4002e8039540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72375910 1250 72374660 72374663
    0x207080d09090504230c0103060605030103030e040504111c0605090307230c0a06030207020a170309010e0d060501081b1005040608040c091503170403050d050a05071a04050f060601080a020c07080a 86
    0x803c44a50006c05603014232070440181010305141d4155851618040c001180181d0b50900403a00d901c0041e003000000c102140e0b07182c0008103c2402441c1d02c01c10707680f07055224941212039601e04400f05940140010644071a141d2056003150380940b044664000d40755102e111060910400b1070340c0c8010ba580b80e035584081e180da41d81c0162204d00030300400c0b03031b060702d1903001004d10f800c885540c40007064088229644420700b0300300300d01031196000c040341400d5849c10700503141518040000c110303400f021a0701940d150381002c1d01c1c0800e942545c00c020590051038450700110300100810401c5601555400c1d500c18010030f800e84429070764032026404c3d9464a00390010081d4090390500c00c1000311040503418040c2208414105401e5948483daa1100812140d00740300c2c02050b1051260301c100101c40030140e1242a180806800d29140b44103010b040e102101c0600450301d00f03040700440090b0f103512548050b0343d40360781511003082c910001d40c8034101d44807541c041e43d000890401c8040120b884041e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72377160 1250 72375910 72375913
    0x521010312030506090405030d0b0105070204020d0204030302100e19050c04050906010f0803041409180a060903030507021504080c0106081605010e030a0f0b06060903100c0207080d0909050423 84
    0x3032a1410000303040ba0030042200d44150174442c140404610700000781c5c1e507202100303c0c000502481a0006841074029030500035401400055072002440060b00500110791090302101c04400602a4900903210241c00031203d580c4552a02a400c44081042110003800b6806480580070190042000d584044844c80c000303600140040003e90b48400074600107000040c003543c10142131482c20840da0070300180b406e11400014022483d2101030b480c1d02c500d443c5e00102182d4a001c0746150120281010110503001720303180c00f0008100c10300109200b043d0f0114a81100c65503a00c0390344103600d42c0c01c8601c01ea000d03503503140c8005c102d071502000f0002d0f007107245c040c80c500698503100004100c1660211800c0c0645c01103124580064200404551071a40c0300d00c403225a41d4842c00807412501444810f1907043c410444c1251543c02d103030740040502641642a50304040e00d452025940720010300a000004000e1070042007054165070002e0707009440703640c54401c40e00d4035400403058903250b95050f90b00c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72378410 1250 72377160 72377183
    0x11208030c0306040e0d031a100909020c190302011a090c030a0903050d020a090e160203030c0702040f0f020d05010512070e100509010e0108010f050106050a1d060a050714030403080a05210103 84
    0x240c0c00c840c6031232a401c4604441030303070019492100c000c11200d050b104503441c0540101301040f00010920148803916445079240031251003608009018040c01c04100c00c600c00c0c0e071354018986040521005201384400503240d0300d1502c03010000070052501030000c0d01080418030600d41412182d000510304880d2540e6202c031094201401c0c0c54140d40050503032903900c451985501085a00442500c1d07220a40e03844640c1c07224268004031700600b10020120545928003c01c446c141c20940e4040d2920001c001c60400c20b80e0b0300c40080c410310307025028940702c0540c8990820015204542e42e41544404031100040f083d5a80d800810480c110a0300130843e0312a40e240140542c070000d00c61088007400c844403c3c1300c2c0d5490010094414030800d40301004000c9110340802c00a01011080340b40f2100117044180d489880135802065608071100440c3e1403208481e5810b4583d10000944040d00d8011424a00d442e402203019141035005101940000280c1249050040e045217034080c0214007a8416810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72379660 1250 72378410 72378431
    0x2070f1d06030313051203090901060306170c0f04021c111b0304030b04020f040207170918100512150103030201090b060102010e0a03110106090501080d0206011208030c0306040e0d03 80
    0x140000000c0126000e90f00070b101101000900200b2441240c1040c0c81000ca82c10300d5410041c1180720300f000407078104829100016046502d42d22500440b00d01707102c101c91201412980c20b03110440031600c2c0307500c030164902101c10341c40c0c17550061484280801d00684402c3d06100e040055999001504040400215200148006040ca020501c5d0b0b5071902551406003903a4031a070407420701400182c01115508034241c02c81c0c4440d8103c900040d0440e03501d041c4e054242a03120303030550011261f40c0c010f20050065002d00c0451401d12402029072000111407103007010140410020100d10540da2441520a41e509107100f44000c54081e42c003030340c000b144804d0b59081c00c4888540c00741032030741160b25051b5249900500420b404040650600d40907001004181d001d0f8050b000c940c100400c034925100c00040c0d21480000d0301d000301d00c2a90255040c1c1d82c1d0303c040ad03108002d405840030f442c22404100180c5090300e440f00440d44440c0c002c000185582864840d1703840c1074507a41480c40400d5841020301c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72380910 1250 72379660 72379709
    0x1608070c12050303190f050916050607031407050703140d140301060509040533100905101101060e0a09020f0306010b0a0305150907080a0f0213050d0302070f 69
    0x10007a144000310640308004070b0b0307246562440001c1c02c0300c0c0f810301c612034501001d80198001c24424030341242c0901c03e03410080c10f29621313502c00e084c0e141c070041408400040c85090100039505290b805450b8540c0009194600038841c0e40445000c58641c050050084001887e42d195180d00341c14120040a04940000d00500410340e50464000c0041d41032004001681c1d2203000c2701c0e05e6440c1a40c012410340c4072000750354800d0714102e9900c0c0c80003052810b899038071640c03401b143c1407406040301c0703c036085440590f00341c41481c200c3c0174058010107013001641d88603014041d002d4203075216200002d007066403155130144405041d100820120b4035491540305514109042ca0710982c02100502819498000a04c03440c0c03094101b80381c245511203000484882e4414060f201c0c844014100070030502e4051001401680c1c11a82e40400b2807801c907030700480103480d1080c0e859a10003114040403042c100343c03c1001c202c00d0708000b02c0441c415200042541e044045d1520010034503440e01c0e801110708500f260 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72382160 1250 72380910 72380933
    0xc1e0305040e0a02040509040221070602030702010206060f03120705030d020a05032e06031509050c03070917060103030804140a06020c07080c090c07031205070f031113060f05160807 80
    0x5011035401808144125074480800d517030490390403903002240340000401c02101c86108004c4450ae40542640016034507004401888264401d90980302d1320f94414040100340d240301041550140d0286407004d548984403001050902c1c0114216400e04080ca02011305a034001c0304030b0400500d02000f07005180e03502030361400f01c01c94035107605203400fa070068140d0908003080c8a2a03040680750207080b10080c05105002000e4481b901d003d024a241c414203070b40c11503005032503a00000b50402000a24404000808503041040202402103a442c5460032213042801a1041c0d07400810f140f480b2a240308108007005a40303101d02000350300c5000c5899024141000342c1d000d0961500640405242a070300d01c032120750301010701440f050325a513190808642c450b00311011000e42e146002c083c050403a42019240c21f0200c2d035030780c040c0061510180a041039010b002004415131026000034013816018242c0c41024441031314005040122450416002c8044031000f903c882d100014640305204550540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72383410 1250 72382160 72382171
    0x6060908150f060a0911030612060103051c030b030d020604120516140a0f1103060c04060503040b04062c010509030a0507030305091905010e0c010206070207060c1e0305040e 76
    0x1400c05034000701800c05054100030610003501c00168001182c540d2410503e00140000e40c07001c2010300c4280002c001c040d0320540b047c51140603200071040c3c4608001804034180d980c4030010301001186000340148500d244a03a490031b041e04c44103010f001e80ca04211038006d04280364020401400e25007480005451400125810040c04000060610b071844030006000c55021209820041107102038a007441c841c000000d040103200081081482201098000c15a1084003902e1145c2c40301d00d0008101e201e07a115481c00320300103100080200d10030654080c1c0c0b15000714004240c1d643c02e100d003031031a500403450075a13148203600060351107000b00344211588200c0e21030086250040340440540903010f80031005007056102c10000d622250180018410320b00ca411084800034035600d072160103000c0380403480045118031622048039610000c0c50038041d0700d01da00681161414000100e413100c181309401c0c0c501d025001e03101520038446003940020035009650b6261228140400040764200107002e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72384660 1250 72383410 72383413
    0x90911120f19050106080607051902070e0604150305010501121509051f0b0406060f0e0103090b0a110910090e070e3708070f0b040b040603050702030c0706020106060908 74
    0x701e2258072000240340800b4855400c801900302800f45400b6000d00341c150046146030081078140124187c00c00041c00184800c50b504420310380150360220381c0c0d104d45100d409c01042d410f2002c108242856403180c02c0c64840c1180f52140031b9100d46405003555020b900807400780381d1840c032610901401c85814400c214040300140140142510760655448c2c000c40c3c9208802040c880340e2201e0519544450200b51000c2c0050240e40c1c1c1d1840040c0a0151480c001c0011401a0701104032030360bc41d1080700540c41c0c0c00640c80c1000d440708200c0703000410551500f503011010410031041c40c1e0782e604803031000b200c1440e45c07500440c0f414013030403041c070310380181c071040c240b000c55031108200d6900c00c05070801c0c1110303015070304410003040012900d40118100d0404022080c241010503089030118085043c0d4140ea20f40d40075075507603004000780a21880c03140a00344801070105000813482500107a820116510441e8100031400c0700799402c01d0480e030b11a40250303540c0d03142041a6038114038004c0041c0910030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72385910 1250 72384660 72384673
    0xb071704050303010b0c070f080610090b030601060f02031215030c030d0c06020304021c0b0103060b100c0206130b040e0f010e07020d0c02120106060203030609090705030307080a050409091112 84
    0x1a01c0940d0307404103009460700464041803018600340c0400c90344d8000c1c0410054100c401d695001031a480707100079942c000700145414004075521049008007041c032440900241020b0386000e204807040302e00741e40303800114082048181d1004001c082c145004e80304240100c8004100401054a001d90b1402e202d800703030308012900c52005420a5401c14820b4001c0b0015075699680e10010b040d1241210300300d0400c031880c088000c01d000b0b814900c0d5050340c2c0b150070304000b1107040008004001000c111424005881680428010b003071420240100400c0c5400c002d4030580ca4903081505508560003031040041c00c1000c101a4680301c1c580140100341907000d10b49541008c0310000c0d140d00d40e80020700d0902c03108400d102c08649603c40800102c5c01c0107002042416140c2400075100d07401500c0d4684075140c10800302d44d00500c04903103030f03045442c001c005500d4030380d00350740780702040d000a0b40301d80a005003480005441c017190b010b9011014031405910514204d030108200300c6c103061070310b00c081c0c507031201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72387160 1250 72385910 72385913
    0x3041502010b040b1008040f170a020f2503061104050901150e010804030912050c030609010c02070e010e040b07180f181a0d060b040e06010503070e0c030601030e15040b071704 77
    0x7241c1b40e0304160089041e4441c00b1a5040103054004641450b403000d00c000140e040700261f0119605491200b85d00c01e46011502074949919006c0b14074505090000a000c020400941c01b9800b2220440310024a40d0905e5601c10005035449400d0380214800814100c680342a030703074003a61079400000300b403c2290081c105a01d008005181e5800741c0c801c8801c121500d0014884c0400003007054050041c00c0300c005240205000d4061703d20001400058410303100017082c0c041b07040c449141615841860565243d841d510b0b032840103e0060101400c7c09028403420507040b02001005000e040c400040380d8030146070041554800c407000d004007041038a451007102205a40803038041c1d140c50b00320b03013400705c1040c1d0782895030047c0707190b000b2b203507001e8074051a8034019080400c609040743c0044041d503502582d5040d0a100d013131000c46008000300303020800106903600a074403a150a4404e00212210068900c4114401540c19101a40c8800c9804200808140d00c81e074000300718622090f103a886400c0c123 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72388410 1250 72387160 72387167
    0x1050412270b0d020d090c050a051e061b070605040608090c10030b040f09150605060a050304020103110403022e020304050306011802091c050c0406081e03041502010b040b10 76
    0x10301600702c2242e00060a02800749494042d1420124800400c01050b0700d01d1800840300001882540c0c02070b102e03076100040516101103401100b8210802102d2408000340030054254032140907550245c41d100308490315050100018005441d254507200da40d1030900d10f02070f04902c0c000b40b009a5552208400031000d4841400308911040c4500b40403c0c034003070210005018103074a000041c502c13494440c1000500008002581c0c00101e502c2d0104007807915a010300102c0e00c54801c1c07203000300310108042030065109078814690041c0900915042c19285e90015184d81c800100090350341a078440d0424111800c2000d081c1801e00e2030006610b414501000f294842e041403280e203104071806400030308a444550100c030f000000081c40c1005206440480d024510301030141512184a1040c9009190900d40308132401d40b904a0300405170440f00100182e17201140c5045600e40307008c10b000028030240c04810841844000d50004100032076141d0600003100c620101c031600c43c1ca42e50b0440c5103003540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72389660 1250 72388410 72388487
    0x60a0311040e0309031006090e030301030f08181503041716081c0c050c0d0e09040f060b03070906030b101a03040503040302060712180320030c0301050412 68
    0x5860109880c84802201c0f41140100c3c2480c03509070050400c01c2c2d104001580c00801074644880041040e000401d08581d660300007400020010701c24020302c10040782c000c4000e0400c410615002000030500c002c042640030001100000e200003011060100700010300903580303240840c0d0000142811206461204580d95250000e40703440390000300070b0100040302a00703113812455100c0922a40c284000c00034140d5001403070580c110b0254803064041d40d44616010781c0f640000900c2220182c03640d84603e81502d000540c1182e140741d030f801314032102c0e86050003060300500c00740c0400503d0501d5400d181e01c440340c00520318658500130560500c07c0d05c400e280400300000c039442507035440395600d00e085840c40c801e0b500040c6d0b0002c000300c0e81204210b040ca010742c0030300c40c00d5030701c0745075030300d5203d81d40e0408084c3d83c0402050302d080c0c260100522032026401000c0d4800c010111004200d05001203400c480d4165010b4a1010701e030b940a004940e000b482149004001c010414031110030007254807007014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72390910 1250 72389660 72389693
    0x1a01030e0109050304080a15050108030d020f0702121b01050f03220501020f1b01150501030203190f050603010b100905060d110c0604050f0a0308060613030c0815060a03 74
    0x5a64480e5040c00c1102580440c03200c580c0001181d075a42c3e200c00c20143d603502180d8003120f94220b401f90000c90344909018030790403600524000c41c10a1a00c90141c0d0180d00002082082e00000f840880056500e0384065a12400e10a0150000d842d01003200c4440c0241140c903d41032140410010000c504001d00b241d0380315901c00e52449420070171668241180702001d4014105d907001040001881c070b0a01d004011826903030543c0c2000000f21103c0a003640c41025456034840c07611041007159501075001594132403ca0782c80819140341580c0c00d4400c0701c1000b00440302d0f556944003002060304091241e81e0300e548088614002040e0f508500070700b54541406154080c0001241001e40000150000c880c0d28032500c1480e07885860078841590740320300c122030130341d15846498000f0500d09404204105044d406a691120700d6507041c06010040c0d100e0042090005043c103030000100b000c609042c005031001e50058440002070300342e112248103010307282502c294914202000000c611844001848 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72392160 1250 72390910 72390917
    0xb0603060d060902060a0201020a0306050a0b18040b04020a02010203060f010c05030324090103030e011403011401050702031212040b010f061b0f0605090307170f030403110f0d031b031a01 82
    0x1d0149800d4000e0088030354001d4002d000450821603254046d006040810310716a020030039965128200a11003c06104607040d285041084e04003801b400c26020300400701c0031b440404c00300401d4011804a920070040c0400507507000c003d200702841c01d040e01285032002407800e55030b02041901e826840784000f6003018100924905550003125156101d10311404004200141075a03603820003031700d038044030010b080c0000c121101c070f42c0c483e580f072000b070b00d0582d00361255441c6140c403040d00644a40d8880d03003040e6450312404861038001105a0020400c0402c80840c0111505143c50302001c40700060700328031560700300c4403018040d155120030b404170b480307032140030746583e409031400c100a0b4903a12540262550f4103280402030340100010042214620515030032000405030303255843c160003428808602e0030810030119000c03d1203203201d600051040c03000e48030000100030826142104010341400440d07114000301c50800324243c18096030b11340c2d509090080902600d00011003803031000443d07051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72393410 1250 72392160 72392179
    0x50604050a060813060617100504050c040c11010f0b01021b011d0402070f0308090f150414030c060a0606110a0308060112021605060411010c0c03080a12020307031407030b060306 78
    0x4d04028040000c6a0400401c00003241c40b00c1d441020580305a4420304075100d4a144403680d0b0741148203061003103410001600c00c2c000d00c2010080908800c41c07102d4204680c164400070380f813900b80b2a0003180d0652080006d41c00521000182c1880b1416204540c1c0a4031027082c3c400998001c0b0810042a4440352000510720b420702c0010b00034051540040d2281e4180c044940406410150700d81c085c103040000c0710003211202143c03640da0348070b018a03101c0c040010070100300022911500c04e0750f41075800095038144114880c14a20301038007110500da4443c0c8401041000e0b0750040502488510301e0000ba203010a10790720080c0c06881c014050a0410680341780f0034011000c2a41501c44c0342c205140440c01d2101c02d810700968a0740d0039275040c1c59442c00d0b8107411510390301821862480301c2e485420a22507511350385414a907a00059102c0303050180f8081d00c10031904492001714070407080c584001849030b501d421403a21000f002022542414600b841c1d5030351035981e120030b8a40c0314808035040c510b03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72394660 1250 72393410 72393421
    0x120f0a2001020d06030303060b04050f09042406060905010f05120402030c030d1817070909020112050f10090e030d1e0212150a0e0f04061e020a09050604050a0608 71
    0x540300056060100c4a52000c100455103440701e0304558200c0b4082c3d84c00380101620b4029900c0305110314440e90398050300229180c525403c1111020f58005e001f102131640d20307807800840c810b08600c403161103c40142d40c2c000500c200c58000d114003018007002c0ca003000d2003111500c0050300c41e2150500c81000f1100c50b40004045545c1080107030440c3c0809030944031310b0030502e1030290154288280c0c1544013102e40e003000c189642400210a490148031008005013417804117180000c1c054800305030b040040340a9001d4040017540501409251031990200741454842014801380041d41c001880300c80c24148601c4102c02d0000a845104121010004080141c841a144ac1c4180340001000c1c907800030880c1c0d0030b00310310711142e03901c01c0d0030700c41c1a11400b116510801001182c14056000601303841030218114906591846038014468a000155202d500130301001d0007038070b18990043e19400040c4443d015501c0a4160000c0205544407400c1c03604100c0015071110301c40c01858100120040040d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72395910 1250 72394660 72394697
    0x70f03110a021005040e0a020f03010e1003121d0d050606060f130b070309171203150d050c0406050a030f02010c1b03060204141c02060a0306030b09060108120f0a 71
    0x10740c0e5000b481c030300c00f900803050f0181454101d0304c15000040040400140300031228022210030040c00b0411502e180e007400341480f00d900b8082d0600c040c05c2086080440010b950b604011003495068a4140510060341c2620708450003400605008061026105000038400290180c010204072241901c45084107440585809044c0c50301c120114076500002c5c6030081c0078000e0140c40d019680f41c0300629110307000c0c9803008072451210b40341d540c004900e0820145408002d9a04104030320756403200c2640c402c00059140014603070588040d0050350401e001c618081c8922001840b082e01c203405038501d0340e100c000c90085c0300d0001a0500c440c08695070100b0110b80c50801400300c1541484244a03100c1c1003e10003508240180350540e2803401c0c0d4880740c3d00c1c000c100c04100c40d0900c1401074444416600340000782e0010030f4604180b40d00d6030004000251410b07074092142040300c0050400e903143c00c0007145130402808185510110410030550a55050301c2110b25020041c200156000700690008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72397160 1250 72395910 72395923
    0x402010f030e0a0b0106230901030b01031d01140108071206020702030c0901031a07050f09040e03160f06050703060302150a09030f0b04030e100203040303120b0405040c08070902070f0311 82
    0x1d211801010f1a00303081140407801c0c0c174107a40341c07643e070840e2031000c842051300401440c4801d880801c1c800d0003558025807003274000900d80741042c5004680b070900b00c0711034040d0400804401d01203035141c0d00946003007035101014a005200001c02003114900d00f24201c0501c000740c0c240074111903000226801903440410480c0c54518002c0d1006c2035942c0d40b130501010100d03003682482540e00c0c00101094600348100241c0d0205042c04140c545000d001c002000000c20240041c081c1d180024803000200d405545682000d203401201d0201100500c6d01d0064100c0e100107040000b454901007040c0050307220142c008104800300319001c2e6a1f03e0400c402624049040d50008222240c5812614200450820f03614040d034401d40700c0d03d00101d00c08040180094029023a00c005a006000402c042407081f091103040d6901e400000034001c0040c4081816107100300c0341520071b0404000b02300505441084500e004001e142c408500f0609240d984040b03080507540302030100204401c01042110042c0540e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72398410 1250 72397160 72397181
    0x905060906040510020a0312050f011814070f03060e0103080301030b0a090b13140705010203031902130f0501111603080c030903010504030e010e010503040f060c02030c030c03090a05180402010f03 86
    0x1090f2240f084201c00a60386c0001180490008020000006804450303025460203004a10031100070b0341e08001c820132400a02d411100002038030342e20003910b420034408070240184003542e80d03217103020b00c3e03c2c9014040c4c60392640b1140c000b202c1880100302191907007003038030b0660768841c4042400740c80304010900075010400c1d001d400300305420240310710142d00140b1064081e00c00c0ca00ca5422300645981c00d0b44400c1c403071040c240580c00400000b0b034021081901004680c00303c14005080c9418001030610000c8030b50040c0940c5440410103010f5036800081d21142d02c0300000082060280c4c2011030ba0350a5860b2000801412010034000d403844802e006880e80014050020482490725003001003441d4841104640840c8202c603540d90a54400c000301c030310440d08000b0009080e1502da482c4001403c0e48035003202180403c0c400c07400c6c0c0d010240003d200e103100c154000c5403909408420803010000c6540441e1084100707800c84c40210340d80145140d482038090a04101720342c0c55500c143c01414070241c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72399660 1250 72398410 72398419
    0xf09090d0f051c020d0f0218040b0307030c080304051206010b090d03030b180402120f03160c030b0103050105100b04080d030e01060b120411010f05071212020c060a0506060a09050609060405 83
    0x244030400d004a9130141110300d00c0d01c20700303010045450225030300301d11400002c4010922040342d040441c0c00d090308a800111809030845102940e680c030790050a000c40c0d000003a4a400010f000c024138a00b03213041c4075255032028040c2c505540340861500203031082141d41c80c01080f984522000b494020b520102900c0c401800c80200385030150b00c840e07822078003101c00301e118003007094810f005d0781400918105085140002146011042c615200019203060400c0b2144030b07540c01e02200281c80c607214103008622541c0042140d00703103a188040754440c00e412280c52004203010030000d809000840f14820f940c5c901b00000c410315a01281400b40000b600064240e100010703200800c0d1520103040c900c61801030441c411411681307401140c550b010075500100092003808003101203807850511062224950400f45400340d1628080b0003070b0703000a8081d114a0b00100d040140e03400381805195803007402261b0461a2903d164006842c41095010303641c00788202141e0100a81c548900b2074001d414001d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72400910 1250 72399660 72399697
    0xd03081b040e040606080303090709090501020c0106080f07051806091f0602030a0905060a050306063106020f0a05030f130504090503070c0b0f04210c0e01050f09090d0f05 75
    0xc02d400c4109800b564203c8450b460100001214100402601d000d010746c04090405545006508000b8124011007540c05541c20414110a40e809104038002040e194010b803041000c0c2c500001c0c00c02d601684542d01440d0081d0b06011000000101b65600010444060361326840d03180c8401c41240b00b1280722a6008180f280104100350000b0107401b800c0307450743d40c8456a03902c400521259026000309607003c900c090021a405150242c05082c8056140b0b990700600751055140a208070800c506117a100a0f0000c0103001ca00c1d8180000401c0304072041c01422080366503078499030303284109085080d842801050100c1c03205003101126008000050082c44030310182e061043c1c880c0c1c400341049a43c10300a940024500d03101c00c2c269484d08001c803040b00e041600d462034040800b6004000b07110700700310090300303280081c003412103081c003401e582e01507410f507981808288260b0700c401050503845410b4460401103e180c0c0080d014464100074600803100041c0b01c1d0080d50503018100c0900706158008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72402160 1250 72400910 72400919
    0x20703020f0f100c0504080c040c300b040e060402090a06080f03030906060a08100b010509041a04050703141506070f05010b01080109020906220b04030803010311010503060d03081b04 80
    0x203201c0c3d900031503c0030400c03510861403c1a5401e2203039100d2206282c0080b12a11224a4982c0c000144030040d800c220001d00044038410003111344030603d40092103d8400c2c03107080040d2a200e00551900180c80800032084916909075603408001c00003032040c00760a0014015460580254005007880c10444076005051540b403a166081101d2821300ea114038000030f40c0c54603082c0c4c0075408542801025110203031403c280603002d040c02030340c00d03070600204204a004944941c89410211000340d0300001c100f0441208100c1601c10140141c0201401d040b0304810410080d040c254000c4541242042c400c100080401c03042c0c02981005045d14040071070040c28400190040010703030200740d0b80c040d03940c2e0703d13810058200e015034a480e80d000300e014400c4011841c03001c500446150140c3e001074692541d21061114290700c1900122800d00010004004110008503504111202400c0150444c036144000c54080703402040c01030200880a00416404e4003c1c448a03140c85d010051899a00ca03182d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72403410 1250 72402160 72402163
    0x51b0a0806030607030c120203250320040f0b0d0b06120108070e070c080306150c0a020f0d0206030c030c07050a0f050c030703120311160b1b0c10020703020f0f 70
    0x440780d89010340103507800951064803c0c0720707a419070407564850962101c0814079620082d0401401c40d0250031306070070440c458409101081200003d241c1d808210382040000c4c1503480d1104001d2a01295028801405001384101c42c82c2d064940d60f900b01c0d80c43d00703110728140d40a44480c045594100310001140007c10000e0109941a1148101210700b540e940f40f040c00000f04e0122000c074002110503440c0b0000552040085800000092071070b5049403240d605c0040030b50000700c0c0e803480c0c0d900c0301000c0343c1141080003680151940880e28101d01c1c0e402600442c2d00c51000030b10884c001b620000010b0744140582c2d050b12005600b1608466600e0201c0c0b805d01c511141c505015111807207407041e00401881c0004403c01502d41c09400c03194103d0031884254060100310803071078040c90003440200004010b2281162416000d079170805031600740a688005c12218070052141c6524080000c00e03503032030b000280c036004031a440200594850481c28201d0078140740b421480c2c40c0d80112480313030703400100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72404660 1250 72403410 72403427
    0x70204060f0509071d010804031806050307141905030916080102270112110c0a1101030605030a030206010608040305120a0b1c0203071208070b010b0309011503080d051b0a 75
    0x1d003070f00d1100d03007601c1e46401905c9500840f501c80852003240b441d24945944507002d095007080c801c0c1080c0d805a00090303007aa0030360304250040800a030b000b02c100000039510490441c10014030406062400b0030071005c2c4400d0a1503a200c40e82405400004180405030400000070000b5050080890311511601c40c03034081e6102100b110030385400c0f84401c1c0480f02c55118010220401611f591140d0b88003c1c0c1c03090080d1001e200620a0744c1814000f84810900c148034000c034040c424001c5100ca502801c0000d170032628141c0009010b54410360091000980006a40307054841c6410079076102e60b21403030105c940b44900c00501e200801da130810b2044801440d080140010001c942418a003d2640d08101046801990107540341d4090f4104101c421505440c208059001c0c5854070304c4c08a550300c51701c403692002c0e4020383c003d01c0000204003240000303109030001d04a5400054828900c2c54440e51014007512560107011381d40c40c0302088034440108008200303039014203035070703501d0310110b00002c2c0100d034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72405910 1250 72404660 72404669
    0x2003090d0206070306061205150d080d050c0301050d080d06031208040308010e060a03030309020f030f0d0806040207120e011e0e090903030702071a0405180612060c0f0f070204060f 79
    0xc80c0c500841c1d40c084c02401008155521603807901c1180c1c001224040152101420801d4404c010042201c040d8903801044030109004000f100d41d6104119107002c21588000c2180c4030141051005200c180c2d52282042c2c1d445400c6000f030768036007907607100440062003654401005000c4502e031b880704881c0c100e01d01910440c000c0d22004003d0780ea400c10f20760090b40403a4480d601c1040b00302c040c0002030080c1d00000001c1d00180c000f961000d18080800c0c90301030300080a08490344000041c40c01980d10103143d99204200303407015800c01a040d550001da001c0d401c2d1a03081440742c03010100d802a442140140503805000d801c0f00002000b95402416584460300d4241c051301803040081c0020100200301c0e4000d403175a9005007111450002404030782002510303000f141503801c00c400034032a036030310010700386040142c900c803802410800100181c60f404c0c0c815443e496081003042008900390301c015194036400c42d907401d6541c0c0340445550f0100d07119940b8025806860300d0300114050316018844030596 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72407160 1250 72405910 72405913
    0x30304201017100609150201021201080a0506090c030706110c10030501181104090203040f15020d0c020c0108010608060d0606080a03020708070e060607060609020c1f0608030d2003090d02 82
    0xd440f4180021402407181c0506004110210801c104806c62400800602800361000504054200840c2a401b040a9024510300ea0102020005010040c0040c1d42c0120311741c0c0091000d0003454003c079850b009184148005d10002d1044100200c506011410a400004040501030703003d081000c3c0051400b8021904441e19003100001c20150500c20b0481c440340b6003c000e0b081915010b00b00c03000c1d50001340200c0b480c10002801d2000201641005a83c8500c400700260300da402d0411140100c480d600c00103000c41d842407030038501590f040100a415600340b0314045074203130703250800305e40c18403000751300244510301e40316000406000101d0400b1142d4031aa09540096a0b03822401d60f40745807a020b00541d08190700c000c04c101d03242034030040040c248102c101090050b80c0e02e44503022a001070410081c50340044d20207240e0154003e400340214415000d08004d103a0800034015a20700034031070f00c20304032680e0f145101190350f6820750020050100a08060781c80c41d001c0d01d060f454060b9005081c016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72408410 1250 72407160 72407207
    0x10090b060105070321090f030305011d01150c0203010b06070311120703120902030a0206070302010504140706090b03100302100c03030c0201050f040201050901110706030b1801030201020303042010 86
    0x1070340c403030421210515099959038032041c004445000c000d5401112143c0044d03500d0030250000748841c001c541c5114002d8030001803035890a00d1451010203040800850a05400010300441d00306c10a0840c4c034420728039080507010028804240101840b4505030360025011a00604142d17100003414242c1c43c014041c1d52070a9007042e0300240e28001d01c44020007084500c0b070312090340300b5264080c1c1d500340c0c00103080b10104900303500410b40300c1d80110b0060b00181d44803070400040c8180e642040c490722040e00c00901c0301a02e00030004115250500680144000010210b440c80c5e0072004504041c40d001005907450404c90200a404a00b05410450100b410001101621401885507922481c58118910000d60b265401102d40d5403182c49030074103105d0f11180310240c0c0c031002c200ca00c0c05020507031000035020a50000b0020303100752501109900a248400500060741c1c04801c0e02e401031760200760360400c008000b002203500090301880d80c0c3c1081d0080ba401c0341550b80b04d44c040003034540d0000782649 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72409660 1250 72408410 72408421
    0x206130503012301170709020f091f050f070309050a0b120a0b010c020d02031c030c030f0e19080c030706020703080a0b090106050f0c01021b070b120a05040609020310090b 75
    0x2c80300280e86004000441000100003084200340101701460201094034421034403042a51704a0700300001001103110003298071022030030700e8200702402820400700c80100414441e0000c1c031a11038010241c1c84a00c0200395241018083c03c00f107005002c00500d82188191034600039985034000c603068203080c01c0c003180480c42c04006445808400740040c0d6500381d4074849a0203100d0f500d450380d030382280c05100d06500c03034500201307103002c41a40091030394000c184901c00c101c000341582d044841d1180064a40740d0311014180c80022400c40141d000741ca0501c0d081a42d08004015008900307502695000004841c02009003a500501c01d080c42a15500310540711110f40c0c80465030000c0e01c50350840d070703030400610005010b02c0190204820010346a0b03e0017134142d4585080e60000307650031612285102c00e01100b10790920500010b41100000ca038203210301c50300c1e0990134042c003506424409980d400480d00f07000c0d040d00003000d615006000c4680000b0b03686500c41c01400d00103401e071140d0200101085 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72410910 1250 72409660 72409691
    0x603011103090d030218041a090702010c1d01030213121a040203030912011b1e03050c0301090c09121b170d0809190b040302010b01030501030f0618020613050301 71
    0x9000e82c01400003004042140c01c8254001d50140c0c41c200c144d40302d8041407950030f035214041c2d002e07a0395600000b42e8400c1c500c0428428000030140280c400d590502c0304080466030b0004d41601c1a00781240c0c110046040000143d009120340070514100f01c03041c80340448c48540d04691030b100c1c548200d00c10400f090186105e01e070a01c6054a0095060300204140d00203032904001001e01c00324045c5c000180000096803da070300001004c0c5000205a035500d807a00f8a08005000300c00d181020308041c0030502d0183c8000041c0d10050092030342c1c890b81d03044c0000c0b4803803081032034601a00d0000e031500d0b035104190801c2d4031410442c100d82e030507042a8510200e001081d03001403040704a904001031410400d01e90b4183c3d11048001c10400a41c4100010410907640d15400103031503500130b69011040741458140242551001d4491905241c1000010400030704603211a4100310341006000551905c04125009094003160000c0d501c10004190101135a00c048242800c44008034003c1111001500010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72412160 1250 72410910 72410917
    0xc0602070f0b040b030103060b0f0a090e0c10020d0807230403120207050f120c0d0b0708010e060907030906020904111c0915020309030f070b0f0105011815090503100506030111 77
    0x2406118020b0004000265450b00081600140142085c4085a641002c01c0039400c0c41d51200c0304403a202c00c40c5020780dc1e010310607020744140030317501c01c006040c8280b4003940da04410707281101000940000141d0b01807240c14250208555403e50100e030f0800415035030103917003290205072001191004107136609800041c0101c11948050720142120594404101403d20194680c8046000384101e01d12284d860302c003103004080c82104444907600f0300e241c00504090050304140c0402010743c040c4002556840742e4650b0000d024600450544100c0c03078100d010380140d003102a0854109044d0244281402002e440100421051400500c011804103410f8916842d03014010741034508040e88d005403646c00641d40440c6401c00c41c1d20f040d03400151104264051030007a14400031007424086140c001e0042680100800d01e131091a00303000111000c40e404503441100941c580621400700c0142c020f112003401018010190b480b25135002c00c0500c05400b040325024480d520300f40188e103443d50018240c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72413410 1250 72412160 72412169
    0x2010203190b01050d05010801021b06070915030f140106032702040b060405090a02120f0103150c0306050315040501061703161a040524151c0c0602070f0b04 69
    0x100460070322110341402400d000703840314100b1604100920392070526000301070090a40d40c00041c0c0d034408004001000482c60030080e0880d8000d035042c011229803200c1100281c54030813100480100091506900030240f4024514506041094941940c80c640000d10304984854a0900c8040d40403140991401c00d6203011590344d4550f81d00507805401c0940c0220700449001d81103610f45134541c07000900c42c110845951003c00c0d00014003c824032311180742c0542200a120400e9100c1d41035540d4070048801070320264845d0b42e51030118020040c0302e500300e40c0007804050141d4010925405469070100004c45041d22550700340200080c1e003109030a907485044051001941c2044102d40380c030305103d40d482105464120680080300302c200c80203002a03008034403540c01002c00039002c0c410640071910580082042c07c01c0c1108100742842c11035040c952090044680414950304112521160280640090038034505001d001c01d1041e00043c054064408405a4080741555607280c1c1005200b81c0c0a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72414660 1250 72413410 72413431
    0x30809030c070605030606040e0907090b150406050d0902090939090711011d0c090f06040e0a0b040812011403070e07050712020c0109060302090907050703020a29010602010203 77
    0x108114891140005e59004040103042c1854996200540400d00d04140c460318400c2e00291010000c0b0b000d10310640c401e54074103592141104510f40b40e508002d00583c86203030248000010100302010440e801404d03481d50003011541d05040107038000d56140400c003240480c1c2c070a0401c1000d02042d08010810100d10340600c0e17112200d0a6006201d41080090000024000451001d80e1141c40c2802100002c040038101511300301d00690b0b01c64980080034404034094040101804044407044030f146070322203000e49000c074034080310007480d5107802c4c207080c3c02800c604031500501003008860360090060000c035400d03a0174141d0325030003881c0c050410309440550582c0b0440b03080011300d2100200c10b5111505007011810301c401c0d03850301c1803108441c20308a00140c1004d02d5071100c960f082800c1c0c2000c0c04440c5411070a20300980d021400208028094000b44000414000200b42c0308006031202d0503444060942040e03540c08410381030f40c1d40100b619680c03d940d01c001080251051090740c2c0300700300c0340c071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72415910 1250 72414660 72414673
    0x2070603152301020307050109030c0c090c20030c0304030c0305060106050c0604060f0905190516031a06040b060d0506031525050c0a1104050a06030807030302030604090c080604030809030c 83
    0x3000002c140300c0000340a41035000601504003c41c00030b01c24403a15034041d4446035440d902e0b51030141c18807101c540095401600d4150825000390340400000460303043d5045078812100000402403a60180c1c000c44562440700280c003004010fa41100003040302c1c4900111403e990702c03000180d445004554a1b4950340d80b0060000d0089000e54018907841920300c480050341d02c100c0d0f1505801c050140c0c0d07607100c0f503540300c0d5036000800c0020090039001038a030302142e10f2030500710780e500510032494412110341000c001c0701150680d0303100e038880e40000030001c1000d5596801c0380382c4080680000c4407041e120313000d03103252030b00045400f8501c0f5110300c0b6150540c0303d04040000c90b07104143c00c02c03001031042210500510089680402915007168002c02011004141a030300304400e64074000d104440c3e860070104e00700300140e00701c4140d030b40d1a545800e001da12541d500340450b0007000e420002810b90307001100005041c05001c541d850086000750b4030305150b5500c0d152403507079a2180003040c003516070041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72417160 1250 72415910 72415949
    0x151213020a0b03090606030c12070909080408030703020703200a0b070317090304090b0a03020619020109050718050f1005010302070305070c08010c020d09030804090509030903010504030207060315 86
    0x440401114030081c02003481640381e1031030500300c0c0c00c11241c118041e4000c90070702c029841c040108001701d5400302c03020ba02d5010200300c4142c8a40d114840c1910704e43c3c0740d81c034074070070820050180c90103005480c08490300c540660030029600c0da0f0910003500e0001d403a0204801c40d40006c0d01d9903001900260002c03486070b142928000895101c60400d43c2003120056040680b611030908240c0614055401140c941d420940000b0440e0780c8100400e00c40c83c1100ea01b080140c40382000c1c0c1311185850302d05a5100541c1c0117090f4003520b5180300c014a54042e44002007803c55501e10784842010021008011558980014200164050340d00c0c08450b07a8040003080346600c00e40080010500c6407601900303250640e038a400004840381c120001c1070351200e0110b084140e04000c4007107004124581006018a582c89080651245000b030039981c68845002580720401042124090000503008200300c2c51316060080d29013505014090000e41040c0f080c0f00c01d40444404141610070182d0403502807d02c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72418410 1250 72417160 72417181
    0x303050703020c030a0809040b0405090c10171303030b040203040c09020f2205100c0c0e18100e0601050a0303020c09180706050918090607080709150504051512 70
    0x8a50440c218468140d283d0b0f9039480a0040101c528420100c9903200d01a1008000a40341c10340c0d1030790701540c40e080070070014050008040410850564a00d6001000205d007186c030381001d200219580b13004081485042c107079100005030f12500a950400255490ba8100b2003a44000e40d00a8040c0d190340f08103004881d003650040003028a0814001c0c82c1050101c0b01ca20300000c00d00c685030810346611010407060924401284c404500e41c42c00040801e00c80d680d420901484e4010b80d140d00f00c281c400107801d40d071141e0180c80d103a000b000071900340344d682c150050060b007101d42002a281c00703440000a03890402815503c00d03039500d50060840c1c1a010000c0c000c0050008041c400c05602425280380036140038400700000d82200eaa80d242d80c0c0340c0710010302201640801040c7c004454107000c0000c0c0050200305203420406030301c0c00c0c1865403900c4034100c400c0c0060384c000e40711020305071014114071600f000040c000c0720380985009100403084034417010701d40100c240c0e80f8801540d41d00020300c450311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72419660 1250 72418410 72418417
    0x16080f070f030e0f0309040e0705061204030210050a02180a0614030a090f0f050d0c17090414010906080606030706090e0c040f030b01030201030506120c0103020a0314132001050301030305 82
    0x1e898000342c4410ba443c00300f0f1070003210300300d00310341e0350030004900c40581402e014554030144042300800c00b941c90403011444901c16042d05012400c402d10200d0b0800d40700f41700e00920001075420902050030b0012030a0001c0d402880922410010a0504089414410021030469180351a07000300203040c40f100400c240e10051614840580d114990300003c0c494011a0718400c0c0940e80105550744a032410038603026010083c00305100d0080e651382c00103042c02d140d0f8688580454506500e50380644017190180c1122a00c00d01d654071540004243c1e140154811005c4407141c0c006c40e581603e8034018141c80d180640610130001c2c00e40a02480480e43c10540207400800c5000c1c0c86180940d20840f0b81d01e11600c5801c101d40c4280100c00420654ac8d0500400f500000200c425a041110b816040d07503840e4044c0b2200790500d500800d100d20b486002c2d40c08407101c00703650003e08040e49461844000354403104102183d41c0001d81240880886008600c980501030603104c1e240b640e400c40e24155450780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72420910 1250 72419660 72419687
    0x30a030b04180c080709270201030b09160f050f16080408060408090a15080619030512040303020d0503010e04080f0c0f1b0d081b03070203120316080f07 67
    0x5442d9541c1c0031804034102e0304800d80ca401100c24082d00790800c0c040a0800e103165204036040d900340000d0074150100300b13240c2e10000c0761040503841c0d02c900b9031005074060300355034070311a610201680170071500e018030000c05030074900d050b80c0341c0c45010300d0f400095a181c000d1809070ba0168600740103201c441e452450740304034042d0242c03540c541400c1c0e48071805450000c0840d0100c444030008604030707003c0d080601d45500134010f10701911101700c2101e0001007948100900544c4140707800106012000700050503040956000310036140354298030317104100c0680c8075110440c0148035440c151200c86104100352411380d20408400784143d202c5840d00029500400503240c1c50300800c0151040c080f41c20030083c12400021006445040c000700c0000000f501101e210500403010422107200041c6000103c85541d039940178408000c40c01c40b10940d01e580183c040007901880340c2e0900c4130b1300e140c81c40003942c4240040381c1a1034071902e034034004031400181034581c4a00e01e401c040114020a00410320019202d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72422160 1250 72420910 72420919
    0x603040c0e1906320d12030605240706050705210405060c030f0a0c200f06060a080d03050408070204060308120a0603170c0f06070905031501050d1b0807061d0d020102030a030b 77
    0x80c1d8442e2a070311b003071500701311689021075900d4408002500b09081d0ba03400c030300c0c0b148503c0314140d14a43c0e400d40d4030b446a45401800b0716582c8000442040c0154240d40034030717400d00c034006214101c90848500454040e5010303102440340000140c41e42c00d80c00100c80c450094100c0d1040e0035240e041e80c0301e000d800508880b0f400d010b0301c0b0800c00008180181c0c2c010302d85401c440100f0001d0040013040f4200701c9c0103841c00b0300600407540f007842508800222909090064600002c1c02d43c0c82c4d00741000d160140b454020342c000d00f0040000244034030b940c064150006031003245c02c5640c9641180e20205c4044c1c1c40018284036491804072050114507000c0c0c0a810240e07401c1d00c409582c01b1a4060506004032420700100b00184030500c11030808015851a80700344d40042e0499504080001d80b00200424008005c00d2500d80e420b41001c0d2000542030041a840c000c0740c01c00c2c1c0e180e42010300b000441202c2c000748960014004c0d0704070329140303040b1104560181c016525286800808502420607042d525400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72423410 1250 72422160 72422179
    0x4200f040b120f090f03090d02060403020607032001090c0510030b040509010614062106030a0c08010b0f041404080d0b09010905040317150603040c0e190632 69
    0x201d0503020001d00600d150080004840c1c64000811a20403401400744c0c1600e50100764138603003400e0300004940c5514012103241e080c0c1c002503c0020514415504029002540030070761100b0990440707482040446520f20485640301510987c2d400c0300c0745048003900310b0b086000d08102a050401040000038104e181c003081c149624001b0806441041c2c2d0b070402d0f00da56582c4c0401008246e1610082a84030444030f20f49032140160107101d04505050b500e40c03490f80c605000ca0010395041000d1180b05511106101417503980d003010341c1c000d00c140c9002c14020200c240c03801c043c030324240c82501800400615001515100c0d900d441e80d203a01b1011424480319550b42400ca0070b0780e02c0018440c024010030b41e02107040e28291500408056a000020100040d03800034000d554a8480c100c00300040c080c0e519030749070303921400c0c06049926245c0c030110b811010798040c054814404400064641010380c410710002d035641c55224130140c045840342c40d0f2403004240e0101665032801c1010704121008150300351 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72424660 1250 72423410 72423419
    0xc24060504090506041b050f090703020903070305061b0304120c021201020412110a0b0418090b070210062301030915180b0106020604020105030c0a17190b04200f04 72
    0x80b200c00400c280c4050303024000700000c00c8a51030307036040741c2c110b50032281e20014641404140b0254224811611800c1c000c000030746900c2c0729605460b100803000381114041380d07890501d140c03103030415220030088100440b05e8016007241d8004480c0156480188220700030080c0d00110303440c3e03a048500b26401120311914415680090004d44003034884e004140f9000802c2d4a0000e1854202c01e20343c07401402d13401d808120101d40c0c082a00d04031006e00000d510000600c1c00300b000100b41600c0000c15500c410402c0c000080d500058051406407408070411a1640340c40c829205141c03c09559070803c010011001c005500c03a40003140c203141300f014481d5540400307850f904169840d080c1d07604030100d1069500020320044041c0c61340144401e00151a550030700390002004c51100400400303078070b0070000b660307100c1520401d420340c0c101c01c540d5502034071828810400f4a1120701e036142006180d0500c461690140307000c1c421b800070507207a4041b80407002c9000040c2445500000c0c00201101d50034000061f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72425910 1250 72424660 72424669
    0x309020a0311011707050406110d14070311030708040602010e0109020f010f12020a3507030207020f090c0a2a0f15090f0c08010b0901051912120f0c240605 68
    0x140903009545801f5190f90400c1c00c002c0040440c252112041d60000340c1d110034003900800442d204880015001d80d0301c6d0518141900c41ca665144201c03480c1c80009070703007402d0120f29030240c030543d07400b980240103200c01c2c4601117090340c40107440603501800c2d805000b0030540c0640c24500c10380845050425008041603009012a0001e041440100c1c82c0c00380e5248116000704070b401c80c51220b40208034590784512006900c4010004c0680081c507900003501c0044d96201408181020030052058070203107807680740e00c1e006170800c5000c40007040c02e0720284038480136010810b2000030917032503021818421584440c094150384a2065610340c000100d14a2484a223001d44111140100c40f42c581d065901e18291418014a0b0f00801042c0d240070050601a034401800504403a011550030145480b00b2500c0000c0421560244d0440340d01001d08004000740d114180c90154810340301c442034041203030026113016580d5640100740300c28903041000b401c0b0204841404040412000050268503400440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72427160 1250 72425910 72425957
    0x1020a080c071409010305030301120606030206030a0614030a11041814060615030f070e01020708010c0c21020604060e01150810060501030b010c0b0a0b0904080304060c0309020a031101 81
    0x3045500007100030300105900c400603404556041d10300c0c51390303903246450700c1d6160300042c02415400b0150711040c0d41032140580003640690380040c42d01d5900d06015540d64004d14107481255103d240091203440c1919000c2080760840d50421102038003036285074108001085130300a8002c0350020303d455500820b4101e015040018541c100a00c040d050420404c4026440c7c052050800174040040000c074070101070140750000307000e0030880700003220341c1c00603810803c041d08034210561810105900b11503022900d03000050107042a40c0710308481c04041c4100340ca81a50800141e8040e10201e00000c01680c82145160403040000440c0000413806a80c4030134039a00c02030165000b4200c00c0b49c4209107109140c010102400c08014201341d03c00080c241c0c0c464510081c15590f1018006105c0c00942d40004200c440020b1003d18185000d00c0d00c6d0070030b60400c0c0e86c107881503440c00707440e004607a009120b1900480c1d0024110045a49136540c0d4403426a1a0341d200d90411190000d041d80108580d040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72428410 1250 72427160 72427177
    0x10e0303040b0a050d0e011b1b02150a09030b1f050904030203090105070807020904110102010507030603112b0f1203020901140a03140a0203070e030703170a09150203212401020a08 79
    0xc03408a03c4c07200000401480c5035085050600d68581012001641e415601d40b5a4201180289454334103005041d50700314600d40c00a04448a15010000400d0211a0203070304900036002e142201501c03035051140b550001c0790010f0142c0d00401c04d401d103940c001d0002c0c10325580710385031413413030880c903603001c80c00300407080d501240c5d5800e4000170769003250f03028000d182c0c1c80441d502c0c0401000d403941e100c522001e0410b42000d400743c203510681422183e030020302e80250038030000748002004102c1c83c2c14242d203410000c0585034000005035040c80148680210344544005075079007104105108050607480e40101c2c00c03141815a00c050025141d8074070825648508841070740180c6918240b40b01600410280a0040c0320380c000c41d80900024030071880b5000c06100a07622240c581c400d201c0b0075a052503041d003000f521554004002d0868039400402402408040f0106a0908040c4030b0000d16280040c1c1d610f0389810f08002c84101c0d4007900042000122030144111801d44840d070701c03089540e6010142 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72429660 1250 72428410 72428441
    0xf06080106090b0309070303030c020309090c030703060609080a11010e100e03100b090a0c021e011e05070509090415090602030f0906100303110705120606010e0303040b0a050d0e01 79
    0x104101500001804020208202411302d14500440340ca03413182d07035a0000505041d911b01a01c00c0320303403081003524000c0002070001c0c9014100b003d0181c9050b0011604400001d0604902151080c03007080c180084071004c1c0020181045141c0e10785115107501c04400741049400c4084e10160b9540c481030f08440741c80c40e10740725595035512043c5418028010b035191072050030041031003000e44681c840b455010109080c002010400d8042c01c80c00c1682800402007a0221b1212040500c0d00644c41181c801740c0d60000710321145044100481501c0301101c25001103201881311090500380340c518564454402d8880907900c0d82c0341c003005001c40f0140c0c0c205568840d408420020f00351400000c03141c011810302e00034616860f101c406104048482d000040400103c810030340803040c2c003002004040c00c0020f10403c0c000740c00c1c0d90050343e00d070000c603160ba0014a4000d8110414203000c400c6030180d81440709003d25181640c1c5090350280c0c001910003201075600d00b0418800d200a2080002d214849170 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72430910 1250 72429660 72429677
    0x20d0212060a05041e05100902031905060901030b160e04060b04030b010503150103170f0d020d0b120319120c02010207050607170103030f0c050d020c0a0b12130c0f06 73
    0x42800700c5000160051402985084030414a01d181c004040545c91400700d00400c041e41c48a2070310550508540c440038065002205000c1c5e02e60444100110503486440f041003540e540508010590500b84800791406000d00d001c11040c080411101000020a06094030443c4180f400310301110fa082d8040769044071302180600070040d13094041c5005200890052080404104103e00820010b00c401460001e800d504041500c02c18400d4407604040c5400e40d50302c8081c00c103018400b943c48681c80c4e920541c503002585402d441c1410a04154602c000001c50800c00203002242c00000c28900306001d11102030505800c0380ea00c4d00400f0207503543c940c009a00c42210740307802c0d0715081c4060076410910082002c11820030705a540083d044a0705407810f000c1b410400903041d00d10400c1980040c0c4240201d4982424050b00001c9031010518142c40715412203542d1180b124190043c120350703492048940001c1040d82c411101c104c8101801408007030f0000707644500751048031b0f0045d030018000c82c0552 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72432160 1250 72430910 72430921
    0x80301080d110d111203130b0105032407020f03030901090c1502030702010c0303060b0c0105070801060201090f020f010e0303041401021b0913030e06070b01050319031e0201020d0212 80
    0x500c07111003450040c0c180500340d5640105401d40f01c602c00d0768510108084003c0c240f41020003080400984221050200d0b542d0420b03a04003610781d41c1600080d9a1040a4000043d103424001943d1406c1c2c0d10340214825281e207a00040c8030841e40207030040007144582002445414400c1c00154010030f1094000034500310781e0302d0100c404502030b90105860754202c54901d240c2940200803142800c0d424030f80708003c20010b00e801d070010b1510390025129002c010032081a61001503000d18015812501c034900c4d40c0e80e980a0480c00e0b6520f095008015040c8203200740c005060010004400c1c0c2c81c14180003442105110200c0d141d074009034820403446118002840792035805004404034980c190300c510b030008503c00c010500c5014064803810003001004040c10900d44503d1459401c80c0d00141441c0e138031000d5041514407000c080c00754911900030389a090761400200b50710341e116107038581c482010002d801c2e084941800d000c1120481555002c000c04a20083c0c40e1000b440f1401600f04040c502e400c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72433410 1250 72432160 72432163
    0x1205010b0108060a0605030405071a090103200f0706060b07031701050306042015041514030f0c160204020d06080d0201092f120606090a05010501080105010507081608030108 76
    0x40038035060501481c0c400f400a0382e103655008106442c21410015581d80302ca151240c9080b00c03170b5000e00503000741e101510144401910080c06049400d0383d0602071541035403415003d0740e061020440203240c2c200942d0300c0b10a0000e01801c44a809400002941c980d00e40300701050358408103003100046c0200140c28482550034400c0d5003d400150000e09980c68940d032042a0110314001c0c51182e421045003c038003e544070f00303401d2a24400c2c041c1d2252100e60301c44054890406072106000070405090044000a1112040c2c070b1140340342c50b000075590344805844600c2030380582440c4801102c0c1e0450900036846500081504501405001400516000d0300343d00f000d91600b1b03d04110790405040d040400d2107042240c80e00c0a145c003025103100d229068035084030011846c410b40000407040c134080c50440110325540706800aa07604031403580c4290491045400c02d00501d404140340c40010306c65544070300c001c4c0180f51312813640039243c040112001240f50031118000c4400020000061261620 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72434660 1250 72433410 72433421
    0x3110d030b01050306010302070f0f0b0a2f0f12090601140303030709090b030c03100c020105100608130201141303021e03060c0702210d030b06041203030e030c0304120501 75
    0x4891908008075484500001c00500c00544640d04141e00481c0340380134800300d600840401640701040f021303520003d00d003081000d20103c402464845c54071594090a00c203400000b00324030264003174050124111101c42e80b80750002c90801000d04001d1002030007502c070717072020341d805007020310001e024541c9000d505284119441d1201c0c0d029800a10920440603002600c4405458006801040d6442020080791811b0844421281d261140c1e800c80d1110008540c841c0d41140019402442140e80e4205500c102d61110b1045030b0004207200300040c0d44a0f850000d0703c0d5410310516090000c400c081011204d036401c083d011f945003120a5400b0001c6151400b6082c403c07041c0703110508501d0064000094481000400c4001540e01c0080d4a20441d07488030400220740e00454018590040e003980029900c0303600080100200c1d25103000c0300045d01c0d101c02654100d40041c200382c8221803c5950890140400181c5001144000c0c405d0316040788083c0017074005080722075000e070000e02e8581803607400d607203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72435910 1250 72434660 72434683
    0x230c0405040c140913110a03090c0b0408071815030302010c0f1809020d0b060c0703121d0103020d09061a0a0e100b03090c1507020301050a1a040f02070803040311 71
    0x4004644080f01c00454815141021001c65815114100700b0401002501c0307940c461680c500d0300010100c80068140d4068502640103002d4241034a03112a240c9005105038000c0e90020340c081101004180821190201900c1ca40f86010a001541980401b40a441604128007607515002d101201c0d60f4081c5e403001e1090000e1401c500b42043d40c03100c010212805001b400c0b0459000501d003402103209400c545d10440c00038010f40e0b51003414080346911490180000c4482201070120f5150007480f0386c207040f0b566450f8512800d200740c0008019002540406030060601307890300741902c00b1902a11031308049100307031100001e10f0b0748100f080080d046503a80200c0300301030100041c403548030315000700c520603a204240410398a45601070110b00c0c020b60213402c1580f0240d42e11281c46007105030000307000003501c01d40c000d01c100e4690880c40026200d02e05503100c4d040c210000754010318507280e0006d0301030b01701d20140140340100d240c40e10111a80221415404102d040c0a034911006040201e0000300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72437160 1250 72435910 72435917
    0x20c0901061409060f18010207090c05040504050415050c04050301060b0c0c01030203060a0906080a060506010c031e030e0f1615090306050406020f0a020a020901170a06230c0405040c 80
    0x19818204054041e040b00740390352030300010114a50419446070001c0341c2c0008505060b5a46854825061420800d038106c203460040c054942c000404d05658052000403c0d000c1d10790030b04083c00d02040c4001002c0042040d2441d02c00072854124042191040340d0003a40b2156410380d559041c00107160940388540d0105036956002c00c1851340000340428032412601091802594035202c00b00041c82c00c2d000e58010401c0a0701e000340000ba00c0e8800290038056511400d400d110555500300103489221818901501195000400303055101803e000d00d01455540c0c1000611040c0b0303101c0072880c6c117040c2e41142c0559844051041c5180318488854030040542c4804007a020b03200d20b00007450410395100c02001281c80d600401d013048400d0301540c15440000c004981c0702c419240009545003d401c80a9000301310120007c2427070350b007440003c01000d10720801405100d40958a00c00140a03200e0510b80800640007201d883c1c4051100c09402010143d50040c0c6441c10325003040111270810801c2d03000e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72438410 1250 72437160 72437179
    0x140f1b04050303190e0a080106031109011d0a180b01031104020415050c12030405060601030609020405211c05030108120a08040f03030605041104030b010801020f03040b1008030f040303020c 83
    0x180e640000031210b44e1111015000d24030140303107205542c4402c0303621103140d01002148012555010550200701180e024a60f1054051450428098101c00a0203010030b6004440000c80b82166031003002a0013402031140080c00b43e40700099003540c1082d4a0088807142d48100041042c0840b1188810001c01d080740d046161618101100ca590a01842800305010004c41c118002c03a6043c80b201489032120740c05a035983c9090714015480700400c07264180420310740fa9020400641510954040d03030409002e201c000810300c105869081e82c0c0701086211841110340c24400c0125491348210441c220340c40e8a500d035410408007038200780035030005d660907034014003425801c2940010500e400c44d8105001c01d07245401130404401811803900030682240c00c052600d01014a00d0f030062046900501d155a2240d07255200d031030a0703214111015041c9041800403402054079440c440c2d0b041080d07070344852182981c5108642c11a045800702c5401c03114042000c000341601801880d048000858103104c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72439660 1250 72438410 72438419
    0x8070501030b03280c0810020901080a060503070603020f1e0703110a03020a1103030d0608030417060c030609060a0801050901020310061803080d0f0501030c1706040f080d140f1b04 79
    0x19124104004d0f808008004403000040c00100e80c03000f00039108460644682c1d14000b0521702c007035840010214000703515000000c03503010192040e0f02c00d480c1c0c0100034100b050b14112049020b5000b829005000c2c80b0704110807150103000c0140c41d00704056100200351103420504000e000040800429680ca411000c0014002039000c12001ca0440d0700000c00526013800748082450f60003071f076a813020740c60702d0040b0101d2405c01c00405002281c6505581c0d509224520703010f03e44401c425245600d0008092011a01c20700e00440803607072110001c1c0540440c282e0700e051b91801e480c0241c40040260354000248107081c00420704040243c003980c10074071122601302000a0386840584005081800085098a8100a02d4020744011080303030405004a5031a820501301440030761041e250b450b07800d00207001e00c0c40030100d2000d1040350084000203001040c0c0e1219403403035200000e0030b00c0c0d4650f06c5038090b0040544e1348465003d101000035410183c034000520480c2c4c410f902c1010301070750340705020400c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72440910 1250 72439660 72439693
    0xe1003151d06220c030f110907091701020408061305010b060403060507090b07080a0315090c11060a05061c0203031e030906180a0f1a04030c03080c0a0f03091b08070501030b03 77
    0x1401c0325401b14030321120124500b00040381584110466034000c01383d80038050401e60140c0e8030000c0c0c410001c1d203112000d06101d0181d080344114411851702c0d401020025400000901a481c0035500402c000701e8603c410400007440c55010342c20441c0c402d55100c00303024403030b6406228103029203c4001020301c2d11000340c999403064081c00c00a8030401d82c580c0d118a00c0b0410361402e81c0d00401c02c010b001e2014040d10103000d404c800441500d43d03024402c2000141a95016009a0b4054440541040203900c4881c8013002d0203881004183c0c0c043c40708010007901002e40c013006042e04100011007607202d0a001d090241403403000342880060020380d03121041d07480008111440c629500a15220030007005140420000b0140e044000d10141c1920030401415004045007440d81c0c4250760704c00c01c95840500301307026805903290510008400a82c0c4005c41030082d400050083c5c0a40920b03222006040410784e02d142541d0003c0b54150030100c4100a2035070140200c85684034118040c00c001e500d04107001c2d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72442160 1250 72440910 72440933
    0x602010c0f0e09060111010c0f031505090f0403141918060822021216080601081009030e031605040c050f0706020901051b160e1003151d0622 62
    0xc2e480392050801107403a50307000c0c26904042d6100040244200010341001401c20f0100040c0030780400e0400340c0c04d020202000b4a0360007520300c014103881d00358503080c1400d1003103400148100c091140250001034104072440181c201e000404103a428203200b81c4500602807025045801aa105041c50a008c040e07041080710340e103c0d000000904816401c16032a80044148640294201d201c10801c1e003854030b0046241c2c601c0c0c0d484a045035100c150740743c41c0b01da40c5100900c80c8100c2d5410540003000d03070503c26000540900e02a28040c3c03000300300200080e090004070717840600b0304000c0e040d0070041760505000b10004000c090900c40e04000101c00d00704a00c1c0b18454008055a60002740340c6181c3c4e004809130b4038181007400d04071805e09101c46049030350f640e048454000318480e041e000181d2510014429101c0c21000542d100716600c1e540d03032802d80c2e03452303070649003c01c2e9107070031611803420014000e81c0a022520f00041045081240220000d021a420482881c1022280c0303070b00419440402e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72443410 1250 72442160 72442187
    0x90c0e1014061309090303060e0c030a0b0d06140f1e010b13030c09060305010513050a0b0604060b0a020a110108131103010209040f05090d0509010c140a060e03040602010c0f 76
    0x1604440a9071000003000c41c4034040c465000d24610b0395001c0b855034100d0780400442d0b8800c2d10204005900c030403a40081c020b044031004035030101080001c0e5150516004143c2510b4041c084841801d142d9640605554000418062101c0704000b0403406048021002d42c000000c01e0003082e48130780c15500303590010014010300c07000801c002201c0d007001104c200c0d0072000f0b64200e009541c100380c490341c03802c005c0c0c4402d100944196003080040341d204d80308050401c0e4019481001492200b02d10342c0c0e06400d081c0000c2c03901e9400380c0d4814000907001c404000510760740c0c010b94003409180c8514500052000040c440c15810410f6540400600100c0303261105106504400300b003880c0040d2100090180c401d000300716800c1810725503203210064081d000640070711000002d95118080384a8212204c0c054030041c90300140c03a0740028400701e1005503c201d81035560078161380c039101068860070155101001a040640c1c00000c0400c1500d80c2881104c041408a00d0280143c1c5403500d402402c3c448078201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72444660 1250 72443410 72443429
    0x3130209060307030602030c0301030c06031a01030510090c0f0305090601051011030c0a03031e0504020f04020705010b04050408090a08030a050406030b0301150303030203010f0b03040c0e09031c090c0e10 89
    0x3258141c0c0d4104843c80003103601060a41d075a28001c40b61080680084c401164010481030380070076000d029004a014081c01d40403540c000f04513000044014100281800d41265980c1b4000300c0ca0340e03c2400b40b030303000c1c0c80c05403980601448214001812964000c051425030340018006004640d602c5011541040c2c6070720b030010400201207034807811032050000000d1907120f20000705080640580004100e0b032800e640402035401d0414001081e01c1e82250001d41c011001040361075640381070f60140144074010700000490309079000c0404c0484000380d409880604000c1034240c40c514099800002802400019500f4907400202c0600710f40282d000b00c0c414151074000d0110b042e1400d500403000003442e0841c2d1481540c0c0c80c00c015000f98401c2c01002e40d0090010720209040300500203c80c000c6500280c01c200e03151800090301e034010740144c801d98060004009034102f21842d0072618944011540c00012030100034500681290f4241e40030054521503113080006000c0711426000c2220307140d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72445910 1250 72444660 72444679
    0x40201030504020111010e0706080a020a09180f09080c01050105030d080408030411060a0909060906030312110909010b18181b04080304180f02090306011202040209040e010905010f02031302 83
    0x40143d50b2080c8185c0180c03219880c120b814a41c2410028800007190000d03100c0082070f85809a500c0b09a1044105c4403020034082e4100700070203420b8140b00510319805000029444e404040200e007502c3c60001c05132031550f03012075842001002841180c2c0103040880090507502c080ba100034000d81c4c001040079108a0005c0000307414050301100082152030001c04060b61081880c9024102d6090f900600c8051850004042500c100b81d20960040d03d8050b20755044c01154814000d0141000e0030980280e5002402032a01c640c80b0604c4050290450301401621035015031b00c5071141900301e0304450311074421200400e8042820785546900300710a419880708804030220781500034171565000800c04d00c0000790014066001740c0c00c03d080214a100d0034810400d00c0003080c82079004d040580395241e00150010030460782c00ca0055400c162000c0c002608010081001500311043c0c07881d40950790351903850341d0301000401e20034560b0140c9012001c500f542081e80b100c0040341d410300c10003805040c411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72447160 1250 72445910 72445913
    0xf1008062209060b031924090302100c0503010605040510020a021c06051e07050c1606030911010c080d020c10051017010509120304020d0f1b0e0c03040201030504 71
    0x1480035002150480380341c514019075261031000801c0c1e140410340d907040c40c041040315185404192800810b00740303003180c0040762064a40b011a500403490f184901200710041d00d40c0c0401501504032140e001790043c148046d0b00d12566015101d00c81d203060100001000140110364102c020354058500039200c04500034054801a450456040d402a5000d4180301e00d11031640380035800f2181d02c91044d2014005522495510001854214901002c810864000501441c810005003800700c09940449031540040c17179803980050b4890304620300080c0c0302d06801050010851818105620030301c0c0221102d005512030442c107002e007502481c55950002440b6940e45000c02a0108808112a04102500340740003020b916100ca0320031140400100e1083d0110401c0602c903030303486400030a010301100111000041c0c1c0c6940014000c9920007180d28484010a28611500c0e80c0c441c030407456115851864856400c0c0307604554810003d51000c0e004200500c0c134010180c070b400c00c3d42800c002c1910703140c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72448410 1250 72447160 72447169
    0x106061d0303092806020118030305040302070e0703050f0f040215030a060b0d020d0b030303070804030e01050c030a0801060905030a0f060515030312190e0d0f0203040b130807050f100806 82
    0xb1018001e40c021580c03980511400d0320b542e4125003202d0350b03008468000e035885c0b200f42d00f40c48045e15494120140c152211001c28002c0c0c1003a40e109200b841517441c1e00e51100340c0825180815115840001c5c1d4410410080c0040e01d041642c1181803a1103c00305464a0780c00a8200038a034007406409590100c04112604e070141c0001025001c18031440c3e44959004511100a4001c0310140300303e2070502c1e40003902c81c1004402c44e4013408196a501101c3c0d0b84546085d91072010025025041050402400d003960100348058a8a00003580d1510b40652414400510009064000130720a40048400fa0006000c4508a501d02a4810408183e594400702c00c0d08401d002400b00c40c0c0c050100007101c0c50750340e548040301c601c50759010740d8500760001070000030401c5800000c004d600540c000ca8200f01224044c00f8001503c65051044a151984400c00300365a9048002070300020f00c8038138020f001ca000c0920441010b0032050303c54551882007080090000740c0c80c0e02000c811b200d105804247d084c0c58 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72449660 1250 72448410 72448417
    0x302070504021810030c08010b030702030f0f09040e0606010507110a0302030a080304290a1e0e0c010e0d05070501050703030b03010204030b010e0f092509050c1b0106061d0303 77
    0x300108110340303030041e1003109a103455911511502c1401404811840c0600030300c500c60322841d0940d5041100c0c0c3c02c2503a028180c8c3c0c005007126003580310a206070a0545d12180042401d4662138810f903440d010000180000c4d588010011181500400100310269a019091300d42c500d4010a00c010703003c40c48030100d04100095040a90140503504240041c800359000850159115820145401c50805542803038080c660201c0c1410725140c0c00440e0f800c1d02a500b0042c1c50402d2403150004120301c181912017116800c0304203099a410040c0160203541e04814000411b50081da40c0360f01a030080da0b5200e444030030310300600d07060110102e500c3c01414407aa106010780b10000d00215980c54070303402c2041203c1c02c24400c1080321f1010b080052400380014100a002d406101d00070401009068418654404101c0e400d0f8000e9035800300001c3c50314681d0150602030318102100039034441c1c141582c40000d4050030201c1d0000c1e81001b00402c2401d82c030002c40c001400c2403008182c038890400000074214032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72450910 1250 72449660 72449669
    0x6040507270b03040c03050d0509030c060906162607020f280306150510020a080313050106090504050d110c131b020106060905010c080304060e07081902090109090f0f030207 76
    0x3c01040104100142c0c0c20007920700420403542d69007402501125140708080c40c080e010340250711074880d00d09008018103020702c0001d100504101c0c56204c5900780001c481c10581d022070004003400c4152400007103410750400b0100d102c6180080640200d842d81540c503132034502030300340c08402443c41c5249691301d8900f0041e1540380e1140c2c5a0702d0030700d1006011383c0002d100760b0200070200010360b40307031032403d0f141d0300500380d00602105020313915148000e40008001490400944884400140080c810080a400d20710700c001100e05003824401d00d0850000d001a00340680c03002e150079003640016040400680032122220801c03c01c041074000703003104c034141f40e40340d60743e54620180e655010b410880a0300c0725035940020640e540c1004460200a0840142a01c03a0030070100d07001c1003040d0461805a40380c1ca08803074090b50f075409100d01c3c0c145c0704c11610480140c2c3c0340c2442c0461130180c00450051a905405001010300380d1240b50300c220380c0804c02000e8036600080401014004d114210080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72452160 1250 72450910 72450929
    0x8130212030708030403080106050a200705121c0c0c1202030c040212150102121b07030f0804290a030906060320031e03190c021011060604050727 64
    0x4110341d1905a551340c0055500324040b80303940c0004038aaa100b4000e8a082d012076a41c0d41030b203850742c00b89c0d04036410000d1079040224002c074100400c01e51580040301070454003480c0180301e050004607510407031340807202e002030421a03101c0f0040045001e24034403105882c00c000d4010303c08840c9100003464119814945900300d40086264400360050248440c49464400c03112444413107604012603c0b80004150310380ca554041c0580f50800881c1625550508071032002c0300c608645039110070b10600740641c3c0c215050440002e080c0182421100380080400c1d10354044085000400c1001c0030f81d02862448204041d07480d1100c40c14800d640d0047c0c8000c54001c42c41403000000d8811310800c403440d03622540d00030b11541002103600780001c1420603510605602a5040c03401c10741e80301c080039014071124070401100c80010300c0940e960448414403e0900d84419026002106c681810300c0750060449128502c7c0800700415581c120000c2109100c41a41e54035052400c000910380180340e40e041511076 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72453410 1250 72452160 72452167
    0x1090303050c190c030b070e060307140702040528090506060d030509150a02120909060108040c09050112140307051f0e0709020304020a08070305030d11040503011a040507050a0813021203 82
    0xd00c12404c1071001501d014110498642e960000f080d1041c1d10f4884205400c00000c00018410604c00d100d41c0d81c0401c80c145840d40780c40e211340c0009055070001c1e1020f244646100d4107158040180c2600303c1e50340d84a00c0020b2100340501e8941c55140e0100408a50050a009491004161050702100c400d250010810500103041c0000b103201900309400020140c811062400031a403411401e4421100c0000c0c414040d40c6d0f1000011604200054070807600c1d14000c12002c02d0078441805107d02030118110850048100d50800c01c45004c007002038102550010483c2c107020400100e1450498460800060360104142a000b4000c1008842862482c0155200403a100307a0390307001940990b0080364107489141d154402e80341c41d90074510004046900030040c2000683c2d09420120100d298414190b00702550343d00800d00703541411129810413001450112600e25062007010b821070941d1409504054544001500300314014007213003a1b01c0e40102c00301045645051039103d04bc80ca500640f40c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72454660 1250 72453410 72453413
    0x1b080a2001022e02070501020d0f0b010e0a030210030b031c1403090607031a03070305070f09050106050d0f060909081e0412030c0c03050a0305030f070201050f04060e0a1218120201090303050c19 85
    0xc2c043c2b0004444098140000505036620840110a040100500c070f600194034603400c1200c00c01c115101007060544400e0000e43c0307698240480740001c00741840f80f400c020303203084000f404501e130750305180e0502009000303111403060000313030107a406001d030300380040c40b08101440e84440b0008021410307031600c102ca5022042200100d40c5608031441711821481c082d03191100e08054400900034440003500910801c0c9400760150408118031403690800204540c68003078840c203850800c48155a10100003a100e034420a890880d010448002d060340b5042505244030240c1406400030003504220804c6441e50500081c016040002c65004046038061111460080c0550b0000c0714540100403080b800581c0c03450040c01558030a1099003d107084913503595852000070481d0741503440d0544039003914007002400c036040300f0388040c492351a803500500c0c101c64a42c0c40c05482d500845600c070544031400c0c0050f600542c40f1070580303500d410905c2d20751305046a01707880c000895285807101e00f5003824240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72455910 1250 72454660 72454687
    0x50901082e050909030403020607020d08090402070c030b3d0806010806040309060507081c0b130b0a06030b0f010f12090c06030c0503131b080a2001022e0207050102 72
    0x10860b50151144a03490b80c5000f6559120f005600c0301a40207041040098014505510040040c1e4400e4481e02e00b0201040089012030f080020100c07080c0c0d450000130300038050b00043c002c0d8480c1c1d4614403030288200500414501e440016402c0c00b500e5108a4610307002e014011080340945682343c1111561b40c0c0d101d0401e9550002654103a003c903d840300702042e40361103441151801a0000d80103031616400024112201a005c45019040b540d2185034030014ad41c0c6044100f0714651503400450f031000503904010007900c4a43c400030905281201500c200e0b11090030711350004c0400d0a20306c07080025410140c404010103c00003089500d811003503c1004125503007481a0340144d5000c00103c42e00744815611440252403110309000c2c0300c40faa0000400d0441868104480c070080c0450311541c0d01801c034a0700318249803c480c00106903000d0804481c6038020064042030920003050100d00e851030304000441403a04604480b1003800c035402101c0903540403607001947c450001c65685801e1039022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72457160 1250 72455910 72456001
    0x501050a05030319050901030204090c1d100806060d0207051f0501090b0f0d050c0402040f081204150f03090b010b0c0105091f0f060314030307021c05090108 69
    0x100c0c819000d440020605040000c03c0d134903c11a11624550071820f108010355050f0414040e039410150200301c0847c45200c04d004107030f800d1059031a800d442d200341203000002c0d40303034100080b4011050b41007048466031740078904941044050795460b40d201c6030702d19000040e00c01e4200203000c40c4507448800300c0320117a9511628044140340410040d80c0d0302c0e400b840041d605105480399211845043d020710910301801d21044603840342044890000300c40d13003c6026a0820b0b440548140440181086540000e0008100d100f88031051280750a06007051095400c41d200c50b50020040c0b02e0000e400100d000e5400320b41c8198201c81585543c0da50360043d03070000e5100b01035080701542417802140440e81c00282100c0c0c0d82c65400d6203260006902d95001e4010b00200c860064003540b030b4200000032400c1d4800070030301b40c03407110007541e520700e46004080c3c50502e600c040000e2400308011302c03642c91a4884192189424246480c40440d01c3e0200714000031503030341c0358070100401418442200c421045262 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72458410 1250 72457160 72457169
    0x1d03012906040b2107021b0f180a06030203011a011b0c1d040302010b0a210501022205091303050f090f10020105060f01090f0b03091908030106120207170f0f0d0501 72
    0x4d0300842d1340d0344041281c03104038401c40080e00c0c07115015400c00710300d0083c0c0e50029030a40a030004041282207001c41d5800a407e81d03240b054940c1ea02000e1081d0708084c0031340b1580550a0902030b8903a1b10b8540024000d0b20060b14000780104007a025408015a880c212802480c2c07200749600810302d00d107040c1c840440c09a400324059071912141c4030107418009244012541442004203140044011000014a00510846030b5550810a46400414100741c11442c010100d03003405400f4180400c1c00020807018084200928138007216a0000c4e90100072510203c4599003280d4072480c0a038085030741e4212500041e5848810100d00c01c0b01e0301d50541c00b152050004440402141260100640300000b07240241050905140303810b02600a003800210303042106d690854418101012800030b02017070740764003110441c000200401c41c0c13580c000b451003001c106640d000c41c5082401c2ea0342508143d203640381c407990040c0101c1c01480d0100903109480c040a001c401d038950714031302c02088c8030007070609006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72459660 1250 72458410 72458467
    0x302030a0b0f150a020106050307120303050f09030328141005040b0904080a02070f060201020706060608091b03010f020c01020705010e0a0c140a0f061d03012906040b 73
    0x1881c4161404034201107001602a281140e10f1100800d180001da0100c0c02d100295921100005203031b4504000000080000e07000c00140c44405103001000d0f203102034160040070f2815000e101d041e85000c412203070001155814440315050340352810400790280c840c00f092051810b000d03045040150701038148a007060300321180d040340e220b80030072046034128006035410403010000500081e03800c2c0028410280f0380d00464200580c1d6105a00f0360143c550001c0c001030750081014400c0000f00c0c0950303005401c40e42082c00b068542900d070301da40d81103040741c8400c1486c00c00110407096102980011600e40602400350b40c0e46044d940342a020b503124140c11545580303040d28400410030045107050489500c440410340c207524048240c1d10215150080c00e502003c04000010303040c000300b03942001403078aa00d601318500610b01000e0220100d0751040c2c1d0290b4180490985140200780601c061208500c94a44807158850080f4406003d95006908010400203043c051000c1c1d10806020b4201d1010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 72460910 1250 72459660 72459671
    0x21306090923070306051504020301080d020706030605061218070f0501080a060b091302090306071e0e101b0804030c0810060806040f0f0605041103150f0126010c0302030a 75
    0x1440780e0b440d541c2c0c69141820907084200e0500010f031082e00300c0d6810120b6405003108080151700002c0c03c0342d000381e00c41c00d016070000043e002e6082c5c0520000008100e1400c04010192800010808a00ca0242003006003900701c4009140c2498501c804c3c80c4031792022044404081e01d44045100502203030150501060448002401c8200389008840c15202c8405603142000f1001c000e0040510031030040c908120707002d02050301d880d201002103510801035551100d0201480e40d00c103003103d61441e240901040a14100c00310580c640300b130210800d0720b43c0e1810002d00c00b401805817401d001114030060444034001800414081003904410030358044900b0b950902482000d4201107c4042c400c01b28150000c100050200b0140c080b10440745004686038541100c440e41c0e44011208211400c0f13440740304066516070242410440d0b078030f000464001001490402510040c04110305204c0d4402c0b4056121911582602c00d9510a11642ca554001d1107408032400020380030350002c841c4000c01b03a1408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 72462160 1250 72460910 72460943
    0x5090a0b040807170a1203091e12050c010e06160807081504110d09050d0306080a020108040b040201020a05070b180609011b02120a03020109060b030706090605070213060909 76
    0x40122001c41ea01040182200c5181130840002c00000da98050304a000d10381d01d4001090110390319110101c0e40d1307940001c00ea002e43c5001d801e19649403005280c07070f02e00360380960009034501c0740f500000012406c2c0b1a480c0d00c4080c440310302419032a4200300e0a8010320b0103008110b40c120840c2c030107032810b0f51500c50b136540c0e840c1700840d1601d208441c03494040c00712500100301414907601040441042c80000d515140e9501c00c82401d80380541411945540402c18880800d5807501c20100a0314040b03026024800840e00000c0080c41c02600c05080100b0031004101168000c0041d6200154004140e039035190340d07206000d5140c1c1250194a40d002c226440324440303880c041c1f04135402c04038143c503110801000100768403515074004070100d81040403005444503100e003c001c004141c0f03102c0c0c2d0020403403d06a14000c0c082d50619031020b406076010b00024019070307030006a203101b41d50749031902c1174680d0043c4c0000f500e00e1030340d80c0c094402e0078030745030f004078400c0c90540140c60b010b0300030304142203100c080c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 72463410 1250 72462160 72462179
    0x608010504050709020f1e090406090b150c01060302090f070905010206240a0503030c03070c050f0a0513111204231b04020403061410080303131713030305090a 70
    0x844004207550020f041c1441081c40903400ba0542c4c03001903150070f00780074100521940401095400b140d40c101c0100d030258151800780244401b50480b08024000e070700c0b0740c1001c100080c0c000052103562203804140400c181c002544018000c640007041c14410703003408900d44002050603199007000800200020826500000e05240240c003820942903000c0700301d00201e000e01c115a81c030586d1014268031b0000e240e0b43e08102521304034490202030740d0348070410b1922071803510499008030b0050a4030300050a583e030b20800200300301d86040d15640c80701040490010014860408490314002020038030b030404c00c0ea60140c4d144101e1048050501d0704c103070411410034081840e50314514903409140070030841200040d03801280140504050300709034907030b039401007694031010140a4200402041202c44112468001c00420424000d50701c1c605000031308040400d520903001d400e8540d40c2400740c503014044011588140076009003c0308203a201c1c98020400d900020005101e0140d40b117020a0f680030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 72464660 1250 72463410 72463421
    0x5030709060303080402270f0a0c030e0304090207080d050108010f11090f01030e120d0506100908030a0e0d02060307110607030b0a03020f04020712030615030c020a02010c1b090e01060801 82
    0x401d03444210b901c1e030740c86e82040f058030102640d100c04154035002e88004d1800d2203407068003681030703421400a030b031820348030390b4040700e19954220040500b000301340c00b100e00c1d0100c119020b90f4003e60000d0f940314410700300780300c282c81122250580140350038000124600c041d0301c4600c01d04544001886a1b561a610504660052000c0c8650100c20341a25110540c020350004001600031400c3d03600404800f0b00f55107054001d203040c0c481c00790b00c55003040a50b14012550340d41e05000e03410903805140c00c000d9025901e00800c0b8412081c0b003a04005c011503641c7d09407468041680c010030190b40c9262603500146080c0143c456030840d48108808180c092740a0302850001d04406880c01c8a032034515000c00c00303148005520950003d0b82009040e02003030081c81e41128113503064401103a20781c901a02001801200031051081629010702030511a0303001c143c40201513024078080c25005902d0070401c00400b10170191202460b400200000c0c0500c1e581c02c00490100b135035008112280e680d0541500741c3d42c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 72465910 1250 72464660 72464663
    0x108010315050a06120311010e1603080906070206071505061c0f020d08040e010602060601080121170310060e090411060a0215010b0309060a0b0109050411070615050307090603 77
    0x54103080ca07900c0c0401c455201aa00400c0b5200114500740c1c0c0c0c201c001d000130000401500040c40b14200400240800d0142541d0405980020320080c001d43da0204180f02c1c00b40401031180f10001410340031595000140d0385c2c1183c0080c00c80d82e6a44003440c0c09442c04001e43c031500942403d09000800d00c1c034180102c0d600340c2c001315401c0668440182e844071038a100c0b00404a9018044070398a8010402c0200a04003800560350343d00140e504140e4080d25125009081c2410003602c40c00602c007840e103114034413001070020030010341011201c0c540401c0204c60b0688071070800b840802002140d4660b04060821a00c4988400707424412601c203000c1540d508480c054182038070060321030f5083c140700000300300c444002c0c81640c0881901842ca00c1001c40207a209140c400c0d000700030b2080d03004041c000303260045c1c014001088400e441c40000ba0980304181b1440344a01c0c0d03100000d17030008407802e0844007203d502100410440c08001003007086010343c4c0c0103440c00b901c200c810125100c00584215410340b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 72467160 1250 72465910 72465923
    0x80f0403050901050a020111160b012c0402010c050f07051c050c150d020301060906200a0b0601020f011803030b010801030b0a09060209040c0804050c030705060304201e01080601080103 81
    0x2d54100010744071540000c400710219942d841e07618101c101620047d1400540c04030580d50400c1d440d0814000a1702c4c180c01c841c1210700801b480008210100d4020110ba1400381c1d2149080d0340c9600058801201010f0b01500a01601006c00600140403c0100664100716008800ba02c121040a0322800c490040281250f00148025983d03141040007802094400349009107000e40c6880341e40140d0700700b03070301207008100b100747e0a20010790410401242e000350b0742250501500b5104020340c0d00e041421028140480740703c00b1460591007032103840085403034800248091070744800151000052403100b0b40000e4079080b07241c000ca44c480e0703040d18126034205840100d83d03180c0c0c0c136024009008030312048412590030092107256449900a0a20740200781d102c4406500e0b15041c20b03401c200c200c0c41900d00c40d8010700003c0c8000d070f403114143c1e42c200f070304000b5810710a4015039a00765070440d481c0382c0503030020000214442c1404d000d40c10b003148460070390710030080e601c3e050011b4401600a0000500a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 72468410 1250 72467160 72467167
    0x6031a13050a1b0503040204060905150405070e04090b040512070308011710051f090615081905011215110301060507050106050a06030e010b1c020d030c02060d020406080f040305 78
    0x514219088560482c011100c0024507500035051840115a450032400c00725502000700810b5281c6407007020010711035804140090314004400b20581c04103101d5192080d591100806e555038800d40e21320340c2284025200300a02c5140e070404003000101101c0c11200c07031040c4911011488412400e031900c890303140e05c84401d1642050750320307140c8600c42e00c120b805034030404000303980011803030103442e0050f900c200b110b4107203649907201c0710041110303a040b50b40918200729081040072043c03044c498a03682c02c0c2c9000401a200e0310616034400c840548a400080d08000c0045441c4c0807000402c807025102c0e0207013844050b04608150140c035000c41a0303d04d101ca09100400165000f00001e08945114800004405e030700d510000b0408030007a0007020000b81d0b1442c400e056030901f445141d2014200321800c81200480303a6a90f001146000d80081c040c9411b5038a084c201400754400c4441c10b1307401000552110302d10302d03610000b500244122000510114041081150344003081130103a60151780f0391340b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 72469660 1250 72468410 72468439
    0x170c0313090c02280204020f09030c01020a020f06070809030a030302040501020f151506120702010b0117090c0d050304080703080310060305060a061d030106080a030201050702031305090601030902030f060106031a 93
    0x20181d884182c2ca10741c0442c84d401000043e40c8074402044440080006070381c4031080c20041c140303001e019285450640d400680b01030096030316842ea92100c1a41194400d80e18141d6186c0358406d800f034101103d81601c25040a0403c2680540217803086e41d0080c2d003225092501f2500565482c644084060740c0240140c001c1040340405402c881c0d01c00d40003402c0940382240c0301c07880c000c00d500d0498160380140d6488011210560b03004060011f00c51400c514415603041512000340c81d01400000b4030710070060b60b1682c0042200520990f00244500010b03154002d55030f04111066900864103905960038520000c07075998028800e0a000e404003819148129084c008141d52030700d024014800c0d01c00030151102d0700383c4e50034040d542c0a0301940001d007540d031005103406030948402800110a41d0030a0041c0c1050003070400f001422100206c901c400c1e652181c00050380102009100a50140211407119613080310000701113040751219941004220109070390f218500c00e903581c002c0e0b80b015014030740c440b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 72470910 1250 72469660 72469693
    0x5010507140a121107110316060e060c070b0403030305060108180303060f13240806091c0c0f0f120305010b09060705010e0303040f030909150b07170c0313090c02 71
    0x1e80035050f0500058503000d06000d2107507034101400481e00100e58005201e03041c02c1c14005222990300e00310008481c0340c10004040d10801c08520b450b40540070102d0801c0003100100450344c0104245640a40da030390722818020003920007200e60b540481c1244000c20300d203084400d0701d408600581c03c0038606585510741005043c00620b11100e6003c2040d02c890b40440314544500310304000542000b000e810300100c410046902c642c0d001c01090f401820400c1f5118002207207041740700441c03040c0307448603038200402641c40704450302c000b400d0349015240941c01c200109070740d41d000344d01440b51003441100f481c004401b506d809025000c0040c0c42070000c4d9136141050f00160444910850011501c60b1000a04924541085805950b00880f0030911001d041c1c000c242c40703020380341c2004141b01c0d80030400503c0c0e400b150184a07542c915040001c0702c6c0c003400b808500003001c42c120506455602c170300c070100c020b58031781114034944000d0105550001c0c0381d00c480d00c54840307061180d8014110b0751286074013a6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 72472160 1250 72470910 72470927
    0x901080f0115060903200301020301141203072d0501020d061e030309090b0f0405040f021311030c0c1603030207080c1c02060a1110020315090721020702040f02030405010507140a 78
    0x80150410341c071b4140d0b20740c0d0280041c40c060b00012400e004038552400802c401207100700c41045043e001080281c3c045125600b80b184046e50140115001814014910307841840ba508043c20552000c90300300410243d60300007404482e10744421001d140040300d5942d00b170078002d1000401040146108011116041d04400300004005001c0c01040b81003030080b80035614100d504941d900141c42d1944114a000c09107001880d580c840704001407007404980f001282b01c040c0094010f00c00106000a03020010031258070a0400d00c02c1000701e0980da450084e40c0d4a005005076803841c002c0c091004a00d0418520070b1384041c130391b0008204400019001d0041543c0000507460404c210302032060070580c030403c40e01c0c1d002007007040d0060340da10308903002c203140303120b103a1079144134582640a100681d40c4c03140b820b0b00302100001d42da00d6010500c1540c14024428030304006d41040c20400300d1702d500e040310783c0614420b44c00381c0001e01060707403800d008403042040c0e42c10542a87c6c1e42844002601c03441007049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 72473410 1250 72472160 72472193
    0xd020618070b041508010803070308010e06060d0c021e03120109090c050a060c0b06011103032e030f0605070302090a0b09030c040906020a030b011d0415050901080f0115060903 77
    0xa4031541c0303440d91200c1c49594025084002d0105203400100384040d0701481150040999001031428400c2a581c018280350040c4035000000c2c9000380410305544d80c007012a29610108030003008403c000c1100603460f03601b0a03840007000c08182008040440001c404c075000030138420f5248409a092a41180061039602c80075184030f03a09450110b0503407101300240d070251017207445111900c405464060f007148d500801d46410441001507001c8582e40000075a40c01110070801c03001c42040c07240301e45890405181d80180201c40c1030320000184200e8003289806280035000c10f0109545000c000d9041c0d00c1242125500840708801c00c0080d44040f901400752014014191801492550006070542c0c0c1c401c0d5041e2030303082d07001a444141c41c0d094814507480800a080c4041c170314203254404010380303240d0041540101e8940d1031547c080d0104102d50000b034000101946400d50715800042e98500740b601d21299107610305140c18004e1940b9441c2001180c0c40d0342da07241e100d03e040d0342d2440340e4130040002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 72474660 1250 72473410 72473413
    0x4150314030706060810110403021516060f021312050601030f05010e03181314010521100203070f08090607120e070303050d0b010503090a1e050123090d020618 70
    0x3500000303407560240030b005142450003415406e0704100070004607110828001803141c0200400c000507190340303d141580c4181c0b05560b6803620200c40c2e00c2503c0c40b404000081c0725034130b0b041c4140004482d96000e85131742c4040722120142c803915401e502030b100e0642c2a0140c000d070310150041000420520040c480c1d02e219500104019481000f160302c3e540000289034458200c41c6007034401810080d42400340d6002c440c405101c4052609c9800c031151038107004a50043d00b00031070038081c912100540c01c2c1e5210310b160441d541c0b504444402c0c0025041514103400007850040642955403090b0001802102d004025000b6174032204c0d0107603500501c000c0040d030001d40380d840100c0031000c14001c220096002e03844441d6900402000303030084410042d48036051080900c28000082c500140c1402c030f05a2103084451070380100343c004601070503000c000612560030241c41d132071b81d4454220500f20703042c12011002565110b550340d4503200c0305050803580c0140e10440015400c0c401c03a00c3c900002d11012070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 72475910 1250 72474660 72474667
    0x806041502031e13060e0316020f0d0c090906140103110913051f0b011b0f0c030b1503010506090402010c061104090603080316050a0504060e010512240415031403 71
    0x403c001e1501c40100da101c0c04144051081c20240903e90050400708400302c805140342540c4043d83c15108848110b001e40a50103511011085441e10b442d001c1105400071003841d8650703a40c40310200940446481150f03458203220b481d00441040b02000c0c1e0503a5400358083d940701c84100e0034000c4049004191070b020028440d90342000c03c4085c032980c0110482c40f00c03d90841001511850185c40c1c1e5501e4070360420541000381e00c4010743c103e0880c00b0701603015959240da02000c0c20003050505d910f0b00054410299101482008103201d0550720020000f60300922095a42d0020400c202c44100d8000e40400c810601d03030b01c00101140d101924040b403950b100c5003010b454650844c1240c00a4008a4640b0000411711040341108480c2c4d642400061408a2034003007044030003009409072707119a03001d01c40e04100c01c426585c050000d6034490b0042542c0d8411601e07225415141e415426008a1107805c00c0009500d4141030a0180b201d12690345040c040d03c507132540e51080c64000b40c1724080b250500041c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 72477160 1250 72475910 72475951
    0x21311090402180f030d09060c1104020310030b06030307031b020111030f0a031404050715300b1914030c0901090903020d050717090607020a031209080604150203 71
    0x288090b2600303076100c00e24031604a40340c100b03001160710400e0f07290340b0a40c042105075010547c0110000b0a03541d45241140b5461018989640d440d104800c3e000c0d405400441001707003500546140e030341120300880780301403140c075403006040d2a88640c0300050000f40300c0602c05110361103500d10003418148180340c1661010400c14002d030644d04215942050700100081d0000c20b03da250080302c40f018001c00300c21038141800d0703a03203ea40341014801c205024446d200402e14050280e03a4a1180d020740ca20410f030b04680505000440c01e803002c030b00040c1a8540203124041d420082910b1082c24000f4101d20291130408021131003084d2903503807490740361091008070b4645031108200070b4000d0402040c04242d0b4122403402030708104960300c8100c01c1110501034000402e09000100800041c0d05640740d5503582c8040c04100e8a100c0d90318065000603000c007000040006020348503200c00b003a0b0b99011341007a100d03848162941d4081d07034003604140d210302e801d044000017540103640020580c00c260700b400024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 72478410 1250 72477160 72477169
    0x5091305010608090f060c120907030503070b010f0e19020903100e0607030c110c0f01091502060601020f0a030203071506030f0b0610030b100f030e01141801060302131109 75
    0x240c1100000500b41000c0c03001005080004030208002000602240e2034400c0f4003854601888e6001041a8842004524048070030320100c0051500f10082c0c0795204154102044461400e02c511240515090b4000502da40207502c0c0030700854108040e03007044100c0e0744200c0d001e5009101c01700d9150003a0b0386400041c88462044404c03a0400754003900711890700705d00207411100c170701d10700d0001d002d48680394000c081000301e001a10403000b1901c1480900010380121610314083e0400a20380d80d8100710100c2050300040c0c068442c2100340d00701d40c0ca00d440f0010903a02c80e80d0b1124000d025074030900c151800203107600c80312080746c240c500c400031300030303a0f00d48580061040c13061055070010403807824011941041e1032045400f0407142000c2c41082d110f030300032400b00d03803a100c1a8000c00184082134200305103c1d40000d030180d01031400034048600c0d8920302c0c00c8004820f41e030031100840c4890070701c0f05d886010b0289070100d98000b403000113020200410b030300c00b0303200304544100549000c10008016503034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 72479660 1250 72478410 72478421
    0x1101030c0e101701060903080d021312031d01020304050310200f070506060901030b0a05040201021002130602161a0a020c03060a0b04050603010509121809011203020d031b050913 78
    0x140d540c1c00d4502c103e4504940c000c01041e0000002c000c03c0403801d0020400c06e00850719480b10b00700d40180e984001c0c090000c001041c80c0c0046001c0620031010f00c0a00d544101110f59030841091a0b104180d03681c00160f950344903034402c554258020300805030007120a0740c0f10008000d002d0042c800c00314005c40d1551180d0348900038941c5c50b100d01281c00f20500000700049070b4401016108000c0550458a540f810f00c01c0042200c8100f64550000a045900c00e10034202550728408055440c0d0300540c0300040c03c0c4049001d40c000605c510518210204408100030048440316103000140e21a04000b070305c40390703210455803400d41c82680d4000d400c035142042103901c2135100c0b9400048500240c0200016110301901c410b11036070414090045109001c1101204520812042542c82512440c44030381d4004442c03205602c00d10003c00000c5c01029445090300d8284a6803d5421380a6000380a0301142c482e140d050b64100581d049074000180560300400c65200d009100b070450240300d0400d8002d0300c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 72480910 1250 72479660 72479689
    0x1914030304030c030f020d021c1b0506010501140906030402040e031b0102030703110a081906030b09010203060f0102060f011a040905100609140d0b04110a0303030b0a050108041101030c0e 82
    0x919004810052643c01030171069820b40c1c2e407002c5c000d04200003400943c1e070b40c030417a144c64243c0c0d2860000035400d801444120842000c8075241e240b0640e80d0b04060703486272004d20443d4007040e8a506800f203500307046412078900102c002e11080c20b58407160240401462140701c2080144001c02001c0d5040300072883c052551511007001681d02c0c5844c140060545400102c01d15a090b414090998050303082500154031140d440d00f2016000012080900588087e030320280c203412000d0305000c42d0704010b4005601c68801926618100e40081d0012692964221100e034240817000c001407142075405e03044c021210816894407400d103501c42c0364000850340140c8002030941c080300340810810b5001100030005002c8100d13203d0b0401d43c00c1020900401500d680200300b04500800034003040403110341c61410301e4026240b10300031034580c90301070002c0082400683c0300b04510342d0001801d6200e03c0000303100f5940a000b0b10748228540c801500030740215a10782d014061240200f0802d620780c440342c1e50303600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 72482016 1106 72480910 72480917
    0x4060b0411120609060d1a04080f03071701150219020d050d02030a08011202010e060a020114150a0b040509010b0f120106050403150e191403030403 65
    0x5100c80785280700001c0300410403010b50420420310030301c260400e90b00d404064036100100a919483c0c0302004002098058020007500100e185551700923100f000c0041c00c2210300c41403400a504200c8030000050190140114030651130170000707004007001c0c442c03d015040b200b0f4000b501c8241c481e40207849540c02c0710240d0110b444408400b0109900705c2d003580d5244845001c000d48950000c020200001c0103100081000702c0d500501600c1b560741610b0f603900307951110b8180503c2c1c0d00007041c071206655075801c1c0c0076a698602c800280c40b6081c0c17141c81c0c40c682c40304101000b26038121500080060304c400e00c8240b0040e110700e20f0050565800c5203646407220350b9284403c201d881910308034092954450000100103402c5005401a2441390041800740084041407404481ea0664501c3d029408041200c00d0402c95480380414603020b4144c1041001742e0190581c5186c8c4242d500720000b = true := by decide +kernel

theorem cover : BRFrame.Cov 72302160 72482016 := by
  have h0 := BRFrame.cov_init 72302160
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72302160 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 72302160 ≤ n) (h2 : n < 72482016) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
