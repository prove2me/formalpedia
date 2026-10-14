-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:33.861732+00:00
-- url     : https://prove2.me/submissions/5adf7f1f-ce38-4406-8488-eeef2608d93b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 599460431 ≤ n < 599640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 599461681 1250 599460431 599460461
    0xe0402040f02030a090c08030906120405010612030e040c0f0914030a0f0605100e16080a15080304090c080103231615030c17011e0302090c250312 64
    0x100c030103030001c0300300c0c0c2044030b030b5061054a0310b0700e40c030900c0001c070380c040040d1004001a5142c40c1125002c03880c20300c10302c0d4900b0300c40c0c0a20b03000181841029404203000e80403034201c428140c0e0345420020b10072584541850f00c01c624146a14036001d000e081180680c4056445180110307151410b18940c060940c204550140180080f02c4002130b144c0810544c1107100e002c2c0043c00d0300b024080d00300e1805442e0045210081a9818409425451038044400944038a80045c40b6075030700650101804100001100000044c0c9010441c400f0100180007a600111000c0000815101040320090f50030f10003e001d01100a503280130110500d01c2e02a81c01e6403036400ca0356680c1e0005002c07000030300c0c1a440903204030340600d1085d0000350706018800340f003446403a0900da403442c5c502082560000602c51000c61048242006245920880c03540c002190010003414191034424400c0c1850b5100c81400c3c6070008402610600030101c5007040088141c140e69205002100008c2030002055256120800c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 599462931 1250 599461681 599461691
    0x12030e0729030903070c170307061104241101201e03130b0a0605010e040507120f05151f050307021908180a052d060406080f0610090e040204 62
    0x241e900a00d0056009404100c015950f6000c1801d004a8014464000e1009010320b0000407200f60030004c29a20b90300c0d044540010480102e14640901b440795902c00c20500d040e04115041e90ba0054418601444141e202c80007070442e804045400c94808421040c08044c00005003c03041c003400000d81403580240301c0000c40c1c4112945080190740040300e0081c0031601004a00d81001540d05480360800c81c07030907003032000c01c0c01c0c400003902c005018180705000c1c42d600c2c8000f401c014891340180d602080180030400c41c494801c414100944002c8801d20240080b000c003481c00750601603400c1e85503140810b805050700020300401c030350369403000d001e41085200351540038040031105065070300340510400300d4035a42c0d140815503940b41c80003181c0d030610410b44000d04110648504084021625411180d131040758a40f0480c2c03e10b41c048a440702c0e400640c045000f0803003a410502450180c062134071801079503922582000184403040c0c40e030302d000595200c02006641f03021900c040d0898402000861 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 599464181 1250 599462931 599462999
    0xb2d04020d0e0d120b0105030c1e0f2205060a0f2a150b060a0f0924090b0306100c030c0203012a0e06070b1f08030712030e07 55
    0xa4408078241c400b4560003907240c884200750051545800401a018240300788010140060200c0c040140104941c01c00040e0780740c3d000700108008002c01c017041c2907150b1200034002c591456500700b84c5048040b20b2403807926011140710700302c80c8000c0310001462586400b10a0104650300a034104a85c41440700707001c0d400c14140d503028111f0265181610f84400000d00038100b00800c111584800801d580c903080c502d03480c6031203d9044030fa00b5407007410000c01d007464103a400c4030182c509600c02c0c14481c094103221004045501c2c1c040c980d80910f0799954554640700c50b150540b43c4000d544540d8001e01070441001d215009040010905001c2d00702211101c0803500820b09581e8030990f420701e00d040d00010400c0400c1d982e502c016040300180343c24440c030300624003c2000c500c00c28101a201c00020390010718244056050b8081d100022031408100395030303c000710b5a99820881e0b04a07043c51002e451074150511a10890310241e401800600ca0f0a01e030201029460a01c910308040850454800703403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 599465431 1250 599464181 599464207
    0x60207140901033c02040b12101518060302040605190909061d0604030305100302400c08010e13020d06020d090f0c0611070b0a17040b07030b2d0402 65
    0x4130050b124500710010201039881040201c44440c4040d610989441d00340100e1508002110350440d042e0040024588550307507243c510201c4260720544402d40c0c18012079415a41c65045441284c0c82528148030301600e4804004024554140d60b000310640c410007080102d00e140c004200c0640100720001d50091502c127804022540c106000342c1660095061104250703251242c50303032141c440b12109003450b0443d40010001401d007501208412161501d003a8035a215441c0c042c00070480455a44148040c02980005050750501101c0819130110000400d80c04980c2843e104030780042414084410b65400c21401103081d85c425141c0c6a400d0118600100161003000e04080c0039008690606e0b029190000291010b0b03000101042a82400442c0d550360025107202038450300984d407600d50304044012910118001ea000030201c1414042c40103010200e030800380940c2d1540d800b03120300c0341802c0030301c0781032411110781d484444104840d41400306440d048164006038000c0002d40b406c50b5481e409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 599466681 1250 599465431 599465513
    0x903080301090203094b0708071d1e072705131401030f050a02060d0e160506090103110c030c0d020f0604050601052107060906020714090103 62
    0x4000c2d5158000144412000e0401503070130004062040401e00700322030703c2904d00290b420984d80082c007140c5000003819a6180040d1108070712408100c55411307a6542009548103114400c200310f400d440424607500e800c02c01e414501c660800b0076080240450040d0080d079020000300f15034204104541c0308054688103220060700501e04041c0c0c0040c160402c0c08002c10800d01d03604038a07405143c910721050015658459504582e00040d8407401103040c0d00f03110342001c001c41002513001c030780000c400e145254241d000060408151084881980c0c2522010019801900841e580803e0501c40a520780d84250070000340321003144100b500308500030b4012440e540200f1900c4000760048890b501e1455410004a112203000710020403450400743c4600d600c07904180219400307418170028404d070f4100e80300c400882748640001103e410350703520a0300502e892222b0140346d0060050300d00004044124802e036103040c0c0c200800341c0c0d80e0b591035039a41025800b103007036006c82c0c080003a6103801031062103d940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 599467931 1250 599466681 599466689
    0x101106010602030d1a152109100c11120921010b180f06041a1e09060d050c060d0603050a030f12061409060333010803280903080301 58
    0x31030312000050708140540b8245a400c540021010401c0e1680c0d584088001c907000700e0032450260f0f18030b80c034800f10864408140c7c1d10308003441d04005020540c0390010752009500d07040c007002c0140e0b001040d811100685100d0315507071158001d45c001341404240d20018a110100104503169010700d009040b409800c070941d07407800c03a0f5036411080041b410302405603804ca80c00c10344d42ca02c05107850350b050301c0c007003070080c0ca00d50256035101d016505003049140651003c441c000c01e56004030346150b5409070801c07103003403000f40107691210105145084c40020004c0c0d01d54020050010700c2408410b00010750090b00b507524040303846044c00400700c0d205000d00301c2d220f802035880e160926600400548420310300c240b50400c20345000010006d1400c550750f0b135a45030100321196141030f212a00005d240192044401c0542e03544002c0e61400c6458a010310003a202c0c0080340b400940c1c3e60790410545a0066500845140c18804001d1141f03880c02803c0812044040c20300c000090303241d1300d070f1107038030780007600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 599469181 1250 599467931 599467933
    0xe030d030e0c0402090109140a0b0417071502031617040b0301091a0d0213060902030c09010e1c030c1a01090903111f020d0b2e0206070509101106010602 67
    0x703404450701c0300078410014046000d440c194a84441040001d1080c451841210709a60044121180550380c2042c6840181079180f221620f0b552106810380440344c0b010521041882500000541c0c40c40e41d620740230600300d00c1d030080c40c1440740900c240902c004c444041101c031089500d50f0080b8228041c0e014001a120040f1140e481c1d43c184841042154003c18802001c0440601c070000c06544800d91410f10f903605482c044040d104070b10f481800390085801480b805400441003140c9100d0000c042c1030303914826a200c14000003140c0900a40556840c0d01c14222020340c8125800b107030140e83d0b1076000c1840b40c1c40308013986a100e0882140003200381c00c02221242c64001290516a00500e1503030401032000207000100b501c40c40860000e2400742c3c0740c001054000c1090852410564044450a0000b4007019004542154441d045000403885c18500c0d0100c1c4082d4401d0500c002030306845401c03540c552314078007203500d4100402840803001c3d180c100659031110802d180c2041c003602c3d000b802150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 599470431 1250 599469181 599469191
    0x30b06210d0e270a020d02130e0901060e0408041715070c12110c010e0303041205010b04050c04030b1f170a06051506030a0903020102121f09110a0305070e030d03 71
    0x1c04005081c01d40301c0e0b4900c40303850000300c140720201003180804e40004c0040b4005a907291010031500c0640142c1480c1468000d004034009604452130300c80724861403d17000200041034403100002c104403400d41313000e00903060611050140304e10511403009041c1c00107088074090034003591142d082c0101200d420000800e5201e0480400101f4200282c01341014141071a0012104001ca560f602d040c00203541000340802280b50315440500803100540302001c0741c11000041814000d001e08104807401c1e0007503103882c000840a01c2303128152400e40340c3c8000869101d844610a05907c1a01040c0c032160840c040d800001d49490103007010003034040510058030482d99507051500440d5401850800260070aa0341c0c44055552841100e600c01c0080500188040c000c0c14124024000c641072000560f00540a1000400e500c280c3d07402410071f0b0704643c4604580303503600501030300c01d1810f004100c80d00c10b00c07240442038002d03042154085000d29104020541032000a4901608a001a07012a03619 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 599471681 1250 599470431 599470457
    0x703050121110907030603020d2d0809010804110a06110f0304030206040605030a02130305060f06010f0c080c0f0601080a12020706051204020d0c0b0d0b0405040b310624030b06210d 79
    0x20607090b5008000c40052b481c1010b01c3c1e81c460341080e20030181e04904118500002400700a910428107500c5200901180c01c0031780c4509000c0c3c0000d40e1000300700c50038491940803880c558800403c5905896001d805a800d03c6d1410a087c0d4164102078004005030341c00748405046003824140341001540690002c21703007420078460743c0c0c2030140050301460400894003038003000f0b103030072a050509550303012920503902c1e012402580c1c1000d003c3c103420b010340c0c010900002800440001c100034010f0181141c40414141c0c2001640c0d10002d40c8116400b0540c280400c0086200050040340d209002800c0e400c400c0701d16540d80031940b0050342040b000440d02042040035079a0303c0c0301e1003180c10402e6078100310350308180c1c075070300d40902c001070a40322440905805c0401c482401c603d0003440c42c2d0201d601d0780015040340352a0018141c0c1c41001c03010f080d10304495150070075400c248038003280d4000c8103c00701038840703030280041402510b0541c0c0910b048a010004281c104000666102850345d90710a511841 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 599472931 1250 599471681 599471723
    0xf07230f12041211061b0c1b011101020322032120030c070b041406010b1c1a04150b120f0f04030e040911090703050121110907030603020d 61
    0x743e20050200140c12414034079031103001402c03e40040018002c2000a40e006090110b24030402102000a000b08020862005039010000c405910300341c032000440c1407480c43e41401c0740411a0310460220500000c10004500c1c40004c3d1452402440d040410b801203081c5170140300c01c6024540c015907a145039402030a080941200320074503181207034924504240d08d03440024002c40303034050f140c4684030b40810300b00171000c848074800c242035105aa21a40e5501507040c0c2542017004000025034032a110f646141000e03100c2c0d200355902e034101c441580c8038035105100c02004045691005000901e001041ca580360001401d0b44410545000d00c1500d006103295000b520043d1800301d03000b2000c0f0500c0006a0490b02e5142002025580010305007083e0610803050010403094a80103074180040c0100c0c0756040e00001d040c0c5400e400d45c034840c014564044210025031100182c80c100c1e0300c20b6060002d2901a101d647c100d60180303404164240c50340c0009940d007268940844070312010305110b80f0340d452 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 599474181 1250 599472931 599472953
    0x40510060f021902190503070e0f060103022d040b0d0501081c050406050c0a0f03051801081b070809040510060306090b1c05010e01051e0f07230f1204 66
    0x201c244003030400211140719500440f980080b000341324103901480760403040a00c550403801080c00a0444030b500380e50300c44240c545c10040e60160300e040400c030009622075009000b22503460014002c09a080d04102c044042200500031040720340e4502040005441c3c2ca0348005041ca4241c9000c0010f1107500d451b0300c42d482e12038a0b0210740d03480c075800d01114013280d402006840845045042250792000c20440f01e42c1040d15201000307010fa504c0011410602d603111010342116035802c1200f002654040005540d01031007114500c0703208036070103d00c100e101c100001800d0454418071550341803a021030005015a04115905144c4441d0f12000b0415103500d80940d0000b004644020012200e003600031984501850700b102900d055441358010411000750f21000c04503103214020092070900e40c0a00704080032a160a5501004144c04501c43c041080e01541c01400e045d25105800180040c041c081000c4440d00c4d26580b00c8140102462415124014070540b40c035040d410b24180b92510305400545 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 599475431 1250 599474181 599474207
    0xc060e0c0a0f030305041a0906070303022d03150f091e070314010501141306090f08070506030406051b0a0917010b031b03010b0a1205010c1d010c0305070204051006 72
    0x201c10010008285c22604913416195517000b00014803200014100891140c1d00c03d082c2c012100081c000c00341075060b805030403c040c0c03005007521030020320f0a28040d90145800e007a070060600300b003c00d004c02c1c49442482c2402e00040c140446440101000801c1e071402199890f010288a070b10340301000e0701c031000b441ea21030030740c2c02e00b04a00030108440715805181405128140704c00d10480030084071106040c0c40c0c09602da031002c3c00c0c103240c44100060202816100361440c03020030b500045203100e400b040d8001075840141280713003140e4460300d4420242030b000c0d190340e0540683c1e4241680440d07240f001080550801d8440030303112885c00e040b0000341d084200031803450782d1420711100d55a03030300410011284540d0022074000f0050722000640104090100ca40c0c0c0602c0048000401401410006144500800003000350340c688000948203404030100c8400d484040d10b9218071150f02030004400e05070701034039011782400216404282200c3d0165002c0c400581c605608002180c1d2041d101d081103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 599476681 1250 599475431 599475449
    0xc0c0109080601060e040608010f091103070e04061104080607050a020c040501060c0f060612050f070e10030b042d0c0f060504031403160c030303060f03020f040c0c060e0c0a 76
    0x9030701d065074081d22003906010326020048040540b5000396a150000009448c60400030480b5560b10000b40000b44228031003210b140b408803198525a107004030f901021140901210461696565102c01c0146403600b00035418200c10f01010a4006080080700d100701e0700c030340f142c9a860701040806490000f26120643c89582850018001c05034403110b07909031181d000c03002ea120440545010f102400003900002500c900f4401c3c04d106100c00041c005100c0d40455064540d4503480760030841440d40112001c0c6080c01c00403004000003403800418982c4180192940d0911405441d1803003400280b2510000b10540748074400814000500e0080008124502400d40050314001028006020314800035201440202d043c00ca0104284101c42900d02100814440b01c4840d18105000141c0c134002600028500710010801058005001050340e40060940400841c00310401003c1c1840f01c44030710403c8891a07210700003a005000d440100000000546524100c0c4030500000383e401d82d00030694 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 599477931 1250 599476681 599476697
    0x8061e01050a06030b040603120f03141506160206070605040b070e010e060a0c141e011505041a1503060f0d08070b0c0f07150f090b0a0b010c14030c0c01 67
    0x40c2d070740c1c249904129052403c0c0802c05000e00383c0020024155580050003007a250600c296a90303900100685c85a060760301c2c20405a43c08808000e40a4001c860200c0c94030002d540000d16490800c01400c04000003000b20303050354030b00e0341c04280300d5041160103c605075182c00c244010401555000c03503201c4428a8020b8401d0020800207007004140200180284c60000d99190064440c90201003140e4002c6001c000082c52130701c1325950b40105035500c0040d195040c0301c00614400600403205c0c3c40420140c1058150f0424041000600000200107900c0d280283c1a81850325400100c1c80e91001e12505680c492900c08140412103100f805201c3c400e03c0030f8400301303000070811702c02d8501e5150803041080540c0d5406018041d284a03400d440801d070003005c10010104000c0341211190603003241030a1295001c20803004055580182c1c0040c4002c80020000303000b10111703844840b41940500d0441104066916a0003c0c000b0764101c10740c140d0000203005c3c111441c100245a2200030a00c0d203020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 599479181 1250 599477931 599477939
    0x20a020a1d071d04180b06030d05040603050c09100c060f02040b0f1312080910090305210418050f070e1003050c0d02040e07020d0206101202150408061e01 68
    0x90751040140300e40c052264042c0d807080f50402c0e07040d0056071108050302c100500d440701004a1029040c01c0d0044802c2039440300062094200801e0440c91114561102c038102401c0400c00e80280c88000d2040483e82d4041c030041c42d89590701960f1180c440800c1d00c80c903070403000d08d080502c19500b601c40f1a0580c18010041007040010301401c5801ca0344104070b19540b141c095011150007140694400c0100c110086101c40c1400b403078100074400f4440403030340d1000c4142c0302c80b01610744078024071002c0c0c0290055080e00b030401410782910640e802c0c41031021490720341c4034062080301030490f00c3c11040f540e84d0340b801c0000507200c0d01c41c0c00b900941542428400b03046000e000505143e501c0c040ca804150300d1f040403070880b06080c1d05580d220b03081c0403011f6480744d4a4006880c0500b20448851005110b08540c0d148800c0c00810320a0080c0c0545000c44185410b10001004004070414101d8006900050318600350500001400c081c0400101400a030b0030100c4030b01c10025001c6031401c1c050f406100c0100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 599480431 1250 599479181 599479229
    0x31905010b040603020f130f0806060a0509131103060901020a032406180509010b12071715060f040f080f010b030c0d1e03030b04110316180f06020a020a 67
    0xb001c80d1028900540e0f994219400b08009019202400000065200001c155010801014015241c0c804d04440c5c40d030b81e0350402c01528103503900c5040d13003000041d008071f041e0803110384002072860300030000c1c0c1c4241c034400c038007007031900408070744185080e58040342182c489075050085100720052030420603001200b07020316910100d5a4132451040c80381611310800c0d1072035400c80e154010030740100941c00710f40e91500e480c40c250344071100044d803a401c030344001004c6a0042e094400045825422811166600704d102c480044c4030703a80782c960080b41849800c003503180c01d1004001a02c41113581044007403602c1c202c9032408181c4007218542d6414441d00170b5154030000352500a9150403604100b1800550404d800b1080340c2600c000000d0240b00002001e160f05504540c008540030b0ba002c00076007000c00c004148500003543d0020800201c42d031030300c0020f84a106a8803640603074010381d0700529543c08090700001410750200000d030b00002820b0b415417070820324040081c0055041c0980b98803d0040c40c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 599481681 1250 599480431 599480437
    0xc18010803090103090302120301090f27081303020d060c11070b0a05090a0510020d0207050d0209151906110c0a0b09042a0503100503070e0a0207060f11031905010b 72
    0x715041545e6080d00100307141c800c2100d10441103003071005c82da0b00d503100c0381da20004e884a0b400e0342c4610380c1400328201c1c04172803074a8005c01045180c00f5010111180d65240041a4001002c40c00c40002292020000d40c1c1e45000402c1c4051043c0d00c00541c94901c800080c240380b4056080b62800d822110f0704110043c0344078100c0d0302140e031902d0071980c0e40444500060001c07011b41c0010783c00c0115011038020054000407255910001502164004d90741c41c0c003000422419810020b4102404802081c01a00070503501260410000c000d1201c0c3c0c440c501000c01001d1040c2e10140001d194100144010700c000e00c000240c2d82c0c0155148a43c0d44d08102041003107100705c240d1140115a50121024825140311100150180309140b030070314501d071040300501940040c0d883c10610b2001c40c00000e140d15000940e04100e03012004040e80607524130341e0344070007500b1800054400c9078035111060b41c086001c0c40b0342540c4103013000c1c01c17944070b061060b80c500c90382542c1019007401c07500e002c00501200c01c551080d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 599482931 1250 599481681 599481697
    0x114190e03210d0905011b050a030e0c010c030507080729010e0408031303020708030a1710121b05040f02040810060e1b120901060302100f0507140312090c18010803 72
    0x80800c0304e070740c189040d9004061845c041003008880c0c00e125449144d2160080031440031543d01070003203503c83c0070310035101da54600c40c150200e4052105240003034029800b500c5418010083c4a04010150b21072034003200a5084000301d601180003076001c068441c5000c6800360107080010500c1d8a020b99a01d0128031025004018610825514200300b503c02c00c43d400103445441e0503039403a41141d600203055154200040e1064021100004444c04007070000340089901032012071105851075100c504040c0454441102c12045241010400c1d46a81c0244006068250b03001130b622443c0c1004e00307080100d07005201c0d60403820400104450b100047ea90b541002d255801c4101040255070300300702c0d502c120310b5069040d10f074000c204010b048c3c040d40f220003107900076200c00e8a200c4001d00122001c2c0460501e91011a0044c07001d6004900b85002484100c01d11401b1249488101401ca00a4000c1107609403a01c0e1b0094011030400c0c103054403501b08a0051000113070055042a0030280c41e40100b2030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 599484181 1250 599482931 599482957
    0x91e091a011e0c140c1e0406060c020d230d08040c0b030f01060e01110615030d09081c030906051314070f0b030402010c12090e01060813020114190e0321 67
    0x204d403880e10705060050102d001c100408014000283d0b031044080880040c800300d01c150b00d00701d0000390b402d001d40b808070015580140500c86522407940e8400501580c04000b45100d04031001100603800200484500440c143d220548181b0f41440c080e0030344855600301c1a08040c0610a1000c201d80400746507040d6641ca00303205401e8134200004070f0b445544461094041d215900034441c2c082044116007407004020303130a4501c1c00c0c840c0c18065a60f00301130f00ca06240c1f45d0001c40c2001404c0c000210170390404055240104030b40750b458845506495083d43c0d0700c000c0341044140142002400012a8440446100513103031785440d000c0302060304121882028402c1800200240071684980d055511041c0c0c000c2c40c44020350452600144100380500651545460754400030a07840e01580041d1b01c13a410882984035510059801140c40328082080c0040b10b880603c0000340000015181e400607512070b68031860321443d0302082501d0f10000841c9218201a0f0050226258485504680c80310880032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 599485431 1250 599484181 599484203
    0x20310150e040b1302040e041a09061609031202030d0c03110405040b06071a0711060103110d020a0305010f0f0b0607020d1b0801021206180601091e091a011e0c 70
    0x9001c20411349500740c010303c2441c40054041001b1000050a6014500800e0703401002c0000c0041c6081c2c840003a40c0446083c6d105070005100240c84c45401b00e400c41c041e241201c291507a9a8030103030710302089081000584c001141c004418403281c0314264161505160500040002050b1000079104501429002c0c2c3d40b1405040010340b0362a04942080e9403103101d981008140504401c5a0403003598004005611100700c0d00304002c000405a0503290008480190b1900c44010440c00300d8254030200e070824112800000405d00c02e104441e00ca00d40000c000c01e056500d100c07850304482545040758400d500502034400540c031494200c0c00400e90007103801d1003406e0001da50140142250b4005503140d0b0000440140c24085440070318007902c020b0300d20042d00070340008200d800c4034044802c107002424850703041146801c41c0c0d103070719455040140540701641d01e840368807040e82c6401620810f5420100d000360800c0d41e201049007000b00f1078522600b0003045005005107071001058000d8140b1a420b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 599486681 1250 599485431 599485451
    0xf1b0a0f0212040303230903070509040201020c0307090b010e0d0519080f0403060f180317220b2512020f090409030905030105070e06070f05011d01020310150e04 71
    0x2c0192441d00c030a150991a220303580c925005000402c504c0c008500c1a201c0400b940c0008400740c00e880c40040e0003406000c0241c1000140070311141c00034400d13411841415049842901c0070f02c01c0c00040c100c0100c0200b14140740d05d0000d8842d0411040c85401000e00d0801e02000c9a4042054080354404003005c080480f4070b070418140e18040c40c05a601d40c1000024004104486036018155841c0789050074460740c035420400d104403412030380c000380104a144505010801c010014241e02c60844143c0c09452039000d6070451042c40004000c403052429001070041e00c0c029808010300c0b000b0306005100302c42d0b20518009042514000c0062801600810f0602842c1081d0003034407130480020300100030210860400500e8181340744106d900951034100441c50a034841c80e0703800340b41240508914640340c1e040d030720540e01e49000d59040d2a01e5607640c2041d5030110005c444032480b80e05090000d42c8a007030400c19024020280e0b40b1003503808410000320801603810002c402e45900044800007003884ca6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 599487931 1250 599486681 599486683
    0x70b090a12030e060a02070501030f0b09060d1712060f0d05071205151618050a03030c020a1d0f090a0c0e04050c0a090c02010e03210a02070f0b0f1b0a0f02 68
    0xc0c05000c1d0300c444017107a102d000f942d0000d000412078a0990b000e0158034502038400e81240c2b254501680c2202d205400107440d404d10300c0c00c0e018070702d1207030080c10800c280448040010b41c0010050742d000001c004184802032034050079121034044200c68012120030345030f0381c050740d809142c8540811280c600c04004c060120510018040d88a450314112440ca001590380c040d6606280741c002c003041400044690540c01d03020000103039032000d8101d200c0f05042d9202038034090003217441280c0c0700d0100f650214284600d02c0010340d07030031a600c0d030340911401d10352100c0d080b1100080c0701c0b45060f8807146410002c1012400c0c408101d44050b1017607d400c0c1c0340d0342015800d03d00440192074000d00304020029085101d0350086d500c0000c194000c1225400f0501115103c0c481e08508441e5641c1d49070100c01e060a640102d00c2d0003500d1140018a0111196100c608803000b06c4019600c03003011004009502070110b06007030340f211801c00c0900c501c1c1c0a080c44e03600a030181403d4402081101ea90034500540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 599489181 1250 599487931 599487947
    0x18080a02120c130c020d0c080301061803060606090f08061003060515030a0803010f0f1514070f08090a09090308070813020d0f030215010810090314030a0e070b090a1203 74
    0x203010308140c3c0400300031000c00018040e80b95016005214260490150a115548450300954041d070218510f03442c2010441d940d01c084c11181c003240c039111100100080c6144951001007089071034484c0750520744500c0182e041d21691100505400000400403c041c1400c800000d40c0d500403800078841e12085491100c2c40c0708824a5900f51040d11402c0307052000c840060b40c100c40d0070191082400d51140440328080c01544280b0841403007851076400e40c1402444c112913101502d203030301402d04002d92160b10500c075440c4d8090320380c040c00040400d46170030000ba400d000f0b08120311040c08094051b58008010450080c4510b040050f000085900000c1c4010104070060b0028143e403140c0880d828901843c0c02c06500c01c801520a41e442c00085040850b5030078102c410b010054240000c2c0d042065000d4074030356808a041102d1914200c0d4045a100040e60103005444400038a00e90080d00680c613000403500400392214090040c160719542e01d01143c1d040c0e400d800da00030b40c0b040b41c07454152032141c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 599490431 1250 599489181 599489203
    0x902030f010b120f0c090439061103090909010b06120a0501080f07170c040e252106060323150106050a030c0c020a06030c18080a0212 59
    0x10241403144030811005400242030603008540e00a0345510403107200d03543d181c5054807130401d90040740101686140c20301c295580180107080501d0060540e00000c444402134540d00702e103100810981002084001c0d0358940608850304050300380c9002e2203ea142d60b8015002c500303210b41c0314540050700201e000c1d00305e484219009000e050301c2d103100f01903085070000c0031030380c07010309901c0e040000400300e0000400e002c441c200803000e40720660510060407082c01c40140f191007244a420007448250300c5900c941188449014060505c0107000183c00d140480300300095144d503802c07551f00b4000c070600d05200d40318002401d800000051010303e000801f0348010740c80034211441182c4012500e03404844440c1000e0f6000d400d81d07030145c60610016030b071361038203000f1403001030014862300794a00e019900c103102d03a00150609a400781e40940c0002c80e0030b07083d03070803d400103511140c001040c40d4001e14128562002464480790903400c000328580c0d2f880c80e0802c00f0748180c00b8803602c9200c5030402c6c0301c510742c60 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 599491681 1250 599490431 599490433
    0x4050402160204020f0d0e16120501090b0c220b0f130308040306090b0903070b0a0216120201061703180913080f03010f0501080f0402012304090c0206010605130b0a03090203 76
    0x18040c1411790b1500d600031440c0580c4550400300f03410582c68020a000f40440c8141c56142c03d001d007001c6041c1e20003c00720300102d0b02036584040030320108407103950b81c0344140d0f10100320380e42c0e4040f003001c154140c5800068407030890161003010701c003c039403040c03e685091085c0c0c0d00d0315868000c40c440450412007980e001038842080000e011042c8084c9400540841c1d0003400710000c1900c27101d80d02d698901c01c001c0b01410641e089004100780c3c01e2076800034016000b001010504c8400c940c5c40301190740340752541d01000740c3c1d9030391030400a641d5a0741041c500c02c41841d004c0c504048000200d1102045044480c038466145140000d840c680031811035005950405032854a4100100604e0340c0e0754000c6c0a181149808042c0c001060b44c406c1d84c0041c8580000f00c22000c50b03451700c1e401902c41805a1058004240b03540002400000c00c81d0041d000a102e21390000c02c01c1c14032424003a0400d941a08030710304014080143e4031088583c42903550440740302c90380072942c64041c98821401856640c2e002545 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 599492931 1250 599491681 599491687
    0x12106051003050120030c030a090828091202060c150a0204140406030317040c12050c09010b030112030e061306020606040c1d2206060f02060a050403050405040216020402 75
    0x1028500c0c0a07003580d120f03800030460324a0303070260300c44501400c00800d51000000c00004183c1e0040c0c00c09903820440b001d0002c11840c1203079550340390542100c0c0444250701c070f9131040e14400d504158822013501b07240e801e022800d1402c1c0351950243e90715244010340107180010750340220754010004107031020075600104d101030402020180c06036005104a00ca00c299404030301c01c2c035250601c04d0804030380e45a00c4a0340d564201601142800c40010300075100050a401c002a0312081d00c001c00103054466006800d0740314442d41084a400410703000306400f980c0a02c010f12442c00086802092180c150034490003982c0d1b14000906188102c2009003940001b00000185150700090254080c281c01c641c141704020b054030302211301d4120502c60301116419800d0500c1e090600490001c0da01c1e000d007001d0b460340b1196805a0003a500a0b42c000030020350f41141003040b03070350705126080d000410400c3c24030503410180c030014041d0059014040c813860340090013040618280175800e040d5175000e030040d07403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 599494181 1250 599492931 599492941
    0xd0e0312130b0106020d1b03090308041206050901020702101b050a032105061302070204110721020a0b010501110307050d0201020d200f03100308130303030b0603070801210605 77
    0x4040c1a0088102c610905903000410a2400421100c410640c1c581c1c81d0040e81402e0405120038001c5c0070030075010300901000c0400802e000354011b0000c2c100080074580030020382e02e80740d411104010720805070f41c1d00c180560700050395404050807215101c3d00e406142001669141000c03003581d80c90003082c40c8a40c1281008164200c0c94000c40108544941c000010b20a441c00d815150304136400c80d80413210301d041c40900c4081e68060034407240054800101c0c4442a80240e25039030181009840717460f240007894030b0010010050105040051014045544e140c0d901c451180006014243c144008280309a5070301c4410010340c1c1c006070300803044510724965090064000e50081900c000b01d01c0c1031403000d0812500c840d46028045048104c2c10380b41402401e4400a5900054941c0480e41e42510000001c02c5c0e0081c007a0120b221144140403245140d4038024089a09441400b4010310040c820070015079002070341241103c8880c071480351210402e0345a29440258120010180340c40c100c1808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 599495431 1250 599494181 599494201
    0xf0c070e0126010903080103062f040503120a0e043b0d0e01081504090c0807052b030f0203130e09070b0f0a0c05070905160306090e030d0e0312 63
    0x1c03044446004448190307040b452254203841c20914060085420500104001160340c0e12140c1640d40080110081e044004501d03442002d114407a43d14181c404038080c0803518080c0480c054071018540001e00e000ea5504015155201c1d40340c50521941e030781d038011080442c0035a142e035030b40104036041e003400720f00c1c00c0c00041d50b4805101c0400c02a20480c03042d81d44d01c0340644a8940c19600c142c4602d0619a5031244c2c400300c461000f072103103401a44843d50079000490040606020700800001f8141141c2030506120a05420142c0c2c1d100492154051100f481f49604100030255090302d014203100600080591075841507000144c0364203407010001860703441a101c500d000709040c4003035441d10365581881502c00d021700c010b13440340c1c8a8100701089010b400380340503000c01482034040d200d86540c0c0305617881c1190f000b00c58000420ba400700344051901e6040c13282e1000703030118020401103508030710400f680d42c1c02004000d9210b41d03507881c00701101c1c8600300103030360480220740742101c240d1401c0d80e0b0035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 599496681 1250 599495431 599495459
    0xc17040315020c0c010f1b050c15030406050c0f1b1f090b061e011107120605010e09120a122712080115080711010e010b0a08030403080f0c070e01 64
    0x120124010359506025170b6100309501055003240356101c1a00160b28040020300040003042201c071841220301804c030301c6d15640d44611100a5008099450b890241000c4d0160b54008280f9804030100300000031a03060703400103403542001d1188200c002c615518903614508415010781c94145c40c94500d0060041c80550001c0281ca44140c0896145072680000d12000088041d040c8440039522a008004c2e54401d80e610b1000c5444401160a040d0b0b40b26000101005080410b1340c1c004c0c0c5440042c4049061180c0340c64010070300d43c00500340a00c642645600500540e084081040815184501000150381101c50312940c2210b0068290703100d518012492003281034103c9001c0d9011712a005000d01404000c0c0c100d0f140ea001e41c20500000c0340b400c590090300100f000701840010608004d140b4400d00c00c02030000d09c49000003410380100001c0003910051b960200d8001d9000300700500c00924082c0507207141c0c00c894a0241d858030200702c1003504020007900070389030b00450100000b8000c00c0070001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 599497931 1250 599496681 599496697
    0xc06090709060801020f09042304050705100e01081501021608240912030c070f0b01141e060d06120b25080f0a0e0d080603060a0c0c1704031502 63
    0x800c00200d5541d22205090313015000e80406c44038001d109801d01410a46c000c03603103043c0385842c02120454204022070402c0c005813416034090707004180510141c1420250b80c2a159100e040c40c00190112800080c02501c00030202d03003c4410700c0e121044664020003545420080350417003140d98940f1800300a0b510303544600320341c0503030f540c4845090800310f100c0c0b40d0b9809035140300060b0081c0c2e007641110240c0c590028240c0030305800200003034008111244080300382148220460440c0b9458103520000a44400c2c050b10b2054402c031000d4110301040d5807121b203502c50b0070303145035494034a0691403000074017203a48030140320b622000011040022104c0010304c500350801400216810300000c0c124641d4500d0700c0207000c40c0d40d03000031500320b1075201e20061f070100b4a5100031a0300706130146030034105500d8a60074030210700e14105102c0103242c144410380e0700c00c1041d241002040c030744800041c1a490301081c0905010200050314203080a908121406103400c0308950b5150883d0152800080d800000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 599499181 1250 599497931 599497949
    0x3e071b0b09010903290406140c0906040e04021c030519020304050109180603210228020d0627030e03010b060d02090a170a0507060c0506010e0c0c060907 67
    0x240114841808a066034850401a03544000d400e04543d0f51020700e00c60311040b00402c01150040b0500300070040501031250384503e001003120700c001c04000080c2540902070b900c4100e0240105401501d601050f10101c41c9032010504443e1100e002061241800c1c0e8441050703908112005000c0c1600003000300500c1281c03101c1807180540c6180200d880b8062400761500045100104102c0c0c20315240303900d00c1481c0e0a8030b0000d840d6030703640d813030220402408a0702800d0078080c140d80b80d41303281c05000755108103a200440102d03003c03a5007000e5403504003980c4000d11900521030310340140200303a0b1080349501a041c3c207144a060080c0719941030a00b2000007200003402c0701c4100a42404c1c107000d400380110002d011941801d00030021407001e0b41080b5182a00316400b034800054400e05400004040303004407000d4411071007107003440ced8207020080d0492402d104100000c1d400140c4001280c0e411600f01c8400da4103079881c4e020010380740b440765040306012841400d0600054440104401049641c448 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 599500431 1250 599499181 599499233
    0x6070318080c0607141009140106050d0c060c1b0e0609071706041a06040b04030b10270204030605040b060901080706020c0d030309050d030b030606043e07 68
    0xc0d040c80d501c0303185030341842d0807840070b00131070b80040c160394545040100210107403068060440508412281c030301009a42c01544a0319a00c1207007070030720588003e0b0100350340012000d40e20351103030144503070740344a20000c12503a80c402d0024040f000c60351096070404078070311018071a81c0758003100000c50191156803190302d190012424070380c0103140c00311103030a030750002410907680d18042100a1014010300b020070f40718250b0943d5255038800c002d0010308441c100c03282d101d6045040c0640c5171100203007002182403038104240440090141c01c0740100d03002880c00156400e490784901301070300032580010034480c248018002049000000c15100d51810b8500305556070313903a07516580d622200d11401e0302607003110006026a082512212a0712030090038007080d410196503c81d8505460800030100003640c0340112096440c0500400703411180c02c5400303100e802101010125003140c43c10307490440c0442c03624441c00400c2d14100c507201145048410f143c54000700e042c9136000c2e01203c40e003803502c10a10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 599501681 1250 599500431 599500439
    0x6070c230402270f0301020d02040906050a03080304060207020609060705010b0415050d151d06040c14090613150b0a0e040e032b020f0a0e0d02011b03030b06070318 72
    0x3482900d658564100010140a51650003206003800c075158068008070b0f840054132482d102400144a16640d9400059031030f40350042c0203040751502c0d04954494440702c001000490b00300800d0300d810035004000103984004510020741c251107880203060300f0060119005051002c1036001c800010b1085d0f405020881c456010110702040c039005055224110012503404146481c45c14107980c10700080020707412110581d4060300304c000301ca2013203040c0c0c000d10401c02000700c080b4822008205106c804d4004030320b01400241040300040069001c0e00c2d10195441041141e17401080d03020f080700501482103610b441c01c2440170340c000740d41c85000c135100c0c0003c2802402d05100f003280c0c00000030055424090740881e51b0319403110502000720f0340500042268940d600750b10050404881659115a0300c5140601c00707414000b810400364401c1060f4421900981d0b00981d4007000c1071450801d04200294500e81075009094116420340c11007004510340d400c0607041175001d4800c02c49103042d00450740d0350f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 599502931 1250 599501681 599501689
    0x110901031212020f030103230102071a0901180809042f0918150406081507050c010609060e0618010b0702010804030c0503031e0105030304121106070c23 67
    0x1080c4401455940c41400c8a14907502c25180005258424078003d4608181c0642c0030340c1c1c6800a0b04252807075850141001c041c10f07101802e0030a01c14201e0029410004140c40d64a4007503134002900705002c6a100010310a1070083d80b04980440345102078042000803414112503540203848103602403460848203006000641c0b01d5062034030700940391454544e09016800066800541240350400c1c034078841680b52464456116105064000c0c0420119101d0800c201c192401c660105850350010040300c520409500b10850b88014039003030003951490500c540d40d005148951040d0460f80c64440b021420b00040b040281c084c01c0e04030703080c1c0802c0c041c0c000007100e282400c0c411070100c407800308070180040d4054041d00c1d40c482d009013806c501c0d5252580300c150469004441d030b10035000c507294071002d0100d041c0d1011409840290001c50920342030214841c107003a030b100005030034031801100300c988030f0351020301702d98482d07034407803803003000c059660700031365402440d9405810900038005100016814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 599504181 1250 599502931 599502949
    0x40b030c09010b07031809020a0201180201320f0d060f2105070f1202010201050a150b030c0412080703020d03090b01290c03120105100f110307060903050711 69
    0x40040070aa4606081408154000c0034200c041c4007101c100344d64940842072010004240403180075039114a011030007170840300c03804c1c245584107200060000140c0d0b0b010788041c8000301418002030b4140c0d031029a091503043d503500000305041c4001442c250552828001d484080e18544091007034985848000e16070307031010700071501c0c00580c060142000310b808000c0080a103011310145d48000c0e4540c00e207816a1035135500203c1c0e600c0c240b00c8040046507424420039500102e507030800c00015040b020034824030b18481c482c81480401c00310208008201a034101c03801082001034205440c40799140658664010131403c2d4003601442011001d002c0c00382c01564642a80001c20b018640c2c2007545101054520501c5007000403605008001c821004200506080021500440e00e074001c0301240084903505802c640c1c0114200311200d000c840d0412a04000610f150500391003002130b6000a9295000c0d008000c1e1400303040008403810300d03070007000400c800d074061504809591289028852851 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 599505431 1250 599504181 599504203
    0x141006170d02030901140903030426010510050f0a090504030206010e0703020405060405132009100203040503030d2004090f05131104050a02120a02030703052d190e0c040b03 76
    0x40c02c00c10030004c4a40c86a242d000e541035201d4042420000290080780c40c5401039007210601c045880f03581050342d0000d81170842140300c0400240441d18001d400c03c0715a20843c0300761400b40a0301c030b1b02e503005641d032005400b0142010000810035890300d0704000303543e44028494101c2c01110040030406151080c02250280d8201400309454280340000b800040d9540c2410b03c0465a0341d0581c041100c2c10007120094030f240000651a11000c5a0081040c8c0324088038424081d544100010402e940303000c0280d070000324009034009201e44c401c080d62007030314491341d40c10540441e0001d408500c94440f541300602a000810007000107545403540b00041000e8080301401459000b25110000d04d01600080d03440300c00e082015041011128102c8d1010717800ba039910031503503004010845860344c9403151690014000240100302101c483c4441c44030b8100080042c91200404002104200c103210070004141d0003000400141c2c580d000c000745c03030b0580c03c45814403031030030b01318403140624001403225848 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 599506681 1250 599505431 599505433
    0x6071b0c030b040602040e07080907060504081b0a051002010c020d0903031e0e040204170105060303070b1b090603090307020f010e15031302060c0d030b010c1a04141006170d02 77
    0x12034290b4540e001c040c1002001224066020480410700c02280180035000c2c0a054490010300e0400203905c5050600130b400c10010000c060100300300e0000002004c850362501c001000a2000343c0794040754120755250069a00140c24080002e00c0f581c0c15440440b02c0d6a0a6080d44c0c8400002c543c1242d270481e0601c00607000802d1080b6030f45000085d2050340c0320b07a0102c0e003080341c0d4980b4901d010a041c1d8000341d2103010a4a031201540b1046a001e0203030755845181240a1841c00d081581e444042d044c000d001c030604031040108403900a60310b030085a160b603d00500590302c0f40f030320900c17081e66a40f001104a008904508603840709500501c1c40a1000e64010810f0315a0401d14005076040c1c2c100402c0600d40d400c0c3c0d000c1d260702503216640200592a0560068090a8440740e80541965a000c2c45581080201400030f00414502154402450441000b40e000c40d159400c01e21110081b11100c40980d0141d0307140d0010400c1254003003000c076105181000c4006c415042540d0b100c0c01740d0507140c405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 599507931 1250 599506681 599506703
    0x1d061507080a0306050418020301140708040f03020f060f041b18020c280317100b032d070f030504050a060b1807020c09061f23070506071b 61
    0x1842800507002c41803103450005242643c8100007000e480c102c03d03903d50710a050401c2002075083c02e0003040030bc5d4140c1c007030307401150030034900040c080b90b0020000741c000c00c840c0480204152003032201c1206660644201c500908001c0e403c0104c4400a4400300d132000c540000c048511200604040c0440300810000c86070411919240c0010758400824420a07005114400b2414800c0c004c0b0545041040a030f200040c0c2c120b80b8018080c411450f2002c2c2c4003000150400c200040485018420b494001000c2a1640ca84240964500c0000ca4601440601d11582084102000d520442c407a04c120f594031019150002c80036030450703034240c81c0640729421029807400450050342000c4100c000185c07120411840d1075400c5c103980e01007a501400181c01c000700b4101c0303c3c40d11003c0320b50090b408584800c08e804041c6d00400c84105a10005005e000200000f600d01585035884294544000f8054a507035443e40e00d003150300c561080310b861000c00d0005854500d0303e02c180403407558003903114203c429 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 599509181 1250 599507931 599507933
    0x10506030c09191b0801170601060c060e0105070c0c15121121271c0212041403010c05030105060a050702030a35130504091b1d061507 59
    0x1071035240106024069242c08042c0300c80412079102e21568005140203004c40f0b241c120100801c00a0181c3c417040c1c440da1010041c040c0880c001c50700504407805414020601c180c18079244015004ca00ba010302e1039440c00040200da01d41014110801070711402422800d40d44400700d43c44292a085c8c6004002544848902d4010800e03038400c802e44e0003d8254107081c201ca185a945002c03c40d4000802c0d1a8200c03024001140c20f544070421641400ba0881c0c400003803c0e07046a5590310300700a905a5440d01e80c4200c0301400c1c0240500d000d807c20300d03551a55504e845e200b00180d40307001411610701940c40d121501d101ca40c0718600380d070306035007004007054030341b1b0604802210560812007042c2da050082c101042c0001c0c0071550520000070b210101c491303c0c200300b80e190f6014031254020004569004010884c00d40b0301150b1a401610000c0f100042d00740f4040c00d1004000704801200616048014400b040c801c2102d842240c07254100343c1507500380c1d0303036040503c20641022094450046002e0040340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 599510431 1250 599509181 599509189
    0x60121021206042a0306020c0715090e063a140f060609040305040605070318031110021b010f020a050a03080912040602030301030f03030f0906061508090c09180303010e100602010506030c 82
    0x8580381001c00221760f5002e484000c4004030352b04c06030940001c1071021a00704840380c852031010354403a0040f644084605201d403c150b05c2c80d02c05030300308080714a201030348200c4001c000280e88070058102203445030004115400c01c1d5141c2d002c2004000602c1000300040f140d01d00f02e044180b040341d03d03a6800c0c1c00c05107440c606541c1c035009440114148160080030802407041c0000300002140102920381006241d403060200d40f050f00703400070f01107401c080d03c000c402d10902106882503040030728000000078040d560880c100b61080d0390040c40740c0103a002000505501602c0c2038021310440080e500e4201c0c1354000000345214611900006d038009000410116009480300a003141c008e0401040454078144128210748001404459540d51003501f44400d00074081c0340c54035000f4605150707100e42015042503648001080300144104402d0340001d16182c03110076000032151206040b26101d584504120810402c11201d055000c40d2000340001c2d62441401454001c05010b0082d200b0045140244 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 599511681 1250 599510431 599510437
    0x1e1209010f050c0102072f1f0e090a0b0907020d08010905250c03022e0e0a150c0e220c020313060305010518010305060121021206042a030602 62
    0xe07018007005201e0950b0004080c0010040b56104250300344041c9410140068a42c80c0303019103a2851007580c400d0b400a0b1208400042189002c818001d1000c81e00d2400311400f08804600d140c20036250303002e0006106954214038018501207a40f40f005584400c400c1360390700003180704000001c15070001007011450035849150081091510382e1490320300d1099040046150240c5c01c0006410f03086108189079042c012034040044d03041e8a00c0b04010b42c0e5a8141c1d003000e00001c0002c0143e910725a4480e10102005155001c5520406606030b102c15007401100400c042404c44001c541004403410342c514154103c40c0307624001180d00300c10303010300113441d1004004160300401544000c001e090007000c0245508030003041c0c107507008160766040000740b11090302c01c0050880342c041b4082c0103000103000412400d055501818004003a0745030b9244000c0b00300c01001c0d01940008060300889448400464013921071030251910344d4000c41b080d01450750104a40320f400d450340400c2041800007a46036001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 599512931 1250 599511681 599511707
    0xc03030c030405011803020607020607050306010e091009090c090e1501090e1f061811160c120b01030201080f1012170307020106031401152d03051e120901 68
    0x1a5078106170100300039482d201d81d0706071b0141e48100b040145942d4108011540205240f61260035410300d0000644010040c6011621401c0d4040c00182010400b5070110300500c2c010b01d0500c0a54028240231044101c00d00881c0d982d1428804c0d1420302d90000184804000c04034440403403a68a000171090080400b280186246e000d0240d188da02e41041c4107403071f0814810401e0000303c00d0700e41444241d810845902d40800c150404540444141e05442034880004a0707890103040b0101e18982030300325a5080c0c0143c00e0841d8811000d07014880f82840c528107882c402e80741c03406c160300c89007100820008201c96000c017007912413105003d0f29030090303031009445104082e02e0843c412400f0000303540d81c204840d0100143c2d52000e00700184205d4550021b4203510140c02040101032042582455500d14054203200800b0440c0619000b21601249040c8004071000c11004640f40d190442d02c0386011074074001c41c000c240790196010280881c44024800805203030900d4400c040380103688184050b42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 599514181 1250 599512931 599512933
    0x503040605042901090e0f0616050f04030606031505090a080c120d090209070c12050a0e130f060b0909060d020d0b07020c1003050702030921030d021c020c03030c030405 74
    0x10720000140f111010b403000501030655040c1645c1084260421500c0080c244070007544400740341d0714802030100d03070305411202c42003120a82000101e0700703a40600c200a0b000382d000700000350020502c50294494000d0b2031041d405545075001d100c0090007030311000d880309001e039081030041e85c0024480744000c01c1e030701040ca4165401c11000ca95000e440741c00c44c280d902140c5803124403400451410802c510b5003d092805c0203144249640c8641003201070b05802801403103030006020480600440000121442c01050801030074810070807080034168848007131984a00702000460003c0ca5601501e8030305070003030904074090340d44c1c134100214124035000c141e030001c004d404e18002084246281c18030400158005101d1644d20509004032b50403901401c3e41014541000e120020307a010085a0503058100d54541060080201e1100103401c150500310442c400003401d00700040c9103070050700d41c403c03038842105400310400c2d031b00005038070445500c2007030340d0010400215151032000103544c0190007a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 599515431 1250 599514181 599514203
    0x70b07140c06282a0606050d030507120504051f020714180a0219050c0c010f0c030e0102120313020414060603010e100b0d020c2a04020c0c10050a020d090303050304060504 75
    0x9100c074001c031003082103581368414140c03120b8240301c903c1c018440100b10075a0714180466031510300808a004411004140c001c50b075400e9051588900160f401901000b4410341e8469814102c1c41c1c2064044030b84403000d40940c220025291034500302c0190a00e001802042501142600701e9403109401070607126031903420b2081d04164803241c01d0301700d00c2c00c2c4c40b43c807002d50300d080045800c0d292034184649503041050000c45100742d203600c20aa0210342d039042c20040f0010084100603400d1140003015481c5c581c13404801c0011001c0c0d00c20301c86034424000d0780e081084190700c14282c02c05010860f070301c1d50021010801004a80303c10180281d0240c0340701a40302c4866103990704a925544003007502d040a980125000c00c5000c0d061003900c0d01400c0e00c01101e1000c01301d1502000c400b40c50062410300c19a80442e18400401c020b004805241800408d0b082100b1403011000d070654000c0c83d6001c00502c00e10b03003860310f02806401e0a801703682d0162541d80c00d550301d40e0345038405440000c1007240e01070301e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 599516681 1250 599515431 599515457
    0x5060d180c0f0f0f0503100e0312040308060f060c12130b0408070612020901210e16030317070e100e04140901051302091602070b07140c0628 62
    0x35030500300207001e00d07070040301580e45014404402d44400c0c0d013121000c034240e9001040341d981e0003d100c000b900d03070242c0081b40c413005240c07030b403402d50203011480303840546080c0c02c1004040d4450300c1e00d03102d800c0849420052610388030500505015807481d00c417096101030181410140c4800140c0400345240302d442c0e21301500c46030710020641041d400300840d9400302c402031100c01d4015960a03407410360380c5001c50400e00c243c40005c01d550503911062a0810740342c000700702e01c1e07092600103032250529602102e000d80192207520f020b01c40c0038072050700051040241212042c001068040c0282035540e9034030400b4052004209000c10b855035440140482d03101d15140c039846500502d60681e0110340b02c1c02341c9140604429094420060844545240c03940c0e030340d00107980c0c8041d040d07044174400285074211407402c4400d80c94004542c1208040e001c01003403040805c07940111415803c003298042d9542c2d081204240401c0b1301036a1460b100b0502c0292180000c1c2248400c00c05000b107013850550303414120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 599517931 1250 599516681 599516693
    0xb0c0714030315060f0706050640060806011a071e140601050a0b0708041716050a0b092e02010221010b0f0319050c09041505060d18 58
    0x680314010498101004000240081500ca01007548043e140c0600d80341c00d00d0040301d0940300301600103183c142c0d900045405500c510700f05a00b12050240c40986e813604081c90a4681c5030807070064900910380710703142600c0c8081c500450080320003907401400240d0800c445c030140d0070400025071034584000d10521007c01c003200c0280841c00d03200e000e0505e0020850410301440841d40c00405003991044004001a440701042071049403000144da0342c440c05075140840c0c0c00d1203540e112200f00703001408020710111010454008d515149249035611942da136090000c04e010324410300828400902240c52241098104002120140701c50340360b9554140c1c862070b802c4000c00e08550010303980801e02c126034400c4640110079010000c91104103940c503242c03910400f0f2003201d004c204100350110100ea4041d0742100300340c0e0217a12a51080c0500d207095141d100c015000081030a00c00c03070a10901c50380d0080d040380c10b10241d580c007070f01c1c0314540452010040003400240c2c40c02c8001510600da060007040c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 599519181 1250 599517931 599517953
    0x1608030a0606081006020706050d020405030703050c12060f01030303090213151503060803071424150f0d020f012706111b01080c0f1305010206220b0c07 67
    0x3a194800003281c9041039001040c02c0002450f5500398401d12900740600d5400003101401c130f174034503c2c048d43c2d40e10001d60b1301c9010340201d50010341c2510400e03402004010012030080892f003001d5480d000d00d507980b030203d1545c0e943e05030b038a00051402c242c01030001c01e200380c1042407040d0002d45a54000d03c0c1d4410700c00f0880302102601ea0100726001c40038001d5800901d403210507031110780350600885007844082034032445040380080c036268645140703081201040c8030000c103d0124180303088001040b20007625030b41000b00e9081d01d0228141d280c034142443c000f02c082c4920b69004c0c01c80030244416074244241c10303165241040c180244101c1c101140e100c0070344180c203071401c0d01680c0c00b5544d02d40341c80940380491600e0040740542206040c0090b034940c0f9010711403607204c00d2a101048e5192500c0e070030800e00c600d110341e9021110000740d2001101078130311201c0482d0001c1c1d08461140d503546803603030b00c2c00c0c42d070b582a1900d141098400c1c0000c540b8000c04950485002c80c141441c4c0780c4103a43c1c81103021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599520431 1250 599519181 599519191
    0xa03050d08040302120403030215040c0b0c0303060109050909030a030f151202030c0121111c09021315090905152e03080406031802030f0a0b01050d0b010506160803 72
    0xe5079a00c200000c1540c103000c100992240d410641d1709060035079a010751035000303070055200302100a000142c240001d81c4108130007080028195a6650a1406841c0c1c582e40203c03066404502c401200051904040a1140c49260140041e5042040241003140500034480104010b00d0700e42000785000c0b9a04541c1030700901c3e010454181c012001d206050030900080d040c0d5040c040c62001407550720600818001d07440805041c0000c4040f49016822105d000b808401c0100c50604a89030007041065402001c004d8002c4900600640e041a024010345020035604017000c40c88100030000343d1016045188180e00c140f05a80c0d0045007148013002c00c480032180340000c030000741354459404100081200e407800c0c0a40303607281c420b0b045460300e494503ca05e2052404041e41c514200d840c001058500d42000c5034014103882d09801d02d490243e945d000e05041c20b481404500000181d135103880a01e6100c02d42e84102640c086030710b40700c04c00484d0b800860a015003001c140030301d01c00240c4500004e40c070503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 599521681 1250 599520431 599520437
    0xc0f0c01060b042c0f0103140f0105070903140c1c02220912031415030a0b0429150609011218150506030c100513172505010e0a03050d 59
    0x4007144c54a01a0112800c8105080c84000003445803941303404404a054075000044140d001070000244c600e0a0503850b1110855483c06013409030b800d07401024103007100e0045410070015480c100205840e0048805002e81c8121140401c001500c600002036100f240002d0050002c15518100003184c01282c80141c800c195881071107604200890f070341140041e0b014a000c000503842010b115005410203045000c0d003500b0745803190b240380d40030005018820340c86030029820381800e1500c07030ad0340c02007178084220550090894241004440000314895031118682102410700e1809020b4260710103100c1a042011500c0031460405082c015421900380c2504038080c40c81850610f11301c480b0080400c01000c50611050120700d540000e0f80d040c03220411a5071942146422400b0340380352080d100c03046100441407800080641c031010081c2070700910001070b5585120a11154541707001c9003c02164510304182d403e004a502c00d880070a82c5500c05095044507945a844441c980594a1844000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 599522931 1250 599521681 599521709
    0x7030209182b08100302010305060627010e03010e10020304080f03070c0506010506070206030604051008011104030c06020f2a180a0b011b0b0408070b0106180e0c0f0c01060b04 77
    0x2d11901e41000c0060010039103040101410702500d80c49803100303a80700c043d041644900220f030496491108807007c003540300b03680407a031400310001c10041c000712010540c086501c000401e03c07030341018001d001103410a040500643c6206020140080d080500103460720501030085406288680d801140584540c0d1a0014440100e10b0032600d08201600650b000300401e11010005840d4103007601e4103d0701c111030102d42680c8094400d0001da4880c0c1c805c0400c0e40c00c0c2840003003850a10030042c011740e4022030300703002169110103003642d699440d00404041c07680059404200800401f5074207041c55041920b4102c50402000011003914541c0245131414000c4070a125542140d4807801751600310030b0070030100c0315a500501040d1a60a0540642503098140c00101004158030880e040d440d030040900c1c1c0e60756107507a802842140c0001035030711802c0384400301203409504504d60900c640518400b0710300d010007180f070724030b0a9084540160a10364035640003064218401c006000540fa800c0c3c1e503100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 599524181 1250 599522931 599522983
    0x3060103230304050a260d051305061219090206040e07030c0309020102030f0f0403020415084c29061327050f01060e010806030703020918 61
    0x10924001c4600c1d40c20940c810401040710303440b0b400070701c000c5405105584498088005180c05d40e18040c540c0c035031071401144c0c1a1a00e06800801810303d07441140071050301a0340300c00900807240306441c420240c2d001c10a0004240728800300501d140444411400b0a01e500c1ca680880d8154110741c1040404a9001040020166061080840800c0c0a103014840e9009a0300040d40b40c1c0300381c020840303c071440020001107000805003218000d5a0290040104d40003041070034840001c40d010705902409959142c4805030302144003d505408034046c600ca03c82c42401000b403000e05600c0203045500316600040800b250984074507402041c10454030070b04110300d0b10f46801d0440c884008503200d010300b481000c001d6a1404800419195803010310301c0c281c1642104800c4c403003d0a00700815140c1040100300341010038569483c100e40c20398a50102d0038280000658034040111809901544101e5040001d450054a07003034204549a120302d000d5035282103414149018140b280031000301101002e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 599525431 1250 599524181 599524223
    0xa0e060d29060306060d0b07030e032208070b030114011b0302060f060607080304081303120909060f03330606110709150608040302012d0b1203220503060103 69
    0x41d902c2a412006401e0518001c00080d800700410100a0314014070040000d83c058020b034442e005001040c400c80c0e845000140640901c01c840b141404140e441000c80003480035400140e54080e5512110300c01e065a0130719410349420a5048001410850004008000803880e4218017600c10f00907400f07070941c0e2410303a0800480d8403005d003603140a0703203041040d44007048103601500d41055101442e196148042c0b044040e074035019420140418050380912150381350082000400c8800c000001e100030f80e922416041c85000230311000c0d240c4007011209049140c040c503540c00c21404226a078801c0d4491041c4e04400311013440d08401c0208141c001b5207000c0b100d003004010300902200f0024401c00100b511994101215880380a0a0000e07450114080500070f4010101d500d202201d580100049204a000088007214500003203910b409048001810410f24141d08951000c1c001d5107004100200c0140c425512000d90042d542c2000c0003042c00d40e01844068000c5000c0c0030740050784a80403c0e51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 599526681 1250 599525431 599525513
    0x20d05040b070e030d0c050111220905010f05060901020109061a0315070203160503090d060506040b01030c0504060e040605030d03050105090c09030a032106061112090a0e060d 77
    0x880c00e000440040e43ca50b0341d40015051200c252900d40b0046690312484c05901400204401c508115000300c0c1e07442c0c8005400000255184c104100000d103140c1e034807400c6048070b000b8041c81e415408124810722003401c0c0200140040407041c40001510601620b421044450301a0300381c80340c440c240510221440e040103c10b000c5503040d040341c0914201428003030340c0c0e031091050480c025041900b15070144442403060b5020082e010742482c4c600d42c2c031850108006d0004035500b6102c1d80c40c0003610f40302035203c0c3c030450003050300580300e10340f034141060f20035a201e40130704081a60164407003c01098940b804d00031416441d40b152404a4694144410020b44030703001003d43c00603030000c0c00f40081d542d0f00000c4561003070780c060902c046c0c64411910203285009840c84000c62090600d0300c0011129804400d4483c040419001c1d6040c0f000464490070040c4074417034103e0b070b010100d02070611a001170090829000b4400400380385282c40c8641d115103480c58450003e840c86041c4e08203190b1004d0642040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 599527931 1250 599526681 599526691
    0x140d141204080c0613150516060501090606050a170603070b070605040303200319090f0308060f030106031a0703091202030a090b09060d0b0406080a1b080706081612020d05040b 77
    0x5040c111210340c40d14010038a13100701c900b0703442c0f204040b12000f40034408407507592030650403840030340023030b402c19102a00080c412803e8451901400003411449001550720b0341c4619030301d01c440313010f00111030118058040c0c40350340d041c00783c4400003aa6070581c00003000704510414000c04d491900b030034003034200c0b038040c85c1408407151038108014100c1d0300c5004403170748801851452115803103640340c481d00504114000800b500b002100540c00e058110344018880e610031502100000680ba06040c00d8904901c80141009818452403079031000488c00d05901205c43c0ca03000502120b56114480d21107810704001001d078000143c900400766220381d1200103003140c0c0d0a018942000e03407001c18802c1c070a81104141469984d284a22550342c0c5030001e80c014010b0004588140d41542070500c000840c601101c40d1820b800c890006420001042c845d0444080f0f444180f1540d0340c0c01d41e400c5086608210f48003c0041489054140000c14400b40020141c0310318000395601d8603191818142e500602 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 599529181 1250 599527931 599527939
    0x925080d3c0503070e06030405030705010f1b030e030f040308040e010906140613052713031b0f120509011b021e0303040b0309010c08010f140d141204080c 68
    0x4090448000c20480240c0c40040c1c0c0381240d40e03952502c4c02220303e440880d0005134410000001d0000780280080502105170089000300048000200c60404444040e070300315a04100c0c4422055003180079900c401d012486010a0b00d250203440746c10700205602503002180d401101240501009151100050241002d103100304203c50810048041034040200402c0c4a2100014030981d48129014417a0091a0180c10403038403415002c11000d000720100640c1005680000c0014000c03003162100d0504071345c0684a56803400700080608501d00d00d40441074802002100c0b10b0400030310b0601c1004100c40207552116241d00000000403c190f048221104401204444150150780d503e4411184403001491809003038240c0e00201c5d0460140d680000c98414010042060f03168064100c4072412000d0354840181e41e032203588000e50704869010742c2240d103100c0d26084440d41404ea00c841c03a002e008a00740d64016a400301203e2404158003a1208502404503041042d02400c008a0240400440e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 599530431 1250 599529181 599529257
    0x1021209060907170a0210020f210d09051c0806131b0513030203060c09040b060a0c06270f020102061b0304020f2403010e01050105030925080d 63
    0x8080c603607039202c842c00344c50001191103102d0805000700304405042c0701c0c0d000e086014101103034140070b5256645102c126449008568415030b5a01c68641d101c1d8024218801581c18882d4040140008000000c0c080b1058410b1000000d000603500b00c100c02042c000d42d03548201c80c504003062020554807201d9032440e40c0c4c03c0c088101c01015100c0c0d40c960703140d25907140185d1290b00030441c00c02c0744081540040e4050007940701344020000d0410040c01d400c1f600746e506200085c07011050021604c110184907001414403100000040c4040e0049110b51405180032440b200000d42803040ca4071154604454092481c0309440440d601071101039440020100780c00c240e0102e1807100e1081303110080000348214084141100320307030f68101c0d9101040c4d07200b482078071103c41c10018103d003540c420302510022000001c00003440350b100d03500301e034801c0042c02c016100f20322000034018044000b100c101d460450240c500420030083c104075903900701020f40d03100106080d161140400d4200000b1403a00001c00103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 599531681 1250 599530431 599530441
    0xf0d0b100e010c1103032709010b13060e01170106080f10050d0b040c32032418030c100608012d15060c02090709030b0c07060209060c0102120906 64
    0x3c80803860b12103402950144a000580300001d00b14465206c03002900c0304287c44802031581030701c2e088250307a0300950328800340340d0700c3e2000c111640c05980c2c001d443d1034851380d0040c00110301c10307800c0544088060428074180007004e803900e041014242c020600060b8503004000c5a4807035009060b13001790101804811803400c4c1004a102e030b805904001c0c0c103180e00b203000700d1304010310b0f40d40e00c40080481c82101c000c0017a9450204501c015108107801d24200f8980031940c19103004120701030124101403800070030761403000009040d07410051442a1501504204940d2640c0a100500a409040f0098685034001503080c204494407900308541c01c3e0324143c140781c802e02c4103580e02081418810404419607030b401107a0070140c5486a140740c0300c4a03c1510008003150400003507010103100f254054000c0e6260fa00c1120700305e00920000d040c0001c281e01003030021001c1c00060084074000c1001610f80f40d44500411110b0303001901186450390f00003480040c1000c1c1030542c0703411082c4440642028140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 599532931 1250 599531681 599531687
    0x103051f15020f01090b040308010b03072c0a030804050114031003060504020d061a010305160212090102030903070e010302030609060708040312061509060801090209011d060f0d0b100e01 82
    0x105015010079081e8015090088600030007045004082c900000d0026401c03d141008452809840c1180443c005800110b00034240c08141c4c2d102c0c1070940d442007418001d0011560140d1140102c1908840191002080584400c484100914056100302d9559850306000524415480301c904503c02c1d401c1c401d022003448040d018204581e0414804100d079140e034000107007003c4200c413000b8241d52038402040308004401c0103180150750240c80c104140e9890491072107115480d13490b04c0300182c00141c2912038400404000c0d141890040c41280c1c100742010303010031302d0100385400240312500244010011031078104502135002a1903c060417060410a1003d8040741014000405101401003030191444455101100501040202c101d1150031010082c003191241d0103007400240031000041100300190007194140181a95203c0300d01c089c0241c198075000805c82510b50040081004655040010001c1c100c0030f890110000f4581c40c2500820131550300e203e02180502c220400306058503a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 599534181 1250 599532931 599532991
    0x810080a210e09100e07090608040f0c090f05150301090201052b020a030b1306050d0f060e1c0206060a06080406050601090b0307030603031103030f07110a061a010305 73
    0x664070310003400000080000307a541c440300b40c000c10b4000000104010100d0010800b2104840c11306101c2c40303c684601604548500c80d41c01010007144601e00440c0c00162458280100c4c54003800785285075984030903561003640c00300a0340d840c0894845040c484080303400500510f099034120001c101e48921380c1d002802d0b5010340340440c0c010640c0300340c0004417a4400c1c4002049500f520b07600b19912240f868010700200392282e1054018100003544156048082c46500c040d81c00082c5820190740300f55981501610030301100320781c00341c3c41e0050540301000411140e111400c09141988038900442d03802850440002c00c1280320340c01c510700030426241c10420240d00682c20a00206141c1d40740001a2905100c80d80989091000003041140c01585030340704000350391081d0b403a40c2281ea90400072070360302d00080d01c0300c0c141c82a000300450071042c060803d400c0040300c00d0042e981500525110345048600900d82d114141c90f030100c03810340640c3d16100b0568400444a00110080c14401c103170718000c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 599535431 1250 599534181 599534213
    0x10c08010e0c0c010516080a0902130e150408040302030d1403220203060c0d140603191e1b1205070504020a0c02090a0218150307031e0c0810080a 64
    0x50600441d482c400100225904107050703000a10680c144070b0000218101d84421500018402c1c5012400d00b807000d0245403c031640041c840001c00196955003401819007440d09445840384d0340003620321400b5007184900c02c41c055100c1544413413075030051605002d9000315070f0040113a00c64804900f92a0072080d00e030803600e00362480341074400d140c904900000340580065494480d4000b004180543c0f4401040200f013a5031042c05000311a03000702151003000d4039240e515070440b4103281446800c154012045500400040c1d040074034003c00e00101541104050b03071000300c0c2c50810085e40705403100c600003c000404101ca0f52030b40b1511030584500403405024480c640000d1507036617003889a11145107442e0014805405401c0ca180202e0003540b24001025203a07011140d0f1515500d44107000c001d040040000e400c0c41c603982d255084002700030428000740c034510448504103041c441031042c407406244648401c1e030142040d118801903048640e200002c0d6601200540c3c0004034035800704c04002d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 599536681 1250 599535431 599535449
    0x111120a09091505100201231e010306020904050f01030b1611010f020d1505011b06021b0303060a15020a230115061b08070f1506090605010908010c0801 67
    0x140400c820444120020358004001141411940c0c0c1a000d8084007400c11a501200d01000d08001c2c80c009070700340e5101e0022100c007008604412851610115901c03644900c1d620a803da90100300c1e62100389a050a130416242e543e40404c1c10035240c00c240c410720760441031552200489614594514210500007044005a490240203c2010b1801a0802c1c54a0203e0900030312040285034001c40c000d420604134903044074240100d42003414080c030701c2c51050742c0e8103a40307034075070204802c80049260115850440e08650708005044441000084580201c1c001c64003540d81c90400c1010810442c0786500039141042c40698403d00c0d1307580010381d90501c213071300040b011a172107140041500319040450352110a942096950050b24400310107e00544840341c0395404505104079060209203c1c10384c000304000c00030000c41010030300c03400c9000140ca03c02c06894261600d020310346001d40b0107681c4040c0019885800c2480705681000851000e0240e4400802080045140c000c04040040c4504404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 599537931 1250 599536681 599536687
    0x7110d0303090c0b09180105030a031805030106090603120305010810090212030309030703080c040302102a08030a06170601051009120804180e0a1104150e0103030806011112 76
    0x30940aa080362880d150406030402c03046585a0040350346622514881c2d12494042c0d607040d120f62104034009050f184050014821851550f5050700c85044030644048402c07001c0130005542e035001d01070b40018203600b0030045a440d20710319120328035800c40e80940050500f010018002d1110008060720681c41250010038480c0c10f40c000b00c0c00c44c0b40c501d07016040d5400000300700b0001440001c01001024401eaa5059080e41c4140a9221034092400001c5d4840001134046110760320401c2200004498a500d082001c60002c01a000340107413407400302d4503010044200000701802d485800000c09807040717600320314602c10002d1500c512050080340d22071201d00c0c40c1090035a100e0103000d0040c100c414422078000507070b420030703c0240c0c01910441c0010151008041480b45090103a4110000a1070050429a50390342e0b41403034020b030850030550001d66891103e6103c7c0c0b03202041700d0041c40400c0540003a17504504006080f000000c100506020700d04211100014000031200d0f4410a45009103071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 599539181 1250 599537931 599537933
    0x108130201080606120f04050601080a030c080f0f030703090b070e0105120403020a020315150a0b0a0f1e0504090c080622111b0c030615131103010609030c05040207110d 74
    0x4d203800382c41d81c42015110404100003d0190540d0302c14004c2c1d0181c401c88009030798a4501c15900c50075601c0050000b044455940001007a510207010490344900e0443d044c106803c8056140b500f0840324100000c1c0c8039034189050010b02110243c00041e580340c00c44141010a0010b040c1d0303c0b42c0c4042002400e80280080e091520911040c00e80710f5006081d1081d804444249440d40340d0140c4103140c2d14540340c800754005262202c00326080700e4050000f2030030b1418901b030a0380c01d81008100300052000c014002d603040304102c0303d9848460880e4a4103601c07613090441c1c40040307411000c16001844100c0042c01003595802c4205614607441100301c0956448051034007021f807002206247e09900041280f01d003003000020308043c0540c1e07010131200d42c06c16000405a8411058580501032441c59094503010308100b86c604041400c44a03001c181e220110030101d02c298026030202e07000440f2407000740304001107910480020201101c055050518540300c0b050744c517054580440c80341e165a0340f070380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599540431 1250 599539181 599539189
    0x210d0204030f14010605060901080f130c06090f09050702030403020d0c0504050a0203091c08070e150a030501060206131a04021c06061401050711010f231801081302010806 75
    0x801556200c00b2680704404076180c9081c200c526603030720307400c02c0d4280305003c241e5003010004e0b00c100140583d6040529210007851814858025001111004244040c40d000c2912010034000810301582d031080c25515103884400601840e81018401500303103414081c4d900da0000a0b2420b40c1c1d0115640d04010001b4680302001c041390743c0c00660001e0821007001240c012650181d8401c044103000c5d13074a0394145d200038000c40c00e0841519000300f02100c002c5103186100c0c2a0014002c0b0003d801c001c0c00030211560505260000001000001d0b100c038014061650b051140a070807405403090503108545683c1c1d610240001180c50b402140700305000101075694010280c204081c0c501d100300c64140b000d0503c0000707032480740101c1c00c0100050f5459181940f180c4120f40e002600614002c4890740ca0300011038007401074503a41401c10090300c00e045045e41005004038480752102c50042d40c0c400f41d10364000b4411203003e1807141886601d03010420070814a43e8078050b07030307942460003d01a0b80c2e414005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599541681 1250 599540431 599540437
    0x1e0806011202090c1c06060e0907140c010204170706020c121203060a03061404030914030316030c120c03140307120b031903020604020a0e0606040b09030304170d030509210d02 77
    0x102580d943c0b90311160603485c0303c503408a421b4136003030f035a4250750400c134406000603001c0035900340000807002c2201c43c5d0501381c5040602142c2900c08009464140e440c18402d83c0e40140700304901191f04082c20800ca0b69070100301a0b02140d400369062a000300c00a0b00e01038030350011540400a50400100007a46035079a0316840000d554000c4040000f040003003d1451840002c48045000c5654024040350709403c2100c00303052100d0080013189000f0b44400d01e6658041c15082c103c0502c05880304040000b05042d000842c1c0c0c0307040d5a5034460707451090800810784086a0144d405084c410814030107559407000c0c004080010b030329000329101030000040b900e08411041c4590300380c2000c8040108040c1c6c0480ca160041d402118098400741e00c540c04101c0c3d008003030340ea0715408102013104019004400c0080c000c184001801d90341000c3d6111041d403e42c030000504149030740c10218080102603094410250041c01900080000250140e1210700409000c0c041407110316000c502d021001d8030603011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599542931 1250 599541681 599541697
    0x60213050a06020f060907050a03020112110705101a0604031e0b010f060801170a0201080c1309090605150108070507050a080d06050102070603020705060601050c161e0806011202090c 80
    0x1500c902a42c1c80100a449152810400615000d12004510000c500146560a4500080c0b101c0c20451540d40107503002d20f04134444103180d6440d0000d50102407030907005061414000c4029282007c9095000c2c400c88078003009100c04c03525080c3c000d1606403540b20560302a6031303001603010000504072000c000c9455080d44000c1c84084641c0001c141032084102c004115400b90729203c5859890b503400c21680c5244140ca110b40f54040504c41c80598803510761207821044c81c00034180381806114031409003000540000e403890303840b030f03800c10104401d5124455000709001d101d0350324400350703030700080280c20040d0102c803c018010440c40144103040c1303c0d07a0244d0343c7c00300741c00340d4801d60004894007400c42071040301c1c0503004003040000c026009000b00c911442d07004000e404e4603551180152101d40090f0341010b4907201390300820082024150a00000c0e007612070140900841c200200d4060109503081002184c0203000104170303002c1c140080740d10b45c030b5040307500340415a21101c20011501540c1c0e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599544181 1250 599542931 599542939
    0x1a180d02041b020f06010b2a030c0a0c0b03040b010b031801150305070609180f0212040606030c0b0a080c0304020414400204110415030515030703030c06021305 70
    0x1255060b0022000301e0844041ca50340030b07912902200344609031140024490418000d4080000040002000280682501c0f50300b1101c803140c680020144e10b5500882d00c00d0026901c2109400240540751b0030380c03c002e1122140d040c0c514900740e40c0d4500c0300d03041031203201c4130000c0100104941302c42200c0d5504003804680020021302d0350691040380c1204041c8419170b81400b0720b00b00455100e1280720f010080c0c0d0383c82100f2407041d2410452081c010103200105014450303081c04081d0091004000507800703203002c1d110100f0703024110709000a44000560141c0e031078100c2005508071554000c80c51b20350100352800844e890780d44500103e0f004d00b0340c0b1891030510459800400023010005030b400800c0320100920081840082c03d40300c0712a41001c61141e01085030f504030180140740c10707080703100c1c000c85074003040c0c0c1003d40da00300e41c14003000c0d007800e28030109845d6000c02c241c0c90f802c200d0580030644210b00600d01c20b495500e02030184100c581010b0074213a0001118103248403c009110000c02c4054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599545431 1250 599544181 599544191
    0x120e0a0f052811060f032805160212040609180b040504080a140306011707112a0d021c06061a19020a0201020d0f030b03120909011a180d0204 62
    0x4010024010107901003242c1c3e01e050b140d140031041c24040e0a640040d884a40040d00e103894005ca80c041c407208080e0b003882d0882044000391020000c502449000324481d0003d91000071100070007030b040c0403060140c0c41171000b0905c8200545644510390b0002c95209240d41d0a00c03410030b204c2d4102070201e4180c41c5030024240003d102c00c001c0214000d02405005580c0c0ba00d40680010840c04140310540300030340015145500000100b0504180d20b4000b03185080024000000d41c800030708040c0300901840607440c40502c200c406000900d03403488030761000c0314042980001e0340e00059010707020f0070880000700054a091020010180d1121000e8400341c40740d8000e01c0340c4000c6440f000e60150406c0b20810110440d40d041181c0002003030b0340f034075a058015000000000c5070403a20070f202403039070800f01605c0700d030041d01e140c81c113106401c400b80103612078696550340306084c41a0140180c0c4070f03440021390500401070101c0480242c6203440c00343e403500c1e44440302040c0003e036019940c4d031000c2d610520700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599546681 1250 599545431 599545483
    0xd020d0803010302090708091011190905120105160c0206040e0c0403030e1e091e0f0718061d01030207080a0c05060c0715050718080d120e0a0f05 64
    0x101450481c0d00c02c071102401541c86ca40d00f00c42c010015506101103510592000c0700342c1b200c035000104501d000004c402d080c81e04685030000014601c40601000c01c00401e028011400d103940f550400e03448410003403050b81081405501c01c40319403495003003002071200c40c1c0300856585a040342c0050803500300310301c0c0074207201c02c1851700785e032061000702c021840100c064845402e1042a0218940301c40d03c1d55a1032905ea041072104203200102006c40480e9a25101240c03540e007103664600800d185102030506241a80000d08041d000c403c0d0725014516142082203081d40c8001c0d28008107040300104010300740740a005034043e01134914018420080412031201a0340d10078107440a060040d400c450184e01e410340035206034410000007420000013440c02541e170800c0341e00140e801c0485490304008c100020314040300760034060f400c1501c41d600000111407240384c0c000b103070181001c905c4c0030411265404d2100d0b503640d26400c16006003140f0624403600244901809484000d107030100c0c41c80800464 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599547931 1250 599546681 599546693
    0x3030c0a0b0106080117190813030311010e010501050a06110a20150a0f030509030d05130b01081f0e0f030a200a02010e1e030307111816030b0d020d 65
    0x42406400f00003900800000b494189420103540502c4544000c2d25154245c0860f0101c00c1202c0c90701030316900c00403c80755600c09181c802d0b841c002e50080e514001035681d0722542030b0a4032420001490540e04242c0140002d94030070345148200c807a5810941c070584010444141050f4907100090a420b41094501112130418007000041d20030849042114503c280d4040c9000d0107070084103030025200b0401811018001c0d0b00254001c040481103030b0030950703011000000d0b2803040355000584100003c040040001a01c6d04070f001d03014490103814003400c010401c2e1006495500d24150494441354001c518541c103000043e0b080d1021010759544070206400030302034018075942c0191890540394000038001c00030580452841e416550945c1d0b140c510410440e000008070f203008880d40444002000c155070420060020a11420081a03900c102c034041002d2084098548035056541c141000b142e10700c0605030407100403082c14005403c80381d600c0805c080110100d40203410440942502041c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599549181 1250 599547931 599547953
    0x2030307062309030301060e010309140c19060c08030a02130e01050312460905090105041b0315050603010e1006110307060216020402030f010609050d110f03030c0a 72
    0xb4000910760080e00700d100c044182c1207811282c00c04503420600061000340c2c824503c541d00c03440145000b0030640415200d600b000881e00c4c411001d01c0e130020300c0c2201e6a040440213104880c00c00603040305d40c5441e00f103011f0401103440b0f038010030380b040c0040000c5031680c0c0d40e41684d031440d1940c0c10b0710172400c1e1150303c0344500031000e0081901c01c0c03185c54803d03104815000212140150003441021015185020303508588018a0703030000100200400c003154810950761510104216640303d401545c50082844545807043e00001c3c0514102004c2d800c0e1319980e40001044d00141e403400103000003140c1c0b0304e800c0c03c134403c0c0c0120368046400000025114441c09000d80152200d110104110ba0348010550300d154400341d00c05002d4105004d0400402e807030b036020b0030f10003100342c140000f00030540d0700040407688110740c0c00c144000e6140c0140507056103c450500501001d50b206640250240c03181040031190713500044c4a40726040501c1c1c00781c0c50a10130b45611001900454440c40360038036201003012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599550431 1250 599549181 599549201
    0x1031d0a06060503190f14070b0c0a030318050a200a060302091003050403021e010b0901180b010504060909020f0d0212010602150c030406020a0917101503050303180a0203030706 78
    0x1101707802400341c0c500c10841003940b4165200741c0288061940e41d45c3d44900b0000341c2d440049901a0000c000b0300c0d520744000a080c120f804c0700c00340c00701c06c11502d80681280d0000d0003100320054003c1c81140058800109003c801d90410011fa00104494046c6201400a103150a41041d6143e20004115030141c0281c07103c028101d40b00c0c2c54240108104504450301110054010380c844009511201c1e0b0403009002c60010103030000c50320300b5107280402c2070f0100a030320004903084456601c805840c024446c0d0412442c003440d01605d0b061400400a050031060701400d0110b503070009021084103a241c0032945000e0f17001c64150744401403071040105404091080c040075026040c0b0400d03e450716030101922a0b0030104a807415601e07140c403241c0c000e40001140c0c0c814410444c2002c581c0c003003403035500103000074084024009852401004c0082d18050400325201c003424210900c00542e01002380c07980b00d09005040b0a82d013840d19441481c000c0e8400019400d4000020346905129840e000001c040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599551681 1250 599550431 599550433
    0x408030703080a0908070312061a3711070306050406090b0f1b0a0201150f1404020c0a0314041a0406080108160509091e0610080a0c0501031d0a06060503 67
    0xa41e03115040f0b0780980b02003d2008091503000c101e010300003405030302c0c1c464841c030342030b40009992500d41c88815a140c007181090003407000e0201d0341000241d088074100c298085102602880d00c80340f01d42c41031814003a403c145050000415144542c000c04004d10001590012000d110a00709400e006006200d10b450a541131a0b4620000e1140d440d01e41e500d901800240030b407440301e0255001d0403d02604030081d40d800315501c1b0b004480380e20064070078500280041500e4180454a402e01e03182200f190480064000c40c01400b02005807600803801000f00c503003604140c00c044040346000d08003840f40e40c004c605071070300d00310391441c83c4000c000c040c000f030741c5060321895081d90b00d4136001c99a61540d12f40c80710004210302000d000d08c0c20010f2815800000c0003044031002e2404d0a481000401444818a1164042010400303281070440f10000207011100c040c080c480700381d40f690740c50f070006c40c060343c0e0525440c5c10403503110b10f0203c200d01c0c102c210f0a206481c3c0513149890110302801d000d100703040c46 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599552931 1250 599551681 599551697
    0x150d060504060e09120d11030f100909081c06080304080f0601050103060509130201050c0a030c060c0809070603020309100903080a0605221109030304030b010303080a050408030c0d060306020408030703 88
    0x440c0c50a214958050404e10380100f8000c0c11044030880ca981c0b00e007040d03910403900e0350080102440308030050342c0114001144080c00e4038180140d07a4100400368040c1079034500f000b500d800400c55140c211041082c020640c5542d000b000240d250103030029600203d09403000080c002080b03007000c1800b01180c0110400c2d200d0990740c4100443c00d4071540d000e2142d00008110103e40902c0c5c605090411a40c410705000c0c1c1842c1803440c4180c1000e21014082d000b00340307103c0c0010704004840c810341000c440320342016100d07801c040c0c003140e940e001035008410a1650020104004440c1049030851213000e9013402d0102e03002e98540181542415106112005d0070010081501c1c9000925aa80301010715084413460301452103001c0030740388030034911101c11410040c500170b45d1000e000900c040c40c01007244c03101d40e5145260050640b500101140c00140c80c08092000041070901100c0d000103450980d951148610044400100565070004043c144002800581c03d800480600821402130301c40c1c0132 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599554181 1250 599552931 599552939
    0x9031f050f060f0121021309050f01030f08070f050304060c0605330a1211030d0e01020309010e13060602010f060501110c1c05100b0f010f0f0509150d06050406 70
    0xa110105403007070b940c000f407800c602c07554551041505a244c90a505406954054040006001c0707903c000c2a1410028201d5000e10500303050b40103080d04001404441d040940c55034079246014000c00c0b40007004c423000024800223210040090b07006e0b29402109403a903c0d55140380252031040143c40c22070b50203080c0b0b070000354041c854014407120a0b0b5003080000d6500d64001884081445c0f0141495100d550050007146407460030300031248007445031040b1010394908000301031030f200c66010b401c02040414041740c40580d0780841690500e50b004c0c2010865490507400040a500e0400102078219140820010b071031541500040054038501000b001083c0c0c560300110b9660302c440d02074004660141040986034141616a2240000c40300d01040080c00706a503000e0400590101d40010641c5a0480c400300d4a044170020000c06800d080c40c40306041a84400303443c3c0c084801400080c0000400c480300144c4640e0b01d102c3ca0161000b5031282d4504500720507070014612401014060303441d00350045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599555431 1250 599554181 599554201
    0x60406050f0306010618081f15061e0c050d020d0801140901141f050703080a050105030a0b090115030303061d2208070b070804140304050a03020d0809031f05 69
    0x418070a000c0c010304074903805c1c0841581c4404500b424108002c0109500003640d03d0b06016003c0c02602111508044000481d0080c00f070301c0e10040d060402010b910b004200311600302c0e1241d54481c41920245028605041086d00e0300d050000c00505103001c2d02502c005c0640d4003084100507002c5a844944d101d0362a038100b0700100078001283d580040e40c8400610034004d0b0a0355449030400020084544881c48a0031100c00281515148001c544046042010103400c0f41ca100e0740031240407803c000561420000a0f942c0d0401c1c6805000320b01c4250114241030029005000161015040c1c1c00503103560380342c010010405449000b5a804502e0748828054100d1250309010b0448a0465080004c01e1b80200480a40a88080751490b5007002030034002402941601d118100303c5c1c03100e110510749810080010759080070b181c1c0300d54104000c107002da660343c03011100a498040d6900e00c010b480529014480e403203070004441e030500c00c1e11840c00d0b1a407009520040148154a414003854807112042c2d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599556681 1250 599555431 599555449
    0xf0106080105030c040b120304061e03180602070203070506031501021207030203030f15130b0108100605030a09113a0b010e0a0207060e0303090f0a0203060a0914060a0506040605 78
    0x43d030b040e0003540c0107860701d1400340c0081e542c5440041c0710504c214080b600c0640385074080e9100c00c02042d1a400c00404d1480d01c940ea030f04240d02c84d410240080058030720101c641c000c0d6000d0081205030f02151010a544007000102d01030a401341c401996030601d1440051180b00481805005108d90b01c1c4040d407030b0820030199041954103400450030340d150781e4103501130101c00a10181c17035901d80030300b68501a0748031140d00351144808000010340c54441c0340010035480c0020543c02c8510b100c3c550800080c5d41c00021280c0c080d450f0b00c3e000404890314904001c000e1383d2505502d07842412114680b41a0040d0200040240c0014000618012902c002804c0803068020050700c10107108004001d80f0007401002a031005520328011320349030550395020100c42041540071582e03440802046005082007100c000311100390001800e0a23071a44d80020380c0e1390b4005100c4506261100c003400100242912507140c0f8000d820260340043c42c04400c000020081154207501c91400c000002805013050b41e80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599557931 1250 599556681 599556689
    0x20a1701170f42070302090a060c030c1416083003150409060e060106020d1107090e15010303080a0f02030903090409051c0c02040f0e061602071d0f01060801 69
    0x40e00760524540c0703100210002011000e003d001c60205401800218046060380c40707101c00b91401610b4506180c02d12410340c059030411800d00c0048400507000c84d40221202d8285036100707582d004000c40c03080b01c080c14204402945c1e21015140701c0f001c02c1c050000b01d24002510a20031115506080c52615403003403006807a0303803c880400800100383d101004e4040d082c00030401600119a2201683d6044120f41200d0782010040e000f040c01408126030501074000c40c07071428645200e00141c0d05103210388410452007901280356407200050f180175420300000c8221701c0181050b80030f544c0d41c0d041c054812141160030007401890300b0090303410304080d4400e4034065a030311401181416088402e00c00103042102c03098420740304940042544d01860040c1003104003061765042100380c0648103110940f80c801c03c1c244202800d01e500c08000c628000b54544d03000540c1071103002c040f003055000381e04140c12500508900e050030080f982a80d10f1009149003c2d441c036032145201a82c0e030340001c0b2440182801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599559181 1250 599557931 599557963
    0x61d041203061a091c06150602010c0f0e0307170f07050d0f030c11030d0201140604020316050d060305070b180a08030307050f040e09150112020105030406020a1701170f 74
    0xd81c480d1860300000f07008009800f9007991000c917070002c0d2002000400e040e04403401038803a01c000b640c103007500004d00006d1507070740000d02198042040142480c00c2c480000e90030050035410064995130100041801410901040b038411800355180c1398903003181c00440e5100384501c0c80006010300b0800765200850340c20070100c809020319654101c0d007492078040e00350340c00c2c425003080c000313a590144104030681075550000034452042040141c1200c0006044078030035803051040161003180030401d1103580b03201d40380c46507a412001401400400381500050160710030201c01050b01c1d12020000c040302081d4011241109180e04100301e000076050280d20066041032011900350341c041d102401c1440310b004c24090078030b41c58041c062003032081154544210b9200b0445070350b10305404001240034140c0e401c48092210301940000c0c2003840f0140c4010b00341070340020303010246841200e03000c3c180550080340103d1945d40d03640c2c5424406d8a10f0b0040503c0c061a816025402c0380003440406241c0200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599560431 1250 599559181 599559209
    0x607061d0601060c210c15150519060e1f08041e20180408030105040608150c0a0905210607090f0b0d0b06120415060501050306040f061d04120306 64
    0x9252000d282400048410034800c00304c1d040e02c00110407e1510160a0701801c002440e5000c0d1032410100c114075601a9020303203e44910260007805807000071040e21600d082c900d5040c484840400d080c9284408030142c1c0005030541d82080b9540600d00d540101d00424800b0400c50032a100500a0841d99500601030b400e00740341451828103034456032603440d100130130410501e80b110700c0d003884507801120101c1d4819400801880f075031920b48103000180c1000c400611400700d036800c001048a1002e0202c25035024082410896140305100741000f90001500c4541400841e9070b01024990200c038400b0401d004160006898a00c41c6800100712075a00d803000407800c0c0b50901d0008143d000c2c01581a85a0319007000c00469118140184800d0b40540c440d9000f0f0315060400340e04100301c54090389034140c2410020010750f070748282540d40150003200e00044007900b034031841c0020080c5902100c0121003450a5018045000fa085403049000b048120117460303000d14100d044414501580700c2c2d0507019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599561681 1250 599560431 599560463
    0x8070c0e181b13050c040807062001060501140327010221060a05011211040e090705030c010c02060c010912030915090503070b1f03080901020114040c050607020607061d0601060c 78
    0xd41c020075040f122a0145e10700c0d240c0c4401e44135040c00100e400c2000842c0444c0134105051281d200f810320400700c0c641c002c0020030b00301701c0020036040c404004400144c5012002c103410050345441c00c00401d203110050400072a800035918080d4101c50140d9083c031014081d445007210311b40741500e00c9400d00500480c2480e04201c01910002602024248950390344d880c00781c243ea071843c000b003002c0e0000b070300400c030a03140c004007152410341e01d500824003035044480329174481c0e6040302c80c0485a0b54100c0348603484078610042540104a080400b404a090f408a40304030f064055102ca641c403405038125250b41080104842e003920410720380242031368010400040807524225907542c001c0540f44580005050036035502000f1a4150010ba60f510781c0001c5a0810350b030244103080c46203e60503050a5145866100c4041640c80340c80344900400000071100e0031552900100e0700b065500c103200304080030014050070803180400c244040d0500c02c020002c01c0d0390f40a2090383c1d00e01903205200324904498 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599562931 1250 599561681 599561719
    0x9111306030c2601020a2003070b13050a050a0602041403030415050f0c0d080a061e21020613090506010801140d020d1202010923070308070c0e181b 65
    0x100000300f80c0e80d06075003d483c00c00d010300380020440805d482c4d4451210078441c2280c440300006a41100110340d2041203d5000122040d04040d4000c405401c5018a402c1c24100a800c2c0b400420005142c0d01850030040d0400c03000303134050b000b918540c1c20580507403030719001419a2442103005000714040640401210703544a1402022512a100c003818140b40034072aa6a10b4002c500d401d407400b0030010401c000c1841102d20454000381110250145420812010000c0d075030706c0350103070b81d04c5002158065407000b9034a0152140c056406041955036501d82500351244941a0185803036180c28100411020342c440d08545058231000c01c880d410921007101086282c5041c030278100c0c0c101c0c441108442c04503140c9407001210400980000c5505460b504e000c00d02640380d00c1c290389500860040b00da003805030005182081c0e0782d1289440ba55007500703062901507c0320740c1d4000b40e420711a07142000044003c0403540f0311555440c40464507038800080102018003400210241c000c14942d04c6170340b100103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599564181 1250 599562931 599562959
    0x2070e0c040b07030203120a143d0510020a031b06090209010306023103230109050319050a1e030f05090d090e04030c0b0709080109111306030c 63
    0x10045200c41c6015602c907910103050700040c0c415005604042211442c0220f08085903900100800003003085102107121444800c0001e058030450b00304c1314800044142c40c020410800e04600c131540045415800c014a249944900405024002e038486404609000003080c0c62440da040d15125003a08402c07480450000070b0260580d03032562034111400c0940c840c4200c880c0a140102c0c4003603981d404c1d0f03041d52401850010400800a400f0044083c140d0584140d000250faa0040001071500101540c034105400f401c94100100c0d482c1013070a108118002008109000e440007090401c1c07000d40c4800c0e030300c0c1d0141c0051030001c610041b10b40c44002c500810300c1441c0d41c08600f0b0000f0a42042d0000e8000c03240c2c00c070340c10030040c3e104030101d90326540c2140c2300400610300c3c1c0004420740d16156600401c3d41d00036100060074803e256010503031181c007175288030001e000c2500081088050506005843d80c00411159008039402b5885c14211080790250b0740c02e89400881242d501c920b00510800900d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599565431 1250 599564181 599564191
    0x10081305070510030501060e030c03070b0f0408070f060f030c050a210f06091a030c010507170a08070305010e060a030b0a111c1b090905040201050903150a05150102070e 74
    0x4007480c0c0c1c1c08185a03440300501c0752500c1d0140d4000170780e507040c2500a0040c104040d1140c0c403e900070481e405081e50001032841c01d03140b80950981e00c44501d5a00714409000b03d4004081c81c0c00388400100c0c450511803809021143c00340e80f650140340001c8801d60480e15582c940c103000403800c024000c9068060400e880d428803040c41c850034110b4100004000300c40780030103107404c11510f403501005010450b000e0010604018407a030b0b03000c10074900010360703102e010319004c0741801400701d00c03401800000d8200100f84d8141502c00356950f080054003c04141040300c405000c40e25143c004510007040a6103d441001e018005850703403405c6480d0204d101c040200b081070b515841e1140400960b0310750010f800007194020040022101040404003900c0170001d0810460080021003000c466212003510100c130f08030080021103440d6400100c4262040840c0039806100c0c0c10400112661044410fa10645070b0300010003043d1280d044c403801c40e43d003050303d560050344416414041071a21600450b084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599566681 1250 599565431 599565433
    0x8010b091e13020117160e01030b030619060509090a20090f0c0906040b180906011b0203010207081209010b03030406021b03010f2d111b0a1b05030c10081305 69
    0x26a40d04620140c4c00d800302d69070300c02210346503106d4440720b411003100124000242030a218074036480020030344e2440001d040491a00070342c0345642c030000840d80b2440c0a0603015140c40c1d03a074540001c18555541c055001101c1d2407850081300d03040f83d20304a040b0701d01003800802c10100b070345032415030456801d000780404004410801890710350759a03110091000704444180c040e240c805200c0300c803034140030052119002c1c1034503104008032680d004801c00d0b5040c804030551082c0003c2d600100740240244200202414070002da07040340d01d120a1200c502c5100e01400900520300d114041c15201e004070702c82c15000da070205103d202c5042944a456400203400350000611040e0b0b814400c00341c8940c103100c040c20321305200781007440345006001c04c012100000400e001010402420228a104070301c40e03101800854810080c8410007809040200c0343c120007442c071954906800355040704824810b5910030b00c01c00e40440c0c0d96081400c1e8070030b22604940c842c0c50b820755480c5010b9480701041c1d9421111 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599567931 1250 599566681 599566697
    0xb0601031e0510080609030c030418020f040605092103090f010c1a01080d140a05030c070605180d03050f01030b060a0e01060201050f070c0c0b1606050108010b091e130201 75
    0x1100290710070310f40328901008000e855580703028121820700402400768502a0410050700707080c03402c008221000ca1f100001d00300c140c0002c0e4018280207008140100328000c3c800a0001010380c3d208018064003c0212800d8013220f60b00103c40c4451180000c074450b05400c103011130381c901e2402800c200b000c0e40060400c1c40184400c0c0c3da40002912075002c5030307040440070000501100d141009014009601c40c1000d0100c440102840b907000c1c09010300680400000100094145c8801803e0f80d40d510f82c012414400703070401c3c0c1228020703001480106403040c0300b80e100b01351241d8400d0040d075000340301a001e500c1080c0d003183c840b56007280b0000e20707032500002000702c0010095500c101050003045180d00001d010f04120101c015000d002a24050402110f00e2030140030412610050081340d00d003000041da109543d101e441031a00c1d200c84050080b91520b800028211419080004c400c8402c80d1503401e607558425091240c81040d14404589100d100d00003106d982d070318204400d142d0300504140e10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599569181 1250 599567931 599567981
    0x1030b0d0204090818120304090914030d14060f0a030f0503071a0105150a1718160e070924020109080703030b0307090c121116030c03080a02070b060103 67
    0x2c141c400e60042169600d8001406002041000950094120040314407555032a195841c4540d280520b008107030b00107542e00709080400c45210080210004c40400f03403a22194000410f8004250700c40041d0111034030000024150700d8590512240d40c0380c000e048454070350868a810490b21030300b1034200d5180c4410004032011610042441c4961090127524406039818801885030102900035046001c04044c0802d9103010740084129840c4951210b5040b400c0d41e541e0300b003440d21300c0b0466500354075024400c0901500a01601d030340c405d0f10307403020b40071010307445055048424010031701c140d03070800e000c0214440c8602404441c4101d02d1442d44004590341c0c1840d11100025800715200710086940c0d42c00c1030b46e882c00c0038041e000040c810054100074106c02001d004d0000c940d00303d00d06068554441c91036084605160581e014050030b080c500d0048451841c000d0100c1d001d80380c09074003090015002400e402000d000f181c0951350f00140610107501c3d101c006401814030703c0300302d10002100d140c2c006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599570431 1250 599569181 599569189
    0xd0816050303040b150103060506090f0103060b0f0c0c030a021f0203070605190b040c020d18030822081b060901050c0609060a0c090305070614120f0a110306090601030b0d02 76
    0x5025501403403101343c641c1080030041c0726071071880c1240341c14542000420440d5980d000c007603e0f1644001d540e242c52500e04038004a0040000c3d4001031010080880e001d0191a4a03201800c103480300d803411904889030a00070580d80310794802009601041e5003c5c60260000e00c9480c00c90010400c0c0110303414400c0b50343d982c0c8241c0b00c0848008909003121418400c00903c0341c0a50403d2030420fa40802084420500080d280c40f1403080e181c05000a5032904050107008100710002150031140140e10303400d401c09640b41181030350b82c0044005142c52800304008002049020441d5080f00104004146047c10301a0769000003485906101c010b211640e2590700900030244503492400c0038185a117020b8040d01c084558008100c81000b02d1b0786010f00020384000b600c0415184980ac2510070019299282e40051080c0c0c40f00c030180021600502045c10b4030700e8191790286003200f9061219440780c48000d8801c2c0030403114154844c20407004240f155001c3d40c442030601001038800404180660045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599571681 1250 599570431 599570437
    0x180d0f06020a05040f03210f080c0c070320010f09061d0406170a0201030c0c02130f020f0c01090c0e152803030e19030506011418010e1b0301050d08160503 68
    0x1a180c0e440b801c10307040c7c0c0001e100c15011580c8143d500341b501d118020220001e01c85c8038010b2050040c2030340003882e5801100c080280c2d0307004692012030202002c000300c07841c44804081c0c0804502142030400c041d200c241c0604502419241555641608030001c92890040124403041c550342050b51041d020072650808905240d40c07212003002000d035810284001030444040c02505001c04c80c0c0230726a078005958003101110361000e020400315402102c1b100070300c000c0c41070080c00e4402042c00901c03104110380640045241c24081c66003460030613580d0481c004400c0003194807120040d07004403460901d00d007181520400c49059401840b440c0c41d405480714032480a5001a400b044d021a2022514030302a250020305441129500c0f001d80d15580d222a61024180601c081010190360300c061962111a4000a80449800786584550b5034821452040d141940d4884880d01129804034140316040c044904803040541160f0b081d0344180c40301c080355042100c0303640c808011641e84902140e010005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599572931 1250 599571681 599571683
    0x90f0807060903021203220618260a0503131103030c010b1e0d02060f07020a06050703020606010c2102070801022a060114040f1808180d0f06020a05040f03 68
    0x24200c01030b0f0030b01a1a10794500c968090441c410020010403500400100d00d904103620307140c610070049450f05034041c1a11444c1100516030700c00382101446544290b44840d440d03440f20703d942c450346c00e4884004a224080505022071710070008074101010602c50071506502400c0700b455126000c46c0002c1c25039106d0a036001c540da441e40440c10745890b02c2c0d500c089201c6499540c02ea04c3e40c0703240011074a8042c1c2d110010f44a03410103d5422500c1401000719120382c0d40c014903600c00300f40c550b200a4000d40102da001e8005100d400d000610319401507044502282e044211102c000b101e0f01451a04071810307284050850007803020000300710340700740050215200c0704102c00b41d000801e800001290016031485000039030201c0f0041140b07001c2c649800c20342030015200410046421020040070f00b80c600842c40c001d00c403000c0f0100921641d903018003841d904020903003005415400820001906c030800203024441002d240c400001e500398028944941c190030f00504059681d60b08130708000d0071350b02c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599574181 1250 599572931 599572943
    0x70206120a020c010e06090a350706060e1b090f06180f030601030c050616140604061d120c0c09040b010303030c0f30020a20010506090a090f0807 64
    0x34180f400365400b8051201401d0010000740380d2841e02141c1690303a00c1c51214081d022034046403c0c109100085503c82e03140582d100c501c20a0740e02403030b444070000d50000070b09444a91034100041601c0c401916094080c40300c40501c420011400c8401c0344055120010b0142e01c000c0400e42203d0340c4c0c903043e01800d40e118625251444640c2040c0500691a2403005464404e0300907600600c001160420340f5002d1361000d40c0c00513112040c3c1c80340c2d40e001c106c9003000540010f6500c681b031600c9910010b030040c03183d8803a030345c00d0000f00141040c0010050141030681072541100c4484140348200c0409000c2e25400c0301d00700c820000d41440482d10101003541c1c203807a08070000005105142c0c042c000c40c464001c6500d4170300c05a4100844c010700e885c4064004070302c90382081e03518610a0100d0140c041403600e80305800c41d51001c042002401c5c8038008000740c040800e01050a070307626541841443d11414000e040001d0a40da100d0141380100201c0718100c485541d510b0b658030100b0a954003400441d48600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599575431 1250 599574181 599574187
    0x3100b010e19080118120c230606040608031602011b1421040e0609060406090501060c05010f0606350f070e1915050f030703061a070b010506070206120a02 68
    0x40354142034030f060301d01205101d00c00c4021140019880140c840003040149008052200e40b40390500889807200b60004100508440ea2003100c00c0104004ac014001202c080004990f60b041031502d070b02948540021080c20082c588002d0b500a940c410940d4141070711783d40b10540300b9a070f042c2a2074180300700d0110b01e83c00140611101000c0b41c000c29a044054220b1074180b81c90030001c10312000d0700030200380c000c401d0200401e1058a454200c4400392100c0d20060220307684500c0000c0c8404140c08041c0c460350f090400c00d284c942002d00c100d0064172155a20320f42028070b0b4528985070340404021300c541c0802d80301c0003104007844003500240122948070f404c480301e080c40c0c440200038400f00f91002d48a039000da00581006900518000c003100ca2080e54081c99a1412030141d60b40c0c0910b00c081c0214a00000420180a030b06500035030503a240d21100070078071a100c055591540c080c505004042c0000300b40148000d1510002410301c180c801802a80340c1130907212852121402525a241410303004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599576681 1250 599575431 599575439
    0x21e030403021902030714040b0d0b0907050409120e0a08100b18060117220b010303033812030711030d02031c09020109050604030f06150503100b010e19 67
    0x5000369083c001c20680d80440b0040e0640010717403540000e01c01c050070800c00c0c803550f2101c1e490b65009007803160300084c0400301d0b040c16810009000f1404483c81141030040150214144c42d00d803080460300c6030802c0088002e0003050005a9286102c04008c0364840caa103040051030303407010018081c00041501e00854000e44010902c000c4071000d100c100d1800301e0030301c100000c6c0d0764002c0720310040070481030a4035129122814504181d100c6494140c01d0031009901c2039003400820302000341242e220340d0382080480141d0344c0580110b08890395070304a60340c498100c0314000100407640e03803800100800d01040c181e0030703c414500c1c40d40716907001c0f02c00c0b49400402c0100c619052081540e07008960020794501010003038000c54448200510b45a695950441c81c0156407190049401070800640429030b40d5840e4100751450a45c0706c1c2d4210b0301c06040400c9140620111200c440031200c000c0d004080707101c840300c01070300507161424000c2c2c108402c8180c401040d80d03c840070701d4038916900c1c0011143d2410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599577931 1250 599576681 599576683
    0xf0303040e15030d09032001030b04020403050705130902010c0b0601021606020109030f020316080304060b06040806040507140906010c14030f0c1209010c080a110604210c020a1503021e03040302 85
    0x3208882c000380024100108003145036103450041e41c22100d045d070081c00511f04016001400100103094000b840420040100400020700c0340030fa841c129404003500f40401c8040d0706641000c0070003400907048016900015140c078080603080700c070500588040d07202c00003c0f0403006c2c1d119805400140e45590307050042c9034000e401c60710204c17543d1010314034007610f21070301c0342c2c0c541e4806000030500c1d43c1c004001000d02040c1d9020101c00d1030001c01c010340d99541e40e80c805650b44c40a507429103040c00350007400240345000c1100c1d01d000300400b420195290362494019241240038541c1683d0150350b01c405103400305d409200401100c40c0102d007094a81420150091400020310305000e11200100306909082e030300460503005565000d01c9030340e40d600200c10200c4620f030175540c03451050b205840c1400b00300007048031000381460003100180800b8260820072555807580031070207908101c07190b600340000400441c003000006124100949007000c4031880300c4100d0b610750560030101502106200801d54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599579181 1250 599577931 599577943
    0x41150703021216170f060d030e030604110a09050f07030525020d11070b0d0b1804060f05060904020f041a0607080705010507052106150d060501120c0507020f0303040e1503 75
    0x2a008051303da07454503162456131000c0282c4198440c4424164030000c15110300d42c0c09d0034012010341507034030a040c81d1504d201600303804000715205024240c0d001c10110b2191140c144038005000600003640c6552109800420b00036101d81c45016420440ca034802500e80030303141c0c1c1071030b46074002d0400344480840107040001d83c10281c40b4a4000407410080c5070210816922030200303c42000412032809400203400210011b8100c9025011800b000148000d66120b200043e20b000c1061000b59562010445044000c4800035408005003c0c2d10f06142440c0c1c1c040740030343c00704030180075072a40c59000280312600410011038940d800011000c0c1000020701425410008600b05070f03082950405807902c441740086c0e941c144201c094000a074440e9500c0c5a400940410142855981c0c003403c00414094000f41c01202c0c04a60452440000d00800e44101d4400d0781d00340e551503003410719981c20811107801c003001c0940c0c503200611000c10107100e4a500340340140322650800c0b0102c80611b0906081c15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599580431 1250 599579181 599579207
    0x201300b0f0f15040810050a0f06030201020604031d03120306120601030b04060e101a09010e100311150a110114060a03030e0102010941150703021216 66
    0x102403016103440a44410100d034040300021603207000840000f41901826010b05d600824843c03040807102c2550b80560b038006400b60486100c1449000700194041e001e407100c6c1e100003030060b84140002004280700e549040c03180c240002501c01c01680701000070385001c82c00520a225220000248001807800440714242e0543c0c010181c03030340d5803442d15010310b011401031025210503240c280d200d500082c1800b9890804181c0c250400000074034060000041c0c5030035041d43d0103000c007840041103103103514440c030388640b50040c0200401c50542d62020003051203140c070a6000b5000400009011120402901c03100d4401d0f1b580d9800250395170b402500f9524107039000403c6501b500e040c45215100e60744484107503030701814140d221541d00d0b80103e00428a10030050300012407441c4800303c112030704503d82071005a11582c0c01000c603403441980344c1141c10414511450348030304208141c0f0608000c2d00c5510202c0c40c240181021943c4904000e950400c0f00d45010381c80c0c0302c61080016a422218440c210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599581681 1250 599580431 599580439
    0x1309050403051e22030605071e110a060207061422021e1503270c09071709030d0617060601031d1204060206070c17070201300b 56
    0x54181500d010b441031056224102c880109000038038079400032601150000303249031070403110452038903182c920078400b42e0000311041400c0c68046840940304002d90380c070429000030129041d580e10882a034489002d41043c03042401801440004248c844c40030380005030003943c022442c40c281060481103c8802081c100a0310341c4400c803941310048007100401e01c10b5040d03c017603222024100191041c1070040750003c3d401f4030f54495500b000c42d4034102442c02805446203640c00961079031501d04500c0340d1080328162076031004081d1005890850038803a00088030382000344046450005007000d84004407865851030b40b0003c0d0340700084803980310b0340d0000e11074065a09008441424561b480d09406003e1030304040e04e580c44105001070650400e50081c046804440f40b64840c01c8418000790000c0c85000098050701c400a08101d0040b9418845503610102540c06802d00c0304c082009500210400c1c0d041040700d91515404a015003018441108041030051000d06800030182c1990f460129050003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599582931 1250 599581681 599581691
    0x303010b0901020c122d0109110a12020f0d1a0115090b0909061302090d030801030c170d110705040e0102030a0b040e150402150703090f2c09070315021309 68
    0x5100100d02c01c1000100d15021400300c6d008404206009200083d0240e000d518110000041004112104081000aaa10003950350352028071f501c2c80d86ea2910040d400c0205003102007034a03d007100b440c0500c28800c0060820025144086110a00c0b007604012819114048151506904020b4100091142d110b0241c80c2c9100701011543d1108090602d5001d01c030b04035050068610b071a0140c4502010251290075008054100240400c1c0e082c44241d40b4450684800310f441d0820350b00d803114080c9444000d00350b0104196040310500e451038610030142c010100b000c00d859903180a40305542000c0b100258880c108900c80c08112282500020311507483c1c452082c05080b400b00c0d0f14210100d0588a1411a03980c42c00031800c002d25100e0b000313a10309000170380c082c20540c0010311003007500c9510302400720303c80e02d41d40d20500c03421442080b401c1e00717024840180f0360158148505640001507a05a804039645e0380d0342c0b04030f540340600030b0300081074012512204251850040500401c203001c000c0c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599584181 1250 599582931 599582959
    0x1061101050a180303180605131a06150c070527070e1f0c35070f06180606230609060a0e120601150e030607140a020f0303010b0901020c 60
    0x5404400f03003004013071540343c0d0142c0b43c0710b02516400c4000d080d00150144061b140c228400b403050020040c2c104daa092004250b0061102581c1805111703c0e0041d10138009d001900d00001041e4010461001c07451280c0140400d464440c024520700d01aa0031000c0a1001015040c50340c6800008040b0ac04010400716054101c0d87c1301170804c1d5101e003c1041040d03006020142c11a008001c0c4200507051010280700c144240092603001e042c4040c068803e0300080b86007581031441c510640e00041c0c4522031302d0034070902207443c59200c218580b84214012401400f150344900030b035038040d0304c80103805059810844c2125a44041032001c40400c031003091030104420001030003401000d40341c0c401c114148060740032a882d03c88000c2c07920840c1c0011100a50b0b540c01c85032181e040c000d5109000609103001020b4075050014400740519200d417514040d890783c00c2e40b0b850701034114004900841c4070300c105403006400c0920085028080b0100749035640d03007035240013a140000850740c0501038800307030404c18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599585431 1250 599584181 599584211
    0x40e0109030c03080915010f0807080a0b0c0a09120b1006090506030103080a09080a0b07020111040b07030e011206030b090601050102060903040b090a0312031505060a1704050307060501061101050a 86
    0x15034043e03030505040c0016120301c0446441c0c640c06222200c0b203d920f14001048084525440004844800c1e00700e80314603407078100e030585030079031103000030515004803022801c01d01d04e0002421015040e460310048459480d0302d050400326003c2400c3c0c400400100c1440b4117040d00c00c05980140145091008410389170801158551205101c0a0304803000415840c028501c1603020300018004a0104c07070b41c450f4a07041003440d0540540390b140c01766280c400046800c07940c035030658044828920205013003080e5074405864984030040c0d900c0c1044460060025450101d00c901009036005050090303051600c40c80f09450000180c004a05652040b0200314000300d0000c01c68058031480c007046a00d80d03200d030020400503d640d41000300100700700820702c4450350f4035510140300d0411402510b00b40ca03a49200703220441c07180c4d000b214005a05000081450480c1c02c844540251281007100d142012544a6000301c0c1c03000e030081c100066000714907017800e4400b4081e1580041607141d0800607202c03216406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599586681 1250 599585431 599585447
    0x301110f0d0f150b0a0e01030b060a03022a070303080105030a0b060d0305070206120702160510050a05070611222411010f06080d0509131509090f02040e010903 70
    0x100c1090794841880b415201c0b0030b030700491181046540d19600341501e0b888403144582080c1c14800004505a298541562007401041d9944501a01c030a00e0400c81c008100d02942c848840810400580600040f0000e2110400102002180003400607203007103140060046d801a40300ca486544401d00c6075021604100c082038203e10b007164a50020b104a1070305403454025544080d52106012840101401c28082124070400d0f0980c2a2182d161008090340c240d0402801650f4100541d4031003c0d500354003820017000b6a00c2c55041141c103146640d62410b040e0b50301070800209040e80890554203000c950385140d04030306665070520400c281803032098210003101c54402c91501c00701030010b11186010360064864014020000d000164043c1039100c041d0801c0c0c0319001c0c16201c3c1031150804c445c441c40680e0b4440704010b0280114004031719000d00500780c11455600544000c10002a401040788900c01c003482c8104084e5202c0c40030741c010401101c1d00e49106001036410151000d00180c2c0c403c4039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599587931 1250 599586681 599586697
    0x2f1e070f03020918100e030a030c02030c060a020a09051c230309040914010e01140907032001020f060a0f1107020906010c03051909050a0f0623070b0112020301110f 72
    0x603161020190184e994500310354800e90f10781d00c41c6403030418501802d0100080c0007e403e9920180102038050f60200e940344141c40a15825070844004151141165001000210400d113480c0c48065100c80000c4c0c85e00d6054641c42d000f4247c8003035a4000c100c0107035034000506801040352034a1a052503401a1030f0721980b45605d00c07859988584608020304a02d1100c80030000c0c100030482c035070301154018001d0a1500360b107050301d4809030003c0e0407050005a550140c0f540102c0c102082e1004101400c1e462408880090641c0a0002d483e0040d0360100850b80c414009204041420b58000c0661000c8035003011390000c00020822034800940c50352010b00d40c109200703290151640b01203040464183c01000b04d9500b80500054001d06060740c008007140940e1000c40c0d18040180c3d5503d03082ca030207d081e201700404500c0c40c5110000c000501034400000b440303142e035824034007442503903010741c400000d800c0540081c803203640c0304055007002d1040012105904c074229240000110300a0210b009081c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599589181 1250 599587931 599587951
    0x305121918471b01021209060402040f02090a0504150806040b0f01120c0b03042a08060f060d0224040603020c0f06150d05010b04020d09212f1e070f030209 68
    0x200310f19210000d504030344044403003003465015410007090503505c8180c180d800380d2240f4280008580103004503c01c030f842d60900180359241183c6403c0c203020150401c0410191004008030001400c100c09116051103a84110500022480d10310300c40d41c01d0300d206800000b10b400c0032154440c0000d83ea00d600c5403d54042c80b810540301da9440c038051391004842c40144181c1800008103042c11440c0359001c10980e18041c0c19030305540d4a590918411900c210b441d1603100952090700c81c0035003056081109001071906805685258545180849500c0382d480040040c0d40003c07030f8420240e042c09100001c10b5000c0180685050010305450a0001d0b80c800d00e210764040b00d511410890250312034880300310040d00941d01c0d2002d0103224401460020b40540c0c61465012144450040e803000c0c0700d070158080e4071503c0d03a101c0302c1240203602207195141d0b0340c03000340b450a004440743c40070002e04080d84480d807001e02c0c0140f2440146030810786a517110314a4102403100510040c2c0e80c40f6000c03648400050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599590431 1250 599589181 599589217
    0xa0611071a1603020f010f020906040302090414011802100804031205100e0f010f0519060804032703140c01090902090d12030501030512191847 63
    0x1c03031001c51441209107075090301d101440c80320308054010401e844400c0c0804020014214021440801e910540e510b0b07660014040000348010300c1d013000145d810a0142841226501ca044006d80c2160490020580500c1030740007000304610740940001818541468400c0003818030740e8003d8803200c80590b0340340046803180009180945c843d00c1308001004400c000603e5810a8103182141200030700401403030303580c1040c1c08203450400c1d4505a00b060b00f0004100040c528184040b2091540a07004500300302c00351110b03218040c3d80b184522503005504003110000740c41c601e001540200c207800180c140c4c1e0844007200c10b50344e03080700503c2c0884000040150303807101c00f0350018805101d0303003400509065803030000f0300301203a06a0100c0e050364814001c4440d95000d40034042d400d03015003010345141d920f45514503a402446402c203e5640440c50007242c10480d04c0f032171101149100c20008001c03a21710310034902096100b0410b00d010400300b2000c045100303480e050407001d00d0f01c02c2c07c81d01a9060819 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599591681 1250 599590431 599590469
    0x604060504031103040e0a0608030c070605130e0c0d0e0c21101407030b0a0e0c0c01060b0a02030a02070504060b0901140f0307200601050901170a051b0a061107 70
    0xa0005220f890318203109507a0f440e0380b1641c6401c02c004099a40c1802146486030104d82d03891700008075107010000300d0003008500c2ca0a00c04544980c4020054460340d05202030004120703884201013401145507414003501c039002d44010030105d42d4800c5d220341c001d80c8240700000c11511411840c1400b03c64600204012948401a4604d0210050b020380a000d1901101040861850034228001c00d0613035000d00c082c1e00b080007048940c0d1031031300441c55541c1c544000f18001d0b040c08401880c1e408901c82c004910349958603d8114603410a00011000d604009042150790345d0503c4000080e2500300c408018882c20300c0310b03014550080500c0709050200761110809211100000c0c2c50500e0a1481c001b581c03440c1075100140084628881c80c0c81d00300d22020a1100184041401c505941014103542166840c040c0142e807090401000b01410380a0061200003103841403044400d94001007004038151450742040c0f2271140d00f03942c0486e041106214424150304004651801104c0d16984007c04074600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599592931 1250 599591681 599591687
    0x121091109091f11090d15050118060801090b0c0f0d0e0319170402040b04020403080301090204050a0b0c030d1a03061801050108010603051f2003090705060a02060406050403 76
    0x104140d060340003225400304002808002089544110f249111804140380611424141d0345a24180d580071001805550360500b00340284035013450181e8102c21000d0090380313250701214000c0c4c0010b0b011642d40b084a0403c0c03940c0380a640010b145103002003201c500d1313680302c44030540f101400109640301c001403018421080201030382c003100710310f082c20003032880708800d00c42c3d8039070100880c00b030340f4484000403108040c05886044c0c0c51250a140084c01e40c2e846078200b000406205500700c1e4048e5081c400030001c0707040b03a0065806017080d2400103036107a0a09040101c03130415940042e191000c1044810714a0f2808002d030b918600e43c1e014007090080e25000d20740103c1c40c01c00d44440d01803251030100a4440c41c3c1e02010142100300c04002c2010b640c0701e2030340b1030a0380c01c40d01000c1c0031980301605080940d8801144500d941c8150000000e440c240b40c0c1509401801640003500c081902005100c503d140510051b001030008030303a943c1c030780080c0000181d22914001c1015001c1540da5000400b4940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599594181 1250 599592931 599592953
    0x8120702040f0b0312090102061005010f080606220819080f0c0c0402030a0b100e010c14010b0a12050f03130306020d09080c01020a02010b150304140a0c060507050c012109 75
    0x3100405548aa502085d4006010340183d140c2d035005104110100c0c40c50103c030400f0f030042e204180d5448113401c5860900b541c60000180000b40c021b402009200301d00c2c080c000302c010310b983d2240c0d88403810341d141103000c5140c5019142c4a41004002d503116800113a400001c440d0800f23540d40c01a900d90b02141030260500303e1202ca680d400c01e00001c10000d0444031903100e81d8036100122141d40c608803114404441c2c40249680c201e010900741d648110100344401e02c80c40c00c5415106c0041138062001c1e0114290342e0840d4803e8064082800f003010800c441801100c0c1d0f983e42401c000d60602000c04402d00c13994010f0303c0094403669000854519400d0650801440b05411460307071651040300240e071500030741c0311080b01001940b0f070080024461a00150f9460281c41e203850413400d644490726410300c4c0c03094014213011948542c00c00c103800180040580c80082c0344170b45506458002e6810001c0c20440741d60650b5040000c0c08480c110314031159191036080007101c0400050380c400c5468050040b034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599595431 1250 599594181 599594201
    0x612050c090d0314030a050601030f0c080a020d090f03050304030224061203070203060f061903053408031b0102161e140601090c0c050a120c02060d1508120702040f 72
    0xe000000c006606c41030b40c1055001e0780382a40e0400124002051203800c6070302e1900220001031340c907404960483c42d81e0b0041c10b07042c90300310400250b91400d0369646044814503042140454004400c00040c19010701038001c03030480304d5201400301511100602200c2800401d003a20940780d01d1035100c500001001070b6546035a010381200c1880c14038001a00d20904112000e6105502980500e030044050840c00b13000c8960150080c24020b040c02c030548040701d103049291590b0100c1c04503124400d004845100c00404010010310307035892444103401035000e056075140002d68010088070109411101c1110b0761a900042d008100d0a44000c01c41c40d0143c107100b01400d224802c1800c548400c0001c51414102d0340d50010422181c86030410585600410103c09009038010030f025074040b540300c5004c1021000b8518241320852141d50008030380e60000905402c0442d41d03800b0000e00011040702c4203014245010040040310450902100c0714410110024015078a4005408141800741c0042d8250 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599596681 1250 599595431 599595467
    0x110d030806220c1d1203030c09120a08030f15090a0e070504090602040510020d0c0b07050708030705030609060901050a09020d060b04080a2603011413060f0612050c090d03 75
    0x1090000d500805405000d105081c4540300813913200ca0390b14140035026200c0c4401e501640c11603403402d0348240c00b90008080950080f010000014a03c081809080300b028071440c01c05031a803d200c0001d051036000144445503100a2000d094103c6da28500c1699002489920215120860f80b1781c5605020b004d5001c00d40050a00710720008010403900508140c030000e4481011000032920200c1c1e460007907410140c040307644a40b601000c40d0f6102c0400d580a189820071514246040e42c030982d81d50320450705d8400094010040c400b8078603140f0100c1c0d0b00500204c03603245180d41084006200c2c50300500c41c01c0555903000504290361211604004010404090302d1615585d40b140070544038400303080304840665500c0c80980c1d54444a20b500380c10f0b9004140a14110780c00c2590951021310405001c0394041e54619104018149034022180640707071760f100300308000f883c200024100440d0300b440300708050b0400307041104118110042e1211284101c424440c401c446080645030740200f40d00304446 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599597931 1250 599596681 599596691
    0x515070609152f040e040f031b0c0305100e12091804032604110108040305130f08010606021c031e1b090501050c06060f01030b09090a110d03080622 65
    0x650311100050720b8400d540d143c80d894100c14030000c100020710a43c001e548081d40e140c000304021500103580450054481d00f41810b18440400024000c80000c42d81100c20303054440d403e20401105005040842590920501099451003541500d48250041c22080342c8404244954141e075502000c815503441c0820701c0c0c80b242483d08008143c10044103081f4001660b13004003280160340000564401e6030840c94402580c0124801183c21000107001501004030034010314640000c000032500080900f400510300191a01000501392101c590001e13056400880410300c0c0b100b4929403440c0c16a20a29000500f10316065061600d003d03004030b8100103900c0c2a4203480918011140c0b01406d0710380b5200c0c1100142e0f1100111180d100d4075841501030b80013075002c9003c500342180c980004100504000c9100704007440841c5144404651920455010355285003d0000741001d003005503005070b9101403400c3c6583c9001d060f485018100a009101040b90399001c034111000022401e44d01c2542406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599599181 1250 599597931 599597951
    0x8010515070209012c010f0b03041a13050c0102031e030406021e0a1709030a0f110a05030909220f0f08070b06090604021e0d0f0e030a09051507060915 66
    0x1515080107280c0150000030070803d191440705e145041e040b1030202d000e070a9a00d0600100c0c01c0d951704083c1c0101c800e1286d650510a011031602d031464031816038216085c04007070050501d03c0c0303408030341990305056400802c051800310541e5924501c031015900f017000e40d02d45843c54044000d00ca0151003420011a5250040d40d0021550040440090700d984000d007821105501c1c0313400c0034040d24a0b0390940e20400c910b40d032150080c00098000c4009003441350200d6040c020b07450503c2840300d401c88050700005064111b6241c100ba076550414800d2100701c1c0c402c1513640c0000c0c0f01400194024140d01040f0040404000d50002d186035015808103065441d0031041c41c000340c6507602900d44621502810340012800c3c1010320035140890464011420800310a50030714480b40d02880302092400d031101d400717003101d0185020f481c614120080044d80c1d036403d80880180803500640000c1e1045858201c420801e502000589111035045040003134041c0044c9010800ea0701003e28400d003d40c102a0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599600431 1250 599599181 599599199
    0x1c2a0f0b0901060b04151b0c17060c030408040303050c07121a0a090c12020f0d11011d0306060603070c1505070215061008090a05070e0103020a060f0801051507020901 73
    0x540108001c000a00910752107402c8600781e4041ea0080f0703400c80741a40d240c2e41046120300d0000009030f0440c20017000c050713116105d00b40c0c4038003d40c00030102480d0105030700c10320311010002c0c140d02c802c80001250550a080c1d4078800c09102d10301c80501003000104044001d8202400300030001c00b0340c400d0414000e0203901c1c000283d0207030403a03054403202000000504007211405139416042c0c0c800d20785d2030103e0030b0010b8400e00b44000201680c100e21262060a0a500c9081221701914007900c145500051103500052400c038020f20800c0c03507030240d9221001540c40c0020031a4124204460381c54a030350340c052044800ca032407824060f0106400201c0203800c503845030b218a009085581c25603900e0380c84410061201d450541c0d507039400c082e55244500755544074058054002940505a5083c501c0940301e107807030101681c1000c0010100080100704500c0d0040c1c0f4800203084604003e1900d02c0f45c3c01c0017a026130b01c14450f0318003c5403400586a20080600120b50031103500428040c0706503100d007005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599601681 1250 599600431 599600453
    0x18080f0715030b1f0e091e1b0d0216050102070f03020c2d06070b010e010f170606010f02280b13050703080d0f061202031c2a0f 56
    0x21103001c60040c8051540c0301e40109900c048010340015000854000300d04d1080142034440c0b010040c003450710000070b9a50120007406440c4408041c10f140300b031800d2110004101800d400d0000c10303000c0c0304004645202c000d680c050002c0300300058560b18501a40424643c0f049402411944000f074140308000c0303e09068401c280c00799003141e548000721818804074012000c0110000c0d41944001c42030700c1c040c969203540400f0050301060030070b1100d6990f05000c9400703130040446051058014885040d400c0311000c000d1034a50035101415020007242e0791507001c0131749140d04200501c81031160a07402000410100b01060043c01810400c505228200ea40038103402ca54400004011484031117103501d4542c5540d41180180241618558500030540e20541d6450302c00c58807901c400f8144052480f521000f4030401720311170143c2c241403040500309844400d0b90124801c4d03040540891a5100c5240a080c140b80345002c072342003064101001e48400c4030a03005000007070701b012280401c1200c03142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599602931 1250 599601681 599601689
    0x90302060a05031506040b16110a2601050402010509101709031c020f0f180d0b0a0f0501140d0606090c051c050606121509040506150307030c0618080f07 67
    0x20b10f002613041c142041928030491181989200382813000400b10817112030003180d01441901000d280000784008605642c0240d030107101c480b14a11242401c1000d8001007031068584032000304a03d2900f17038006401d40c09240405ca0081d40c2c00080807800c68000d80b452160180000c0440056203071240455680381c1c40801c0c15a100c441141b4502c801402034002c0d251b503280114200c80c1056001e4034420400e0b08911298520a074031004940543d440392250040c0c02e9005080e095120325110030004180e444000d80d0004440c0782800400080c01074181214007910101c5a410f058510ba04111019101d50b4209450b83e82c0340500704021250050000c0c503440500758942d6417480c2c2000420340c101c4400300e0b08903401000410800f2210499840340070740c444c4c4124000112881c480c0042101200b04940454117603010b00c00340000b080d03454018040b0b5680480050040f9420360fa2520b03541015403040743c050180991789004d0010011204030f014200c0b04080710b072009603540b1681c0d590145881 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599604181 1250 599602931 599602951
    0x10f06150203040305150903071403210421031e0b090c0304030e0d150903120513020d1709150409061520010608010609090210170c0a090302060a0503 66
    0x18880c01100c1c00401070310700304c1350024090060420100360f110300e19507008120366601d010400c900340c0041c61612050a0310709140c1d004603194914100c807102020000d20b0340d001854032120810000800000c09200e2548031443c55500400c0301601c103a01170a01205c1501000e003600c000c1c0ea46500e019441aa80c071501200d100c071040e181d000c2843e182c2c1c4410b80c0c02500181c10f0014000040c00c2005413103078454461542031540100701014482191055102280001c1c60100060350460300c5004194101d4500445040e24024a6000901c4194038000040012710203224891a250307050058805100015003ea503001000c1d0101080c65406802000b502c0c074600031b404600c024580071104a252003944482c070f05030015100c2804141400d402c0c0700000d40d00c0d2407001c0780d004428000c64004050004020404102e81e204101c0c1c0f01c0c1d25265280c1c100810740003642040600381d00184d80001039103843c5542d908014004036041c0340d445e08007941110000482a5441d43d21000139482905001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599605431 1250 599604181 599604209
    0x31b12031110090f1a22080409060617060102070f030f110303030702030406120b0f090a0f0213060914010804031101180b070815280510090503070e2203030e010f06 72
    0x11030000300f007034020b9502100d2907140c1c8078422116428240300074851b078083e500c0c650502c1e0f9281c6040043d1401600154001481c3e8500221140259120741e41c00410074005020b1160404145040c2c0c100300d44000b0b0854155030040c1014000d0440800207002800b9081d6596498205000303075480c0d0242c452403000a000142d98015015144203c2501d15802021f41e1501c0469108200c501500a0144980340d0b68481c103501039141580b00501e40383c1411130001034514078104015002400a038080c40303e03044d1980101e58a682d001d41d0280c0c2c0107505051960381d00f000100c07500e00610001c1180f032041c50103c010242880b01d90304160b88199602d90b0303401c6495441c198a0701100d1560301c0d00345d40103448098281d0680c2410f02550203c00071340742194144036038801c0010b55644500441c40301107415110140400d090610414019005510001c6c2c120706009400540c0c5841c03080c4041c451507000e0601c001098403039045000039905000007130001110900d42c40005090622401004407042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599606681 1250 599605431 599605463
    0x403060914070e012603120106031b0306030c05101407030503062805060a022a01090f080604060b1804060b0310110912070519031b12031110090f 64
    0x3c00e08241650ba81c4110780464a403840c01c288500e403400719041c01c1e0380c081805070714440184000c0241c020a003540d0f0110b45006003003030f100340704003142c010501054101241400071481c40103c240c1110310580e0502d041407450b980c00c55600550300d08100205600080820a1560142c05140035032811909066446003200c14422460300301c0c80c0507144d04007040420806464030700c0140103049981c0c015203050030080c0c440b10440b1031051b514178500c900b032035040d2000c550b407004d012006070030081c481004171424440d1280e40c0340c0c80207000401c080d480d01c0504e4081d07114641c2d4003c0580310607a13595900e081c5072410070702400021152314082d00c1015034400f42c1c842503003d842c5640200c207107a149080e00c007205010707182c0365240d1840c005100d81100002d8541710040b03806002451503082116807411490700b03100d160788510041803002c1070b144041c80f01c100000b00120700e569241c10101c0c03503080429021418680c98051500300281703846c0050007444100e00321880881c2c81592403041b60285 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599607931 1250 599606681 599606699
    0x72718030f18080304030602120906070813061e0c02120310050103020706020702030304080318010c03080a050709090c1205061e090901090206070602040303020d020c090c0f040306091407 82
    0x881040980012811000100054000c0c0074588866942200070305000d619910724030b1441e03010782e0088030065800900c00d04218554042341c2d070007402840c0a03182030b0a15100c01003801c4400b400701d00508140c40c001e18104142c581c0010280d01c0060344048d05246c501c40c440380205203840d100310140c011346421100801c1d06500701c80c0320754984d030f1180d04403d007044011402500400c10449100c0e508210742d17409aa02000584020688400296601c268071142480c1c4c82d400b000c602d0741440381c181070300780000e038100421039803221100e01e0000d6103644071401101e0089041d482011002d107405251901942d0000c42d04501429281050001d0789854090100d50f6401c1058448041720407070201c1158034003080c01a8010100c42c001254401d2243c0000f03040e80d000c80d00072150307180d00003810000c00d60180305008000301203001174801d18005a0104001e00d10040c02860345110000d00a0a0310840605540c080d54009404202039041c914200e0007084030620305000310302c6410400200007035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599609181 1250 599607931 599607971
    0x20c0102120a03090503390706020706110a06110d110f030105331804020c061501030905072310170c07021e040b010e09040b0402030727 60
    0x86104250707440d0081c2c24800318000c0c45141002c44890004004580903030740314802e0240003100341c80c030200c0050018002404000101c1941c102d05411039407013005107030380225254080b03c14504008107040c40180082d42004d1060a00411544c9044420302e225004880a040260fa55043c104480c080100d40c3d11050f020b003280e00c40041c1c004100500c01424030b50181060742c42d070204580c0c804105072408001c916a04043d140401102182d9032000141d88143d0703031a2560203440851402c000c2ca80000e803a840c000742040d1400050004002140e403007a071011880301d0300681a00c04660f202c0b0b210703091941c003010004400381d00c0714038489890b240204d04076114940a84581d030803910307010040f030b660b840b0090000c1009441032015201580300c50781c8100181d01126103506020b110303d001c110031607218540c603d0401c0350103245080782e500e60700281c030341054101c510301c41181d86500c0004d01c3c00c1c0303240d081040c8071150054400100303903041080c4207144480c2c41040c01008000360b41c42030018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599610431 1250 599609181 599609203
    0x71406060f040b150d02070c080c010e01030603050a1704052e0e031c090e040515010f060c02060310091e0606021906150512100f060f05091806010312020c0102 70
    0xea50003642c0a402032284c40140010404808003501f840320a4035623040000851f40718072110b80101d2541d01e0f2a69000c0d1010112501c2428104a03090450300c40176034a5400311802000030808100640c1119084070a0b2002081c0003480b075481000341c4240040205c0c0072806811418404a0010491038000ea203d031900c0e100150040c0010701400d040c80035041d0880300c4600c04d01caa00038003c5040e07000d0300d41461003a4005e030000c02084441000105503072005921110348555180c4090103807950259440b0280c940448803a070301c9480303164881c042e20f2881da004100052511354854180c0e0001400000c4514100340b04021040d0342c0c90040c0e84442c0980c130a151a00d5501000c1000100c030380c1e01501c26485103044603074105481c0c5010a0071070030304080c4910705900c00c1d404c4240f07100c0d650040001082c451207041c0511441e00c580728400e82c0c55401107d01c2050404005000302040240441250340620122051540d40e42402e02c1c4906001c3c043d6001405851050813075940002203040e415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599611681 1250 599610431 599610439
    0x80606030604020d0f0b0c04031b0f05190b0d060f0815071215081e011b031e150e0708070e090c04090905010f0b120d03090206071406060f040b 63
    0x1694a940c04c220351801404d204a95014800300d04c0400b040f0494804c80c81003054004841e03407a0f0940c20603641502c0c030700c0743c0c1001103241d240d02031044540b905c465108035481961244020064080001580c191076007048400042c04592a411610030381c02c9401150312a01114040f1520340f050243c40369895401180f43c0c0040e640424031184c8101ca20920003015500300203820000d240c40c0b643e091800c2d511904403079000c45e85116061031030500b40300c40e81600c07030300170450307000c600c030f0004800c481030b001c214149a91f8000d10304020b69403110315407945002d00d108100c8068108504405100b582c0070744103d42c00346100086080307010341041405404a5183c2c03a002c203000d1000c100694400400c503460141081c440002c0001072802031404951041c000801d5103041c0c05203000c100d900405809205e42c0684104040a41000c21401d00031501c910300403c3e07800c0e513400810307014443c0000040458507251540091403901154884c01100125112202d8008580800040e40c9440340500e1340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599612931 1250 599611681 599611693
    0x3c190e06041109072a0b13021c050604062c07090f05011214071e15050307080103030809030f1902070f231203040f06110106061d0a080f1608060603 65
    0x1020101075502507061462409a1500030040d606c060107084113a80043c10000d881082600318038000362094034035041303030407546010501340e110b03103a48007800b50001d02a03d40d04c1100800218001e60a00f103011040750044800e80c10101d412959043300d0302c1410160380c509200280c207030405000d901e0403100c0794045041c008003d07464001a034102003213070000074460f5032800260840d0303c5c544400082c0c100c0c0e1001c000b1a2818604980580000721090b080010030410008119044400581500d815141251880d07075407500052542c0b04072007007100050300200d654440309017401ca035010403902a609803040d451340e443d0601c50412941c014031285820b802c008004103010b4070b500003440003006001c9501d03402a01e00040c250390294200d01001c2c44800c070305000164010702c904c0325154555008020103498064000c00b40d03203203558801190007800d00b15000302da9910103e81b01030810502070720141c10040e4500c60f0354841d84488002e1240c43c40030006070103540811911f110f81c2001d009401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599614181 1250 599612931 599612957
    0x10806040b0723090f15120a060302010f0813170c160303140904020904050406200901021b0d0209250216050607020d0b0f3c190e0604110907 62
    0xc040d082013115075004441140e94810302d03070b51080341e400e01b50710740314a080d0380f412086580c2e100340000070104004141030000800060768480403501e0140c80d20701d007111164031801d041d413910400c0310700c1c09005034009285950042910a00030000302c4442000c45039441640c1c2106000e880349440081c011840c1c1c44003004182550400400c940c5100500c0107140000d41e0380040d04039036066406454240d5125000c0c8540c005091016541d82d0140c102c140c184942c0c440000d54030305000c85507100166100c85079045980320116840b4615600400c0007023245400003103582e481c10040059044020700c071141c0050140042606400d6588041041d25614100420b00029602a04c0100e8200c1d00e142a940f01050700c0d91080d9024601c03280011246007400305242c0d8007240320342c003400f811040c03134100c12041c44550b403055265412065a01c40b46035541d082c41c03c01c0c8212a895092400d820174118030640c03040403410303074030592041d0703884411114440c00707205012000305c610074041030254046c25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599615431 1250 599614181 599614247
    0x709021e070302010b041a0310150e04050109020901120c050f0604031203090c0f03080f0306010e030703120f110a0b09010e0a030c0b100e070c05100c0314090607051e12010806040b07 80
    0xc510205080c1404180d9640c01c00c40d030310800c120ce00395141d9540d1200001146080c40c441070043c10a100c030380801e0f00958503500d110a0051260b10310071130301d4081035261601d624041c2c1c1d0045801c01e4245034101c600302e4000e4081d042e000d07030494082c803045101003850f5008480030400e0b00e0700101c40300c0c00c22200c0b0103420b21550002e84407606000051a01e403d507554100940c201651091941403038800ba5880b000e4601c4080c0c8040f40c080c4003498000c1ca1400000013594000940c001100b1642038640203401e0780108050b5150602c14010f8098241c203142c2c200d0f00d50890188070b00e01c0029143e6036040381015420f864011041c0e22202d580100d1001da1151845200183c001c1e8281c4000d45440c012260403961014080000303c0d4031510075441140c031910f511a40111844043e006914041c3c200030b100f80315100d4032022160b4584c6a81d00c9880140742540c0034a4000c2000f0212540c40c0e2484584d10401200c0444040c90403100050110348103602500680885d601c0942c01462a50451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599616681 1250 599615431 599615441
    0x3070b040f05060106050d141e1b040f080601090c0e010c0804090203040b011503090309090c09030206030f0414010207020f152209060503010e0709021e070302010b041a0310 76
    0x5035040c00c52007007a40049142489114001d1406446903a81c48080301c41d00c0f41542e0070745400306015070300702c0208060302c0981440c01c00c030804180030380c11403a0385501c1900100c0c9004414480100703008a0041280c66048615000b6508000202d4482d41e0742d905144058031401d10031240002c2c00740c20310781603650041d00b602c143c41d480b0381d0388a81000d80703c5102c5400c90f00101e0341507a1500c4c6140040014180540801401540d03030b01d41442500700380d0b1006810b0440b0b0b8410318113403030383e5142103e481c14403a030141406964000c00d840e80d28201301c0c2d00c007042d89205403000d4644d480d0708000c10b491480148200d4590366409030440d15285141c204002908032941c003180e0340000c04108104180210419006111841903005a695410280582c0440380b5075046a0300bc1d80c540b492048040794005901c400716201d02c0310145c0d888181e4228940926103100d621005070801207810000c041c0c041d0068800500d055408010002400324204100c0c103a803031a071a0950050100000d14080075000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599617931 1250 599616681 599616683
    0x503010b0418060207020a030f03030b010f08040f08090301090c170115030c09020901031103040501050f1008060105040c0e060a081e070507150e0f03090301060b1e0a1b03120b0108010803070b04 85
    0x4000c940d0341c8c0d44540c0d821091220080780000d0740c0b81240c68031583c00070003030080e40b040f924110300c040c0780c168cd079224284001c00000e0101c940119202c1102e90b800d4206440e071540c00319a00c05800d03503440d940074001c1804524000b2a50070407800550869507820031100b100d03040407020816500d03061a28009500c803c5072141016194a055601c0680443c0158050340c0f08034000120391070816080c1300c900da00507001c4c030075034444854100b080c1d880004101d030548208550005100d205484103484910300c0c500500e030012070203c1c0c080e000f250417032250ba228070003400741c008803213481c0400c92800e600100c40303020128000f4003403a004a480b032000c99046c0d0108180020b001c490440d080752404400d01c10074840703a03000140081c140d09084c080d160052a035600d1150030440c400281905031300044c0c2e89a40c400c4004210400094450140504002240c0b00050b031525401e08000b01002d50341682d1b100d07001e040070542c0c101540300b06c3c80c00d03048070100c101550a1911680e00c04e4040500984 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599619181 1250 599617931 599617939
    0x52404050d1806050c0705220b0402090a06180e01080d0212070b0406090c09060f06020c030f0a020904061b090518271e0309090a060b030f071e090503010b041806020702 74
    0x801040310740341c503442c0c1100a400e07010010016450f10708d05c0d80c140c8100301040740c002c030300600c050b4403603484484a00c0d040d0f6515080803c1d481c581c284080148080d141d0005030801202c200005944a000c54a0000100540d0075a45080141006256103100e205001080d68041d00d00040104100b030340030040d02c0d48510074040c40603907158450300665415401060001c11040000c0110540406c0301010401c425009800421420000320313403034007d0342c80c010340103503010700010301040b1090b408059400015500c440c1070440110006013522094002e150041d4000ea004e10340c81d9518140b407610802e030030a068100408211010741c80102c1c8a52022018440c00d0844401245406404850b00104400850701c4172084400c02c01107010184c110307080d0901e0f01c0400d004040341030046a6019a44107003405c07041d100c03040c00311902c1c5c9044150b81c070107100c010710038803205074402100303422117804070028440040040104002c64040004000800074021070110004040360080c0c46642c0c0014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599620431 1250 599619181 599619193
    0x40503161a0d1b0509041a0f04020f07081204031115071809020418060509040b060f01170f160215041704081905070608090a0f052404050d1806050c 65
    0x42c1e010f00020303107801042c9010940104150310340d414103210310b503030a4076240203601c00c01040f2004114004040446280100e0f0000b070b03051111422131080b1003225034400600c0340e0f6810041102030081000341c0c0c00f10006045402096900000003909050030fa6003403400340c205485924060b04d6050514280c40b041c101c44600004118050b480600014480d16401e45030815a10801a00300c441c5500518030a1b00c07900240703c0410014201543d115030166042040040d080d070060319942d96062100160600b203404114001e484140c1580c02100500c02280240c0c3c114a02aa200c031004c0400c0800075914500003004191303511145542031220a4640d45400e485c1c164840c1454214040c00756031840544141c002c11408110807030040c20180b412028078140507080c42c0d02c41c00c034454040c28440310160340a06004081c410800200c0700d21501c85289041500740003e03c07070302118262254080c003039445010a000e600208551100714544d42240d608050059666420000c146000342c4140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599621681 1250 599620431 599620451
    0x210e0607050102040905010b07080406030b0609100e040f270f14060115020312010b031b04171509060433091217011406070503030c040503161a0d 64
    0x580051500ca40108000340c1ea45007030a510f5015240180c0c003291005208011010129044105440a854440c5004224900807c00085c003a0045401c05948000c04100c2c204d1543e80103405c04040540c00c1d601070203da42214250012036803500c100c00c1c00c1c400a0641d000e080d0040e051100c80f40c2c2e11030690001c2c0807805072509410b8080c0010311070b80c603901c41c500500040d06005100c030350303840e070a10085150a9032440c0320005000107101e1800c00e0100030010501300007400660720810340c881580c0c1900c90f6580c240d40304c0c0640505055038942e010341c04120180010001c0028030404030f540007000b02c0d403115524258034000101106012025800c1c10046503224003280700e00c80d5500007000702c0d900f9460b09200041c400d00e40b01c01d009200900942c81942030114107050304442e002d01d060320206560a010490b544200c000082450000004000c40398880c10050015034405504840c0092107070007442061460502405c05840501c0d41011110090800105500340c030608003c40d4075251 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599622931 1250 599621681 599621689
    0x82a060405060402090c0f0a030b1f05041404050c12042a0501080f10150c02181b0304080702040203150603070c050f07030317090a0c1401090e04210e 66
    0x150340c100c0d0780381c000c0428001540b403d1131485800c005260003d6181000900e00d1124506c6003214010a246d12042e198410b81d0750000c80e1400060110404400380e280b00c06e00921b1944240030340140130007141403002c601c2c1014801e062182411061603031519941051300da98107000100304035031030116140041c55036080005000b803a1040d010700300600030f0410002410841001340881d00c1f09600d4001c11108021410701003045491418580d44007500c2e200e402c40c0c041e20807a10180d04106902801001010091090f512030119103621303039102182c0400ba100e00d403109a0f00134000d03660511164016140a0b0300950b00301882c901c40305040c2c1030701d0004c0fa0113034004550200224440000300014020184000080c1c0c0070498064580e490550740e015042515070028003012502c02d1000540c486e1003001001c00a9801040005141d50748285110024407966881d500041c06404009103120301d41612901859011044c0740080d49181020380c0300f4607200384540100543e1a115080c1515 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599624181 1250 599622931 599622943
    0xf030b04110a0e01081c320a0c060b09010b07060b0a09050906092506051804090f0606090204360f0b0109080703020102060c180411070b06010c082a 65
    0x540c07020030100e2036240040040c18040d04214420308171b00c840b0392403200c1a40c00192010791105400c80d40700d100a03001048030701a40a1161040c4403840001c968001d56081100410528403501b8244820070343c0c10140004254203109081c01403e040c85490006032003504140c2c0c2d19140a001140e00b20b940d46400740c107560341a11f414409800080611040d9002448002000e2200c0070703d29100e0100030180350840794491042104200c80030400d089074a045c1c07030004071021f0000f0420702c10741039a8106448281010401190038529002c2c0009004105000b65011108403400100000c44600740c2040b5420748030240861070390101140c00000b01c0035205942c0854111800010b48010040c0094030400307194000d449540c1c0681c108100507a800200c40e64071285402a554482c41070b071642140c00c03008012220b0f801424241007401442c007103400b42410a0143c0b548011680f1032000558040c0e001c0100a042040100b000d00252501d5129a0b16041401c41a11440594038200d540c2000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599625431 1250 599624181 599624189
    0x9050313051309080d150302120d0215190209030a020306070509190e13020d1205070303240e0601050409150302010e03061e07121d060a060f030b04110a 67
    0x88140c14096401d107684040e004490300c0000f000705942e143c0380e102140c040c4002c107984031600c40d8610f26100600391000340056502034114100540321100c038540340c0700704e410034000511580340d9090b403410454075441d0090300248400d4200841450020020354030080780030343c16200b881028801030320204103880c841c0080c0d40d02d140e251b034070f030008000729444d8000c1000101c0c80200018030020a03c01340482c1c01240304c2001840c0d030403081c80410104444054040e08201090849140b031541142c01001d80c01d109550030801302d669107510720010700e4a034202d40c40700390031001c0512002009652080d000081410600d0520765129801c070705a9170050b40300001452000340800865030802105065001c0803801381240e03103131400110441c40c4088243c00319640702903012810140c0241d68002154442d031100780002030346080600810742d20084100706030b109000010702011351522402064806c0e44010141d10384c43e6880b55807103940f01400c1030b01e46401111007040d0355556401410010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599626681 1250 599625431 599625457
    0x110607050d0c060b0d050705090a18030f08010603060b0901080702030f0a0e090105090c0708090a15081501020d170a0609180302211603021203070201063b0a090503 72
    0x400580c0c43d203030b070650703d40003441401030b003100070300100080e00840d4841c10383d072095501202035510510080060701e01012100f01c5140425840ba05056014840c030131041115160140c0d00d036a40d180032012100a0300c0b840700540000d00038110590b00c80c01129803c02c040e0310480742042078800d044805075106910010216031510a41e00040c1003003100c0358018902101c2d041c2c00c0b45404030702480c651081c194002e00c460000600c060080da500714803600584902170750f0702c3c0c440c410140040c048440688160400f4018800b11135010340c400a0782d00e9030140242d40e0f003a80b101c0011003412500c0b001800031030300c845e00d513000400c3e01c8400d0f100e07103600c28052107955041c107541ca0601a04050300301c141c5240301840020150304143c2c58004585803503400031307201005800d403424120306011904403403503283d440c004144106603074150001d80903a008c02e8614813114040c00c1080c00d01c000c0300e0201d130821001c040407030400b60440340161540141c1d44a00455002540d0392581d003190300c0807401d1886 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599627931 1250 599626681 599626697
    0x501080c030106090e060403050c070f03080d0e060402031906092a06020102070c03080304030e04050903040609080a0c05101b230307200a090603050a032604110607050d 74
    0x141e1800340201ea00800c5000c1c0100800c5001000542c1c803000d000b480a001e0040015101401071410007441c00200143c44c0b088900da9120f00d0220107541c0f28a42800a030350800740300d1140ba810210300207015650050003410b103c80a005181c283c002c0c0d40c0010b8a5144d82d50007100049040d401c0c4c64482c0750740d44071407841c1003448007140b0759914000c2e820040843e071040c002e10000030072400d03000040d01e0304200c003280c0f00d6032580380460342145c0b81d04225820500300350502c41542c80000152003680d00981ba10b9161985820846507504481400030302060001c40e020802400d10710800f410300d139100c1c900006900602d400344070f03407411000b108488101000c080b0315001914060402000c4009001540c03810a0365191201d1004910369403040c031038081f4065091a0743e4605100d402400c02d03103018032002da40ca041071034491141c11401d40c00f040380448824488810300300ca030403104817080000040c81e10750351158101d0106081d81e458211004101140120fa0100000704030408695030303041c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599629181 1250 599627931 599627953
    0x19051b031e0106020703030f0507062706060911070b070c050f070e06060309150c0c120306090a02040506040b25060509120a021b18040c0608091903051309050108 71
    0x190755030050340024115046603d00303100082d80000032650419031494043e8540500b400c6c4200241038480799036580d101c140c0782c3ca00008250007200c000703c1e03009a004020f03083e03a4602110a0b01c140f00b00000e40d020041081ca4002264010f03215007100180c500500c24040966841e490086078030340c3e40d041076000380b0040240b0f11000d017800e5404602990300c0342c2513040c280c3d07a442d41e80c0360003808009501c0300000010310030b0710420241c0d914990440700b01c5005801401c620030040d032082d02c855000e410031400041942d40305000710707402c41e48081c1c4407500c1c0918158480c3d009401860041d80d0604465500c5a800c3c2140b08013410824002c100018903405d040c441e40745002000800c1501c030740f10a02503c4901c94010624180802d0054000301c1c0364a80d07240021423210903500e1030004150134005100038044401d0301c09090b5203d0b61107008190f01d0300384159559110703400300003050500c06e40c4c0040000b441170024003030725840903a10302c40460310b40c0519421b1707036002d800210055102e099805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599630431 1250 599629181 599629231
    0x1e09150d0507030b06070204020c0c09131104020309030403020112110d0c0206062b051009052d190807020307091e0513080306012a150519051b03 64
    0x198000d0b005082c10442c0d92004000b040e000e001705800a807007650b01003088a902c0f10203009440b0754280080a81c0301918202031810110200b0360416a804040861030844900341482124002d1641d00010340c02c0070301d150b004440c42508004929021a02c8540d200d6074808030202034800f2050403280800c1040d0b40f10740c000d2524000404040c4a80c0c088400103104400c1e0760441d03125031000c1030704a0741d102e01c5410200d2030242062240030781545850303030503814082e0200303512541c03450340080051003d100c1509100c0303064880d1900e12003500005200c54181c6040100c0841c95803103020603d0030f013030315900003074145600b5510646013151100e00c0d41003007488110b0545e001541d018810060f07401d040143c100b0030008001c00622103800000801c06580c05441d0410001c50014456400350864070781038103281d800034500712003032250720a49103000074050160300c0c1324854a009400a80982c410320340c0c00f8041c0a040d003010070000542000c00a80d014000754440c40410040b030502e80c82080c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599631681 1250 599630431 599630441
    0x13090501080307110f09060f0111060421050c0d0e040e01090506090d05120c22060f02060105090c1806090d0303022104030206130c23090115051e09150d 67
    0x13992048111900d401c1103681da4608403a042501a81c0040003c042c0000590b12100e12803609520b62050004100c1084030382110003400e040005542c140078119030400b40e4680c040c034440708d1030942095640000407031240401d4660100002d00100d64920920142801c4034034906007950950010002c21000c0c110410001510020310319010b840c0007050705941450a030b01406103090848001007072005068855848014140450a6042035036594800641404128002c04000d800380000000e100e10b45a45400c0c82105102c48140c90508401041c408420000b520164001018004005242c40e91884503000c1440703030703e00698900c01c8044004402e030f9200c1c3e60b812451122820040000d03404260b0030f070044051403100180d60004d04c1d003510036074813607081507810740e0f280600d0f1041d41c004150b03502a4008284e03407030099070343c88054101266842105c100c01040b002c101c01c070b0003450000c0020b8040c1d2141205c0c3c03800c00051a0004200e10300c9803039482c0c1200404101d000e160081440340f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599632931 1250 599631681 599631713
    0x3160b0c0c060f04030209100e0c0304060c051c0e0a05060916050406030c0b03040f0510050a0507090f06140c070f08100603020a0e06130e060a0f1e0213090501080307 73
    0x14280c240500304290484130300c01e0b800024014092400481c3c403480c50541d408025040a0303031050740a14006103454181d820031203064030402d00308521402e507580102c0840b1401752526a080900d0802901c5002c050920b928003034085105000c10711000c1541400014000d0b9100d20281a800741040d03017041c0760b1641d030740002d4820b074a4240c0800001e0a014507050403507109040d0140c680d62a820b20410006038600082c0c400c0c01074010316880c2c0b40641d40003501c16a0301000800c4181c4411400300c507034217240e0003030202d455224401884418003074603140c0c414018089000e450302d900c0101c80c13420455694850780000a02c4942440381403024010003800796042802042298030f9900002c1000407680b080c0c2c2c0781d17081c0c2c0304080b0742c46440d40c80100c212000b652005008441c4440009503581c5000c4072071700c0d0306e00d2600d01408807162075400b070000c03030310606982440c030381e0399070020b94000358858185000c1e400f180c0b400014442c140303402040d000300f00c0031010715242c402ca810412a141d1108203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599634181 1250 599632931 599632939
    0xd0f02010e0303240118080c01090e09121c0219080130020a08030c0604140102090d0204020d09020306090a0605070e011b0309050a030627051b03160b0c0c 68
    0x4000f5039515000815136000200460345410302c2d0000c006881c820200350282c2503407459800b012035842000103100e001c10400b80d0320f1840306941c440100c00000d10641d203007441604050000002020383c9009003c900c031103c00c1c12442d01c803140c0b10500132a804201c0340f1081c0c812500260040e15041049039005026040c655541030381c140c2d50074940140404011030000300c10b07264083c00c3d03443e50407640740900481000c0781c1d502e00c0f04032880c40d86d0710012a01100c001c01c512800001c00403040c02600c400100141445100040a90800c0f0281d080303003c0c1e40203000d03921008040907941c200460703801134541e80d001d460030014505006040d590024091410311580c800e80f101d5690740a160402842d003500c4810a00c03e805142c110380c0100540e00c103d901210080300403040c04242c1e402854401c2d62103a612039150800700030500240c000081c06172403504040005401c82e01c81401d11421740c003000b02540c100380b06903081140c81032059001450084030124214a009004114152000b48122 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599635431 1250 599634181 599634187
    0x1d0a0519030507142d0d0e010e0609120a08071502070201090e13080301060e011701081f0e0123130503090d080c0322091406100c050d0f02010e03 64
    0x51400b4126118481d0010411105080520881041480044c5403a91240007031603c810048405003104100c41c07282c60818001c005114800354041c0081e261041410784401d80544145420042c40b6008940c84603085102e0303001c2a5140001480556031842c07040309a2a02c9178014100b142442e882da0700b100d040b2074410841c54001d40e0700401040d040700d401e803c11841c6507a83c3d494602790a2441d607801070040d0004400030514a410248040c0045800e0762000842c080426940880040030710481409801c505c5001d02601c201070700c060b01a1716161404602c210003081ca41e802c403002c0d007106203001c01d6440e190f080204c0502c0041c54000c21003038480d180241140d00d03015141e00c10b00e41a10b1080c4884a004020000c0100940f0340e0311129006680c0c441c41c3c1d4001c11103590034141401c3c50781008003030010416906503c64460440741c9205456a00d58480042c0032050204d5400c507420701010b510040000b420170802142e14182a81d16032010007000071000c4c2c25914503e9404045400034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599636681 1250 599635431 599635433
    0x906030b0f061b0607030221041e26130b0304080f0c010507030501050d021003020a2f0f06130807020a03050d030911030d0203031303180801021206040207030f080a1d0a0519 76
    0x94107201e01000070140c00104680c03110316044da400680d1500a05800750312407000000e100072184015040002948012a8010302c40c2c982c0200740300e40d004808000c0e2002d533090181c9003440c006940d1142c855000c980c6884042c202c2e0000c81c2c1c00030800d41005a445d24200580c2540c10300403540140010307a103005125543d40d00040e60344001400c0c250802d6404511000340c1c3d03200e4003008003500c501100c0362083c6525241415280e103424118200c6d40d114150400003088000a2041d10642500402d18650001d81ea5540c80542c006081643e001215200100106400748001030f0440143c0c0c400160908040c036040c1b040140180846100f40c10032a030144030b050300401202d40c0b103410701080011031021440c082d01c0461b4240111903070303042042c402140442055009102d003036a554141c424640c0c0320070412099214100c0f0050000b4080340508031503d0189c05020742000e04190003141d520410403030380e001404440408003169000040d49000d204040c0808025001401004088403180d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599637931 1250 599636681 599636707
    0x7090f09080d09080f0f030109050c041d06010c060e0a06060e011a0c010929090a0305090108190f14010b0702090c070503040306020d090201020c0a060906030b0f061b06070302 77
    0x1991035102181e61943c150200700248802250003407080c990201d5103c1d882c0d10b05140d040e1b0400d010724082145420302060400c1085c0301640c00f2035400b482c0c501e00c880c0381c02d20141102c15011380281e0600010841e0600014058020300d680420540700800d03ea04060a02406698003a40503101000900c00117004440c00010400c3c2400151000d032940c40c0283c0404500412044101422504071050174120000034054040070440104190440070b440d120007503a1110f440c0c00000700820001c000740d1201d5409141c880350f009000c0c02003007a0b070070a40029102038039418501240c50360303680d0052422030071600c1e0f440d90142c15820502401c180c9103074007040d51404058080380c44004007041c030b07904018081088401441d40f0440a41d04da1b12546100c201400101174201c0c003600840b9502c000904043c402d1100300e49940d52a040301528200c001d5005007282c16860f500141d0003e03403881c40342c54581c000c1241002d803c0d00c41e101402c50f51215800d084003d082e8000301801084080b00a1403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599639181 1250 599637931 599637937
    0xb070e1203091203040306050103030206060a151707030f050c21100308070f06150e01051c0308090111030103050d140703090b161e02010912080d0b0d08030907090f0908 74
    0x40300756600030840c50104010f915601860340010400e0713090100100405902141107030080300300f51002408242ca82d4070a214603000385400000040f6a044d00c6000484a00d200c2904400503041c0000c404510040000c1076880848000b40742c18000244060140a548803442c10100420f01c201f07003500700103c0314901400ba911003d440c18002044903010301000401030100e50364050b40c1000301c11032110140e1a0b0000c140f01d04641d01e00d4210002519050941000c200b02c00095a154591015598152000000a400c1d50380d05c1d940c40e4030901c140c030308600095000e58041e0008103690340408800500a07000e1545105602c0c2c020321094001940014245c019150502c44480c0c5441110404980036004440054000b20181d80000340d5001202e8146192500070f17622221103d4403a07104503440304905000a1080714104505c2c882029154450908101d00810a402c0303070049403074041030381d001685c1451081d04600c408112080b001d104413285450f200c8004d1148420640704d000d5180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 599640287 1106 599639181 599639197
    0x31d0c130203090c1201180b0a0608010605130504170f090307050f0d231f0509160b030604060302060a21020309060601050a0e04090b070e1203 63
    0x4007402224869400311000300000c19216042c41410074440f1035079603480d541c554850303881c0f0b491802c90031060b5004041c84c1100f41892103050080320502e5104d040345a251031820841038580ca4080f0a181c0e00c2e2820002701e540d41c9080043c07101e05203140766810010009130604403c40c803000589010700c03058044a0059032210140210305000c1c034100c503409000c0518000020f40030308454032180d440081c1e40f0300300458402500b40352100140f048040350580c10180c0c84444550b2042542c482c460200810a88040195031411180385002d00c2043c0d21001002401c2610741b6003001c0c00a5602801160392100c0c0c1010041c5040005840c282080350241040001150140240c901034201c0d030003d44041e8842a00554455000307608da00c09002c400d2101c940190b032103200307404246004215020b100d140000d4010700480d9104ac03c00d11a00344911a00307070491000080c0d51040c = true := by decide +kernel

theorem cover : BRFrame.Cov 599460431 599640287 := by
  have h0 := BRFrame.cov_init 599460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 599460431 ≤ n) (h2 : n < 599640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
