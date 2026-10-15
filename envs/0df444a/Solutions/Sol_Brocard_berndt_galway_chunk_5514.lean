-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:59.041998+00:00
-- url     : https://prove2.me/submissions/e92a5966-4302-4106-a2a7-d07290e64cdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991546762 ≤ n < 991726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991548012 1250 991546762 991546769
    0x803040e1b1c06090605091f0527061c060e010b090c0304060e0616050c0102210907292208211201060f14070623011404020708090a 58
    0x2102070b0394038090300c1500e0580350b55403c280340da04d113080c00810503961886141c40d040141101c1000c203a800710b40e058004406250009900040c6080380c000c11103141d00904441c2901901c1d043d03020b92648810130154005110017503003c0c5180b4808580450350030740c083c4021140c1080005840303201e110110b564031a00715080c2003544404000c2000703216071401901c0885203000042c01c030614010700d17241040c040080d10320b0100071022a00c5515840300b58110b0329146450041c061a840c41080e000b024a003085400b505980a00040020102c0c2c5030011021258029a220040101e000325424602c1e00148107400ca8801c4c8558051a0070b07070304a42c208050010407000c2d0228001003556018403604910921994035400c200c0000d16080504102c0d040d114540b40c164002c0025807400c0b00d41340c06c5100301030404100004c05034200100f0354480080d0300f80711680700b80154402d1846d144488400d02c0345400751002141140070038038240e401040c0191144180a08146000d40230039000b0311540c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991549262 1250 991548012 991548037
    0x2a03080402040509340810020c0706231c09080d0b091905100f14090a1a040f02040803040b0705010e0d2a0b0f04060606090803040e1b 59
    0x80502080d400c15005203903000c09007500804280d00328030040940c01800700005004613000e88045540c0c1403014500800800d0382c8403c46e00080301e00d0650200942c440c20712464a88500f2600050160007402045c08010048001035002c042c40000f05201da40311060210203007000d00d117503400c0f920321846519020750040d6510358484086c80e81d000c04a4370348411083c4035030090700c100107201c10010016008140308820100b00760712409000c90700380c0e0300d94002e000945030810002c520307020f1000c0070040c00b42d4100d9030f030a110345500b2040c00488203241c60018804c0300c04103280105081c00d030085480c0f40d014030801403400d940c845045055400035000782d41d040c4d100003031001c2400030034080e5042c00e0305d141d0701500c502c4a0304140a094901ca034048004444440c02d1441410510342e0303911000344e500007210210900e8403075041090740000302c0d021944113243c01c0d800700318507114818850607110000000d510782030400a203026141c2006100070b882005003188901d030070300200c0c00f8040055160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991550512 1250 991549262 991549277
    0x120612030f08072c010c120f02010b060703052d12060406060314011404140103060b01090801270c031a010911030601050301170106090606121b0c032a03 67
    0x30800300c8080c1c081800c01000d100e50901079071030010b002404550001c403403044803c41ca80140c0700c1c40e4500c50003030003647d084045441c1460300b11b112500a00c81c994000c2201492100400c2000d018a40b00640041c805002031120036a055891070709418409a041c0452280c000c10311942d43d002030102c0307454100f00f400b80302d0103040902849015114a0038180b0007104c1e41e02d44c505800105200e0381d0701100314031840b18060307200c560003141804214000a0280e40e12420520007900b450404039001a551840000b10030006100d1007060b91a42e00c041d07a021511f554812818100c039600030b030f80c0d840128100000007101d60320f6580030b0505051304126658500052141203401c90030403c81c5a0404200b04000c0b45e0748281140e05581038490071401c101e070704000b00c030700400c0d09801070128a4a01940800d405400240205000d03d52500901c10322419903643c0368501c95407084980426803c480f007a000a0040c00c0d80304032034070040e251510301132000d4440c000c41103200e10281c000c103030320 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991551762 1250 991550512 991550537
    0x70e0a020414030a080a140f03040c0305060a1116241d0a02060409020f0d0c210e07030b071115010f050303030702100b060d02040b131508010612061203 67
    0x501100d884002e10490180006010036281c03480703544251800305041261010ba104042000b50080e6080ea4103100d45564580c50030b807426483c440c1c81800180c0352440340b81c001803005802406080002d04081e2340071070428030f486040c02c0ca00c0c030101100b00e403410203a501400b444084810f8064000800500110381c0c1190440c04c0401c08040e50542d4509800203018040503031500011103088403181c500059840d44040758058650180c0c84007124010304101100080544c0011070704035130340d480b00c1c0148a2880b03101005049807100000e03026160440202000496480340d4602d40c02507050400d409140c1000c4000340c10710005080d140400c000035401440050107a151810141c041600107502d1030a0920002e0b40d9011b110059210080c0c998034103031002c0d03c50206450340c00d4403500007551640e80b1005001881d800407900000345840c1940c0003e4140500f1000c0200d41c1002d0710747c1543d5900302041107a15000074500c0300d200c507440d5840042c120350f86000d04580720380039a60b052420f810703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991553012 1250 991551762 991551779
    0x121906080f060f0a0603051b031b0f09060105090303190912030806130b120a200105030a050403031d03072001020c060714031c0b03011107030f02070e0a0204 69
    0x2116040340c445640840d0528022810001d0080d4000e0305000782d1001035a00c1c4d0560030081c00b80d80c1c00c0102a030050f034002801a0464000c4214050412030035191004003583d002da0048003100b8015511460b140c048441608062888030f400aa061410380c0c505000c480210f403031584180d074582c00d585000b9071140c4400e03620030b462401034081d08207885c60b00c0c0c95030f403001070800b000030301102d00c43d18000b00100f500440940c0305001c000c5003d405422109c0004044039280c20301201c0a5559a005c00411203240250806a03c0d06081c140c40742e50171921503108030710003070100410407414541d4564509000000540e101504190070400a598510140c41c00f0344800804090600001c000c040f01d85181d80e8000c603440c1110f0b01c00341c0322152100210b080241e488603410703584c8101070100246103d459000c41112601200361518244031040c810301c01c3c1401c0b1095450305035070141d030138440398001900c10a10442c08101c0c03403045560b03158948010105988090b1400c5a01d035134000340c200b20816 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991554262 1250 991553012 991553021
    0x140c0307031a06070b091c051206060a020607050a05091c0317060a14030304030605090304050312131701020c0f0c0321040302060307120903020304240c060f021219 72
    0x11115407103a900b820501c0007090b441c2c082c08800404200145000039203c000810484981c035064103494503c0c250f0030403029203c0c0e4040840000c03880c0c1801c1c0002c000b41440c108a070002111580209120741e94040e0841e03854004214900c20400c3c1000320342d1031a80c4202e540c030140e4508144102c079900c550700d03001c1c1079200450700d401a4100d0038001c108095880d025140215401d013400300100d0450700c00001d06600c00d0340c1000b0301e110f02c1c010a00c50050000030150059990550032104040c40d204a40201c90055980903055030740c515905100c101104102032410324400300c0090706000d2180c0c855800e012000001d91400d40c8200e50000840c81d00f0440f52200d035180205145880030216034060301d0303100340c0c000a4056a07000002c984000d100341c00b02d40041d000c8030000c1192007124640207480358024480d818840b1144100c0507101e140d00c46401c0c0c0105510b881d1000b214015590304006401900c03540401d0076400e2100700c0d407550f02402c10900c0790782082021203200b00002280c60841c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991555512 1250 991554262 991554281
    0xc061701050d050a030831110604030c0b0f040e040f0201260f0c040f030f0b070e010509010309080f0a030e100c02103209011a0f060706140c030703 65
    0x1541d0b1405118049000442e28100031601461700c2c4942c0c4d914400000300c000d081018202c0c2501e4203600743c0358050030940014110912031924142e003102d5450810a45000314040a0000880c01c01e080018119039001060040142c440050415a847d02d01160255046905807642c14400809108560740000c0642e00186002290040e210800705080f81c050002042404003440c1c1902189150440400b5140189151a502401079031a40741030040c1d541082001c0720601560342c081111107020344e04190030305006035240c0303040900c00380044010301038240003521a4202048200820b41040c0300601c0f000d440ea48002c1501c0c003542409618103098101e450170100e24007140c02d01880d80c0440c095a0a0842d10004103003541511042c40d4071802c402c0e1030001741c21101c1d0520f98550002c440b50351051f49035500070421040c06401d074096420807580300d643c0c0b04c82d01e0300c41807655241c402e01403d14107015003000541e101e440864880d1595060303c14850b00f000200070080c0b8958036010701d0a04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991556762 1250 991555512 991555519
    0x3060b030c04022b0b03060907180615050d1b030b152d09040c031a090603030910051603020715090e04021c170301050f0a0308250c06170105 62
    0x13010800702c10728a50198185a49025902049488001c1011074010212000d8020242c440600304a00300d10340d0b82c801072090800841d49400096003498192080108941c04840210046ca105200841c1c25078490520303004d00640e00c405100e151a00000340c1d5284070340e04d8400040b030a03203486c00c100441d0354280303c4c0300c2a034400b00030441c02200d614468001460342c1044110802d085140b98400781c1c020b00c4007003030b0403500d012400301210743d0507005034880b554403400d1990116084410f01400340811601a030300b60784100220052800c008060455140f1546042414405014440807100c40d0105090300180d110031804c2c4040084005904c04540082c01c040c407107180b90903a0954050300080c030191141d03080a40e540740f41103112f1240d004240d80107400c07a1001105400c1c1201641003805810301540104090740d4090406804000540e82c01c140240c2c2009034203c0c19001e41a04140280546491044110005200030804401900094403400480c3d00b02d001001421041603100070711 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991558012 1250 991556762 991556767
    0x30818060d1a0a17120903191a0112020a03170d060b09030724050703051c050a050a090807020f180a06080105130809010e0a1a070c06020109032c0a03060b030c0402 72
    0x400d0300045c100740d010709429071241c9039102c500001c3d0070250261007609510103c1c08052082207100b40025982001c2e00d06030522a0762a41042c000b000003040e4029044001d008042c00441c20100d104400844012856407800c03141c00c0019058510381c2d80000030200001c9001c0d8524603091101c41c01500240303420b56081c3d1140210a80e40d5402002c0c84001e102c000a0b1203418148100c00312150407461546507511001c98962840c004d00c001c5a40107462813034800892040c500e640105108540c000c01c0c80b070300f042d4258080200c40e0b81c000d604598844900224520038010010701688103248280000075043d1a21040e2800d4410051581d40d608082c6442c0000094141c410749544610038a1301b6200d910788140440c00f4240c440e0403000503010081c0c00c1c40c0b42d4003404001890107500c00c1200c0342e80785a80d803006038281c0e024540d005001c5290301d4101c4d00e00b020601c250079154030b0030003000a21600c0100120307030814860707041559130b40c0c0c840c00446250b080030000c01c010800291070843c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991559262 1250 991558012 991558049
    0x9050601030203132406080615040501150e0a1203021c020604020d0321110a090803030c041806030b19051b031b0408071202030d0306030818060d1a0a 66
    0x200ea840c3e03414010300c5c4042144040d05845d40c010315913084440b5400c02000256142c0d02d0340d5036144004c99045d0500515a0725400311030801d40540b50490f0790326040121840849001980e000702000441d541000800c04005110710a40701c441d204c00c2d00a401410520a60b00c680c1d1522010240c410710541d0710040a0100503200d0b076404c2082c2c0c940501e070000c8a10000081840c14880070808802c220307041c404441e10800e682001405d07d00c1e5241c48940c00241d6880060707489000450300c04902160510042290300040351110035090010040007611030f032241e42e0038075500010344d1009041a01c444804c1d01140712407061503040b00d03e4441601060204100350300c2c09206c01000c01c1c2e14044228401c545900f00c2c0010307507000d030000381c00303a13165030fa11203281d07000c001019001a88a8810034250850040c0203105100035690881c0c0307440d16001d81c2145a22180181e403c50350341000e002c001281c040359903440342a54410a03841d90100c0d980241e0300700141480b56410031701103104043e9105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991560512 1250 991559262 991559281
    0x220609030c080610090b040905061914190b13020301090501050a0e06150c0a0503040b07060c051602040c0e090f042315070203040308130602120708122d0109050601030203 75
    0x84044600305040403905440d0140818041c18080e007004001c0e11401050007542112f59030780704106440200708000ca08404580d08500030010340304074083c0748180046000d444400e400c041e042c2c10380941040c4240001401c0d0000b283d009902400103660703034030300511a500c4d008108100a2a40a0341d94455003484030000d64000304405161032594000217421030000406c0c01007007181da41280a42e07460b42d541c0d504505030380d40f2200d001c82c1d6080ca84a852100d2600400c1610314100d030300d1010b042c41584039400d210040c0a03018145041c8950540c00010703e646007203000e403180c000c94620001505141c5013070b0103000c136080018040700002510300403505100141c4080c041c1d031541c500904913202e11801fa425031049410140c6014800554400c0319488856200d04955596084940c1c0c2d21041000c12650f01445c0d41c01440f540303080040c80c42005e01d0422098000824010342c04032074041e03c08241e030541003407040c0c5400c0070469004005003a103a100300ba60202003802c09515529014950 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991561762 1250 991560512 991560541
    0x504060609150309050708030a1830060b040c050703030b0f06181507080a091a2b0f0e1b0f0d11090106080603061605040b220609030c0806 61
    0x30b40c020143d030781000c80140314040111000030290a4283d0b0b580341c01c0c102c001081d1145013040c2c0302072035002150010780010311200030010381da401d000700d032451184410840706008074080c0644510b038680400062541d528420320009506030344520ba034030900b514000e030507076802000c4184240080804c00c8200e444000440d250900440c010101603030f07104000402e034a410070841d460501c00441c2d80c90400070f4400041a00315890307111109075994410724075940141da544003400802c401d02059074003200400105e9042d40072031040b0240301800e402014100e0340301c000200030b4140c031186c801484940a101550b07072003c0800228424800c05c60104180d1201030b4900c82c01043c0c081d601d6414098192510401680b00130004405540d4a00b0000e000c1a0140d072960301c00d00405012440d000000c614024405001751111030a0034504002401c890b0004070441d4164901c180c52000710041b9404442e018000c6501c0e030440060550a00ca052001160001442c941c40803040c8090481c84800c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991563012 1250 991561762 991561799
    0x181b0f020d11060a02090a080105040b0f0114031b01030b09240105090f01080601170a0f1a0d1103030c010204080f1e0a1e021e01030b180105100207031505010504060609 74
    0x540c1d2516540301103841f080310343c0d12600700e6528041c140310410003142d03942405a04043c0c120609070340c0b103187c18a10030b109403000650592111185050011072083c900044010504001424102c03007808640c9070b03c021501e121491b103480c00d03a098062510460351140e00821305e48117017000c4403000031504040419220300d0500616100040780707a8841c44084a0010300300503461024140784203c40090940644210a41ca0a00071725032a4840f240e01d0003014141c0046c440c400315840d54580d40300490400744040e070180070800c809008964240024401001c01100a014003202c095000781400b012000f000c19440903182c6230700c902c02000800302c42c11600982807035a1444040d000700007015541500a401010504440358011107051003442d503a01c080c3c90920000000d40c0400c1045800940420f40c4c0c001d031400180058103061450324a07505450040740c0343d65481e070302c070060880401145812155150001880642444e00882c2c0040c5524240700d031701a801c0829104000f05240c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991564262 1250 991563012 991563031
    0x306092503090b06180f0405010615180e060a0b0a0207150806040c032304171615290d080a0507140f07181b0f020d1106 53
    0x28046109280344003058000d0400326010300c104400e91240140c05090305090075030f1041e40d100e001410070b061104c4072143e916031048032001c40e0741d01c071200050110000b07001030ba0199640e1070045005058800320f200d40d8001500e5107400b400085003d1028004644c010a0b030780d41c0b2180a20015840d2450355405440c00044082d8503201d00100480c41d0062652244900c1400d89400200c4540c101484502400c02900d0620581c0308155080d001e07903102c00700e56800e285410010619106419060360340061150a07810a45060081440501d800144862401045064441e030801c52030700400300c1d07801100803092103240921040d0003d08d8510640362030890540351032902c00c65840046d0b044859a00c444810b4454840728001000d41d08022030803034845031b4001520300401e00008005101040d00d41c018810981010b2910b00b8140180905001c4d441c2c60b41d1090020412003800c0381c5010003103594016112004100082c5000c03d42100300c002c0c014514980c0e6a040030126039240d1010428 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991565512 1250 991564262 991564279
    0xb070506070f02150406021b0c06090402090103150e01170a0201020a060b0102031c0c110304050f040c05040918020f0907090e0606070510020903120f16150e0d0801090e030306 77
    0x50750503401d04d414250403010016a134400c003c100f00c20303540a466902c10b85e2496041c080c3c031007404d59964003186040d041e8442d8080c0210821480e09400811183c50180340c041105103d020000036129510b40024202c482d03110014842a205214011002841140104040d4400780c0010b0f44580398988050002c0d61164080c01d0305900800032039200707100521460300034001d401e241600a080140043d00001c010009140d4107a0000041d00d060b2000103000f485121864410800108452810710701801030601000a40490a10540ca44108a450101c14000562041000101d05201e1003485020b41106000115034444950301c10f0b90f14000c0c03103501d1030b00c411001404c10301959200404a104100d4103248a4000f41c000d0a41c1c850194115124050f01c07103044115409090b010503085a01801004824007062040441c5903004e010403c41140900248006030b03105d03d09c4001d03040e40600744150010340e0003090f050042114400030040d4070340720100c064031780c400646958418801d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991566762 1250 991565512 991565537
    0x801021b12040e0c0403120206100f05130c020118060605090f0408030a090228080c0904051b01030b0409230c10050f1312060606080f160903080310030b010b07050607 73
    0x1400100d85c09507400111901142210050003580c1e21002c903041845139400080010705140100100e800390741c03005000e082c104401c25204001040124107134003c5640b10aa5004420080c905251a8a0240c036020801c20700306000c1c03006400025122800c0e12100401300408a1110400d598000090300800300d8801c2c400d00005a0700c00342a010b44149040040880755149030000d603c204865148040c0c0310303444540010021754404c101c80c080c0141c0c1101500642d001e1039000c40160011050400181c13910202010800320f90343c041c801c9074007844d5002c0d5807074075040981c01c0c0f060114000e0700078600401c40b4000315a034000c50341040e405200c0041190120b042ca45800d64907005480d80840d44503d90300c0803a44090328081c07030262501890100040f814500c2045203920a00e03a080790020710f40c440101000c00440401d0460080001000010000850300e10045014211a02c0ca40010a007142080c4504110691085130030001c00c10030040040c07c08100940d0140c460308040704e00c16079 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991568012 1250 991566762 991566781
    0x31b010c05120d0905010f020903060610050409050711060a062d0506131d13230706031b020703051506030703051c080604140f150603010801021b12040e 67
    0x2030960b40024100012030314a800100320340c00841c115000754000e0140444018215040b4810403044640603000f902c001403060414506c0c242c1038204030300c0c0c1749140568482481c0d04039241545c2420000301012141c041010703007001055041020b101c010083c003860684295030a52660709910035910042400c41c01400302c0a020740300038034025050554400101100b8040b420f00c074005c0055150500302c40c15150310149041c14400c2a00560310f0706127a03000d40390310255100c100900288070201c1c01245e07400b107006000e80802081c0e540c4002c01c0c0304107034000e40041645c0b1144200e0440d0701020003000410b000091000603540d20042c1c9800a03110342340401d041c5841608060700307520401035a0158641c0380f211212103103405946400c125140c1000b0481030712550b21141d81c0034102070000c80d5002c1401c48040b0f4001103400c203002c01c100494004951f00380c00c02da202e090942d502044e988526180010031482004069010388001d03035030180b4040300d6012700c0c001c207586800844001641043c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991569262 1250 991568012 991568023
    0x815040618020d1208070c08040504020d0e03070f030809010905071e080d020c090f070e0f0111010c230310030615120f060c02030c0a02010e0f0d080a030506031b010c05 74
    0x2500038001680740d80c86400d00910800849480d8800500d05c07038001038034588130701e103244240d6601120300e81c981844d142c1004003a422886036292090755074505a04101e00820081921600c0340800c8e40c7e0f0b0760101d05010b03144090003401310308580d040c1490000069808240c080643e40392030b5070003400020701c1c5041041604c0c0d5810040d07081c483c003045a10740940019078101003000c210b50030070072035650508000100d501a2028404601e08503510207980c82d007500e040700c400d00180b5241911f0030485038000d00790341d1441c01d01c00200e0103030300b001c12450103241c0301000c3da1050541d0081c61800c00c000ca8104000d40e5101c090035040e500c0c000d015006030580001d00041c0402060103484c40214100100307800d49812040760030500d0101003508190010003601c20980c1c00300081e2290000c02c0d001544c8000340c00c070300158041e04102599507a941c07820005540700d0b00525103581c9804440d180603046030406400c0307510980c0f00200e540c4410b41032000f12140d50100703107030900400c0100d2400900c1e01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991570512 1250 991569262 991569311
    0x90626180f030436020a030e1605040b03060708130c1e06030c022806090c091e06120f050c030d020d030f020301030b06121504031808150406 62
    0x500030003a540c50803001c0000600161600002000740d039150a103c08560a480034118219508401802d003c00c0079456000e09026101b5060120300b4804000e90306080c1085101130706a214034618003484141801e114810000005400402c181e09200c6800b03030082d00b008201502c8640b6078040c090800c89500e860030000c0800c002111014800f01800404072165406010002440c0030401d10030184002032800c0107640002008894421100780d01c040500c410fa400d6500301e450750700c54000105007a0112004050b0301070b000620128031017038100b0541c10140d11117162820031300b003407050152034402c0b109850350103c3c4600b0304031a946031a0342090500882e05034180540d00c43c0421440c1c000c910260700080c159010881c0d10241c0c2c1e0036204174082800003408000032080050076509107a41c0303d181034610703071045075000e001c2c07907110405c10f0400300e07011000030b904d089074442d001e1120900304010389044c0f0082e14001e00e4010f80d104500e4001040544940d80302c0303112200b004018400040d80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991571762 1250 991570512 991570561
    0x150e040f060507021b040504240605060310030c0f0b0306130e0a03172404020d06030803130204050f01060c030c02011e02210301150f030b0619090626 66
    0xb42c03800141c040d45665808405045200614035100011720f031a108007803003a580900d5050040c2c044102e01025800280107841c41c03030303550f440041138507982c4101039032150b11040007010310a415490b015500040f01e511071496100b143d03c0501c400001001565072288060300e00c40d002c2c09400b002c0390041c0142218089080c010010100c080c12390001f06610742102a40d00003000340c80707944041510030381112200303456121500f080d420318601034000309010328805c403010401035220307241d00d100340d071041e641c00804821504074101141018041d503648400035810943d03456241120103001d50114403001401c12400d05014400c684c05142a0745c241442070300c2c240744012010360041d507603e00e1440700920340c0340640307407007249a0110f80407a41a114000d02c04907c0c00380c1d900043d03c2c444000c49207201815218685180e094032044d02a102d40391100c1e0207588800352600c40039120380c40ca5045441000848180341d004c90407217160341e1403103003012040b4a20964415008041d21100c00314200007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991573012 1250 991571762 991571771
    0x110f0106090e072709171806130605090d0b0906100e040b040b0405010e03041e080c0d0807060e0d050d1a0a050d0611120717040c09020a0e0a030602040f0504150e040f06 74
    0x40061b52500945550016089003c407403040d41410482d042c0181420841c07001030003541445514030441c045c01e4042406000c00000012a03500c200da0010100c03203164184c0c0c4424200b102180d800c109150007050540f40004190600340c41c0c4409501d8000d0010b0606807485001c070f02004425400080b05c00f03450010f8031307200e503200c90ba0040d8401c58449070800d000c3c4d40c1c80c000b2884a102003410a12500028071840d0003208236590010345400c2160280c5069a480f00d1481e00e0700414808038682d641c250761000d50b034103031030400b060481d84514200d5145800c401d610044239182e0725070300c100fa20310844203841c0001c080d01d0408090700b0003040001d00d841c000700d00041e00d5455607202d180038034850b0311003001c0300d203c00d4244900d0000499028001603090b440400c0501540e41c001c3c0b0700f41031145051112809020041101d900969208a440b40c3c4c0c001400c00c0401f011030501409800c04850520807041d88801c036194070b00c8207000b10988080c46002060400055104102a15900c20307020300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991574262 1250 991573012 991573043
    0x3130c0e0a0e010e07050904140706120c05090a050648030c0303041121061503010b0609041526010b1008040f0201110f0106090e072709 60
    0x901090207075041c2140341e0601c2401c90240a040c0110159180414020141d070351415003000355088024200759541c0c668210850301c40c00f010310044000d803586031508040d0300508400003044442c580d48000400405001070801c5558200301c00c030885500301c030040d44484054030140c004406503510786074141400f0400c3c0b1843c0b010303d04c0c1c9514000f480051400c4001d0710048143e01c038440c1d500700b0b00c404d410070030000e000070303049500d603503482400600003100c06808100c52480346110024801217a9001400f080656100094241d000c1c95090f402440001e41500c02700304c50b401090040c502ca161582002e9502d9000e04454100400518004500c2d401c500c00820003002c1504d41342c05401d508210500c042420454a00d181e4014141d444846a944544410302018120007049040001907100306110f4a410481503000810704000000e656180c44158422500c84010301c02c0300f50052a001c100030080605403001405010b003810001d03110029046008052600c070041038407059683e0b10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991575512 1250 991574262 991574279
    0xd020414030d050304030c200a0b0d0b030705221b090e090a03080406020a020709020c0d1812031409063016030e0a05150709151403130c 60
    0x90312900000e90541e84a2061050700711114402250003402240c41141003034006030081181602d0f000c51442d490040400305000181a441c160707000407028103001c0f0760401c1c3c0c01c2d4584600c201040085004184251401c404103611b0300340000c0c1d0400440c1b584030300c0084554543c1100e100407000c1219000c812102072000b0740400d0544c043c1d101c5141c2c540c00003500003000014030720b03855905601c1c0c0146550f140d81d51100a9888801351000310b010700000040ca840007030002d421407030010303005020343d03600180000f4003d105000e02c025001e00050410000340c1d038028603900010b6018a4150801c4012100c003829900c42c0203c1c0c0e50308180f00007001111105e4003408a036100c004290359803580b003c0c543d403070104d001c0203884a0031804d0500700640c0a940c026400071050025100a450042d0280e4880600304510200195480031940013008807080d4043d91540190a0865003a852400e440000138281c0022540688800200201180315420518a003042d065400304070b1040e0703181c40e420f5a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991576762 1250 991575512 991575539
    0x111201030318140d02360a050121021305010b04290a080603120c0d090b032502010902061305010825261905010b04080a1211030a03060302180609060909030d0204 71
    0x116411a2858001f0600d0700e521409980c0c1281d00406224003034090750350050036142000328040782c0c0a44008618006c0c0455402140d0003044070010158940c5c0c601398500300030f40641d003246031181d0700b03506401e4501d0aa0034150303821b00c1803030f11700b1745165500c560201c0d1406c3c4e260b65002d0500135000c1400066400300281140c031502e5180c0c0c40c145166a00d8100090ba4001901c200718101d411700722500d1142c0d1600b520740e520095910010415000b9a004034040340e0007030521031a0300008038014007095810080d50390300300805400f4412004403156413044101c0d00284d0035410003c4424449811043c0040490203407064500c00c545507041c00d848141c0752001d4040011111401c010001807100e4080d401c2c3d0703003203032102d00251504800641d5408414030203503003031f01c0a0040c04803444c0046101000502801c83c060340340081c0c1ca508600400c42e0000110400c2e000c00440a810441280c51700041c082d04003070140c030104013503100e07414003d0035402040582e400042c030215000402440b810799 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991578012 1250 991576762 991576849
    0x30c03090a0603061410230705071e0b1303080a020105042001022e0c0203130e060f0d060f05131511160303111201030318140d02 57
    0x30840c61866075614103030f050354428858004280c916016440d0b0504126060104800c0315183c415801c1c00c03008201208005001410254400e0125121042210401541001c0c02020a01041505a1403d6203210039454040c00445010109144003640201c80041c0059640080190340354441d01c0c10080c02000100c034141c0d10340746c03694210144042c0701024440301da40103034058410030782d400c070744108150355441d880603481c00d5041701640040c880c0d22070030030700c6042580030f55a1034681a14241c9009810b42100391480a800103001d16a41c0b8800301c0242c1150690344d00c2642046400c16800815504101160b404d040c1001c101d40d1181c1d01680c580542c1c800c000c404184080c0c01c1c0700e4021035400150310042100c04010782d4032141142c12820710b01e03a00c240b4004c51a8003100808421540040c540f00d240d00241c0b00040c010540c1000f421042000103501208609141c1200c0c1301d10a500303258400d005840c034001c01c00664907a50701801d48040030420004410308000c518480c00c80c103045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991579262 1250 991578012 991578019
    0x23060117060a050c180d0507030b090d09150c08120c031611070302090402030a150c0905040b0a06030209240c0d0c030f050d06080613061b0c0809040905030c0309 71
    0x2000034001070b0a074400c0a01495403580c099090001600210159882d8022070646c040c4001741c000b40014410000000658032a00c03809503e400c045104a151070740207810001442141c942c03d01101114028000701c1c08114072304035100465501784010184a003802c840503202209081001203070348900214003448002d4544154100456000c90305e098980c07403a4000781d0480e05042000d454240c20b01508940010141c07115482281c0e21001440c450580b668800c5468003421800300c1d8020100c080184800c0d10309001c0e40400388001003141c03543c3c0c01100e044c1035010403811504d071a034480040c910a40c0c600a9420f00c10100324003090303504140c404408a10424021048062003030801c05e076841d500d45c845511805050b101a1810b802c04071207030502300c0d902c07400018200d1b0100300c400c1c0142140241b0302c8005980d82007141c195010421100c40d071010040704c89421a62011140c40e8085c2c00c22040c680b21240341c00020058003945034080d019100105103d4055507010008101c40308045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991580512 1250 991579262 991579273
    0x91027030c050105071e0203011b030b03011112071d100201090606060504080604140c10082a04050108060402041a04170a030518010e0406140a0803130323060117 71
    0xd0004407078502c1741d44030041025492460001c80d0000c03c4018240301c62005001003102502054844008a552006800082c1d105d1040440c582020710030516034100744a180d42c030b00301102401140c80391000d408401004400b4a91400c100150404421042d81c000c0c41c403c114410048000d0107003241c0041610420301c2c054000030750340c0c024030464044a10a00160002e03a8075903c1f140e50302c0b401101d0609103401140125207480d61040c500f610220860348502016003001486c500c600c400301d06480c01d020300f0300801d01c5100c00c294020782d82114003d1900801da40e4030130700440e01900582d070125900181c0081311100400b00c0101903c1540c103e003141d1058108201001e80d03441c00b8031640900880d070100300340e20b985800c100c8040d10256043c100005046034400109084070119030201051401e521352981380c51508182060003842d210005504064a1114008030313405148002442990480321114100032001108246020703180300b51609503955031903041c02c0706251194082c417809003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991581762 1250 991580512 991580519
    0x20307180506060403030903031b081c0f05090613030e090c19031505040504020d02030709051902070c0605071505010803300703020c071a09040e0a08091027030c 71
    0x1000135501100d80640c0c58040e0701c1d01d10740b01038803445045010340072040000c07c0b0100104001200a000503207241d201ca41080341034201e0901102c03928027401c203c090902d01031000302d08000034069008565100b04401d00380041c40c0644040c800510b10540100781042001702020758103001c1c113003a800d040d0b0b00c03502071000400d00f01c003120001d204200e01e00c158a40d06002d00c1c00d10368030aa500c503102401c41805c100390741e00043e01c5c000c0c0b41e40c40001440d4894041006038402c400c00a064440507030801d40c2001c02c5640c0c1c146508200c1c0c0034082c10440041204418098001001c0c0302912007210108082d5840e5852217482c1d5005941c03904001503a030054544031403203191100d40364204000d41001c162540c007000ca01a41c018103184038a0310409030041298880c1d95100001c031044a02407036034901d80c04080c0003e80e5542034a8a025401c000c00203004540b44c2401c40346040011034403031203048400c08041d18038940368100000031410b0206072101c3c0100682412050f24080c0280c2e038111640d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991583012 1250 991581762 991581769
    0x613020f011b0605060d05010213210c03080a0e0604030309060f080712050624041a09010203070605040c03060612030809030408070902132d050a0e04030f020a020307180506 76
    0x4261008440300c00c40c4842d0341001c161a40d011982141c00240100c034201981d4480e0307426600400b07184140e40b41d0561081124102600c0e481031204030a0a07421440c003c16115041d0340d889074407004c4c0103002e001900540c4c0700c1c462007155407a160000c061503211601c906009086544500a01020a00510000c01c449000d40700c070505c42c01096a90200c091036001000d000b600000c1d11003500302ca58009640301084045180d4941a81c1003026103031901d01c1c1211105c0c10b11035010700c00c2c0800400b0030580e403e5987c08070442d440c40350408400305003910345152004590980e54805407031a4a0107001040e4180c2429203421034500070343d654185038550b10020340d201e02c0756104001050317005031401c00c080e118035005031054441842401c0d801a03553307100480106012040c1c408644408146909003083c140c0315080071741400e80700c90682c2c5040c40b2043c10302c9000500040c050216001740c46c1d203ea031003004442515075020702501c0c9515500c00000b00303910403480d03c0b84002d600300400a5490709 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991584262 1250 991583012 991583027
    0x10222090f0504200f060c01140a0c0c38010504050a060806071107031401230f0a0e011b120b011d09040503041203120509240a0b030613020f01 63
    0x344c100c840300c0310756006005107140b10820241803039006280f0000c62281580e41402401c6425000400440e082c0140c0e072420b01c00400080a00241030b291903202e40d078456104900000c995480b0034806038445000d0070340c01c2c00700c0e4000c0100d001d503c03001503559004203203100220b0403a40140c0702400103450b684003d10a4688500034594654000d0303000510f154482d810052054029509541085440b9158900002188a08100d4581d1200c01c0b2007886074191204d030303500c0100c0304a03002140c1410349011100c1000544a03054041d00c40441840d565002c3d40030f9107551401c1403c458088c021603001601e01d011a404d40340804d131910b070b01e5000c0741d40907501100d0b10324002030040800f03840220401800c04030140050b91a480f0030700010904100307698007180c0c0e0318003d445043c160000350f1802003d50301c00602100701c0780c1021641500c1900c01680c40c031041031000074a02d00607550304409100500c0c0c1d81a0700c591610401d020320600c040d488400746141c0d8000d80744900c40e0840d500041d624403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991585512 1250 991584262 991584271
    0x2040b0406091d041211060112051c050a05030604060e0702150a0c0504050d03020a020d08070b01090b13092603180604022d10021e0601051011010222090f05 69
    0xf4071940b002900003104442243c0c541d2840c0d007000107440300510016450714100343c000e02c840104520204085c011704201b100d811890301ca00300c01281c034407540010100d0080c0c2820b00144900840810143e82ea55003058014180b842d00c10811807629960082d698040c2c4c1061020200c0c0758004a05900d10600503c4c0a8100c2519540d280030b281805010504600034000e404501860b15240b005a0f41e441c1c50206172401524001e031251100e04000340320f13074810380c030158130075203004500050741e110500c024925800c81440021068801c0c21300c01100001c035400103004101e02c1034000c00c02d007030f00700242d0701552420f01c00d8900c3c410111021581ca110903a0701a600c008541440940289a4054140c42020111500c1c1135a9004004a02d80204440c001000740e0042c4c075100c428001c240080300c81c031021290050036a54500030110340d0500c4144c1c6101c081103012620020452402d4040351080d509124844003080a0919126420009070080d03e81043c14016281054001400f41d035005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991586762 1250 991585512 991585559
    0x403051e09060a0503060402091221030f0415090816060b0a030209010e0c04080304230102280305090307060e030f0c0f060c0a12111e0a080a021002040b040609 70
    0x24442c400c0f0702503645070070090540358070903020094100c884d103407040d58420440b40b5000a24113146035805440079540c0d000c4440211038014800c1040b0680c209095903003064000710743c2c65151182c0c0d0300900142100803005009400d00180e00c84942c21a45c240c96215030203824208055a0b800081020b0031f142803002030743c010000c00040c404044a0b00d10716402c024407400e01b03403805072f451304000d08640255000407020820007980bc1031000302d1854030b400e140800d201414102800070f6a40f40b10354003120a00c81c1c40d82a042c4031408260107002103943c07100001b02210111a42c3e03810040c464940401602d0103801000311450010900103090f100c442c1f030041c1982d0f40c201480f030600a05802c404c01b0540c1e24402c040741503012a108803100e8028031065a503d85202c801d081d00645054900300c4950505503040d070226503141c101281c05981c5a0f4448005541c0307861804040740360000c001c0c081c0c086141700180c002005600c5000505c100c4503142c44043c4955076030707091860312402c0c41260082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991588012 1250 991586762 991586767
    0x9091b1421031b03120114090a021309020a032c0f07060c060c03180f050706020307050c060a0905060f13090501080d080c04180e25030f15050403051e0906 68
    0x100c0c80306070000240c00d100c403c02142d007000c5181a440c0415070082e405210011000c1210780000d082c000812a44200404410340c40d200c94800180346405842c490501d07126404501040d442d0b200341c00c0840342414418003507020800e03212200014410b0502c8249481c8520040045485408a6260304031809a142c081c24100c1c261983c2001c1c000c0e00f03c184d020117590701d48400052401d0030441820f02c0c029502d804030000603180c55031901e901500300030199841440300e02e0000d000021701100700c6178103603110743d15003902d94001d44503491290401030f0f0084011070380c06421803880004d8141c0021282c00c00c1c06080d52548107000b110800c1c09a21095003001d14440d044d54025a545900072110300c40d101d26080c1d403043c001800001708441d1404a5403030b10000034001100b08101441c20030040b01490321440070f141c040c068803c0f1440001c000f901030035503000070f000306000c500c1c10f21401082e052109140c40c2c6001003859000b0040014255842182e500c024092402621b40007a000341c405031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991589262 1250 991588012 991588027
    0x80d020a050a261204051b060703050904020c0105090604050d090303050306040207150e030a090803030609060d0f050a060507111f0b0a15020f0d05030408030109091b142103 76
    0x80ca9503e56800016000c2e680304544201c5600e014003c0c4052840100040d205061514000d03003044c031003500b03030b980403507049840d808669140000c5034001039050422640d140c1c40c03c404a00a400f400d81d525400b0f520700000c2250f014800700c2c1940c03140e84030b041540c864406110b0265450800f500014002070003d100088007410581e00a00c0502d01804040550520840001080d900c1c405850521074001141445188e07070445400da000d0020200070390304610300280402c0e02920001c00301031041d000f40184a051280c5541c0200c0401e40107019562181e0450409101401c02540c1c8078000035402c1c02c000460080c00301c2c0e00109000c201101c3c0d03071204682581c2901030700d0526541c540c081403864002030112510324010070200107607005040c0c540b803180442420401c004030b20b441444810010000059000802c580c1500c0300040c0002d0b01e04458181308082109010b454048030061080200b900c2c1c280f0720250b00b10003000c84020612040d00c0441440010f0505840441640b0600c07000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991590512 1250 991589262 991589273
    0x304030320030c0f0a121b03141b1c0c0903020901050d05100e011d0d031b0c0609061e0501030c060c0305033d0501021002040e042006040305030301080d020a050a 71
    0x404e440e4041b4503001c0d06940c84503035140c04954806840161900101060441146d01400340c850030703200941c0d505416141960112816418200403128409000035a81034004080c4811002c043d603404400c1001c40110341014041685500069101e80100e100001d910310342106a4030071258000060002e100e03603100100c0c058819030414810360b548520710134000b06626400080c20070050300041403000340c0e40c000070b0100c0358003015100c41c0d080da80c20324181150304400b03000f0095074060030008401225003070100003000610700e50300709800340c40d58220301c0c940603401c0703c2d058030700034010100c2c869503504044c2d0ba01c000710a8000c020170414400100303075245030205468541c024202e0700c1050a01d0010800c402d4210040c11041201082c40c00d1000d56410401408400d0b00f980c011071920f81402040c10300300c00020001022000c1303800e00312030b10004109681c10030804c060306513621181c49140142e01c03601709028044151103109000c0905610019100d940103030400003611842c0080e4403030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991591762 1250 991590512 991590517
    0xe15040504050c06210108150f0705040e04050c0108101214070905070c051507210b040e0a060f060b0406050a11060a0c0e0a080607030f0905030304030320030c0f 71
    0x20750b0b1901a4000d00700a0703481d440300a00040c1501650341d11101040d02d0f850010a4040c1c0020005900200201ca00c541440500d16084482c0090a944a9507070f00400c40d4544240e1f005450019089400d0204018000408100c080303803d8a0f2030000396516407c89501d54214810609114140152800814034180c10801000d00c80f000ba034400c42e0f101e008400548505440080025500540310702c2400300a01000c00f030301e49003044030b008500744484018812140c0e0210440855407040c0681c056a10b40d500054024401810038060071180205490b202c0b82d0300c0905503141c40c2041c40d08200d1260341d211b19001c3d1400040b0040c20682041e4049605400102d107690600928a44040d8428010402d1314468941c0a4000c41c140101c20002003805080c00380190003004240000d1106d080701064840c2d01c003030380d80303000a6607220501d02d000203010b03844400f80850000000740810301d40e25401204848181c030780e03000002422048070421612003101e9040c8210701c14409000d1010740d1000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991593012 1250 991591762 991591771
    0x2010f0b061c0b0d0b060a12020f010e030f061810180314120405011a040b0f190306020d060e100815040f0605070201051603061215060806011205070e150405 69
    0x40041c443c008500441c0004607854000e0b03030220b2032a000c0215610706800d071500a840e442100d4190340c00d041c2c0c0414007801c80c04003d00c0c1440074000d110040c1e5103041018903d0219101c00320755003130604041441c10071042c0c400000c094020b202003401030707800900440076200b0040269840202c60790320100c41600388040740d0940c1d820200703e000c1e089072440501c02e010b40d000b8400080c1030400380400d10701e24072481900c58011410b0101000850f601c40b80c280031541c0003580c1480894000e0544183d00c8503668100a00c02d92010803c80301e00307800c41c0e1140c02074542007904601d50b51110220a03a01d002d151003201c145501c0048400b2418102454090b04140b0407003002d044100503a50303900075902e04680101c0180c2d900c10400c41b048041c05014411680c0c1800d0400a10741481c0341800f01c1d020101c03003d0000e0a04182d071282c246a00d5101e00700800500083e1040c55031100010403070030580c01000d54051041c4e8502240039034940e9034280c064082c0740d503040042801a000e10004d484005c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991594262 1250 991593012 991593067
    0x20307061b290106110c010c111011030a030509120c0a0314090a1205010c090f09180609050d1103120105010c02130219080c2d09040603030f02010f0b06 67
    0x1036810034811840742d4a00c1c040c00e4140c80d05d4101c020814140c51600d014800304078100034030a81c4060104095450f212000f54003900e0542c1031002d01442601d00518401e96441ca0f8480001c96070354580c1c0c56441940210514410f0712244e0208010700f5a40c1d008a400c2c52405800403106034001074001d0540610700025000242c0c01d2031282c100107624000141d03c400c4c4101411544e8030104a0b080c0b24225440e8144d0500100ea81e050000c0300c03036003420b5401040d0302d840c3d59500140b20102410210001c440c0e000000344005244c1d8074080b41c8440d1140d1810000c100020311011508402100399000d202c41409030390045d80c45c020045a4210720040103070b8100c007401002c4100c0d980c4600007452451003109001024a0030100001d1042200600410707003610207004501205c804000041c5d0716200b101148d011180207220f191049106807192030358060b00d4050000205074129112040c003a1141e0001c01c2031400d1100f55170709440003c500070740c0c888020458000d540041d118040341c0300f010750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991595512 1250 991594262 991594313
    0x90c0f0d1503060f0c020109030219030c0c0b0405090c0708121509090601150201090b04020d08040f0e070815030c220e1023060103020d090209040f020307061b 70
    0x5214509181e51582056032001d458a0414580d1101c0340074184075150148000c01694900317442c000d48407001c038905e0403800d0fa00010381c034003814420b540490394035802078202c04c51326a845080780313400d901c00d100d500c0c0204106d50020f40e03400d0380d460548800a8014001a1503d0b016080421810307000038030b82c144d00000451005110307100c0010303451181420340003c010300c0d418942c42c18040c041b0301d424441113a040901a4001814a03140f00b500180d0540e249000c1ca000d40c40c04104a004039009142c1c002603c150008107a2400c00c0410b000b4115030300d8280690303c2d6182014205519002c405030154015490010103062594440c804600c20300003006444842c81c00ea042070390711900024200b540000c2c01000e03510114801c0d0020000c0502c0784c0070444442d9142c005503800c000700700505266004c514410402426000030304041d5000306040482c0c034151074004420b40203000141e000344100035012441500814021042580d072880b00c4244114a5031104903042c040e80ba01e80015026 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991596762 1250 991595512 991595531
    0xd080c070804120302010f0b0f1302160f051606030e031e0c100e100504030f030b0103110304031d101b060905120c010e210901032705010605090c0f0d 66
    0xf81902d00c2d07101ca01c03a50020480f01d004500c0b5a0a0341d9204000c20b10130f11120521410540d01d460812291070010300d1b0268444c1c1d41c05070707028000803004070050400a1a01007034420000c1c0411900d601d982c40c0b030fa007101819251881101101c3d20717011b152400740d0040010820300030f08400c180035403980d03e48100b4500140c910307003141440011000c210b8420f880782030350301c0c8100051200a419045c030000400003807502d42c0b0020202c00003000401305050380c440b82d031440e50740f00c2c3d040940901e4000b240320b540c90401c0d190003002d07605959183c200038001e4042c0c58801d882c1020910100c201c83d41c0d5000d50800c1c0c04205416940386500044559556905000c8002003091010380703c49030207002070540720900441c60301e00350784020b00060415003007090140101400042c40a50504c40e504002e41c40d0755450f130040c0c0c0204403013084003072010899000c945a0058500d0340041c1c85100398000d1122a94a0003400403846003030f121080c04210500200d84203000e0500646810012044080b40e440c21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991598012 1250 991596762 991596779
    0xb090409060f020405090c03070912050f030301030c18150b16051506010810050d030c080d0608010501051c1502071b08150115080106050a090b0d0b040b030d080c070804 74
    0x102c80c6201a5990041010009480c1009100364000030040166142d4502601c4c002e0003a40305002e58440303803401e80300e10310034000c0400803062850041d40459943c2e50312410948040e2182c0d105890740380b0302080e8603400300305050103110b451064040c01120744904050546d105038004038461440080e08406250101d601003019405400c0c0034040c1c034001d820402c0004200030401041685074160460041040b074803058880703900e9075054600144ca0113002d1401210a119241c40c0500310740c01c1900c04910703504194400750403900300720350026420300c1d04082c1040310010842c0c007400c40160006800c0c51055141c004000c003d100c0c94806051002481e0142109076035a00075416607400071401d640c40310703100e0800314054008040702d0000300f09a000300411580d41400b41c80100320f004522088014001e10418015001c69011140c860a912400600418804680c11312031400c1c0502c0903c1410040303012402c4c101c1640d40c0400030b07542c040d80314001e41c0c400340c82120454420400040c0105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991599262 1250 991598012 991598021
    0x3120f0f05130354060918051e09011b021f020a0509031f060e04050604120e12160f05090a0e150a15090c0e01080612030309030a020111090a0b09040906 67
    0x1814840403804d07074280c54074180802c1e0740154080c0200d110043c0310407030756500c5041c01004540c401280d130341d0b02e000c420f0514070aa42c0740034542100c0c1d101480001da806400c8849403200303101c440d0202008040040380d46504114100021743c10501120201c0c2c04c450b0001c0c4580c491608007149440c0d2400c0100b89000921101c3c859501c014080395a0b41d805180207480060070025090758150606440d103546400020704001c1130305048165140680d4003451502000c01c0e4024105080000542d040545590280d44240c0c104c10004031b01090711002c403800ca80540e100a48584450303618800c284008080300e450841842c481d5103230303c9013400d000c180070a100781c91440e80480c2500b5000350703c1444c1d02d41034000030101c1c1e00f440b000100c034607400041a41c102000746010001610b84401048007011b66000805141c00008104100010b00000a1003801c00c00d60003044104100074408125009608001340d0040110800700b069010301c85c007800c000000184000748242042d60740f1001c64 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991600512 1250 991599262 991599377
    0x60a030c060906081e0609130b07020f0f030703020d08090a120c1b03020906060d0e030304120216080709020304080d05010801062909040903120f0f051303 68
    0x100b412406000003907000079003c0d002100d0242d00c440da00700c0b43c110302e060b085004207020b00070260100000c0c12505401050002c56802c500380c07408504203008009d40355a00030804040c03512858030000e0350904000f01300c42c03045400d03502900d00344450540403203812601070000ea81c24810405804081201c9042449220055440e40516810307a40343c04100469180007101c40c1d201c1c070348810030160f1070301241c050780102c089400582e9200c0616008000b0503c0040f4541c00d4807010080008022050905080d00e0344076400301c4074100b0000551240c02400390003550403d0f0041041041101141d4003e5a00580315070f50040c180b070441c0d9800000c44200340e100030b000382e441b500c04002c40d00400600c20039403100102204d000c122800400d40a40c800ca403560380c0102e6407074455030181485140724101003601e0207010700c4a0011080124045c013400d07500e005407140350901152035901c1e03200700740c1401a41619440a05059424061200c18a40c1200b400450500c08402e02c044507040e0402042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991601762 1250 991600512 991600517
    0x170402150f0325020a12030c020f101a09090712032601030b091b0d0c0305060c042102010c020d06061a0403061b1407020d021809060a180209060a030c06 67
    0x702c030607405400c007008503c00750410340d080158480040791200f044a90038244a05011404c51003003101203240060411031050a0300902003418600111a0840c4580388809201d04c0082810b010400141003010740c3d07000f581380e00c0450308000b00c526501222807514081d0038124049041140608030300007910700308014100c41000103204001314032003040c1d00403000c1c80050910000208404e620801d01e00c82070b42c425a44940180e0810200d00000409507501c10305803001800c140c070004440d0f400038018001402003ca41030045084015040d01c0301c160140d49014030151030360280045030f120f40c00c0554186884000110f8610181c0c0850000e4088225025945500d141480000c4409401c100482030614110800c3d595074802d00365015020030248959961000d8400545510f0502100030b4120161740038010960309200b5245200301d54580654995030388001c458000c4036003198540340f0822824400c10054200b4101440c1d11a1b400362050050342e441e42c480540b41140303507000400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991603012 1250 991601762 991601791
    0x703020606040c08010f0e10030503160c1d06060304020a0305030f070302100b06090111010e060709060305060d23010f0212040201090609030b011a09120715170402150f03 75
    0x80d003401d103d01c0030690a07500e4124125410200c0120340c2c541c041c418110703901c11b0300000c0f4100290700c081540042d60b12100f04c1c1e907903c3c141d00482240c040c11a00c152a2140380140008444104602c050060a03140710b10344055034840c000c0205581000d001641c021000400100004800300002c1c41c06500e10743e03806d40c4900c280e00e0001e2030013507074071008a0540e0034103048024030b454060980c1c0d03201000742000b410748942010b042e80100a00c1c0c0c140c4800348100d0092003000d6030400984002d99409075400e22040d81c800d024020545402c0030010280418082480003c0c01103c440210080d00d4900220703c1988140c044000d83c0c20900d03000030000b0080042c03208660b003100a0500500075130514088651a64407042201c2d001403044804d08500010102199001d40b8112101c800c070051030300b0340240300c01d68281d941e0150b602a500400328500c40301c1e12032600400741c820402c14402d6140c140c030b41d19a030921400d0703a0102c00111528806100e04041301001e08040c51159400048408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991604262 1250 991603012 991603021
    0x16030302011a0312070f1401110a0909050714130f0314011401081002030a09080d050a0f11190203040b030a09020f041118010905040213140f0109140109030807030206 73
    0x10b0504940c0d9120b8820383c003040055201061040580e0b2015401c850880003040e0b40d4100960181c4030000410499446c2503410280034160101400c0b001c081c2d50f072000c61803511180030104407442076500e900800c614074901e20009820400400940e0200a038070141c0590740c000d1284580415003084480744040e030a403101c4154240700c2c43c42d072000c540d0407180c05545801542501da06090100151003030300000051161000b580040301c0155120320b600d5501d040c0f5448450007010107035000c014250518050030141e0f80c4074015440709c6036600864514100c41c0a21030036405003507217140c81c2580000d00000948860501c06140700380400341000c50f4000c801d10411100d061410071944c455850041865200300d10142600d44141c0680892003081141c0c00042e6800d40d40e0b540b000740c1c014000525881c13a44103c02140d0300712000683d884040941c01d0041140640901d146980010351041c000c02c8034540200c1e100c10410018181040c1305900c03600d030080160b0000c1419030160344400e0612 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991605512 1250 991604262 991604291
    0x1104090e010603080304030e1f08060103052d190c0504030507210f030c05030c07030c051206160e04060308071505040816060b06030f1b0705070e04051603030201 71
    0x10503044140000800440c0c0c00c5950340009408090405000c00490360741c15000b0781c031525031030401d00340d050012600994100b20700404504c0103d80e0030340001c3c2008082a103036000e004420340d800e0b0503200540d05d095241d8101c004100001000b20b880030540c030b00c03901c0c2282020b00c40d070f80d00080140c1e030707a5544504504009280c014181d0001020040c0d407101c40c0c88181c800555015030b5076001059007002081410115004075444a01500d9804005400c5c40070550000b039510481c0e110f800c903212050341d00d10400c9144848022041c050742c224400041600401c400c046075000040e040045c4a1503201d4081011201c15030011079140c100019110305200486a001001265045052095140c0390b940c0600c2030043c3c0100d0302610550366642000c0082c2608030034610700c17018142d107031245007002200c00040400d550711009080380480d0501e6042c0d8060071109800d030042c000300000f625101030300102d0503004006990902440c0451805008241d402c2d0000714041c0d030000c07072011700c0400c03070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991606762 1250 991605512 991605521
    0x9060b03090706110304170a0606090615050f03040206030709150302210709030b0a020d1401060314220f0f1202060604090201170408070b0a050f0c162301110409 71
    0x3c02c0c00c1c01003541d07250a00080004c101c80540c0d59600040007260b40c51000c030340c60681101001003005040c408040b6107186075900c660112201c03a800d40001410340c08082c1d520b4460842400c0d0011420000100503050001c01035410050500d810866039507189018542100101d49120019400140d4601240e0b604001320140c4281403490700043c0c1090b00c40544106c15a00c8000d180c1d0201d00002a5410015410707100380c080c410704140300580c0c40540d013102c1c0800c2406003001007450019200c5410210661003841000030b5040c208107440106242c040c12a252a0112080e41c0282403040000300300b0002c2880e801d11400d80c1c030700c2c0030240200c003904045004080a00440c07a088002c070240c0c2c1e00107404040e0701e52001010619840e6404c00c543c02d4400c1b0074001c0d0403211450280b082c440e00d954440e81c810781c002201d03c0c01a48a0325000d107010300c83d054401d0082d048005211300450f00313a50304840c454001011400424540c12012402d66070300303085116010102040411405c5241d006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991608012 1250 991606762 991606769
    0x62101050a053603160501063006050c09121005221403040f03210311030103142d06010902490501050f030f0c060a02030409060b030907 60
    0x58031029203008070b100d066048159100c00f00c103104403081c5551078401c24021544100891141c09005180c24101940031302094443c0d6180c0045040d00f8104440b0440c8144121aa035001c14244002450310b07448040c080152920010101c100300c40c1140303607035074042c0412000440001d00706a0582c0c0c01c5403070890340300620500803402100c051451401c1d000c068020b04550015640206240c00004686503010380d40103400c0039080d08078044103118040d14400c1d1032034020150140301c02c129100407020388803208040c0c161a502800107000069804074528800151002211640c684202e482d0403103081c81c11108004988040b5281801d09090240d140507100d0460150b1400c422108440f0540068040d01c5401c545001d60305046c0d00c0c140c5190349500115000101c1c80c1207190b0306d0b044001c000030700c2000c6c4aa50015010380751420003240c1c00110f044c041d40178020543c07581c4280700e440c1d8400c000c89804c60004200c0400c60401d580300d040f000c0c05131070301200c0c2c4a190a11200786498450340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991609262 1250 991608012 991608031
    0x17272509200904020703090b132301090501140702040912122c0a062a0f0807030c0309020612060102060702030c0615040e01051609050f030304030209062101050a05 72
    0x18090440303035121411542c03080410755005075112a43c2c10100c0700d126164003e803200701e6000540710f155040710782015043d40e0507d54080d068041d203615031800c2119011245010075201001000710b58000d0541099240035210854940b002c1540000c0c2280d0307450a040f21300a500c001c207215050340c0f0921391148040b038941d040203400e180451442c41140e4240b9241409400240c020001450a0014401056000400340000050780b11000340e0b43c2204108050640e07003581400110a2041c94604c0603031029840316215911a61411006407182c0741080052584803941c2c04c0042e12050000c0c0b1185030b0020002240303081c2807000a003400405041d034403c40d4018894a00300c0135010524503000046000745290301c440000c0802d000c0d20b0504070041255103080100011007c4c0c1c12003071040a941e0750345000c51240c4a03020801c12080e4140700c16050b03030080c4000d000504107101c85a400040040a1207800c2104480741d00301c00038102022040740e515030082c004440340d103000f4a50414041e9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991610512 1250 991609262 991609301
    0xb0c07080d030b0a03080d0b030a0602090423390d0f060b032202060a0f020c09100902160609080406090e071b1103120a17272509 57
    0x40700000d543d004540000341c039030140000c91f241c0303691041e4040c012112025040d284003040c181000402904120782d454050303800c08040c40b0700340d14501c0d174001c0c0890008480009a8031201c40903400e140c3c16000300144501d1500b121030a0200360181c150000a4010010303680b1211a841d007000d41343e400b0a114400707800c0c510140b011001600c2aa68411041001030882c8611541c6941d080c0b074444ea00a9040900084c440500ca5806224540005403d408440d0b0640218043c004000b000715018446101c0844083c010600e064000303048510081d0040f0860041b56201c03c0304403007009104880100000a04110b0981c00081e154000c0c1110a070003682c40c54800805401e1030318000031002414108402441080745130318284038100300180071203031800030446c2c001c001c0b54407450b40340000ca9003c40d403410b001010410350038032541014002e401c110090201c1465023004911016817240100b4a41400d0841d50140c04548000f080c0c90310f00543d8036001a180881d40304005d4040f030310300714 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991611762 1250 991610512 991610531
    0x281a0f030c0105130915051c0201021018120e0909031206010507030c05010e1e070f15022812080601080705031308040801050403030e0a1203150b0c07080d03 69
    0x45507400c008042820310943d0b48101400d2048000341c2c980206091510f000c002c894948040b81c424829170742d0a0b1340c207450141d240520910044105480240181d00600e81d00440421503007104200c02c001341031f180100c40080d65103000c0d1403006803005001501070070310740e02280740900c452138004401102841c603080c01d40d5880003c075a0300420365814000c00180b400c0401d44904d102c40c40150304a0000c00920100040742c1d515520a1052601184a00141c2e04008000851003078111401061400740740c910701540800e800c803241601c1001c1d4050040c0350188440c0154138040c1400011015682c10031581c5401c00340b4450185110042003168010440c071039070040541ca0704095603040aa84a54038400401c2d015154020000d10880d4041000142c85c041500842c0c040c61003a2000d11030b141e078101c84161744e101e903240d02508078600c15007845801802603000e9004202a603600003061900c0b1a191111544069001012503004031410860441c003408040107560551030140150600b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991613012 1250 991611762 991611769
    0x9160b0f0a0f09051e04060b040f090b270f011508060d1410021c050903071104090b01080a060e1911030a0b07090905070804021305281a0f 61
    0x74801d4450309100d00d1003a201c5500340070301840c40082c00300500700200041400e4a68010000840d02c50740100c0c107101c0089070200d0a01d00342c80540d80074921503107000d403400390200080d0100074022600b064400303680c50840e42d0343c00182c0403909154440000e007030a200b920307413100302d8050340024403618000004034030700303540300440350382100d41181c0ca414851614106000700c00d44a4888a4840c490684140e102201e150041c145840703c0c100030314031001100002005031130b0200c605030318541013000302e00b001031039080c00b0484440d40a00b00040c806441d9441040010b0b00ba0014012a0b0040c0080d008101c0a4065102100601d10207803180040c4280300000d800301c08000140744011000a01c8100d0b1420072280410036007105904c121810041006004076119000e100d04d05420440080c81c034034040c05000340035035809065000080c0448041c40000c001c040e0180b103500b40b43c211144482005e03460400402d00041c8000220301105076081d11402a44186040c00348105191400081d40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991614262 1250 991613012 991613017
    0x9050d020616051803160618090605012c0d08090906010309050d050a051e09030d1b030e03100c0e0a090b0f191a0703030c05072f060309160b0f 63
    0x60b240d1500d039440a641c031300090400c03485c03102170b0b0800303600c02c50001105640034454080c01038098014403240b58442000c031701600c9842c054240417840fa400140c480c9403a5025014081d4004181c62120906013800241c803540b10320003e41d4001ea011401d16801d1400100040c2c0185e003d08040000312000d071350385a220005c1b80050800c3c00004100054054041ea0886110f0559407080e2512051164848540c1e60050880503009104909819030864021123907400030000e2040e00044940c80e03a07074112900020011520340601030b5100d0b040e60500103010b80a130300115900c4114250841340c09000c040c00c51030388001005800c1c96600a240e440302ca00d0039211038000c1ea401400360158059160340c08115034060503010260851501c24082d1050182c003406100755400e114600340da0302c3c00c87d054000e6405c090580010055aa000e050100c640c440100c1c40984211041c0c18000f030008001d03802c222030302030f0160001500903005501016110f0080c5c20052031050400254101022060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991615512 1250 991614262 991614277
    0x506120a02040506011b060e0706090b09091513050f280b060705060403020c03060f07120b19030308040b0c0a0503070e0a0302120109061a0102100510050409050d02061605 75
    0x56070343c0d10216545903c035420304080c1d801c83ca07040c210003864614040c2c005014104d42101d550060340c10200b41c1910441d03544040381d815060300341c20311583e074080155401010b8405c203845c2c00c0740c40078440f640d100c010300c070300e0034480c0c16500007545d03e000d9423041840a0000d040e8900d15603040c0c11440c02d42134020110262901d030081c00100c45c4000c0300070807218419080b000c3d00318490541000f00b0180c0c009651080f41740706405035a42501c9032803018022820540d0f041c2d01003a0540381c200341c100c0f003941c031202d8181c800130000302141082d5a0f128143c2d840a0300150001076400d0100002e12034010581e03500980a26806032600007110300080c41408083e004c0701c200081c1091040540d918070304800c01a5800078802c0b4600408000b04600825155004803a07441c10920b4904540c0041004a004500306030081c01001105144010090400600a466442c600c00c004900c1c2e4556214000016115900070a101e04014034041e140200003040045d100350060301240d0800c2d40103003130b5100d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991616762 1250 991615512 991615519
    0x50c03090f370b0c07030e0d0f02060703180803130b04030203030a0c0501060b040605190e01080a0e0f0a030906111f02070302010912230c031e040f0e06040506120a02 73
    0x26100b554100d58614544408040c043c01090030600040007045070040464900c2600c903070380d0b0000c1c10428024040c0314104003800201411080e1030260511000030540c1c10700c203243c0030810000b01c00d00304401d900d940d0005521640040b841d98054084010b007280588442c070784043c1070619503400242c3d0780c450356605404014009000d501000720035040034014001201d00f4948403a00d4900c02070040c0c004110710094960310940040499000d039002e180c0c0988180e444400399560907c0c48000381806070b10305207081c8541c900031301d4911000d001141590784240e0b07407058298940000101550011034a5400c2600401f00c1c402038022100424081c1440b203400150312000f8508050780141411301015020001080c11000040d92101e99040d05919484281a500300352407800c51a0340503181c82110158020000d80b005402d0300602c210594440495140c176158030f17030700804210180c4d540200c40e110084810300ca0f040c03600b070140c1030307000e603066400a2020b0500081d0f41e942d101c1086000c2d02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991618012 1250 991616762 991616833
    0x22151d040b0307180c120c02070302090c12040c030b091603030c0c031a1b0a0e0f031e060106021005130f17160203152512050c03090f 59
    0x1542d1802d2180500030020079034100c00110204642601030107040004e5000030326070424004880c03083e0301c80c0c0885080d080e4000c00c225421a42480100366002c0c11a0545100500c0140341c0d9200301820144200e1013001500d114918510740b0002e860000b504e0349259400841109984801d080441c4045a400d40740c4038890440d24240840304c600300e6040504002c089041c4401800c8803c01c40c42d02a600d0300d440850342142c1b004500c0b0382c1d0301452407030800080001404d00300a290040308211503400c0101958240d081d80403810941c42e41c0e40c030003c2d000d81c0058004001a030340500009002c01984030013840725103490fa90300b03400f22403001030040c80000d8500030002444042c2000800060380c20f40c800390744110013100030079080c41c0504100e200380310782d485c54074510200003c5075001e40484c1c90000681e40d103141510070fa0342942030940081008007801d040c0081c903d07025040c0030344002d0711032036960309241d1070301400c4c080640100007856020004020340c1c0395101c1500c03240b01555400746e05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991619262 1250 991618012 991618031
    0x9050f0d0819063201030b01320a1e1407060e0c06161106070f12030f02030408030925060e210303061c0506010608070522151d04 57
    0x1000f00029040220104001c2a40c40c43c00f440311044144004a04031101402c10f41100044059450003070140340007411901e9000314001010070f03820108940786440314000050402055215080300081800054408100c4000c07421880b06541c030710b1900f4604841441161130507180c45108202c4005d03c110303950f04600c1c0c01036074288051104404001c01e180d0740d0340c090b007584c1720703012000c038030300741d0340c1020030307000e800503890040c040b10311050344a83c1c00308402100c2d45414445601d1007554800345511500084164081803000f103201e54420f99000e0b450741420b0588074070700031080300b440c40300b00e82ca4440c0c103440d01c40c02c02d48401101c030b00b85001c10714040c429000c5000c1400300c004540815150101c90344041c0070105c0514403490003580c2e9050f421100302c0604c10703010107050024255410600c010301101b80320f1103c25510694a08019103490302c406c2c901c1310000c040351844131603484d10035400d10040f580c140080710990000e00c0d040c0e024030340b14811045204049284244120f03a03509080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991620512 1250 991619262 991619311
    0x80f010303080415140c0306011205090709020f12010320030316140f0f0114060105041a1623010c020c03030409051018140105041107030309020a050d0609050f0d08 72
    0xb040f040d0049900c8540701d007006e4120f010581c0040d550740740030859014040c8001e4070700d881028403c01103040141700c0b6624210300f82c4002d500240c01c0c4004100c0030424190940da2407201103000358400c00d201c1c000b200081d0001403032500c00128035886034004001d01c00c405070a03021700746100d0ba008451030020500c0400142c0c0b50244000c420076142c06101c15208071514107500c15104407880e04981e07402e0783d0b0751000444692169001d40a04041d03008108681001c0a00c003600c0d6015504403401514030f410307242d06a52040481c0c406d04146858107618085202c01e0141020401c1507000904802c560701000989902541c000d0041c01656000010246200545000010181035217074891101100d5080e002408104019501011500d40000b505081c1071040018101d010a0b5507410001681d5084001e4900c0c0001a07030b1041c2581c0010135590345074083d0300d0b801441f0366000a1130038854a0b0460802c00088448500e41d00040003600c241604030304459484010480c0c407d00c05400e01340703070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991621762 1250 991620512 991620521
    0x308060f0a090209190303020d050f0913151a070821091501080c0a0b090d02130f05010b030c0f031305030d0e100903091205150702030901080f010303080415 69
    0x809074010001c03440000d42c101d003503000b03001200003951040c9800d19101c3d402c1420403141e101c0200182e000720075040d0b01610443c0584182001e442d44a0b2410507903c000640c841004030340c0d004110342c0c0d02c04005d03411030000c0c000e400400040103c585100540e1000c1d1246029544c400b40600e100010460750310100b40c81017050911080010100310b0501c80d0805a8a10611801c0c2c451481d00000100344950300003108010b440000303001d034491a041400342101740e00081a1550803020481c1c0100051796040483d800408800070001071003402c28080c41706841041c0d0240b140082c0c1013060001904068040700e078510200c00e100c80d0342e07486005401c5401c080c40718001d0410302020641c0f13008400590001c440f8a0354407400c0310347e1140c18244d076074100c402c18200100424254001048040740304c0e402039003150b01400603111402581e00e00c0200c8048229140c100581000541c0441984c00c000c2176034000e48110581c180301d41c1195030203000000007400c003030310144c3d1724000110680c10329040f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991623012 1250 991621762 991621789
    0x3232e060b09010513050409212102180901030311010b150405010e01170f040210020c030c09070219050705040c0504030b06150f0703080403020105090102070201212301080d08090a030806 82
    0x100b001238040318109145064060f15011054074140742c038072041c503486207141510804005010b00b07031b080344130380843c8001c0d4828500d0845c1004010700201503617980042e458000c60007074503074126261005265030300311070102d42c44520800c13414111480c0410310038152002d483d02802e081c0c01b58400c031001a918041c0300141071041d4036400f070030800f6601c3c00145041c01988240c4a04041c44160002a44c8601034440070380e403d42d01516001c2110b2801d1420749403c04042c4c015a050304404800700c000d10441c010082d180341e07002d90750400030b40c2014482c8032158140b6241c4141000d05580d16101c2c0d10341c001c1e000c0e510842544002c000b9070300b100400c4405080c03899806583d58456840c0141000d0001c841c154055442d00300040e41264041c000c5520090b0305070f5a01000c4c25203144c3c850720124030071185208030b41e5640b4080e01c484080080001c0e070350711600141d202d03941c58010032a00d4143d5014140f4104440728080c00150070b80001c41c203882c2c3e0351504082c0b0585e82e0300404101c4c601700e00b05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991624262 1250 991623012 991623019
    0x80112060b0d051005010b040308032413200712030c14041e050a0503280204052809031d0f151c090c03232e060b0901051305 55
    0x55070b00401c940090604200a4034400a12035a0381c3c81741e12000501a43c0b0001d4203d0400f00005450074498440e201e00c40b20940101d03410440f070700e00100c0c00c102425084194074655502c80650b00303840c00020070180e04040d1040502c0e00c4001c1d92141128843c00c00c00d21309164460303002d003543c42e008109508c9582c281403a0583c66581d26201004183d5200405850031446c5076008100d60406001000c280ca40140c010720f01e0081d50582e40302159041c2c00740e07800490780710350840c0060f500c7d80641c3d4010881442d03032110740050380411a11860121003501b03e083e2030801c00c200041e400544904007040c4e40214a0100240c01006c10001c48425074401e6010781c0050f184844040054081c150000241200d4a007120b501c1c00c01c1c00c00c84c1c9102c0000781c4101c1256904200060441070680070454a990f404401306211000d054074010841401c2e248401c0042904004200a040b50644c41c0340007600078010a40381c000d8682d80e9105101c0c0c00390400800003459031058042c55104401490080e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991625512 1250 991624262 991624279
    0x50132100617041113021b010504080f0c031e090111010b01022109040c093809120609012a081f081009020312070305160f230d0f080112060b 62
    0x1d05d000025480840e951205010008219045050521540b8441c0d58418003503440d205182051030015003258000210910040000300c81d406001004020304d020403207196500c43d440000050141070300d02c000000b20303030315190616185030780c006507481012069000c1340240d100303a40101c02440c850124542c2d0060b003095040109540c0c0145140126400c00280400008500100e14a02081c0784400300d8800c604100c1c00d00c001007018001c110140000380781d80d040100b00028607082100456120389540d42d02d03001391541002d202501c2c0381c400300302c2c03004900c501d060403405011072501810200205051490a0041141800310078000d02240b9088400d281d0f800d1074614050990704508901a014150000806142d40b10640711400d6242c3c9509040c2100507031842495011040140c40c8031150032040c0000c40d500307000c14110454000351074055640004543e034504030401c0e0800c0c040101c3e601991030303001e42c80b0026a040d501c111501140700880c500b0040060280280040e6100b03012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991626762 1250 991625512 991625539
    0x131103190c050a12170c1e0d050405030a0b06040e1603051e0d0e0a030f0b0a060e0105060f0306120d080702011505010e04090501321006170411 63
    0xa145016456214905038145070703445034280204481e06116108010040610100001321601c0c0a0391000c014021428284000d03280d00c24504150400ca0301c1c1e500312a40b03100c4002c402d00b070180880d0207500c3d0070150718141c50400880c1d40c0380c000c10700103040c24450501107a003694031500300b00d00c0c040940e01160088130b451a91003010232840d200460b0503210ba800c040ca40340031800400103a00b010038000d040c503a41c1c14041540d00340c115207403051f800300d41ea90003c400610801803030855a400360104003400e10b8281c001c60111121a04070001c80c1911000401482c1e81e08011202d0b0274000316102a103940318600400c460290324003002c0030b0390013904180f49009500c228620300c50316042e80240061001c1100c2c055220000f4020940010076440c201c00680c00d241c3c010f41e05c81e5205500005100021540c85100900d215140c81c01c2840c141f20707081307140041d50600c039810200d008401e90641e85061303070140c03190030368808103a02180c5860005041c001052200c0700420b40180c44000500300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991628012 1250 991626762 991626793
    0x5060d0b0a1508190209040f0210270308041206060f080a1514060913170405040b04020313110d08030103062315060d06180c080705070803131103 64
    0x80140d025a01c248030b01d000643c808001050082c1440111101440e15002d80900000d1030700280280c0d40c0c05c00c405074580050b00d450040c5900b140c41c1d50745030b000f02c2c0401c8a004030401d0900210080e0480751071003d001013a00c11080354111001030702d000c655120145481409400e6070b030702c0200304401d945000104842c01198640384284540d9001040380400c20403042112150b18280401045801c00039109003410311503107030080c0407542c0001514280d543e43c0c00c5001114071001155480125040020b42001d005140c4d419034111019405c43c43d0504c41d002141c507107040e010300303450007440200b822034071241d030120030715600040b80c6542c0c4c0d80c40381420340107000501e0703558078081c1c4c40c660508080c03248450500d0244400c8070f403100c6a64030010070808650006402d440d41107030348034000680944030008031041445c6240c40440c100d8490704004c0c0c2030440042c41d050034850100191400074031500304481d48001e100045c4e000311140c50410215103010300e110309401d440307245900901d055 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991629262 1250 991628012 991628021
    0x2706091712040b040618050106030302070609140402071a0f060f06070203060f0a0f0603050c1018090c140d020c0610143a0b01050109060e0405060d0b0a 67
    0x14065144038011508800c88420a48501402504001500d00208000803028100c40350014020074002c14a44c0c90560140401e410001044801d60b565800410405d03406225540c010641c604100c61641d1920728801c060b00c000e2000030f40f0850780010050101301d0000d0401d0080c60800011210070700c0d0544460f00750741d10944240d44100c1c04c1c02400101468418210b819080e80903000d07007420385401401c22040c0d68050074010441c2c2e12021181c00b03410248c4540002580503000030000b00c11270030140303c0190f55249040040004c076118894280c5000b5000500721079030310800288000759550105c0e15200119644801c11100050203c50102c01d50060082007918009031016500c03a00418585e61030f2610410004105090140307101e0300d024000b4003040c81d11060203048000d0204003030844c48624406540241d0801081202482217140900d4090082820003004590510030b000e00014641000e8511507034482000404070748a41070310080a0303130300014640250800650800180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991630512 1250 991629262 991629281
    0x20f240408070911070303090201210204180501080c2112181008190608070828030c29040309050301140606191403040c14222706 57
    0x14420b600e000300d011070040c454505840c4000d49098030380101544c05501508000c2d41c240e06000c1203c0340140d41000115600640e0416600b005907210308000c21032010083c428800811549070400601040318001400c40705403034200c078501003030070600341074a8026410b207580c5403080c026a82d14480702c0250380042c2810385403a0140702c8409000805008904400d1144032000580c2e110214085c3d807e02103845000607426900030600c01d40307614449103416020381c0840403942c81810744440e8011100000001c0e42002c071200350915009460043c02c6401080014090320f084182c64001900280c1d658450b00a41d40c21500c2c1c90702d45810003030700000741072060900035401e0081c2c4c1c0c8102c0d10310301c064038883c4e24006c1280342071072080200f4200d05000c114045051004840302c820700000d154000d10310851140705858615803d20107008015611039400c3c500815030710b041d5500850600d1410406c01c10b0103440005c501d8858000521803041c1202d50550410300c0702d8240e814001943c0021018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991631762 1250 991630512 991630529
    0x316031509051308123c0601030902120304050a0f03030c02010f09091b020105090106080303040818310c0509010f270905100b07030f020a08030a1406030607020a020f2404 75
    0x402c4950490310f45040c4080095110350510300602c81c054410a0006c0341c1101040c500002c140d03810354085418032000030242d03230460b070000c07078108807900d001401c1c14050546807411240640c0340da03401400081d10101c009040c0541c864070310441510811811001b410011024030503110178144440d442802164200019404d10b4002804c65405015510440b152900150315507500c0f602d0f20000c03a0001c21048000804035016600f0656401e02c6824420070200120103801000c40b6205000311144581e603e1a00d00b4610380c2060706400500b580d00c900320a0030031140601a103501200d58a01e80c003419686c0384104002800e482d500140400c05582e62940300302700c20345814942d00c40c120300f10310035001805810410b04000030302c079600c40101940c960042350242145680c078150207800c02c44002c14081d41d2240c4051800c034440724099048481600034024500b40711000945901d00580041d0181315148200005034640c8e014501407280e5441ca0800810fa01400245840d805803051941d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991633012 1250 991631762 991631791
    0x30a05061002030c07030f0501140115020c0d031d0a0f151b0b011703091c030e1012020f090d080702091b0a080a1506020102031603150905130812 64
    0xa09038000004c448980c540c00005200841c80c65590700070305060100201c80c40d540702c000c003040341d0a0100038103010305a558858a10701540850082c6020b10368604d00f81b080d85c1c442c1001c00404c2d00806412008c180030300e074080c82d24418201045c0e510360140d00c002d014180b8000e0008d0060226070321604205170a0b500c4491001e0901e0400d80c003500318620103042c4001820040040d401011040c5503c00b0009080d0390030510032200041c514506030710070703c240340e40d1508507404041d40714140c4d03004000200c54080701804c500b00010f0082140c401190840c075400101c0d0b100f01c002220035030325010402015020380a206140180d019003220030124003580c805000b00d40046c054001d0301c0b0140100304170482c00c011900380c041382c3c51440646900041c1e81c0d9002540b03040c02090100c10040c00490b00050703079038100207034441071f54819000c101042510308104003052070510760205007200d00c9107030040745684880718481180341045400400615000407541001d5040550140c0f091508000020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991634262 1250 991633012 991633039
    0x10c150c1808030f1c0501080a0c060206100510032012060a23010908030304031806030e0a0b09070519030309120f060e0708070b190c0507090908090402030a0506 71
    0x703000034030502519a5981050042d11a80c40c0c00c440908002d0400d10002c041640c60341c1c10328011548280c0000b03d5903004482030070705011010041c03200522452005183c0d45c94100c02c0c04124003083d0090a21890b038000214000c6c91094003c41a815662014003850b0b07071100c0c04200d4a5840404428840e81c1d0000010300c461800001c040c08440c040c0d06003120301504580880c4520703440190f59818000780c0c031000f0400e41000c1029500c01e500c2a1215899400101d40090507183d840c0d0113101003505080c020b28000340081610050268021008155a1210642e0070304028180d004141c03c0b01a8040040c00c0d01d1460303d004e01120701940380c400c09144c582c104d142c8030001d0882c0141c46c98103407403a010000b9100e94481d0100c407144500751041a03454215250501c00c155000000c5018007040d1911105440300080b50004901d08091032015015a0307a907441700d680380715160f001559244141c00b88500a03007114810b507001042150780f494604102c034010710007039481502403420b40b600341 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991635512 1250 991634262 991634297
    0xf0801050402030d26070315051c170409090312051012020909101b0e0a030f08030c090a030602270906040c051b070305160b0306040506010c150c 64
    0x1980200e0b00a4003400250484030010358540740e070351105684030517444030320100991658800901840e031039600810040f901500c0611802119000705108221030072054404002013983e451a10754802c02d0603100c407d5554030700895020b154010140301c0e0030545800100b5a11501d0400c2d07904481c0010010b54880151800c003006407070040c20300755010a081030000d0725105900c1a846140c10302112540b942c0d42ca009029201e4060703c400c190300035481d1031410396800401d0b488240c0c0040c1c0d52802e2540c515203454052400140001d04801c0002022441c015400e034212030b5029006000f1443c2c081e03813864141c00a500010a48c803003100340900d00003010082400d41c0ba0b070503100520304c0100e611000d04000003040066546018880100901807024050302c8882c0c40c04468680905942880c500700350b4142440812581d02c1e0080c1c410303085c00300744014020f03203030010000d64001030a9502e41006036445080b1500c060311101d881101c82100c0f40c1603800a106052441da039020805038a990403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991636762 1250 991635512 991635521
    0x906090b040c06140a11030d0c05090301180f0840051009090b060d0e0102090307051f0804080d09150f0204030222060b0a03020a02011107020d1101140c070f0801 71
    0x403045150300c10081d004900b4860034441b00c401d44800300707407442c0c00c541040c01c10458014034441c00c08208086209010f6181c2841003184600f4074401c2442000074035a9007190003641c142c03000b4079014000c140c400e8a0b4802c0b0482d035039550300e00c00141100c400da80e9044280c2108101052440d5580c1800110796800c00c40e030b04a1802049072030311031455040801c8035014203c03580b500d43d0041c00c2800411000c1c8518025100443c0c511000140c3d82c0795207005050410040c1e40005015540a800e16001040c440c60a503030010046d06e030400580d1150b140411061040d4600c118040d401c00395182d05001c061140c10882c8410b10008002c1c0441e81c6d21024141c1c000d600c0081d520081c2d0503a8141c1c05442c059000c01500140e0f40006011038503031004c0445500211200340020f540443e000c0d5045030240f007030480401043d01d419061045c035074005043c0c3c80900390010480c1e1000b0710241d500c1e0340203190946580302c10a004940b110400540c090342e0303907050b01c902038405c0a0040d0002c0d02400601c01d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991638012 1250 991636762 991636787
    0x4020f0a06081803091e120105040c090c0306030204020d0c030c020705030d080c0c1c17010509061327172503140703082409070c05010906090b040c06 66
    0x1502411960382e00d541440312001d003485080a400100250a496501c0c0814180c00f40b006c0c040402c9181c29080600c4160303c081e55401035240c0c90300040c800420b00301c401080888003049400f1414440001045028000c5540000c0d042400030500042040858001c0c0380e00351200e80d4104148010000200d0350b403070941c8259a01600400001c0d003400c0e00c51102d0580c4014070090182c90405a171078050720704511040d000c180d4402501003464810b038040100c0421443c0210700080c55410702c0d0000d4803420001e0043c1e4405c00c0e40e41c242c54250520b540101d060b8003580c0c041c002004400c0041038034201210314084036240415211042c0300f450001c20740d11003491158001c443c20505881c076034002e5041100982c280140b40d0400900c1401c58001005110b02c255200c3d5000c1c28079240b44440a0f007064503c041c424510340488031075403525026107500220600e8821500c600da0b0038603a005201c00c030400341003d800d202d82c07001800b5511410a01030b034450f1810349000307030f03482104850402050f203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991639262 1250 991638012 991638017
    0xe370f0c09081c0509100207030b0a020c1020160c1404180b0105090606040306061e060f17060a030c0e090d021501050f120f0709060902040303050f070501020c0d050304020f0a06 78
    0x308205c60400c59080d850b91080f6004a400c0c1648079200e214104804640000000750001020490131100748003925456a400a003072064020310b000000f0001c01248840c1611100820b20752404203106003084002a0000302240e8030070b031208010081d07000c13100d52943c000ca0609080300e600c1011503881c03210f1150081030155080c2d090a00b0462070303000182072103030304c50700501020000c2070355032140400600a00403000418086807100e010480d83d40d91080f4140403144203daa120b40d0040c0c041c40400c00e602440210300c0c0d454000185002655410160185214420104000407800c51742c2e80190020340843d2802200ca05040741c1d00c0d440300a0380c2c003403071880c4001000b66040c0b45c03923403c0030144003c02c2100082c50b010078007803900c005503049103010b51100e40d00308050030040c400c08024004141c07042d03240c503066440c054400e1140c1c1c1c0d60024401170006da00000e100c1c4c00c1d41511340018242007680c0306501450030007001d513042524243e11540c8d14005491091404c040c0f070404440d06078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 991640512 1250 991639262 991639267
    0x6231009061d09180d0c0f0b040809190815091f0f110405090124120b0909010b0f03011b05030901060308040608010306050f01120201030203070c14070e370f0c09081c05 74
    0x784e0f1101c0b23041c0d60140080315060700500c005c222603600c4600700040c0d00703891000f001015140c010300b0b40c03404000360400380e40691070030240501325501051420540e580c030111600e540490405c3c8600429100c003100302034518044411161224400090040380c00444840c1040c4e43c0315a000e03102e01da1402c00380141a0541c48014860b1406001d407942840d25811002548580c4070010a0301e032001100c01c114165514510060645020004181d0098040e4001c1010f503c503a41004107090603103503a031051050110005074010350075084000603641c480f454030f8580e070380ca074000b5104200a02081703c92038140000140d921390520003080c122180078000c504040815001500294000390040f404c10a01300c1c80790010541507900411484040d40013048880d1078800301c083c1511000d4510340440e808400d119020300d0015840b07000c00415812205805404800c0c114018404658407187c0141007078200d2040b10780001c00c00382200c000606a412240c00e004000d582c281070b10b1440400301e24113 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 991641762 1250 991640512 991640543
    0x30c1e0b0c1c03060905180d0809031e0405030708070f0b0703020309060702130e030301090b010507050c01080c0c060f010f120506010b0d0f06231009061d09180d0c 72
    0x18080701d0700c2c00001c600340000c0300c035120303880041036071021180459800e004100c865040301040001190307590381ca00e011710705400c00109050300e0788182c4410280c00400c00700c54500d028110005c46000f00001012114120b41d02c40d51140c465540d03104d00900107544100c001520068082111a0f141d070680c051490f02044000304039240d045401c0c02c2ea0464003009140000030103610500307031405038040003140c50350701d440c080400744e0325182c41d03550400c201400207500190000940030f401802c2400c18040742d42c0c44018040c62030148820204052040000380440c0c4a005109a03043e03400c0c001041d180f050300c0d5210074400303410415008000d980300d40010020540060302038500000440360100380c070446485034000b44d4500303404c1a075840e180c10141c41c2040718007451100c18400309464140c0d065281d80c0c0d001c1c0c0712940d04d201d06002c1c84006a407000c0004000481c040690380014034015060074044c805285540900c07580750110f1040c0703120401d5150180d9001c54000d517000401030401c855 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 991643012 1250 991641762 991641793
    0x20070804060315050409350d0b0301090515091615080a150906091a01020703060b010215040812181f0908030112051203131209030c1e0b0c 61
    0xc40792034040d98403010100108417541d070b074002c100c410390103003515202007004003d501440c900049981c00046113114525a280112002039844282c101c110008040c101400801d024010080b002031140c05448219a84001801d12030f40c090300514040f15002240c2d082c0341d806540d40c9000e2008900351001340417003561300c119005c9034441c0b83d40001150f41c2148200c4082286541e81001040d02e072208002c0c41034480500c12080c1c5070080d003100c0504442c100e07001035241c501e10300010f003100e9259008800184d001300110003221100240c2c1c058103182c141040707200d60700070004a03040c0f0107050002c185207452010580141c591207030050400c4580b0000b02031120104d07210640306050311507661501041002010b54024a04102d11544507462842c020b400c148a48607034016540040c401d02038070140e01c13443e0f9a6a9030388494070b140c00c80e0001c04181c9000b601c89d03100801e03a0651a00102e5100c015480380640d503000081102403040d22200c030200c0501a054024680358080e100c060070250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 991644262 1250 991643012 991643021
    0x20c180a051b0a0f2309100512071e0f0e13110316090e1905151003360201030c12090813050904171c0f200708040603 52
    0x40d000010034102d014440c603078004a810410035100420f14000c090140250051110300e024400001c01172582462089045164014113941d140907184012000e400c29015070300702c554400d80070b102c00d1002d1401020003407400301e1b806914034440c4080c548543c4207501034207106090740d84a41b00c2c419050756080510801441d064051141552541c1c5800d5214065000850161b0410320302d41d81031040e10030014100b2800707980b02c5103012200c0010070141d007440c80000c00207041880408240c0d626001410b04148500805159200700c5a0064025007034041c2c1c0543e449401c20150b1403039109a950816114200851802c5441280e00d50b90400542c826802810400640d0038100c601200780100d5070211801d00354101e5060710001200090176151100c010018601242c81110614041e504c6182c059180a440c802e0950b01084458065054409480d82132204042c100b1461400c0302c900b03406815600207541c0c0307031070744c061244070f01c3d0394180111691250451001850036281c050104e0007030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 991645512 1250 991644262 991644271
    0x30605040b0a032604140a0e0103080f070825150c230c1504020a0e13060b24030a05060f100e0301180b04060606090f031407170706020c180a05 63
    0x14034051106184030481c0f0016002801ba1640d004409030031050600501242a81001d4281c5003140c00402c001a841c0b821a48420010010399840341c0e000d16203800e03240503545140b5001032415024a001d0075480040c2a81103000750392000e01210408001d00440303c0c2c3c1d08010300054004070003c21910391030400714002c0410803c00d40e01c1c10018200c03003400c0c03043c802807215403020300200740001d40c0350440020003e4844800b240c2c0841c206018120460f0340c280d4001086036884000000c0c05036214035504020010701d00c0248000500d4010f42440c075441183c03050a05483d0a01190003410581214940648050f000c2804054030203004e03144406a40380803a4590b4031a50b40d00010b140c4204c11440d0a0303c01c44107040e42c0e0920f8a041e00c10383d117280e0414400c110180b00104441c20306a01910f08980c0c110010681c50f69000c074902d41800043e4000c29030580104804404104e00011008204c480682c207a076a012210820040066000c0c10540040341150340810310064039a0702c1903810 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 991646762 1250 991645512 991645553
    0x5120408040305010c0f080c0405010e091306060f061409030304030b10180506131e092123040f0b090103021629160e01021204030f03030605040b0a03 66
    0x60503901e075140f07402d40394100a100700280c929096000e1141d0050307000380d009586001d00074200f504003000203124040a140701031085c501d06000c0745500030071340d001c0c0101c50f8110005004181c0c46088415460559204000014000d04031820454800302e084d0703180c044004000d145854996200d040420002504003c0c1d1921003810000d48000f032a01d19511030f507038890700858079141000802c4105405104e2844019051030071955241c05045030481c17240d070798204002103281660404021403085582400711012403003c10902c043c0c1c001c0051400444107000402200d030400140441c83d0046214180360410103120510006d41098041c0c0850081031400500b00101d80b1032800c200d070a420b00c15a002000c014594884a40080c80c0f410000801c0700d11408074108845044c064103908002541040074400382000c03241c1c82400b5042005410100c01c940351600ca003400b50f0743c55481d440c100d010a2800f40c0009880c180342c002c1c1040316000800d070701e20941ca1601e855040d0403242000703521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 991648012 1250 991646762 991646767
    0x1b1b120616110f0c0909031c0f09140c0301110c06190e0102120402040c02010b1507020a0b0a030f0b01110a030809030f0403050c090604051036050a110a05120408 71
    0x42c8003820000711504418460090a00d4490a400d02c40100006450900c0d2a003080103248906001c055a00008800e0801e000540c0c0e41e51420141c001d10250034001c00707103440c44a00f80b0841030000344100c0e41030411002046443c0c20f54050b5401403045a104883d540c1100000401d050030003044052101d0109002103581a101c1e0f8080382280d00002c0c240310600300780410b00065042600c10b210500c007150008200007040c0745e002601018017206185810100021810110f407600c0d02d08500a0000401c030316200d40000380013031301501c0b804403400f03551460030704140e040d51320070500d00d40c0340141c550207050343c0b1203152403c907a08140180340e01030380d01c0200445180460208000c10041d030290010f4050200c0031010000c0781400940304510540c24541845800d03641e04281c1c90403a03100c00c0d0081d5144030203000c0c040302c1044092200c1d480c50421110502c1c0c1d51381c1a0080d920803800058100103407000c1e40707084200344c09400401400600280244042c1241d208012504180140301450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 991649262 1250 991648012 991648037
    0x1200304051e0111042c0c041a040302030f03031603091509050106051c06050c073201050c1b06070f03020a051e210603031e1b1b120616 60
    0x1031544154808407a41a0354900c0d0500545081c140b42229070744084420428201f45024042901481c056682801c01c1c4400c000610f4a0350411a030045a0240964803011107804207907440380c0080f56080309140e0380b141904180c62007440b686121030340c440c0c41d502080c10800700880003440d003400202c2d0a03640c1e80001080940e43c8504075021108070f20300b1030002594034580303078003610b0700603000190f1101c00303000c0680025001c10401541809120741c1c0c900c00300c40c40082215a169205c2d00d0702265281000b840460304a950060101175003043c8000c85601c2e405204e956904000c80e903500c0011220b110f0f501e00740c1e00c00e400070306040e40b1070302e0110b05010036901442043c0041c5440000c0744400000c05040c120000401e2240c0105000c02c4001185040004661644075a02e22400304142c2824851103440f404002d403418110840c3c08800c1d2410070408051317540244403d88a40702c805030b194280c1c18a0702d1004001c101600740c0240c40282c954002021122101038095000c0c002c02e007a142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 991650512 1250 991649262 991649291
    0x90b09061b0a14100e0712110a15050301051c02010c0201030f1d1621060209212a01020703110109180b0f01030c02061b0c0f01200304051e01 62
    0x1a01111605000e881c50130f10043c115000c8841200c0071070695000f01c801000b00d600c40d03825100302c890300004500b03480713815540011918030441d04425806010103081c008826480800345041e03d1055030710a1552105144849400010601c0280020710905443c40194031030f07002100c510300707405c0c8042061014882c1081407070b005680352018a901a11070a501401705056050040c14030544040c0d008880326984002204003100182c45030340c00081c56115510f49048000000e40501d000c0b00454058480c0715440c1c0303441da104070001d02d0f080751003080000810350849070035040580090600c036256640e50702820b40d0b040703103150501c1081c1c034000074080b03c000c075440180d901b01070340068094080e004101c4c98441c01d410721410136140c00212500c2036000100d03550050b401c05200820000300c20b8880f1040e00c51804805000e01802d944840780da0310540041804900711414400ba5445c0384019640a00003110054929880f008480001c3c42c0401c6510803080f03c504000b00302000034000c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 991651762 1250 991650512 991650533
    0xc0c0b070c0528020a06030b030709020c0312011e0501031e05040206071e0309151d0d0c060504030611090a0e0717040c0510080709060e031507020706090b09061b0a 72
    0x384240b89003420000701318a0050882da01818860500300680f5405c20042640e4000b64040e07111320b80d41c00280380c11114410815204684003446400d40150b84a00464211540300d00c2454100c40c6402c00103c0c4a60103405004d9450000c0c0b0b100362200110026090050300020f0002d03600080200700070004601a600d5a010700f10380e84c0401c02c1141c44614000740b80712100d40c840c2c003507518014504072a04da4003c0d01150b03915104009241c140481c0d10000c0d00390b003072007240104a01e08102000440a80040240007224025141084031032511840c42340b10b0322031011003c0d8441c0f110202445a241c4030214140c2001c03003813070315280948108640d05c01e03070901502c4c1903d0481c03036840108054506000410041501c5180250690600860282002d04540606001c0c01a890844141030301c0c204040d00810800d098400034034107005401a40b0780c64039018040c00100b0745040400c403804400210791207410003514951421590310b000200e0200001c40c062045d0080d51b03002400305440c101c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 991653012 1250 991651762 991651813
    0x3090c0308130f05030303040209070318051006120c090221190c030b1f1b1a09071404020f07020316060809190f05150f0403030c0c0b070c05 62
    0x74000d59a480000520642100d10342c031010204804034000e00c002e44002c81500e801c150f060f52400f02e942c44a50b07064014280001d40541d0b4040400f01c0f40040c040002101c1c207010f68114420011543c84104201500200c220003500801d041801007040304040c1c0d0040c518042c0f448030f00407505a01103181e500c2d2140079a111140b69001c1810100b410291b80300314142d401c0320742000c000400500e00401c03030b480b00d0346442060b10260307010581000780c0070308603140c6100e2584500e1855002c1c10318181025103c1d4504240026401d0f1001a50700b031000500c45040e1445642d40b00700c10800082088040d501c00c0c02c50710440113042c040700c00180c8040280b80d8400c51154503000d031141c201040108071303030401455007120358414100d82140404410b142450150004008500c0c0d5015080c09850007a6407a04800c1015588040103c0f540362207066a001d14440d1360213200101c007803841100d080d0380070708018022807504c101141c00e803805269682ea8043c822426a094514640300c0626003481003032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 991654262 1250 991653012 991653023
    0x11704140a0f0c050405010302011e03021603090f06050a0801170c10230412020103020702030a21090501142b0204060306031a0405030304020d0507090603082106031c03090c03 77
    0x12025042010074079820004e000140c60401540d89103070002070161210015141c00c101ca0451076401d481d200b90111703030804141b4903c0c1801281c0a00e801054005039206030018402801d4006ca40c46209804a07218a055580c0346015a400c0194000b650803824245121912076900920b0350f0751175203902c40c1203605040d15841c00b000340248095510b07020912070084d03100d000300024014420a54014a04190207180040c1c0711101440441d1400c0641e1201402d040d1031030031030001001d0b4240e01c5903c440c059036219100d041d030303820054584061201c1041034244060002204041c0c124140c03186660104414800304180b40e0341caa4100d81c007a8101c400000e0302c910341481403203c2c0001004000d00c859159100d41d25007502d03115164040504024410303099162603a051001c20050200540030182081202c140c2c0c4c6e26014840e544040008990a0003003109148254806143e461168002602500c9110303c0002802580c1108816a00502d0380c2c8080c0c2d040031071300010152020f5881031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 991655512 1250 991654262 991654283
    0x6030412030923010c0c0302190c03020d050c10050f040e06030c130f0e070815060105250213020903150c0708030c0406030b0909070e040c151d0f011704140a 69
    0x3c0385083c00e4402480c1c807039040c84800d102210000360300240482d440f01c4440007080c0c401480c2d2604d8004807060307a001035031020141e045030040c4003022070b407007151aa00322031390140361260b508180ea680c000c0c48112000104144820801c441c03140d034100d0790061009056406c0b105008001031000000d40d0394030070352950385050044001169200307000012451000800e0741ca417501107129600e01c4541c241204131030b1100701060069000780183c0b12071940441040c2c0400c034140035071400c61120b03001d00364401c10224004030240c0c1c4051003298109440a0040c0842000704012130b08009005001040c152508100c80c10100351807c0113035010f86d040c800e01c5903940c0e1034100c0c028140d4003d800458481e850a1003401400d010005a4004444c1656007401150741c6500b00440102d05a0344075103489206403185115240d8002c01911020180c0002049440c07600e005008489500489181c04220240e0703424041c40300b0f0b000e00e164440e02c0381000c0c600803841300301c0e11410721948150445501003031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 991656762 1250 991655512 991655573
    0x90a050111120117210a180b090108150301020403060e0705030105190906060e0c07021315060305150d0c03060c03180305071106031f0e0402060304120309 68
    0xc0c05804075080c6444919030800211500b80703150901c0c180f042034003600d4104064040c000003440035128440e07411100c0050f070000c602c1d004010341e000d030020300c0004071141688950348640111020580b940a10500c0c02e0001d400015651204003800c03e81184540140800b0705aa0034001000a18400c44002c07921940f5004018076011a0790800e82c82641080200680e100b100c0000c100024003003140814524500d041240040500b504080ea0303a4050000300301c86404900c0041c030815209031a42e0001555900d8a035040310100c0041e0340314050000c5003086060f20980009420181d07441440c04a4a640b81c00151170407502141180e03100112103040050200a100c0d8003100522401c0a106401072200169107101e901d401c01010b01002203825414400c4c214a001c204030409480281c1e82c2c101100c06000d41c00d401884040c4045400c040852003a258040c0305021f280c0c013030034650554650b50b0700c640c2e840c1506003c88080554a080c05004581c3c3c002e141d1651140c2410490240c803407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 991658012 1250 991656762 991656773
    0x302040f060b1611030a02091b0906043002100e221409011407110a0501050108010f0b0f0a090e1002030124020c030607080718080c0a1a0d02070303060806090a 70
    0x1011500d18806e4100c4032110016860b0400e4060740000c10301082e0300f11400c2c0d44c04035403140c001c003043d043e000310003ca00030a07031202d041041c803071080500300d01095021214110728800203d2403002900b008003202c50003c400d001380c842801101c40105070031006c490424035000614801a004110107403910f401200a98108071207035003000400d00280801600424800c0c2502c0e0040c3c0190204002e003261103980110600402d111981d001e0028005969100f204074080c140303043d40b5254007031611280b00c0d42490909002e048150f000340c040b4118a1400702034100800d5921101c6455004001c001401c001d10f130b1000718042c0c2081c030b004514008100202c1b80d07091038418228815035005c9140b1002c96a00040d0181d4404198a000b6000e40e60701030301128060780030186114200c1d0700c1080464480b402003401c83c8032090940310407195507990390304400024445103d03500b0040f0308005020780010340c0c1e001041d0f424001e05000c113501e6602c45032149025411140429250000b500c000200308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 991659262 1250 991658012 991658033
    0x31b050f09150d030c0212010509060702011e1104120f330902281d01050a03080903280203010b03030c030d09023001051006090302040f060b16 63
    0xca0940d6000c000746800209111400a0b48007a1071181181d07640d510100b505c110312000381d083e40a00340c10340c2c140e00200040c1c080d10003922100d04a002c1d02c0d0000d210184144541c1c91640080b00d034010480000194000003820128480f03178000b0300410021584125110740c0884461081d60726460503007150400460b900d580305604a1650804c02c82804c0d141240300002040003014580000c49441d1031002549454100c2e01351166207118544010040d143c0d036905004540680800800d00904800600e004001c2405000c3d0b1021071400c1c20b0010a100f20007800103414080c08484840f506428610ba00e584c00b1020301c0d5200740c41171241c80440c1020b00410140b6a4164015407c01c58844642c43d124042c4580c940a00c56403805410259980c0b000030300320000280d00040003814003548800c41102d401002e6404641c208004109460301002c00002151110b40d00c00341c003a4250750130080909049418000340980b502008500c0c8085817000744140817480c0402e0503c0d410301c3c03606107481c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 991660512 1250 991659262 991659289
    0x12030c0f151308180a0e0c07150504020d0305030a1103100602160807141c060504032a23070f05011101060302180928060501051c120504031b05 63
    0x104603040b04400181e445810b0724051307203021400707105562a5102040c00341c01c0e241d0081c1c0c1507020443c28483d07a0b83c56000285030740c83c06004010f4405084c440307120103807542614000c1d0800c41038024100401d100d50003458000c0c43e541000700307004685801d0340003036403c00d0360114032010380540c007000f100350104002c015041405e00403d14030351805c0c013880e032100614442e09548001150007078074030341d480b10b40b0420022010450b00c0107481c201d0800c40c00624044a049010800083c88034180c0f020002c0741c054018010b56161008114580e116000e1003201148240c8103280030b18091032134902448076201800011240c20540b5141c0f10004101400109070b106180c0d2410000703102580f18040c6608840c20a15842c0a844d110000701510b8400300c102e0250151003602c100c2d403c3d0515200210400c00d010b410280220b0362541c0030400c1680c4804525201070402400d448005140382510042d50030041c1841810325590b40c64101c41000d036001c5d00e040b400602801403103e441c1120202c0c228 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 991661762 1250 991660512 991660531
    0xc2514041505011d03010204030614060306010e150d0618020a15050906180319020307060f050306040504020f30030306100c150f0c03050610090512030c0f15 69
    0x103540c00c06a5801800c03000780540383c100318551000300b5008083e4000001521400760086564517504e04080008162603420701c0340d0708040304080340c99407900145c0345058480d1a0040011070301c444d0761151140c6032021400703403c094000390b250b001c1038942c0b01d141843c580340ea40c3c2203c050942c0c410840401e60b88d81010b008140f001c0901c840060b23001e0305640065005492880c0e8130101105446030501211044640c54450180c50b2484400b0a840c0000c81c0c52003501201d038000e440308030a582110170742d000c0308001501032000490704d280175008140c02038006000302c3c2c2c498003900045400412a05904d04011514044910702110001c0070a0884800e0740c018601b9420800b000521615180c1d40c6001006441c801020a100e4400000102c18100002c100b104208061a000c05400c040d9068030220740fa02000461501b852105070000d803509654041c0164204000c0210344a201035074080c01784000d1001004001e41000f01d403001e40c40040040c00d500042c040d00045240c1c00031302c079086 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 991663012 1250 991661762 991661771
    0xc0b06091608060310020c07060e06090d110d08030a02210103111002070b030a0c020d0201050f0a1a0d0503040f0b040e0412022406030d11120c251404 66
    0x1d410440700402026001c49203451a1141c5401c0c0029240c482c10041c40038040c2e2000a0360840740d40c001400100b05c4240781c0381c0d40480089001041118020060141e030046400594080090445086881403e0009001419403105515060115081140d20040d040d46c0010140e002814403200000116440d000103400341d0304550354450014050300405014140014900c2c001034000d008400140c56909105904c070701e00380b1190005416505d140344058001c00c2d805644251040c0103462107580e00400400c0e85480e054500790041401007500203054000c14000c6559070384005004031524001d400a40d01e0f0390402d4a10b2030b10030980d074007011110700100420440d00019100681d8402e411402ca2030fa0409550020790410007078110400c3c0311408114880381c0014100c020714060030040c0d041310000084130100340d802542e20395070f8046c03651181d2070004907441007100410b811080310050341c5851241e070400c078800007640000200703500b510b00000d000c015105040740c000041c00320f40901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 991664262 1250 991663012 991663021
    0x3021b03040f090506180c1902010506090103140c0a1d01060807120f060b030f0a0e0309061c06030b0a05040201020c0108060105090f210f01060503010204031e0309090603030c0b0609 80
    0x80d07408810f12804400c580c4900001c0c5082e9100704030007400702007003009000c540c600030780500103590046510b101e0300e880c850110205d043c0305100c3c0610610740600012a1a400c1d92501582e004980c151955584121120440c20b0b84861001000a103c0100700c20341540030b001011440c010140c0001081101d1541040132041d030080c1c6401e4450034010b0001a00310001d0043c2c1d000c0c010580021400600001c01c2c0500480418400c0d40b081301a10300810543d0341c0e580045490b803055020956001c10180402c10786040c220703440d10b0f864080328800241c101c2c4c2d03d03510500d074804121071030311900395907004110039941c040c400c0c091078141c00d29251780079181c007a0019100c0c3c01245d2003203000303000349510030002e600c8070b51002d002502d1070b46180301074800030044603944024142102c46507508100c00011a41014029035003030fa681f141d8a013100ca0590302c80c40084541040c020b404000e06018001111005882200050750090765400c00090072810820785044029150710f01400c1c0c401d0400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 991665512 1250 991664262 991664279
    0x40f0836030319111501030b04060e0609120f0d0606050d111215040b0312041a03040f0803070c150507030c090803030a021b010c0e1302040b0a08090a0c0603021b0304 73
    0x1122610001c0c01c200138070544940340680782c040240c4a40a88800400000c030130b0059110045218521618007072140341c840d1380d030310380c2c44d21070540d01070072260302c020450b0070032141d1607015200404180b501c43e814011000010b409556441e071280000c90400148a0310160082c02901d41c4681d000300018a03041e40e80c0c030046501c000c018000c07007101011440d01c1207207031380d241c0000e884844000c00300c032000100c080d100c0c0700b503a015115880012564240b8611036894030415a84581e801001d084000c0c1c40c15259100c0b26840284100c0c20003002401010000b0301d50710488000c4d0144000c00115441d09590240444041171203102c18008003030801c0054420000440344d100250007405a00d81c0441803507042081d0030075500e01055400c00f500320540e550300c500000042503048600d05032040c00200e40310100e03c524001c1c1002c100040280401660180c02c0443e00701075030200312001c4010035210383d41c84041941000e00002d40004821714001d055609000c3d13044011005186802d1620054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 991666762 1250 991665512 991665547
    0x3060a0501030f140709080705010207050303070f020a0305070f06110c0d03050a09051f1b0305070f03110105090f010b060f0322050a030f030507080f040f08360303 72
    0x8141c1059141e085050711038416400c40b00c1e1520002d0244841d5060000018082015a02030f1309054401c203900002d4640c40001c07001c0c111200600518034221143d00c40c1281c220007500240d030001840e080010000d5010810100108402240500c46506018008004a460140111039079101d081034040558490600030061541400c10b55030b90040b0a1007078071910420380c0000e5100744210f03252012500b04140010419115941340f18083c11080c558826440b040d5001a00007401440a540001c00400d01001914040d041c90b9045402301541c40d400e44104440c1180b07030340c020a440c08061075003400398034683d440c00c942d202c4c10500d521141c501140401080c850203004c0398064a00d07081450700383c0307080054001040c0d4421030050708000c0c08040e8000d035028000785c82c180015800c2c3d0300c542e072400d00070401c54030074240315282ca44a0081084c40d0360801d43c0c4c01502081545040513054521441c402041a00801710040c0d10040f1041c2c0c500e07695015009401c10000a803001c1c481509 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 991668012 1250 991666762 991666769
    0x306030b0601032d06090605010f090b030a02041a13060801051008100506131545080705090a0204030c0b0c071a0d1505130b040b090103121403060a 65
    0x80001306050050702130001c011115240d058030407601d0300500b060380c0c0c4a030840300680740c1d5650107003c1c1640d90310045412a0501c4200380c0018203d010911212150100460700201c40c0e100241c14140c9801c17802a240700009921140e817003002802c640d2603c003240c05c000003441e00e82810b840640c5454013144036030f10b0f07a03074940c0208806900000ca03100f882807040c0c40500400703000a521004204a0f03038200782d0f001d0150346400c41065800108036441882e41d0000e1035005200120204004420314071480825400103c0d442003e10003640304c410b207404040007c20581005040781880d00b410b1090703804000d01400c3e01d0900400060000c24034410118089542e8401e01e603903503001401ea0f650901d240d5030401c0103000c01c2803144e200c1ca00c50132070140c8405030b45900b0070050045060244880c055103841a41e4202d01103540e0055505202c1d8001c1085501c0584003041750400100003c000d103000f40c004452551400021b85201540003d0181038410310391102c920f581002170000342d02c00064130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 991669262 1250 991668012 991668017
    0x411091816050d14131703060609060307030f0f05070906030207081813110405040513110f060d0501080a0506060904200d0816030f180302060702060403050f0a02030105070306030b0601 81
    0x604003c401e071441c2d024250103025040030b904582058000390241310205081605c540304544070700a42c14140608407805a00014500e0386440d485405009081d0070003400c00d0140340e600c0020081007883c60044441552958030002610f1500c954090f00c900318940008080501c140201c5000901c141d084502e500b4482e03c1c0c4003420703480d200002c0d0b8a17028255909010505041c3c9a809248140c1d001d442a80c4086400740f0050361008002c03600d41440802c0503194402c4031502d0000340c2401c4d20756000490001c0d106510380510300300d08400380c1e0320aa02c481c00680c00540c180003030100501900c1e4106000f181c50340c2450505880d486108035545138076902561100507000017a603143c03c40c0d2000958008035172038031200740b4190788136000906802a40880c0050444042c0c0c540b0440c0c1038001000c0302c80311005001d043d5028045160070a65003260014004c00c03002c07001c907108000242c00200d0740b0004142171f100620605080d60000b400e0f100034581000002c0c40014410511554172040c00e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 991670512 1250 991669262 991669267
    0x10c020f0f1b0f06160605090c010e010f11010623100c0f030809031312030809161202062101060306080706120507171005030708160320041109181605 66
    0x80000880c83e00c90b6008510170700800e40400310130000c1c95000103119004d0711003905c1c952030f0188015901c41a400c502d890004100c0d10707842403014041d02d000c440300302e00701000007511a2034118051820344090384202c82034a01150391301442ca4a02c00c1f104500d5400c0c64064108070160750781c0c3d00c00c03400c4220010107100c0c9100004100520810588140e81c06614020340a550340709030517034000e841c00c0030a4000484550001c0c901c60000245840400c418588104c02c252809100400b00c030118002287d001008000c0043c11445000081d4201e0220f80d170031b441c407540f40c100c0141c2103800300d501052454014820405c5580d0b04524076060200c0240004585669007410889501140340801c010b02c1815400f0b20007003844000c541002e1ba5415011540250307150b00100c0da03281e051074045001c1910500e0107000181541c0390f030541074101c0b0f003103c0c454210b41c0030002c0c0990b1400c20003c00000c0d00402d1038002807030030390309480e100201820b100100b4185150400d000c00c14050240c010300000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 991671762 1250 991670512 991670539
    0x5010f2d15060210050108281e0c080105060103151e0506040902031807060c0816060f0c021e0a080a0216080a0c060507050c091902030f070314010609031b08010c020f0f1b 75
    0x25003071070701801380010141d2704002442c090b41e01e61024000d00403258640300004506502a200b00c0354904014445920503500d003014000c400e031442c0c202d500c9002c0e51000000303110340f6500013034005006014009a140d162190071f08036103e003801c6a0358030943c080e603c1000907981000712440d0854025100541d1684401071181800009030001095035241110182c0d4108036603025107450903480d82a502600741c2c86a40004032082183e423450150440031010340025030640040003408420f00507030300d01c4040e000b8108074528442d88003903116000705000201301729107005d1483c060109410240c2c145003298456a41d1105081d003114040d40030f0030046905034211320100302001c40300341c90031f40d640c1c03403e0103004068000c20385a8001183c10403c46008246441400605a501c0d6a4802807141c3c43c5480e1031514045050078003d04044d0300740e010900f40070a0085401d00c1c019900244054903040c44c030a4501910050401c080e6044184201c03014400c099441100e800116035200800e4113 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 991673012 1250 991671762 991671773
    0x90f0f150607030c03021b03030315010e030a0b07020607051216030f0f150b03060105070609020103022701081501022e0903090305010f2d1506021005010828 69
    0x51040840e501c000041070100400d0b51000d05801024070950079070360303c4041c8000340034400110380540355268005100240d0104036020301000324904c1454802c255540b030750042402c01d03c1004042c0c0b0420f4018080048550b010002c468120074146443c501c0d00d0541610360400d10702c0a00b001c0a141c4c0d082a4616481d4400c0e0048001d40710389150810003c880e29070440300400b440100c0000d8550140c030001031003200700c5c041d030340b19010603180c41b4580801e40d518800201a2114100c0c140340d801d0054150303081c03420034004004464064a49440980c80d80007600c80740004005c06007000c0c0e070f100d045002c1d0340d0100c4d038000862202079029403e106c109000d1582001001081003110340f800002400707242d441155203044a014030001c122410b01d03480120140c60000c0500c80005403012034440385070070101c0c0b040da0340c01c644d284000350b034003d0303c1240381a54061307912001c0145c0c40101201c29681d80c900c111070041080200804804e0b009a43c007082c00141100601502882c12802809001c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 991674262 1250 991673012 991673041
    0x14131409031e18100c06111c1a090a02040e04030c03030b0d051906291002060103050d0e030c03072c10090213090e0102070b0135030d0e06010303020606090f0f 70
    0x1540610184000c40ca1445062103c0e048040c00101c012981c00c12003105460502c09e28144918224940c80327002c800d00d080c809207181c05004260741a070308100004105019401c2036010f14400d50710040001c0745810010309441209250501c074160051404000480000e454025070001b0006a00408514146600200241000030200b420000000c840c07409030700e020008040030454501e60000c0860700d007203075039005c00d0200510a0b0702c0000c1d0300b100070740200c84c40300e014030005048462403c1c0d00030100741070581035407200d0024000c9030030f458a804000810100f855518038801c0b901850201422074402020b44070301070003560b00095980510220141400c064801a48244610020b6041c0e80f8000c1d03210311401c4c0c0e14080c10300c0003c1410304030041c1021170700004880480c201203900041849003200b1035a1703240c02e80300402a808036001c407809210703414020b241c0030b0411589582006401e00c1c8008003064032034100501088140305841c00c81c2904403801c1d021041803640d0f0510b0860100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 991675512 1250 991674262 991674287
    0x20315041802040b031e0a0b0f040b070302071518021f0c0b0901022a0601090624090906140907030e1906090c1e0f14131409031e1810 59
    0x170302e5210071b02050001034a2440900c03481d48090b031030703581a620318030000040d10000d042c129100081981c00c5c0c0b085c4c02604190340240300c858000b005080c01340307044480c5440314690307900452503004198509007a0250307452200d0a10800109407281c3c00502550340300e0b0000b08810885d602041c6401d50035810b58a004034846100d0f080c0401c503001d13004c02d01802d014441c0962040c500042443c5809000e004221401c0c090389403507512100c200302d512509440d82c510104a04070100080c041500d0043c0c200034841c261040811010078010b0040d1100020b03c40428141044070030804801c0000e02211844e402002c042d5184100f89040e001521078090080c14000c9050400b165102001c20910b20301c5040300d070302c040782550724501c3c1380e400300c014031403415000102c60401001d410311400624160541e01d00000e010803000d00a916070802c1a6145032041d44045400c00d101400360f4100d1491112040c1c0040c1014108442010386030144010507004144101621141074003495110444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 991676762 1250 991675512 991675543
    0x5010207050601080111210718091d060c04030b0c0c0307030f02100911150405090103230109110d020f09040b060f06030402090a0e030c0d03020315041802040b03 71
    0xa03880340d800c04540c1c40c2800c0c0941c903959441d0444910000803800100c035116246070031070800d2120340d965903600c0118010207220600c140180c45414101901b0040805420440030010340307000414034000d40101c580310000a81da0001003407200013442c21040d2800c880d40481c03440c445070384104003204280a0900180d009100c007156240815800c00e004c00310b42c0e000e5030b0071149c07211001840d10080e2003650390042d11f11088024420064100a040c0302d1250030941c010519266964012444030442684180e6021086112080c828081c1076404458020420002d00505146442d00a1010216005180319041c5184504115150034032000030118004200d003540b40b4082c105a0f446e00c0d811104580700300754150686901e032400700141c034056074004e840000e05541d50b840e003000518244110b80c08030301c0207104d400c0b400b007000c1240e01c105c00f22a0740d0168403030425000c1004c0305001490500e11403030801e9203d02c85800110a45a020360b01103e000c20300c40800c2001c00c0c200f9412a180c81d01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 991678012 1250 991676762 991676767
    0x1090f060e0114090f060313022101050c04270908030f1501020106063612050c0f0d030f0302090406030605010302100503060105041e05040516080a0e03120c0403050102 74
    0x60080c0c010740c0d014240e45003a02c9100380308030784071280030f05071007400c0039140d010f5003080c03030101503040c0032018513448040d501134903a400314540c0006035286141e88403101441c1c0b111280b07550300c0f1400e0041b5600048520071050820303003404e00c03030314810500c40d420441d1f8603c4080200c518182d2500b0a406c07241e04454959560b0030840443d04405a040302e1070340c425020134240740c285501c144a006d0440d55180d5980840e28100400c4a54003101400f612900184905030700d900180381d003600303800030302d10180b03c44200714840ca0f25a04010721821850321542d58441500507179200c0b66500c040c0e6940c03503e4070700d12404a4040070f600900405003016007217490074002004010090f40700c241078074000c60721704001e00441941101d05210403514203001900c1844104031095030300703c0d04882480300107006511940c5510106007210011104071090300e0282c0301d61003540c1d8100c80c14035085210181c003030110441d2811510f0341c0c0e12840300007455251001d000262000e02d410140c80107140e00000a65 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 991679262 1250 991678012 991678019
    0x15010608061206011a0f070212030705150408040b210a0b010806041a090c040506031014030a050706050901020109060e0102040f06031505100318060e19050304050f01090f 75
    0x100300c20800c60706140102002080340c2030000700080d80604030f4088113440a007800222440f40c16542144110003120717801481800016a074210a40c98a00352160003962540c145048c414501000102e40c1a034800c44801070101107518003003200c09854400204079692604100b00344915031a160318403050380c05200c1804910000c5411420110ad02640c03220155150f00c0c041100311080040511f0f0b07180004481c451403400c0882c1c036a07070701510081c00d072803c0541d41c0010611940c02103c5c0300d070203500e0264040c01030340f8000c0811584040141d00a210b40d01c040d90791507585070001e00a40c2c0c1400f10115002100303038403d400041c120303603020005004481c003c0807035602030f4000e8051104410080031021442c54824400e4599921707802c0380130030000340f0f48024410024582a98407040544400c04c08004984100c50140764910078a00060005403403030400c1e090004c05441000084180302050f40401e1001007034809031030301100c1c200b0b4048660001038071082d0580e80b03c0c1010070742d40b0f0b4000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 991680512 1250 991679262 991679267
    0x204061b0f0605010611120301052b20090c090907111e07061e05120a110705100506271503070303030c090f1d0601050408030d020c010b01090e150102150106 69
    0x50101c0040c0c1d01f00c0c1c2e900003002d07503220031501003405000d410005501d030342c0a40048890381c010a1040c0c24228000c0d0f04040e1b1507003421107021000d042900e040b10140e070811800c00d18241e0b5404140000b4040c10b01200400003265104c0203080361003005106041124981402e00462311211551041d9003207044141d2441610b4561611550000c5904914041c2e40384403103003021400d002084e03170703000d203026030810050381c0b40c420241c032280140d95079945540708803440200030000b1900444c02060042e0600500e601598801419107001d445050b20140712500042001141c2420001c11145556110b0200701d6141004801c15585071003a06400414950554001c142002996503500201034554100d00d66402040c8268418505820044480c0c0140b0890b071541006051414624080c0d0b40c0244515540161b1070f55892180c2c0050403205500091098141c801800e08140b500c05107003010b02e031212000102000d50340f9001614500707840c0e100f030120f01c04e020301e000c454080d25611038000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 991681762 1250 991680512 991680527
    0xa0f0314010f090507061107120311010c0e150702030c0303070326060619091505040602011812080a020f0a110d140d0c0903020607050309130204061b0f06050106 71
    0x1184880d500c2e001ca800b007005042e000d8040c0e0780b03820000405101d03242213811110516402580c2d4102d02820601003040c2021020003c103107030007541c03948800a10121141c2c2180e00319504141030000d2a5004544e6851755001c480c00c1c407040b401c446031925000d0010038140300c41410625454000043d6600c10990400480c403840240c11811050000c038000589070950b0043d101c0c03075800001031040284c1e00c1e0303007000da90900ca0306a261a001455030f40000903c2c0c003083d046290040b40011800380100f640c2482203002c402d00841c9200303e0110503440f045e820880c08502c903c00c03c400140002e41f12003035501180c80b4007810402c42541d4050000740106841e220300e05001d101e0041002e4510a24441c1c5900d04450440022075031814141b80c01d4080100101041e110911548140000160307442d600901910343c002c07009141d82c5d40c9070000708050489041940719820b413041c003061098640c0164a0040303508146d080e04051700207820200722070207000d1401001c460400001241550f8030094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 991683012 1250 991681762 991681793
    0x3120c0f0f0e0907031d0c030a140a05070806191104050d0309030f0507030b0705070c0e100512030a0f020f0a020402070611030415110a3c0c050c011103180a0f03 71
    0x202d03161152600c04446444103070fa01d0010323038154400d19915003c00c166016810310500b0074800c80d0030700074039a52610300f40f802c10383c0181c1c4e56422078000c100040c0e495070144800f882413004c0802060840c800607a08900a5018060050010003254400c150198241c0c101568000755801011125854065603950450004603400b9441a02013100c080c080c005541d100c690004031020035a04100380d0351040c240092001d00c80e500b01c8500003481e515001825880306511b10091030352200c184101806c080303c0c054030705045502c41c0568100742000860100c0d82c10340d0403107001d6034550b039900303003000501800f84003464800000428041008081c0780c800e80302c22800b00041c00541051004410580100c0004401003484101c0e84203e0fa00901025800c410790307040441c45240160307140c407240c0000b1108078804a84403206020501008008207044038101f407809001c00c10f030b11502c02c0d807607006003d5401e030043d4119810130050380c3c50110702c4019003102050070121550360708010601c90541d03c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 991684262 1250 991683012 991683041
    0x4060c170a020a0f0903030516081b010f1d03040e0603010914010203040b150307031707120c03081f09021806030a090b150d02060c031905040303120c0f0f0e090703 72
    0x152944071340d4001d0724403408407a01516040c0c18000c03541c0c600c50b840000c0001c1220ba4880030890035403813081c4c41805c1e5640c00f5110000084001000020304202ea8280400012a5030304c040c00f0b420780c03d000804c98040c4d81042d24803050b16103d10021078098611010700400104012207900c2d18098158065841640140784201c166114810344650f480416a41d0a07090b802001d81440070070203124007468030310070340d00300103282001940711004942ca4a20f9507000184240302e121040c113511460b00f5400041c0c0c4155420f03800c561951812070002ca030301c40c850361940c000c625100396041c00b0f500481100000741405a03a032800714120030092810b01c03030031102185040085400a400c0344812000e40e180078040717075070319000d80c0c0030000e50780c100c074080004c10310042104011020425124040410482d228161100c0c01c514000d45010011180381030034030320707080d188040d05510000c0c030300075079a560900b03480c01e540a50045503403811043e0440d41040241c024000240d078580d0202010f0200c86 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 991685512 1250 991684262 991684277
    0x9031219060b0f03040b10230303040b040929010818190302010b0103110c0a0b0423010c03050a050603060c09012a0c05062b0e06070e0301060501090303050304060c170a020a 76
    0x1f10310350394044100780159913207054a0710282220036010800c11a800800500701c6e802e00b680e0740c200c0202c951041e042680303444d0300d17400031451500703100d01c0801002c0401c0643c03000c0110340324002402030000824070740409546030000c5d0301400c41402500b40885152130070700898115414081c0c0600300465030750303002130300e410500c01d01603040409442901e040e400141000c0c040903150001c28403006001a1007602c1d1024080c4c4120140c0d034550500e0508040010a85200060020341100c60080105880c50f0030203080000559000c070303045901070900d103021a226040e840040f2542100005144509011140301c503418004920321060310390301c24603601000030b4440c0203100b038600900070311840d076168ac5180c1c425890301e1000344d4003901900711800215221006513180c90110240c51100c08038158941300012401d082c02050060700c42070030512900c5203555801002031000a201038000780e541c00c0103007180f0384160003680305021070742c480b10700340d003080000d80d0003e51201d0703c8030010404c20b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 991686762 1250 991685512 991685521
    0x1090b06010f111b0f0307170610050d061a06070506010315060b030a0504020112091104050f01120b09030403122c09040807050a121709031219060b0f03040b 69
    0xf40e03505541002850064900c4482a64903040040001c000340c43c0e01004480d0003060310f880c2001038400801c114a44070044144030402c19090400161407800703c110041c40a010310b86030303014421204d079440720b030005062040814045e0000b0503400c8040d84900c0c0010f42c801409000500300d07043e00e024410b050508010040d0880c125520744c8940070315110b0070300001d1700441423a440681d01038010b0511450120740c1102c500111080383c8403c5904102c42400600203080621070316070721244010160105504050301c8090001e0b001c00c00501c1d400d26072000520350482407081d940210b074800c03502400c04601c2400500203002411002c04405101005c040460380030503031404c121440600b402080740c945880714030791940808000c1d0b4180c810484a030300003c41e81080f444020000360390f44021183e4040e050464120301900b414010303842803002c81c41007000d00c4541600b140f010480c0210703800e00c2643da18090882d540c01885400c0010480c0c9240d0b418000040d44910720170080001710750358 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 991688012 1250 991686762 991686767
    0x4060e040506091602030c030f2a0606061b03030106050a08071707080405012405041505030607030203100906030f0b0603010507080115030b09040609060605091b0f070501090b06010f 80
    0x400c5454a0f03001c004000822080d94000499070480c28903841641d103040d061901062855000e03040348180c4490002c0c500941400c941c00e00c001d07055102400e91040c15004160319550180648030074071920002580c0102021484011519603200b4819244c4942e542d02010b0065081081183c010035443d100144407a0701c100342003500010503a141200948a6500845e1704150040007154199030300d1948000e02c41d601d0a07541043c40110041c100900d0900e030a110a54036a040344400c0a2851001403025540c0402c0b0241d00080e00d140040e202e40da000d09500050400d90301090800f403030154044180000c8016100c0800e0240511501c2500c8850034103003210340894944002450380c1005004241c0c90103d0464003e00b540b9000ca15a425035002480e050300a880031a43d00e5030314030b814000c20406020f400010441280c404510385003401c070000c924030b44088907030300c2d03003c00166441040c16044280c418154100c4000c120141552400d541c1051054070350741d000c1a80c0110b203400a03407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 991689262 1250 991688012 991688021
    0x3031b03090a051f050906120a0c0906021f020a0903390e0402210f0304090e030a1d032109032a0402030a0b031207030f0906090506070c03020901080304060e04 70
    0x11a2403425140d044c040d18048405802110180744c1c0070600700102032807004e61310b26190240200001c00106d2001c00c54010f45810344540c08441550031401280800c404402d00c00300411401346009030746d800150b48200c0f0a810580c01c000c0081500710103018541c0e00c401101030400640d401c8102e0070a159403610f1618003340d1003003100f0300c01075200160040c103041004600408124052601c541509190b460034a40f0919000f5403e0b800031508000c1581310b03000700800c0041d980e020398030b0840c485000401035940003000303882420100b40c6000701c0d51010003800850108800d20350303001c500201160b1000380e10880c1c11522034450316840c89500070756250f080020085000010420303040590a000103074000515800e080d07980c8103400a0503440c18000040080580b8498680d00e2038140f80140220360000303101e104101c0c1000080c001e60b90028014420340c0c0c0215040750300d410003458141c20003005a04000c3d0400d8182000207410300000000d002620210788072044c80350b806000340000c60307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 991690512 1250 991689262 991689289
    0x7110607020a02061c0902031209040f3b06150f0f100e150c06040b010e2701020c0a060c020708191209090c1d030d020d0e03031b03090a05 61
    0x10000300000e09404900702e418517803034102100c000c112250a9000a4245200380740c0740c02e00442c0c0041c2c076009c286014410300592046d128010010480866200101c1441c02c000d02c4183c00244105008030300d010765200001d0304000000c44401d8a80f500c0701068501110f068a03000380f41c102e82010081c981042d4000600e04090507528000300e000b1411254940900d54891304a8002038140c030108480c6030003400103452000090241c0e0a05242c4100314010582c064000d40c519501404000600400c5680f604446943c6030b140da144c203031505900a105e40c526200c010310030000e0600821500e030300810b81560007034081d680c116a075090916158600c7e0803101d11030204003021500051160b80c0d1443c0c45c40c031185030049a4989602000d02150781031079554011428501c069030320308240703e030089a9901c0075000303400440c0b05114065901c3c424521098107003c40040c0c6903042c4e443c00c10540c0c901c4000720742803940403940710082580300d0b4003111040d809001d0b0701202007141e0600700102441c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 991691762 1250 991690512 991690519
    0x60403170a0605060403050a140f150408091f08100b0915092d15120901180305030901050c0309280f120e1f0309050708030307110607020a02 62
    0x1030030101001450032000030040607555555940114168403110080d0000d148503200030118001c4504280005002c04400b110345980040e40040c048500803174401111500d0301c80d00a2651154a04402039008401c072003508000c42650302001c0302c1405056038452080c3e51030341c1c192901d452090700681e1007140210300c0404000c100354211420410061a00e2001c541c10183c2000c0d1140e0003d240d150034201411101c443c01c500089419020b040c0300540a0320445006c1000c00464240354000c1c02111440c800f9441c003c40001c9590f042034011804540c944192131102c0681850041e2240d04103440c0340746190318010000b41c11114400c116402682c6170720041054082c001c034110441d030288055120850200a041c60008007016000300b0040c0c0b00e5405000c4805c071080700104080038210247c1d1056030038be000d0211041400600300d03581e180b1403401150081d42c07030410300d00e0f00b0020760080e807442c8800001c00240a6000c0311b004030804170841076498646401e03d0480e40c40141e00e002950 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 991693012 1250 991691762 991691777
    0x1818061503063102032a0909040311070306022a0c0906060706020d1a270c0a05040e0a020307021606210902031015061706042307020c0f03060403 64
    0x40760100403082402c0e00f07280580c4454001c0c4000000081e40c00c00d80e890f00e030b2403810034059802460300c403102003803031000c83c1002070030000d0304c4000075000b1001500150a000b014240030200d0142408038002854105805660b81c0c0c800e4943c0400e080c86088400d2074440b540c2c7c0d41003100c030401146070000b01a00500403442a102c0d0301c1000180d034000e0f8012a2515030812409540b50541d00400d0341800c0b0080c00c075120440d02c03030306000c05942c6a55951168103000443d084d0320640c0b0180450300441504011601d07512000e406684a109039080380071485881c1c003c001c00e00310143c00540c480c0c2419400c1e1303200c2249032005c540d00c1c1500e500601005c14502c00130b0748005032490781a504e507035410020106840c80c0ca034010030302305042001c80c40c20030350308c1d4a043d1160055400c40c80004011a03d06040000f4120400b11041840549014403840d110050040003800d411a18138080050100465072070810240107952850300082c064040d07012605541581d26020401c544100d402d03403100e41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 991694262 1250 991693012 991693039
    0xf0506030a031b05190b15011202090411040e01140d3f020f0c01050a0e04091b12050105160c03030c1e05030108010e010204030f08181806150306 64
    0x480801e00b107031488003800d0340f206200700400c40401690302c0b28004103801c00c0e85a41c003810400aa44001031180b111900110481c1d102c0d41d13030001c4144103181c900b020040c1c0302c2400700001000b4110b03c030b91033418404040340210b12001394010450480e1130305a05100d078007100d40c1c103100c20b1000c15000540025641640d9a0503415038500190100f06d2844150f20440ca5401704c0b1401c3c1d181c84900400140d0005401d1554000c041021469201c0e09003001070804050107001004c2c01165262640155190b2a502d4200080302c0c442080320034070f0030394059040d91220b0b461103001401e000b0603107d40d0709080c00300b0811f00d000004401000f00c95500c510104036252403d501a0007426075180820811080d14461070020010710341000030a030361615582d500d03084103e401d4030301c41110404544d104110404c002100e00840c031408503440511a600e520401064848900d81c003000c468000e8000410342048070b0201140c54460042110950070211409130026034600044400c2c0e41c21010100255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 991695512 1250 991694262 991694267
    0x30c190902091503010b03091e030901051e0f0705011401030f0b060a080f010b0a05090c07031103210106020607031b112503030215090d03020702010203121006030f0506030a03 77
    0x10b0160b03501c003038140e600700d002124154110303031310907404540100008018090809428454246c00034800e00c003544400042c0d9181315224882c0440c20b905010001a00c608103168642000402e03003c0c0c001800d49950100074004000c0d40002c108850b2546003100015044d001e42e4482070503241c10402d40724050b00d660ba241c03983c800010f491541c1c01009050001800c1e482006403403c0600c2942c0003054440310001440001c2410303422040c070404414080003100c03000002038802c0c0d1901403030a0328200c1c4800b5211400d42c403a81000c0780d09101484945c0030f80c69200640301d812a50035508131101640e64650483c05c48000c540201d2612142e45620190b40e031003401e90040840e101c40c242c4440d6849060000403040341e1105d44840040c3e68a000c0040c150180000c1d50390700008414200c1c81c0c9041816940c403a40c0c201e083c0e0b014581d000c502c403c156442003041d120601d02c01c6030409070501300f88000301310fa0941442090000303400d01154a212080798002d040c0907000290052247d11202d640a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 991696762 1250 991695512 991695517
    0x801080d0c030c0812010b0d0f02040509060d020a0314010507090503010b0a171005010e0129091c120905030706090b040509151918060e070f030623030c190902 70
    0x44d0b40e04070080c09001c1d01100076104160003046550719156451000c00ca500b000e40c2c4060041c442801e03c140300420a40e1202034440398482011502c142e1010796902c00075107503641070340014101d020084900344c0e071688150302840c000e9042da02c0c0d80c8150307a0380310105802d0301d00006410340c00c002110006c10894000c8401d115804111809896041480c50f298808680090307006072190302600004200304004410b1000c074080c140c082d0110700c88900780c0130503064840c1d10302c1c0d83c0c010f0b80c20190300c0010440045030341d061154000d144d01e602d011800c01c01000c51999018a6205e8040c4c0100041c0440c0200302c1002195248102d05060516110410441c40d00091102d40e140b900080c01a22a0f55054140c010b0b00c4405422890031500b4407842c10703090210215100c821625090091005512480c61203900c491686441001c6400030f41d01140a0005680440701e807807800d82c8803641d00c250510350a18500d40a40480ea031004c121010000f00403801d058103080c8441da001d0601c40030149400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 991698012 1250 991696762 991696787
    0x15030f0201031d030a050904061a190509061b121e0903010603050706080a060b270f0909070303111605100219080a080609160509010315060f0801080d0c03 68
    0x81c2849552904500703410355200f41c03917a1001540008000540749454840e14010744404680e4045803800a894000700d8852240804034101c10716074a01d0456110381c0454003c00c00c00b07801e040d15002c2078010066061240305400805002e030400c80d080b000031324000d46500c00340c3d0280c80d0503001002c0c6030a071142d522403864a50155240d04011011441c1000700703034020080790303483d45a0b80c0b41c42070981040b9620f503004103542070f00810154418540d0390980541841d102d404010107140e1400000303d215402c1407010340c000055200704000c1140219903102100d02075102d895140f11000031107500c0f0040e010b101080c561444005002a00f000c10000310601010300449a85502881e1035900c1745070316540440d00154002501e0380b02a80c002c500b42c1c0c03c90707001e4520600d103003401c600c0340ca07401c6181e00b080010031a0108052080e41c1c825001501c41502e110000205213488205c0140007941101022000c00e01010002407896000101003949215a80d1440403080544d5000c0f20b000085c102c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 991699262 1250 991698012 991698041
    0x51308180109120f0b010b071113150f05040b12030a031d0303090705011e120c090b040f0317030f04110111030a0807030605030304060e0d050a140f0115030f020103 72
    0x102d021a0b542c42c0c3c3ca0001128a01900110242041520301050404030517080b60001c05018444030001a0b003441d40c080082c20221800c902260542c048c0c40c000344058403070300b00c0d1544144400160000c1d40702d0036001352081580c0502c01c40d06840c0502c1444604144400324070f84c810400e000e84a403280c2c2c84030565004400140712440040450383c0d20390f808c25548100145c101c2d103801c01140d80c100203e85031048852200c0c5075091411074014105601040020184a455140650210703200705680300140400f1691aa11580c035241410510344281c0011140c0a1031102200d40c60501081643e11070104a1102c0a4a0391280e0f640f030343e582c601c1c0d03821605100814183d100810310910140800c400c15a6805c0e030945000074004054819943c171882c00b030f81040006001281d4802140200d034001510025104510380c6091481d009440b032002d0242c0c0c118103001910b002002c11070f00c24003c900e00c02800620301510508a9981e4207120040130488101808001075009030842c000211455 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 991700512 1250 991699262 991699277
    0x9040216031707170f270312060a271401031101091a09041e140117060106080106080703060e090a0b3702040504020d020d0513081801 59
    0x610801180c10000300224007140d00028510b01c0c828040072580c0c2e1040032460300142450032007042180365072024082191500380700380001c020807078521803802c600d14152003c06070080c03498042030326034200c0c92154280180c0200866201c0c0780120b545800d90300380c00240300441c2ea1802c1554009132007114000c100303585541c00744a0405030584810300a60056107420103c403a450001440c0348220f400c41044051241c1644c14010311580665012840580c1c0028192074456614403d0b130a40741c0030148000d04207880d4100910b01510181d040718444e0815035031034215224175a8584200340601800a01100010001944030b0445690440001e040020700366842d04040e12418100b1511a001e0358082d16800c020040e42d0254142d002c107040b08840082110300002c1c245956a804c0240c0d1004071180e20410720142544c101e4000340002042150359a220079107603000380d040480b1440c0e07030503d0200007c80140b0100003000e081903102c0b000c5441c05184245080e10191001107050401c20034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 991701762 1250 991700512 991700527
    0x510030f0f050f1f050d02120601030c170706020604171c0b010e060909010b0a022a010908011509020f09060424020a0f0602030403050d020d0b030f010b060906090402 73
    0x268441c080454400071030100321072034680300a80702c2c0400500b208034007880041319180d80c0442514118240d4008483c03491605015000003514041c02042c800c5441c09120000070401001d85900c02c202e9030003020503a42001e82c1070711030f5140d070200d11501c40560404400180010361801c4041c141c0301004074203038204113083c40305031007140040c4040d4003140da603944901038540e0424102825403c0807166540b420070680c0104018172418030441d4110b80000c585040042d00038813001c95001011000c1031141150b03c0c20811b5403945d1070303580e00e001c200440703000700b050b8906006000303040403851100d07103036585001040002540b1080b859200d203202444441c04d550340340c0000708001d1012640d88200d41821001c4103000f96090480002594403040c0e080000a18414030060079a07048a401a107960711420103440d24860402c0b20380d407107440000e400700700f62170b07542c4204450f001c00d804031940c48003080441d500f00c800d011085640301c2c2c414040c2c0d00e214903200740240a2800064005800e2041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 991703012 1250 991701762 991701791
    0xb2a07050f07140a0e07020f030a0206151005190e0d05030711031507050708090d1203110a140c070923060109050d2616030e090105010504051003 64
    0x42400c4805401a03001c010841d0307410031141001c0c00030102c25409a00d0150b0009510f480188240460551400b002a03070b094000e00a00c03e6880c20001560360b26440300c50025120310007200c0790040820321b010524994100030001107031120075521583d2034100c2c18511480520704410b605800c000c03c1072001ca595440e40700300180b840388034100850301c455192500211010182e4480b80c0a9841107445854682c0b407001120b0b000304840c10a2543c0b19000c0c1042d885c0751244844c40c136041101d90000348108441141044004101954108802d10355000d03980d14a2054010400000794030320a000c00120090005010205000e4210b51344e0641e945401801e035103020212485504982c0c150801c110310ba044c000341c0c0302c182460506001c031300b4040081c0c066003482c036024016400e0130290605160340b41250801c903890303508901751642020740492010b07580b848011000680c1e0b10426600798280b042111f0b058880c140c407401e007001d040c041400441c00f00003545c1802c040d29540d42c1010004c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 991704262 1250 991703012 991703017
    0x309060c021828020414030a0803010e1504021305010807020d2015010e0103140d0503011208070209090610050a0f050405071404090c0905010c0f1403091c021504030b2a 74
    0x184034000160f00d880c1b40900c40f204202e01480002e000b500940c6c4681e00080c0c01104590650f540e445580c2c006031070716030400b1030700402d40074003940040c80084d09900c1140030180010448000340d80b180c00c940e0760180d04986800c0e46520712400710b0903007019100c1c1400400e1b1081c1c1c07010b010340c04481286a1b85030341820188400c0e40b1054816078524018002d00c590401e030524800c01c454000c041c1d00c42c0104005000d4441482021008101082c82c082045081c40450f450250010891415800c010544603200c1409503408480800c46107400205c504041903600f04031807451150b40c1001c0c0c238107018007003c1c10004103203400b088000d00306110462072400184c0041e00c04080c00049900c403841c409032959505401042c14440032400d1040000e026038030080c1c500b54064010703079901035105030281c654060703803048039800000b0305801e03200041100c00284280c3e000321032019107002e0031a160759840c41540409403140081c1320001d01c10080101c4507042252601d44458030030100307104842c581380c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 991705512 1250 991704262 991704331
    0x4030f020a350301150f140c010b0103050a060806040204020c0c0a0f0510030b090a110f0a0e1c0210050c070b04150206010803090618040f050c070309060c0218 70
    0x448109600302c81406912416204040050407458915410600f0304510401c80ea91400104490b161210621601c1125480c00c030b0200e20202540f201c000c0000603002e40b21a0700022300080c41c000c0060042c4003d40540c034101c840507070241c030407070301d854082c00082d5004810201e500e01c100081d0f4100c2d629645d46000007010411445140141407400304039101805407030620030142044583c03141e070347d280d8480c00d030003140761a0000f4007181d400c14003034210301503810103540440340828207844251700032104200081d1300300c03454081d10400440c20030b620b02c0c00420181d081460440400740c901d000d8802024590040021283e0320b558405041c05580c1c845d8008240d4515420059400c1c10380420a0394007400f819000f035814000b1003404902180281141443c3d16140c040c5028615183c69000c950582c02495040c0403c0c50f004850003000e43c4142d82c128001307900c140c0001f501d58811500c2c015100e1f070007410034412203c480f03030551070414090045c0000c6130403000304590500e0b010104071581c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 991706762 1250 991705512 991705553
    0x30c090901181b17090703050607031d0f0a0305160611270609040c12020c0102040312080c0306040c02030c010e101116061e1a090106031404030f020a 66
    0x554081070705502c180c1c0e0040301042010074583d03103c5403074030340c0040b110340400380c15000c0c0c00b40d03965a41c0082440c0c40c0a65001401a00521051000301503264101164204a0440449451f9402c2e001156501c030034a2800e09183c00076402200043d20910040113641e030100820185c070030007a03d035401114803100000140380700c000740382d0080c61380300c100007040e059499040843c40c006400101d80c4c075100d4420042e1083e0b90b94000841954000c1000da000c06581c1e4204549800c40314004034000c1d805408140e91a0102d0256031000920406c0745500c1203407503c12940c00c64a441c8140405004035a0b049010740c0010f1041c0c5498010902c1000300c1240814004c00000720180102d03012110b10001111252404000404802e90f1360b1098404a55201c0000030b011242651031400521844a80d842c0312801c0101c0c01602180f801e000c2c0031070402c01c07907103981166640e0728290219104000e0000220420000007008640514603490414803180181c07502c1d14415551105001a801142c442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 991708012 1250 991706762 991706789
    0xc080f0102090109081903031d1b152b0b1305060a0902160206210709030302010c210510120803040611130e10030602070809091b0a0302030c090901 65
    0x1c2d070f5a40400b00200400c14031000d04070b5070403000f0761001e6040030710300050249034480c449142c00a07613420100810850003816105525000441c0c0180c440194648034841c1141505450407003940000301e84800c13060415900740302001009800c203d2000b03000c00e80e000303a5030300d0010398036031a274500c1c03440c01c05c0e1005800500da203400350030410440241d8114106051040c0228003007124013028810030300343c04948464482c01d1440c0c814000d018034500c11219003da101c1401a0301e81c00c03c3e800c000b941e200c0d400034010407684150032101f04144140c0414810850300c45154a0040e95010700d4012034100d48010100da00c40e400d050245000c28000c46000c50000104020700c01c5901c10079802c806803400140ca0441040c2a41a071000b01d80944a2580f0441000c60395107421301510000442d03206034255258205410b1641541e0003404143c0d0040002c0f1000031004c4800c030820f1281c0c1101c00300d02e1030a005013240100c00a41004052840b144402c02000b030712a0343d00300e0858000d2800004428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 991709262 1250 991708012 991708027
    0x190c0e011e08010204061202071b15031406060307030507090510020709050c070807150207150603050c0a0509010915051c05150c07030507030309231204030812040c080f0102 76
    0x400088469001810a1348140000d0020561007860300c03002c580d0551f009070321210b080c10501e101044c1c03000450118051a040068042158070b1048000305e081c1d1402c00080303001c8450201c1120045035850360001d0b0030030004540343d000b6030281e5000a91340c82c1c480c215540b03c00110b40300d160401551409070f444600c041110aa05002d48c3d03901041c18507d00741409880c0e42c03680068090044020514281c120140c0a088032a506543d102e6811030304280740b01c202486007100800e11804191014011105208050b007040c04000040760f401404000050b8a07219040c4000c15104120780b4a00800d00c8000a00740d842d0302d20302c817000200980940c01c5518514042c2d1034049800e00800ca60205013042092001c422011380d2500c2c0e0b01401e0507903841c0302e54038084008050380040240320107025051111042d9020f0010785820030300104903400c9a101c0ba80c00449801980300003415100104130741c4110101721188a60000e02c5000d0381c140880d01c507200c19080034248400d20055039800304080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 991710512 1250 991709262 991709309
    0x51905070816170a020a05070c030f2010030e0f030f0d0c0804030c0206070f061416142205030d030e16152714040b0a0503190c0e01 58
    0xd03038440542c14082190f8900d0b1586003904280100151455680400c0a91400d401241114203040e40070700c81d19661922880c010fa1144042041030300c000ba000d085060000e01e10100560ba1880010419220780011060407005081f202c20540d0060154110464030100f0410261250803d0074400d41e4640c003409e0210002c8944d05c03549541006504000e02010a8004184202103501035030829134542d43c070b041c40c0203001c00300100240410b24040356401d41c004242030040c000e045d8210480b00303440c41400e0844004050b5640805138542c10800c440d41c49584440c0305000c1103103020300000040d601d100090401d1404404000840c0d142d0901d00c240c1c0c981804083e41e4403059850140746141460030810f41e0881a4040c4c20030701400c00517403101e02404e03d2a40b2110304880800c00420b0f49c0f100e428860002c0c0000e02d0901407802e04000608a02d0800b50340000c1c0c034000781c02015024804400220440d000c09005c1c0c5584880030400f091000100700214041d00c1d10044001c00385e646088007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 991711762 1250 991710512 991710541
    0xc1201110a17060a05060a05030c1204080a0201050609060a140d051c090f12030809071503060302040b042708120f01031b03080d0e030d1b140c060601030519050708 72
    0x10244561000e44c014007459950b503098402c1200030745081e81d01c0c1e507941940502c1c00e00c41c80d407001700d01503440004c200070400300d40300074410784a541d802480a516030405025480409462311a4841180001803000d000c000c8090b031403100c002440300441c001c60b62595400c0001d01001000c40c40300441400407600e0700003000100601e60802c81c15091858101c0781c2030084c1011360010108031820380802d400110401c140000b62a007605800c6040e800c00201400030402d62004074002da04190300c5d5400c515061040c0380d03900c1420402e540855803042c41c0c0c03407210411b880303044a0041d020b011200c03615001d174100c42d1260504054410003035065041043c0c005400c0c0c00311000102d4654428400200b070b04050f213843c401000804107001c4038a0080700e0843c0180c03032421002c149044081e414140380300701c540c070031500c40d5240d5450b4003010009801c2c2c244208854003108e9800300000c914107500c80c0c0c0c84a6071100304034a28130889280f490074035040d28030a503a10400030382d4138824403001e0316040d01c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 991713012 1250 991711762 991711771
    0x60e090906060303070206030403450b1b0a0c290a2007080a080a090b070c0b1c090c060f0e030604140a152306030c1201110a17 56
    0x1c10452030a400001c1d41c074443c40000030700403900440484e00f014040d145251810200d54110305d00180e25080c00c161031242c44418031042c0e003500c22904800a501c0c0700034000e54981003500343c6040d100000000b10300e402c44540d00510700c035000d80400480c80e0600400080d000705400081c050105c607a4000d106400840ca00080c08000c001e0441000d802c0540c107109030403c402104a0380350910651400d211459118003602d00820341ca90b41040a040020f180c03149a5449540701c0a407207000c4c0710034a0150000090240f160824140400060340c00500400280070481001070501900c85005880e800c00b4102d0303c1d105015400e01c00b41c1c8c2c12640d54601d03040189841d004207a01e410001c0e42c0c03528040c1014181340d00301c5c000701150f0340052004000245d000602c0c03050740307000600040b00900720f010585840701c825a00f0f4404c044d4242002601801000340180310188078002082000006c250484e41951b581e0381240c844509164003a00c00c1d24040d4458200c01c061207401910400d84c000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 991714262 1250 991713012 991713031
    0xc0307060b061612030e240112020901180917130915050f030a08121009021305090612060705120108030301030305030c0f0d1a041506020601060c1506060e09 69
    0x10400440040a440c455502074001e082c030346030714420311307820382c0100290034801400d405000c071001c804246504000c1c4a1986075018141c0c581ea070b0f0040031445d800c903070100075480401d07030004010010f109403500c016140c84203000141400903954808a282c04052094840c00000c65400b0403c08000b600100500303c402050090b102e2650b8450b0100f0100c0c001d280c40341140410403840d5842c200a201c50241d4040040c43d55180100031841321282c040f28009240240c0d403001041c404154001d64149504030001c110086040c84104580407800030b0640fa008400c0c0c0b14128130004041103d18018a01130302c94a95a503030009880c007175008143c010082517481000100f0019a03c0b81c1245e0380700d40045c00450304c884480f0f2810b1004d2040c800e0118800342000224220259040c0043c400c20364126402c1003021040c1d41d012850762035911482016820440040050354051211a194144100070700003510358544024411110103400003000904421071a00450410721040c9410200a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 991715512 1250 991714262 991714267
    0x3011205012f130302040501090b030f0d050a2105040311240c09150703080a0b2d030f0313031406190911030a0b15101704080f0c0307060b06 62
    0x20030040101032024941981082c002040c000f24651020300c0b10295038020301c180003550f500c65050012708003083c0e50a01c03030b0040c0400034815400026a091003017503903884140c107080c40074000f95002c07a2541e010a0f080c2110b4019111802400d10070300d4800e6100c4d4813400302e00b01e202180203190100360b4480c1d51682d50444036015151030701d2048564400108d41da0b6036aa100c5503000700c0c00880381d078604035a2082001ca11041050303002100103114611610081002030003003401c02c016960710602e4181c0c041880000f250f00301982180340d2132480d070054111072190752003446140c40d50b40440d06c044071042d844141130041000000000c00c814030454010041401c082021416070b005111241110b1940c4d40380610070010410080c01c001d050003001d03240300c0305d02800c190207a13030000c95070400c6440171807014480510300101c5d00b60007110242d0315070580280c22900360f50311100182040e100c0000038044000390700e030001c0040c503036a08080f000d96201e420518100c0280c901001001e1310804c000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 991716762 1250 991715512 991715561
    0x91603180206031602010605030703050a0b0c0f030f150307080a0b01060f0914042a091a090d0212010c0207080609071526152419020c060301120501 65
    0x40c4803e59803c0421014180303082d001014003603005180729803120703416004d200800014084c0114100c0c0b103250283c0d02d028000d540d0310780e8a03212441004840c50002c0e0061012800700c3c0e4659242076880407012081402040012002920780516984209000c0c1d014580c007204004102e01014010000f40c00d10009010b0b81c00400303415207100d4080c2c50341400c0055040441036840d5080f410f881c0045245407144107004841c1c18038400080c51034080402c03d1480009805000007140700841e00480c803082e41008103d40400c00200139825040e41d00100ca004000102d076401c2c07148a020607199002040060b1812902a09010f0000d282c4400d9410000003003061082c0b09003c07e141e100c0e145812004900e50b81c0714881e42c14400d408201d80321050b01c040041d2041c1390428404030030000c0b1a8010010254118450000d403001525102c4486c1408104040300100500b00c9110030680107451801001c2c20100c1c0b100d401c01d0b03005002e01242c03100480705024080c411445000c0d01640000c032001003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 991718012 1250 991716762 991716769
    0x602010b090601020c0d0f3c0b1504020c011d0d020115030305030c072a050603061302032503050f01090912110f030720090f0c180916031802 62
    0x81102d649401540c03074400c0d1401f0003c0388101345140319400b00c500426a0403114000041480b000b103a10b01c400c20498119800d1020940c452034850380c00b8800c080c283e0740d604801c00a1171400649030390419000d001030172082c0e00a014102004010314008448000c03105003035032600150314260310a691501041d4446400e00310060003d8a0701400d00550f070781c854418501d010304c1598405401d501040d0307207600d0050b00072034200000d807554407161019141c886042107a5484203540d102d901c212502e01002c3c00013040d8019580c0a00103115011903c00c9802e8504a0b030051058414002a80d031010401d0b206441c0e55044d015000ca10b07420071440c0f0466549500c4070030103103000c200f800034585020841c40b608000700710412914400741e80d2101480d14080950400445a42100705020104c801403401d041841611038201d015450313509440d091403070343c0164403103400c0c140c440c40d40070000d04090b01e0b40c070840c6000d0080d01c004a03c940d81c00300002001c6420280e10f2004490302041d880001d030340c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 991719262 1250 991718012 991718023
    0xc080c09061c0b060607080d0605012015070201090b040c1e030f061d070e270607140706180b371d1b03030a0f0c2a0602010b09060102 59
    0x40d0302c0f002c19549502e5010002d0003500031507000400d0000c0000381700b1040540c580214044038030a88541018821300010084148013001c41c80c1c01079802100b8280c2c042c28411007284c1c002046c0d0000242551285e26500070703960046500303481182c01c02c50b081200b94030044d0aa02c500440600342d03004142542d49201150021000140040d610703020360003049440d003c641098208800110340c00d603599000d15a004010450b000240442c10944501c1540f00980743d0140c814480360207040c00d03549200051f51441d0b90b0030340403608113500307012410000b01d040c4195030f201c1100d1070500311502c4441c9044001284010f00e10700c01040141551215522403600004144200b44100700e07940e05031070740c2c0d0b50041c401107005802c40420640c028070008404505041a2811811106840740480b42410365922502080f04005940703544c111041a00c140300d9541c803240304c2c468084101e00308000b440800148a440c0400d5503846200070070440e80c09224800c09144140c078079104070300e410340002c1d4070351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991720512 1250 991719262 991719319
    0x213091a011208040b21070f02010b030a020a0b0307021006060e030d030b03031b030c250f0b09101707090f08060609042d030903140a0c0b0f070c080c0906 68
    0x40020503a40350b04810050b01b0036a184020300d08a2491400d48802058120a02c00c100f0142d440c11a9040c0981404141d0a140e0740d00079014030041c500d041c4c2005503680c00240240c0440c01942d5080b07440c51042d008840061071640c0d1742c0181c0103400c4007003500700011290b136002418944806000e5588011003511080e91071403940444004003440014118820109032900a0080606c420190365460b006408902840c40c400144140c42d0a8905c1c142c0f84240185942c0c00700602c06641d40345003000e20070001c0d8003649007960140018000d0280d11410a0395104045104a401801010b1420640000130105000241901c1c20304078042115080d01510181c9030340d102c9e4010040240c03440711841c0b0313503803c00800b4003045080350600800001c0a4001120441e90b00003050229240024101c4905c0b40c11002c0b1420642ca0140c1090055004d400a000c0703944050205e0004174039403a485000400e901005820f034001100c08001c0c1c02e0038000c0c08144035200c0810034440b412419070b40f40116 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991721762 1250 991720512 991720529
    0x120903020721020a0b040e060904030219111f08090d121d0303040b060f0405091f1b080f06040903022e02071202010606050a020c09040213091a01120804 67
    0x10320003140a240d0b04110701d4103020b50498200d410006600307103800000d108440e0030100308041500c2c1c001c20082c2d40c0400741e5000d00142e1200401b007071401040b00e122254140305c3c1d22074540885504001c1100c02c6041040d8441082e070980016092a820001043d480050314001d807482d64007011015181c2d00006a206000d81c0d0390315080c80c8000407040c4224070550310340044035207038a080e240011a1080460b0054010585890030281c0c81c00d244c09518000c1130580e01605440c0e98485980782052101c0e10f40c00d8203151070300791842a60904041d001354002450750ba0301c020740b5100410500f4140080c2c0b0407405580b03020402c2020960100d50254036103d401c01c541c031843d0395038001d00500a1050a002605480014640c2c100402d4108a142608032034009104141da1454261118010310b4441009a04804400c080c585490440d00d50f00510040c1010091500413610000319014080f08981400f40060001e02101000481078014042c000341c5071510501e42c0c1c0c1d00c1002e0f0040707100e11000e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991723012 1250 991721762 991721789
    0x21203100311031e070306060905010b0403031214161e0c021e060a03020a020d020706121d0316021e0d03030203060301093302210603030d020406020c011209030207 72
    0x505a40501029000c1039940e04c0160b41c0014213007000d501c0c0d01c12880100c5285282c030100044035140c030700405048521408a450415155850a070341400c0c03441100d80c10306545070600b80794501c0c05620907000c0c4209403c0c04140c02800c60014008202d4042c91210f00014640c5000e40c090784505121803450381a2101680c0440745010360b0403504002078500d5005602040b40d104140d17165010302420800d9078200d903203030001707160140e88444c800c2c02030b800051025082041143da154110704c2000e80d11f040c200c87d1026500014505540180710390600f0480c45a082c8010752404000681039900c201154003050148040081c1c2d84c5004900c1c010181900407001a140360b401303510542c60756400078581540c020f0006802241c0c0c4074620503240a900d0741044e0448480060303c01c4d591442c0011f050700391540d1200c1106c003d544d030006d005e558144030401c5000844c1d05203001610040070a900106480316054001416070746000409100c41450200d00002081c1e0001d00d0348101d400340d900c400f8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991724262 1250 991723012 991723043
    0x3061d01060e03150108030a120b0a2309131b14010c1a0f0a050106020708120c010605060f030609130203100b0609032a03011119210c0212031003 64
    0x7400d01c0c020000000381204481c0c000131b032100c00400244005803c5076038140119410010303117011290305410380d981100b0251070034080c0203502d040e041c103061170f00c850041d45403424400044452408490100e401798031055144100040690141010302c2002003030418541090399003074101c0014003040b41085a40d2500390244010700030b449007214000d4582019515007020700c01c288441c140c601588042ca040000074240c0d00c08160784068032082c00242140450340c207580c40f00b60b0025802140c0355503035050300060311744c3c0f104000d002c4a400390b10302070380300c1c0340c40c604201c03055a00400100b801ba00f0301910000607500840c088900b208104c400040307948224010074803d016400c01540c26101740f1585256556401c03950141031504514140d200d4140322042c18240e882015a1840c3c0d080d0034411801504401d182e521110400c41c68849076480d01c40007060340b01c0028010411106950303490142c10b90303078180003540c10300011811051031820074002098025480303200180038400001c84c81c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991725512 1250 991724262 991724269
    0x240a0b06130905100501090f03080310090501060c1103010504020d021e060a020c09090a0c06050f0f0d02041e0803090123071103100e0d0f0c050d02030a03061d01060e 73
    0x8038104601c07084140c52050301c900c80800100000e5074003420701400d00c1c4d000103c56200340700c060143d6003104152890603246a80307030201500050000d0031709a5a00390040b800c3e0340766110743c60080685680740490002d1608150000c9a10030544c1d6000764107040c10040982c941c3d000d03030400b0990655948500035122408500c40b8103400148903480980020030b0a00320b50b0014002c81c0840b42150011040c4d01d0340303103000f555582e1200009240050403181045070714000d001a110018038001c0186c82c0019542085082d0b50100d410302c0002507000c03c0a001c1040503600c20700c40400070f6075010300c034036080401555890040440c0d0310f040000519070190100001001c80d04101c010f0301580c1d1701c0325440d00d0031a1511262401950181c07240000f0741e4019070786801100ca080400078050a2403201e540e07400c5442405a10103035040c048180f000700000703007040141804c0c041a0b54042c0d525118841001000da840c590b029001c40e525140d0a0101454083d0100d41103c140e4244016407000b8800407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991726618 1106 991725512 991725517
    0x1908073c120e0312040308040f08030103060204090627020f2203061103070804060b18150f01030b03121b0303070f030506010504080a0b09120a11240a0b06 68
    0x400c001c21f002d08441604a401080780b00f401c2c1d4519110500703660b00a910440348554002070400035550b00f8031420010740100c4400103e40b0203144041240d04400a05052520f507000840820754101e01c030480742800d9400e06845140500b401c500045161913110554896080200e00003544401c0300440c2d100d1401a00d4680c5e00e521241c036200000c110350000740760019402c441041207403034803071815031045603162182c1e840c0d0702c0b0741410700047c121104142410325042c90f814050300e942c04680c0304195440c00c0c0250361210070f11781504100e401c880000040500000080c80f0b81c2642c0440c00d00151452502c082c480c80e12090011941403045114001d050307001034100400281c20044016003060207401100d0003d851401040c006070310049023036001c0f0f48404007825614a00b88a00800d406040f0118500e0401c903e000024809004003064641640c0d04149415951410305 = true := by decide +kernel

theorem cover : BRFrame.Cov 991546762 991726618 := by
  have h0 := BRFrame.cov_init 991546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991546762 ≤ n) (h2 : n < 991726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
