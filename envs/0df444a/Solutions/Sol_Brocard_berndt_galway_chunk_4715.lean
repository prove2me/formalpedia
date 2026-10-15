-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4715
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:24.583187+00:00
-- url     : https://prove2.me/submissions/b975669d-1f20-44b6-9aba-669d6a46e6d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 847841726 ≤ n < 848021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 847842976 1250 847841726 847841777
    0x290403060b06090d080715020306060909220b010e130b19091709180105010525050f070602150f01061d04050c040f051c03050c0a08030406050103031e 66
    0x50100c51900860390f02048100040190541c0c003144001a0f032001c0000701003081503040c2940c24214114109240081d01900c100148184244030b20004140084072503017040c0b080000c0040e21182c917401624195000740b07404d1007542a0385038150006914022000b00c82403003594003090000d919918145c08640300403041c8a8400e03259510f4440d54001030100e00410602040a408292126003080c20065000781103036440519100620041203266005001d490123521020a001c010300440605040c4061032400e02420074030070803803210400c08010401d08141c61050b402d0b030307000011550041140007030655114803032110720401040000c4c4a1381c180820020040d00014100030a600003800ba0f9100f900c1c5180c04610008040180d00c08819460b40181001d40e9800050248030070030180381070002c400603052180000b580d0240c80302c00d000c070350801640202c4182c1c0700d0911303080100c001c2400b4001100840d942e0f80380c045103281c800200700740e814800e03a078401500340a5007061b250911031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 847844226 1250 847842976 847842979
    0x201080c130e060306150f0103090f06060b040512190201050c01021b010c0210090b0411190b190206040f2004090f050105130b0c0306061909290403060b 67
    0x203018801c4000140c048200041c94141e0700701c0c056040c154101424020081c1080407841150321340c00c442501d90034416292441c007401d0010300070b410340c2402c8030810005100201f04a10b402c0300420000720020281c425a601900c4015803644854034007079581c02c080d80c0c41700204d04505c45c2d0300015031040f0010300c0685c240100160400312401404000c034120007500c940541d44503074110700380c5c0e581085150300d0781c25082e100340300800a9845144800b14080c2020b03094801007440007459403101c180844a0305d01d80c8540c2070030190380c2d00e00010581c0001410010f0400320320300b80d4003c28030014a45001e01d40103031034800d00801940e5603199014904207a0f40e1303038452200c058181d590740c9100b008025070182103071020030300003850314608450004001c904113001c0400600b01088003030001c40d6000c2a420107050362901d80c0400921580039401d62546010070440301180815071104c14241210340c00051144441e1031014840703040100d010f5101d400100a10003040421180c0e008030703140190 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 847845476 1250 847844226 847844251
    0x70608090a0f1103190b100f09020918090303070801050a15031e0905030705010f1803050d0906091b0906050d0b060f090711070806060a0e092a010305130f020108 71
    0x19480003090409494010303501c41c0c030710b0b90030705c1006019034014050740c480300300b000002d1440d052030000f010348030084c0030b00c4000355030124502c08076840d00c660148140e010b201c1c1e003035028a131010000340e0300d610440f08040000c41040000030310f410005010803d403a0100e140c110200031211044000701440005c480404509881d40c3d5400540781c8030f1b0b150494000c4000d07640c0c81d02c06081c02c03401e50304440128070302a440c26400c0442d2030800080c5c9004150f151510680c1d515900550170040d150080024141c2490190128100900c10080300e49041001c8400d07440c007079444051100311000c500c982034100c06107001401c00a89a0b100030340d40814010201307100c0034103040116002c031008980d19800700d400011850030b00031041141000a0030b1400c01060589041004641c001d01d0510411690085c1c7c80e02040c00c903042440801480710890f038104c0c40c10101040560005200110054086450040413844141c1036182005900f504805151401e50080d070045030b00d00c500610404021a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 847846726 1250 847845476 847845503
    0x5010e010e01200304030b130302060f0c0d02030705250302030904020d0207050709050910090507121113200702150304020109080d020604020f090f1b09180405070608090a0f 76
    0x5a0030294a0583c00c0180011a100d50851401864180c8060030303646041d40034000d000002a400188540d03c060075000700c04440c0c0350404440964054280d960403018008000c105849510001a01451420000c41c0c981c80d840d40c0f0328140400403010f4040c0042c5c0041201e80014209074000340121300884500500c1c0600780e132203160500110741c0000d500e1035165814000b01d58020828504004014103041001a003540d130b900365548840e1142c0e0000c01c8401580030148640c80c001c111618401402003141d1494100e4064010144004048035100c2a00d05d40384d0240c000700103544045902520030381842104480100c12500004c00890400c1f043d4800803480c110284001441e0440540040040d401c040c410403c4604c41110503d0040f401c1a04000d20002c0d003a4000350000b5a007000c0c804c1e9900b01c50400d40b1300381b2401d00003940050353f40030840720002100d00e02601c100e024006a0b012103440720380880b50350340240c4081d01030b03500c00300400d40401c154081e0082d00910560b5030b5002ca1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 847847976 1250 847846726 847846757
    0x90b0312041805091f0f0204050909070501090f06093003050d050a05061305070e180108011d0d080c070b01030f1101180e040c1d010f0501050405010e010e01 69
    0x1a8481d030480d07251569842e0b819140c0d659680034498101420344041c00c0c00511840c89005410800c3d05c50804c90368850710f0021400041d6412240035081c060404002032408548207551044c20b0701c103d90010b0141180050000444d400e450292a0729646603400785141c01c0d00400500c407a00c100700f03140343c0344180311948000c804e911410001c0c460748038151103c809404520031100001d10403031099082004100d1545e44000240001c0b102e00040001c21382c540c4001102c2c8010091200c681002c45054020801e144002146048602850090050f40f2094420720445000030800c407841ea4401c1d80007010700d9024906041c0e0282d070804440b800c0c0401900c8003030f480c110a034000d607000d40b000d007103810a200c401c1840110b410b01c21b00300b000c034464003507420524402c15440f0f0804900103036000b280070001c80c124100c00801c640024007404154259052480600030f1107502c0c06040040c00026095000c1e006940846005859050098210780015665480c4aa84490403c030403001c0c180d400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 847849226 1250 847847976 847848013
    0x10b1902030307271e0906060207050f04051801110711040902060708211e0a0501030b060f030703050604052503053c010f1401150f0c0503120f1807090b03 68
    0x508954040126441d101800007121f065401200842d0040c0105000742e0b1600050900350031415903000803039590300b40c000c6140701c0392020105603650904048050205a07080035050150290158000d00e0217994104070441e450040c0003500b05074203103e020081091034018054603030043d6207100d40425015a919980c840444940d80c2c0c981c20420380c1a10059450b0761294880484902000254119151030b00c02d20001000d07280f2420380014540980c1e1000d1001900641d801411540c80b405e0a1038001c1e200d09110210401d070301652100d001040150002c003104484d00b11002c0c00343c40300c07405411140c2c00703041d080c418040c110a03206407031034010035034040481c01c1c58280006203d10380700610301d0031307100314201500c0c2010003000103201d2111900015503000405042020b0075542d14041a00c1100d02180090400d00001c21414902c4400f160250b1140e0401d54600240350340305280d0300c4d080d06030f2281144050f40440d80620a41c049540480e1000d03c00030201d55007100840404000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 847850476 1250 847849226 847849259
    0x6031306050f070306090b03120a0302070f11030f21072a03050705010513120c0e150108010b0a050304020f0a08030f0c0106061b0803040f0605010b190203030727 71
    0xd804802010041480ea0505c110b41c054407034414240002c0280000095480704015500c00300c000380054030a11141c003c0d4111000f09a00802403046800e0505205030600b0440810310300074001c0310003420840801141540403510340c800c5002140540c0b0450781c0103034210b900c01326114000101c001088618541143c6140d07a4005640c46240e41146021403c1900641c000da0500c0028000303010b1080800c043c58040d80c894004241c03400c0d005040102d0704084030b51040e1030301c08511041c8000504103221703400104200380c917141801d903601c0c01341c1c5566102d0920f0210000700144046001850401304802004030003c02d10b11609886903007284c25503001d0a1030021f0444001100003030201d0a009200c020a0f003410b02e034500c85140c80f881c00b02551325600041205200000090801003152110b15020390000000c11103507849207a2074059601c408546600d031340030841181031031880081128864819680d800071055988108401d0004452a030744101c2e00c00d10350042140c1580e90320204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 847851726 1250 847850476 847850491
    0x150405031c09020a24140d0c050c010c08061509030f190204150312140c070b07050105060f1c06020f0d0c110d0905090403021c0f2604020603130605 65
    0x660281e0a10400411081c00c0d44176140d078050804081112510030041500ca0221710300341b507405151640080740c030700e200e4207030b051b400d440c42c00d107420301095407003400b82c14840c102c04000c12124960013415a03010404803006c6902840d9130500d00d200d496001c002d001101e002400301d505241c0a00801801e121900505400c4040c1c03a012450070340c5818080c1d0a64a051030300904074a03425911072404d40c0b44074446120a00c00d241200b107448030000e00440312449800c1054500f010340b11802113105d94420343c8150744940c00e040104106240100c100400e42100034115262001040344100711402801c1b170541d403403039007800900c055859a00051207161405c210009444c3d0381018046d0807000000310b058042e5002c40074100a00303800808000a8171801c0314401c120b07940d2494100c1ca0720f01c18881181544a261100031846508513601415080d220b40724035140c1c41c209081c0180d400103c0145601c0102424003144c05400c11308001c6401c852407119000c03010316540c5460056940998019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 847852976 1250 847851726 847851731
    0xf14040c18090e0705040203011a070f0f1a09030327070e04110103050705120a09020f1002060106090504111207030b0603130605130506060f19080c03010606020f150405031c 76
    0x2840d0f0080240000c5000d45021581141103504240311305481e1040e02c030100815a200080403820b00084400c6807403200d07805070900300c517500c1e14030b091215080d0036101c11844a046070301141518202205403803090780c03460b03881082c2050100c0c40050204040644c980180101c090101d04c05e80042c2d8054450360080b20703036481000c0e03800c000400302c0310700800940c1040b806201c2d40181004809000345c00a45c24000400c00c9000380c00010303000049441c0da5a031100248959400c4a90080380c414100c0301140c55128038035907a4002e01082d42c140310451040250b0401c4145884d0b1080105507800034681e01d0006401100d0401040750360740281c4521103903495038030b0000104841c500404e036018825100c0d0702e8500481341d40300f030b5844001810303291007900c540a185180d034440741c080b964200090b410300300d0000d968004040d142c1a0303120956000703508140012440714000202c203002c01a10b0383c02030007042c51000280c1440c01780500111110b0000300a82d030510912055085164180060f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 847854226 1250 847852976 847852991
    0x3050106111504142a061e0d0f09060504030e0f030729040f1806030b01030f05120301170c090405030406050313080a030f051303020d0c051e0c09010f14040c1809 71
    0x96001070785c40a40d24420b0030200310701190416198640949140c241b503402d0344501c000e0a00a001d42071000308088400d00e083c3c5880180440d075044a405580251964a401e8159609118034000100c44407a01070b0f00040c4100302c4000103070160811143c50800040c1c4d00c0600f0214140b055100341e0010b800510b11400a001034440b501c041442c0c140300c2c20040200707a2031079440e44000c840520019104560340c100c1784003480021301401190720110000242d0700c4d078480104c2c502200b1912010b4481e4440c0d103801e1a1b040c20001000c6015640100c0114206441c220b412142c9520003040440880c11921902c40005c2030213024001c051040d0320082400240a801d010445d074008000642803500050407401094000c10704404d200003a2420f080c0070200c509006250489440b2445d49006c0e806d460500f042102044249801c541181c8840960b40e032181d0759526900d25019160921808044070010352401d580311010080356801c020281354480c08002444c688658030080c02c3d1502c2e25074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 847855476 1250 847854226 847854283
    0x60702030f071d1623070b04140c01021501050d050a080f0d0b0d0c150e13050402030c0901060f0e180f0a0f180b04020604080a03020d0305010611150414 67
    0x712a60040c000000594a40951140244800700141c0980310b17440c0400c1e8121701200301c00f0101c07200c2da42c0040d001071141c20306140000c0b81c80040b013080e15580c09a43d0b00040380d1361011680e114060162800c0c0c46940e401c240401c8040e881425041f1410b200d0b2680d007200107200440503040030855024840e849129042098040d65582e500581c482e0404d400c640000408400703841090314160b201c074048120900c1001d40c0c510860049140e4444050820046201082c0d080544118800e60594070149110018001a280c0c00e0141a020030381924084409a100d012518603100d8010150300704031300100711400300e407403040d50030b14480e03a008810441200300500450640b11000300b0100030b0300030203a10401b0004043e6800500398511040800c007990307030700c40c1a10064940301041e5001520549006036880c07900b41c1c035034800b00341031500002c2c4441c05460b01640074a5804060146005d40c0399200440e24030061084808010348031010010034420040c2030b0105096602001e5400d00054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 847856726 1250 847855476 847855529
    0x80d180506030402010c170903070f140d0b1b0d0e25140d080708040e07030501080c0d020409060e070b0a02061501020c010c11042c070305030306060702030f07 70
    0x3008580266010030074407005036405a61048025000008070030400016101040a40b03d00e0203070940c1403040600116546003841d03203601c21514042181d90303008648038240000001c4000c3e024010314400400100d8044551002c1c4446806003540107190600321032501088585100e6011510350001100310814801001456052040c00c04001c00140c540090b5040c001030508026020781650034000c0304210b8134405030703070300030707074007006942d00c035929100c0401d400a812210000080e00300000001c0c076006c089080c004040010380086080801da07020310001d04030004c8110782d050354507824221f00090511003440130303014100000f90b4881c090907009240007406030116240102d0032048904503070f00026600d1160340d0a00304101140c14504000e100c0000f0f0b0108150080c0c00c011040d04217103541c640340c031a408000030707880300c5900c184114983d5440703c90200a05a600030408070381c00345071410141440ba1710003803c41d640b25004400341410031181d5808000c54000c00b426102400c420803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 847857976 1250 847856726 847856729
    0xc090207110420160c08010c0203032410210501090204081e061b0403060e010504150b030604030302180d0b0423030301060c0c0e090c01031a28080d18 66
    0xc00c0d40d11040c0f00d800e0003c00c540e1050120304202403503184050804c010324031012500400800000304151146110065140d9004a850074040c3e004580c00f03080e401140c10148410142c090314103043d0701d0030360005448607039400101a000701d065182c04564030702c1c507000e06400780102c0400562110f1410400900c1d10381c3d28001d00d640c40d00041e00505e04100e0016035154000d600305184d131a020301d6600503030145d10071900098601414102c203003900100c1504260302030f500c40c11001d40e1101012203400d08840c1d4401c509a415004035010034003080c4240c0203400300c030b00174124020169402c1000030743c02400c940000c40e90307400e84070200018044900c520034030740c1c0c0e00c00036241c00850101038055241e2005009410902111240c000c0a00810900720000b0785240328520b6100d0510301c4d103c603901e0215104041c0001d06019042c002c0035045032202c5020700f805400f42c01c02034601c20503100441203002d0580d0b165003036504001101442040007019000315611650480d6090802903c0c010300907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 847859226 1250 847857976 847858001
    0x72007060f030e03070f021c0f051c1d120a0c0504060e07050403030f230c010606050901090603090212190c0506070b0f070201091401020a020c031b0603040c0902071104 74
    0x1481c01c1c03072040d803c0100880e02c207036a2090300310440c40028800140c40003004109101403044068140041200090301c4800c44c40c010401c480d010500722807a0b2200514800401001407034540641155200c40c04031085074090092626400e003600c8c10216141a20007402640c9005504004100d01e040510492024200d034410392151403820003130161883c440d5200081c2000944d440a0444606c2202c0d43c07810312064042185403000f000d403c005080c0c0081101e15400d500e4403000184030f80c018811034015031010703114050480d1400b9010340083c219650306a030050503a49406000040c14000c900c1c2c5603221001003c0030f00085d0503c2010a1400c0c0c00050180900300048408103008240059025004107d110396a070b8503407c2c101e02400e44800024a208480c4d920010050410f4001d40380b25801c0f0743c2207515918034035041642d03490600d070240f02c2d901c001d90f94062150402c04002c43c2e2081c040c015141c0c2d4140d43e80341c8802260700941c4103481c1e03032000c1c0c8550031291800e4051110305198 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 847860476 1250 847859226 847859231
    0xf0c171918060f0f0c05120a0807030531081605070609080c061612050307020114041703040c0b030103050a03080109090308010b09040b0402120406150617072007060f03 74
    0x10102c01400501d5182d004809200d04c2e040d1a004444c42000c44d1480164804140e400d900740741045040e89800c501d28038408108031000044000b442481f50f14400c00611101d0b414100d0b402e003080c80c1501c0004c541c0c1482d80303005034454020911100082c400711031066840d02603100710342026410094546c002c0c01c2080354508040105103c0041c0c2c028045c40221125581d43c0d4000b0080d22042c140550001c1c801a10740e01d0a078100b075049030107140b080f082c9400a11001040502401308480c04035001001c1d09098a40010040b0540780510740c0f05209a2640085640f40c00c0c0000d1250030076031040b607859106d00c001000705039110401e0b40c0140240c10040c49000e02c1a900503040c1b050500603500d5074000130858001075599038004002d010b00240c403c5588a10001401c0003034a0112000c0d01d10509001c8451130a070007690340d5038120f070750540c0d82d00d05140c803440702d44c00002c0e00604581c04004d070a984a40b6803802e1000581d2200a08000400d20070349490009402d07100c08007908400d00d031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 847861726 1250 847860476 847860479
    0x1200c15130515041203030b0a09020c120702010c23010f0507050714030f040b121303120c180605030f010608060a05060f22030b01050405070f0c171918 67
    0x7074440c001e807410369408880d403807120040c46030f060311a401140c0c0b080070b01604a084200c14903030940e0007441c2e904416180740018544a01e181d4050f4070900c0c4850700f040c1c3c801c031040365452140350050503206105142110310361000d80c8441c40001d01e00803070b04540c403c1620507100c0f011000d22030600c818242400c14442480c0011014010f4041c0781800f80210900c598040c103400320510898101c0c0d01c80c00310b803684945e1103240029030740c0c01c0079844004105d01c10010500c40031010a0101d0a04d0781641c0d1000100180d80301c280180c000b080c195801d02c403661f41c040310007900d80c401480c050000d07031350380e282c4a00c1c1c42000180c051070103a12010038880d802d0103204140d12807401940036100b090b02e540356204a01110b0b400180b03d0b035801d1945141e00c1c0080c011703040300121700c49804c490140e040b60815989800420085420568090010a811b210f0030003409000e4440c2500b0540644904005000300c1005000b1560241e800000c5100401c600c091308950001c14041200f0103484800340c046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 847862976 1250 847861726 847861747
    0x5070c030c0b101a0c010b040203060303070206210a09020906040c0906050f040e01030f020306280903030e1e1203100306021c020a03021201060c0b1501200c15 70
    0x3110020028018102c1240007841c80c0d0000b4a4400080504030f245004906000844004541009512040e19402c00d2400314041c0380074000c0e1382c012040100a5440c00d1b01a60801980e9400700d01e50200c002850340304e003244055608000c5210705000c90f404a0000064410481070a100401d100e20562404000000700340d4000e500005031005800c1841c1d0b2003d030b1400290550003a588455440502c0e0400801002100000c811115209408039040c070740711700d400000440f211011500c07640140040c112101c44c126002014041d0003820005a528400c1541d00c2c101041001c01109103a200d200b04811007030108802481000c0004e00c0c103040d400c0c8800b007441c014003d032001400e034a80100700402c0284503a4840030345074400325001c650b2100b642c035010300070750401c5400300c80000b01e142c00010081d000c1c1000080c0c641d4010b10724000e9a486625100113aa88650201d04000003103e5a180202000150040c0110721900030300300060794804100c0702201c0200103180e540424014000c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 847864226 1250 847862976 847862987
    0x20a12050d121d03120c0c0a08071712060307050301061409070e060c0d0905010c080a181a03100603020a0c24020d0b0916090306020d1b090905070c03 66
    0x8141d85065402c05544210300c0300600700300c0c4084400000d18900c0b4411001c4000003e042c5c480d0741c440d02c0602941e6400c6040c11502610280c0c50240d0401c2801000141d0b601c0011310442c1d00c50240140c1c8183c0c4880140d1080e0054511a000c1254010074000280303020402013000380412070082c400d590a001d80014848982d4850034020003040e00410109806078150009808000d041d41d5221409106080c0d540e0b406030401a020605104000ca110b503c00d4100d580f030740c0c1d0041c0000d444c0c0031018100315205000d1000c3c01098003038010000c01c401c4180c030742800141d04a28815074417410000515451403140b50f0100d01030605c10071203811503507002440c00e1010344d00140448480d00780c2d9032083c01c01400c8803c0c01c6c108640b00041c0c00d0740c04961a0701c9400d030b4007000e0f00d9002c89607803681564a84080004403080105542d80b02c108006001900101040b25062a0201c0c81c40c0c604410245145421280318002c1820044280301c2c1803145e1040590005061800c403912901d03a4901410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 847865476 1250 847864226 847864243
    0xc07091d0f0613080313023604030c02010c0c0b16030801080d170411041b02060718170304090e0708161202010503060319140705030114060d051504050307020a1205 72
    0x20346600803002444401c24944c02d440c0306c5401500100c03c4c1c1804048201e001c840c9000c100001d850b06140740000c903c507120000740b00390380c1a180c481b001d0100381c0054586400401046400d82c4c2d1010b0013284103c2580040c0c5181160382c40340300341e0760405150181a4400580001a281d40601a800c8070907a10106201143c5504410000f0035203c1d4240031710303503207080c20030b0a41150410300e04d941110184a03184003075864a600351449515001c10131112601b9009106000c044c20020078011058044070041d00d4a6030b96044914040e0340740c14032825200c10000081d075070b4001c80c81c10080c0003824095001d5030075080241d92142404e10445048103074507000040d0400c04040001a074580f020425602d50113411064212046071341c1c541742c1c0440205001c241c101d40101d5a002480c1d08050081c02c0032035002c8900108156141803c1c071138503100c0000107803441e2040c9000e108407014403056640c051405071014507502c9604d40140706940010394044580030003d950a030002c100c0115070940c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 847866726 1250 847865476 847865483
    0x3140406020c07090213090c0503070206060f0a081f05070206040c140f06131418010e0606040e160917030a1805040606031d071a0c07091d0f0613 64
    0x50b01c888503518074619004441e001112440c1c4001848441c9003007482d808011503c1401090242c40c901d5041254980400c0c0e4a04002d60b0101c004101d00d803410604040070f11401a01c0b1240d1165075407011391900c18100e22550000150f44510b04d040441809100e6015505000405807404c2a030789001490406201e094004c11003414003a0880d40c0342d203940ba86005005010b25203894081e804501c10111921413035119181d48003d03100c0320305080c1c099010020700300c1018107040c0c0c60905075210442c40286503a500403004c00c0086030451601000078007034501c40061200d140c1c504007015261b0030194001041c01500403002c1c0084003000001c980c40c052203843d203001448072260b809081d040264011603071040c100000429440c0c1c1c503921510240c010090000c0c9010500c1d403e0076203e100a002e070100c3c4c40303810050448803082400c020000740b540c5100b1113203a00d9660b000242125603011064195002c071205a10b40d4000070464651403520f4880030b4034031400c00302c0e9080106500141d004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 847867976 1250 847866726 847866731
    0xc1014060f060712020c27060a060e27040b0f0903040b1c06090f090c0b03090307120c06062301090b19050d360b13050a020d0503031603140406 63
    0x9000c14406e116000c40d41c07001604207004000e4403803a1450340780c0400306500312801c010300000c500d450600325500483c0e20fa030701c909040e426101c06228046c000700301e003450200ca91002c801480d552130400d80c0e10a0707004031120302d82801d001044031041c0901070441922503106000500c0307502c40a00841d0070b00c082d14001003041e40c00c2d0840c510080c0c10180e0180e40c01d21324040c001911078140b03820039410144522041101c0984520740741c000703404103940320a103a6105200c80c0d030000e4150124411210140e04003008290041d0392200103481603500300803004055440140c0c06258a924600d0300300390300342000c100c040c0c140600c8040c2030280510100c0401c280003030300c0071440d006900311070f5802d14800c41800b003441d290504040e1016201906a070f05c107030241001ca807049d01519250071903a0720180d2074009803206408200c13000e03418042620703d070054040200060b9101c02d408095184114099030300c9141401b0110304c070710715403c00042410700b42020784d80f42004080e56280d00c00d5103d0b900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 847869226 1250 847867976 847868003
    0x1002030403020316060b0306242205090a061a040b031c030b0a0503070806010609050307030b060d081204030e03100204050d0f080f040e0103021311070b0c0c1014060f0607 75
    0xd01806c0d4400403550180141410300122528a204802d54900b101d80800031318084801401340800000700030215080d40b00180154510503a04010b4004080034100c98441043d0345840c001c6400c0034500b0003425244400344440c0b03080a0050902540c42100a010306110034940220a503400a280b00f0030107583e2020360110340d842400c02c10180102408580b0541d80300c1c80f80305c0d40e49100303006241c0441e000140c0066103250000d41401901d500090918850312103100b8055440c41e00142210490fa0074400c50000c002d02c50b801a10440c040d9441c000e00c06c0c0100c0038181042c0d00c0300c0402c0354660040009010075201c001c10070303001c10344c0800001c41070303102810000303141c1c041d262055151820000380000c01b08400703220141079074001c0328901030700703e441103240c0c2c115040b00400c500601403e0205201049580e43c250750b109411301c4005240100d510280340c1000162801104081e96551081c8a41540b80300141c2e4006000d03a26284444c2c110b0000031358038014100001e001c5058a8030303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 847870476 1250 847869226 847869233
    0x30b061e10020708150a0b09061e0303190216060315050f0d080307111501030b0106051612050a0809010203010e0c0a0e0d030f020d080705160c03050a06050105031002030403020316 79
    0x6100000d008042c1038400c40114003055005c6880160303030020a107803c1c101109981e103007041c44c00c0c2c05001d0040190510441c8002e415018810441400ba8980401d2008410501d501c1d161554a1100c2c2d50140030b540403003480702c40c1001070940180040500d002401d0140d0300055200800f80c1d141140c40c40c0c00301c54040c00148080f24411030090440c2d40100c1072022407504410b007032500d8405081030701c80d010070319a4031207401a401d10018002180600c01000300c0c0d07005074020225428541c00034000484152141c0c03540641c0601e40f0f20000e100044d003a8030443d84a2411038101c07c0c4000290b10b90351400c92080e089000180c04041e200400007101c000882c0550010085000d014140b07070422407850034041c1088601c201d03404094060000c1e81044544a400141d2141090b0345a075030506003c80200c0400c551440000c84502d43e800c807011000c180d08004610041d0b01c5000c02003859810070003031504041c25224840807240c01481408000794000c070945114410184100006207507909 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 847871726 1250 847870476 847870483
    0x3020c030708040806041509030c020d1103010e06010504061212030b0a031506170102070c031e0602030c031e09030d0203040204111207031b14070309080d0207030b061e1002 76
    0x344024a1100d00060004290300c01291781d900c554042c08107900e03031180544000064132201e08006002850000018006160140c081205d8a0146060211176900500400d00716074195209031a254001c4004014914240c02018040d02c50030004004c90015540e0320451000701010300c9080c182c070703505d000f0000e44803016094020364000140c00c03030b040d0704035001c81c00070301c01c80c01f07000f5107210304600c0c800c6804014022a01a294407420245d00b0603c1e5480d003081c0e0941e00601e006014005851090100d00c0d10700280d8080c01e404290302d0340c2c0c0c0c00c186550031006188070079000401c15081c010000081004400d840c1c0c0100132800c050307969a160f20020f00242500c00540d81060008034042501d0150100854400c0b041c0d61820030440c4510400100540180e08000c1d0014403030b80746180c83c901b856405811440d00c01d0815401070394941860742e00704001d00c110040160b000d03c41c10824000340e00300d45500b00300e040d40e0200321680b580030742155001692069500441c0c240c1030f80320040784200f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 847872976 1250 847871726 847871737
    0x50633040e1203060f010c1e02150d0506030f070f1a070f060209040f020310090b040f06061e1701090e0a0210230306210a0209070804050105240103020c03 68
    0x20a0303940e5000b400c080c44090f500252203440c0100c0744207250f46050350049995004940d00801c2c000c80c0004400300c00300c10b01c1d51201040381c1114801c41a0b170000b1181c400035180c14021504003080c5032814000345031606510080d1044c040d0b12a250400c8000038200c803480c03c0e03403c4907580103a00c940e4220080380718400c00300000e26401660000070140001e95020303202603401200c040c442941803480c040141e001c103940c0400c4070b500203c4204001041903100e01030302c4d00050008201200b42052600445820340e008002040003a40f42d840380d00c2c15807071108640c00003400c10701880d13a41c820080c100380b4814091040704c0355a51004c500c414a040102e1400158001d00314075002c8500c44008000d81722034140c01040641d40e96494510300108000c0d00e22400015048001111604150000510355031400781c00301d024804c003040c050f841e9114024480e040c580c560851a08091a12600b1204000c050203600810001150b04401508000702d0000303600340380240e00d80050a01035421842007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 847874226 1250 847872976 847873001
    0xa020f0d0b24032407030c02101503021e0909010612080702220e070e040807020d081c02120f1b0d1e061e320d060905063304 55
    0x481403844040c81000504d41c000c420003018882107500c42141c00d80c03c1e40c40a5542c03402613080a54002214507030740d84260000c1986040c0342034001e5982d004180003c0030080254907820f2410045c0b013450410050040e00100c0000007080698036119a080f140c0b4030204009100303100008a6106559401316410001c3d48040c020240d0040000d001314002c120351b8000003254040c0440010b840c4421911481c8166004940149014803d50070040740b50300e42d8000703d41c0c1203810300810301080850404503080f0b860b513400042c0d9407058558020036078100140394040703040081c420080390891140146100b02c00c004045601c8042e1540c4401c00f5044844a00307908800c000c502100c681c8507508100c08031810300f50b00c04030402180000d42c481c00c9041c040c80900921803001c2c1031141060325100c400403000680320140c4403d80c8400070312080100242501c6050300c0302d10b25800c1c41400d0003202d8024500b19100002038428080c6505c400d00c104180f41021103041c1001040b80e241d681213442c02440c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 847875476 1250 847874226 847874233
    0x5031905180c040e28050601090b090f01150e040204080f060109150b0304030f03020d0203180d090849090608061c03031104080a020f0d0b2403 63
    0x400441080c04040c801501001c03500c211100450307641840d1151022810102002d09441051442030320b100d03107014074000850880a00c0e12402080e030074003d05018105041001c10722118400c1000b0a080010381a414450903103001000084898562880350a010b070070310101001544002500a002c2c0764032080040c01654001c1e01c807001c0c04640941a5400740f042000484043c40c15103400580038014403203050b00401c04503022a0250b821804070845610b005071414107084001020b0760001d03602c40041c16802c0f00c000320201c0301400700d038924048030b00c0c156100a14240c440380d0340d2040c100100310307034100010814000c0104041101c4580c0510300d0258020b101c1a610040000302d540d04c8800050002c4102060280c456120240920802090200700e001143c0112505049606040b002c1c5680c69003560300c207500c1100903000514032140941602c43c95801808002c0c1c8400e2201441131762109402000281203e503195000b4800c02c18044103180c0c4491007210480c24144850761620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 847876726 1250 847875476 847875481
    0xa05010522180e060f1003020d0c08070f050315060f0f030c0301180b34030b150a03150f090209030f0f01020d06150c03140706060b0702010f090b070305031905 70
    0x14594000085070f0314414103c03104ea5954400012502d207060340d03500200c001e2540d04001514117903151a202902075012210101c1d83e42c0111841c0c250340d6403148050822001d0700700580e14041c0208160850060004209850300e000020202d00ac0400d4191141602c00c01c0710049403420402240c130060007130000c2040400390004a02c1040b404c102c12036100c3c01c4000002c0001492055440700c0b03809209601d4110050010b010002844444400c0200f5684209102c426603800d030b520320150700345031601c6030394900303480000b400d07184000400340190112030710400402098180c610100c0707840000040c0c43c0c5c8008800a8244490000f00f65201d104003003c4c811495010342c01000c228003411010480c0075614012a2940041404120082441c0f1240070700400e010307204240d9900745442d4921b180c40840d0769082c0403160603400841e801403010450310304658010003520040300590038030700012442d1140c10026489107210050070800b0110102e210094070855581c004850b0306024400e92 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 847877976 1250 847876726 847876769
    0x7020301051311060c06070305071b0b040302120a050f07020609030304090203010509150102030d1505031005090d020c1c0c051e032a0f031011180a05010522 69
    0x2c0705190015240e211840120301084d14005045840302281c20000e80881d56440c2d030103400402c002021041441002000d40a01440141180d100c071441079484240038201800e0003840d154000b0039015407454100031a030b55964020054070341040040780410b98450315803000c12040e024034107140e41c0501c804640464600f0094000d5410b8580070340f55480e8540e50840000284202c00030101e0160b0410415170b8001074483d0000b0703400380d8034045000500c507500c80220b86001481c00f240c0c1106a52541444071170070341840000070f0342445100620030040c442000550303a00c4d000d0490901040003405034002c01070501d00001c01000300070078800b803602055030b401903078040c1d145015120740569050009000b1105c0c001d01460380c0c021545006801e02c0c4402d0245100188a940e44d1600c130316414500705010602400230401e001e541c80700d4075110f0b8454030b0020603034450310b01c43c82000b00b003a0134481c0e41da20a0645007825121010009040e100b40c1c9107151a00040d08400c40060b01e00c860b24145 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 847879226 1250 847877976 847878001
    0xc06020a030e030d120905010603020a1511070b0406200601060306180519020d06030609060e12030f0a020d090f081e03090a0b0910020c1605040507020606150702030105 74
    0x141806034846101854002c010036071a0100120410046415054100b03810b440c04e50150500030300c120000214640c407600010040d940c0d43e8003694010465404007140701d40e02030319030480b540021000b4603003903040080000884c0507a020308000c0221066000703107201031a00101100f134100384241c4415507181c84000b07018041340d02031520440d0306901d041500074624850213104d2140807020949002407619000d02070340c0000e040420701a102c00380807010801a12401c0f10041c4a0f0f1000103034600c1c03d003003aa003048009004060002030610801520f4050101050f900a04041c40140c1e9240191004401848107020107051085600d50410400c0380f000001d000b05440d901030f450f070402c070142c0001054481228161100e81240c000c01002844052485400156100c06c1d05c40e02c100c2030640750100d03001100d5444690f0310809802c0e280d4401e042800c0043c140c05e58050004c0c0c60000c0c3c01960300e078005010a4061345008107003110100610f800e85001d154010001e01660820249060f075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 847880476 1250 847879226 847879243
    0x106091406090d15050405031e030709060e03031201091b0c0b16300f020702031b0102031e180108060d0209191a0f0a0e0c0703030b0a0305030c010c0201020a02070b160c0602 76
    0xc0b54a000b00e80b0b00820400c602b80c900c100e00ca940e4091a442c01e1002c00c4a59107000c00c030f5250036104c1030007104c0d2085800b00409018100003040003e03148075000030130984220b00e80c9040180002110140c01084500009a0340103800741d0300c005d00891041000c95104039010554034099000031280d0100360032500c0c001c2d154111001017804108540100c507400c0344600c0800035072542c001ca5a00d034016019441d03140d4000c605005690404261205500e0000b981b40710b4100c1e400b40015804558424140591300c01060a181c0140c1510b403040c04100403281003440030380300b41d6250000400b0142940d14011a10380e1b0b002081c00480d5100c2280380b120462074034120302c036256401d401c00d460700b041d69240e0225083c03128a800507864040c0400c01c01da00a1a0560415450390640c0c04607440d41d051040c02103228000a41e60b03a007030301c0902405c44001490460469004200240c4481e41c0010b841c800d80c0c0e88079909030741da0b0140d051007030384413450480f004200c14901900001c2c69500881d0825 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 847881726 1250 847880476 847880497
    0xa0f1503050108070b071713061101062c0a09080c07060201061401202503110a03080f09030c03010f091205211302090903030106091406090d1505040503 67
    0x200a980310f42c030841e207403480c034001c4686083c01406030002181c05580f03819002c0206100781450104041041c80101c0055044040403450704044140c1c00c3d0001d01c69440184120b03509a2100c0d00c00b4004104904012016a0000700000c2c3c0401c04600c101e900c000c650a030301c82d00d4540c0e43c1c0510742c00300d6102c403480d1060764003552030490001161801e0402400c0008016074505841c0c80c4582c025010804902e031910400e4030030344602c4c10300c2e0480c12031062965038011000c2e0310000d1035484c0110844003000c1105000d412105420000902ea06099894480c00d4682e40341e141e101d2480400e20b082076010a40c0d5056082c001242d051848950000400c0780c0207605900c3e0912018805030b900b4803e4041011902000b803001840b80418044140d03044002048270644081c01074000a80107081511400c4840d0800401000450f8008030f8050040103034207821144c8007052000210300c2d00510b030502c0e02030445200305004105804605007542101464100401e06250406680d80d4100c9500304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 847882976 1250 847881726 847881731
    0x130c03050a0e070e04121b0605041218091e02030406140c07110411040801051513090b040b0a020403020a06020c041d061602120a11151608060a0f1503 66
    0x42d840580202e85001980d0080c0a242e4040e2a01d5480440846504082408100000040d5000003640da0f1038034020900407280032480782424102103600428079801001442054108040541080000c0e24120780c1006000982c21450300c452180ca07020594401d48101d01c00002c12041084542c40070300084040030902c219940d4411a9408030b1285403c003828402140c10000c00900c1c0503082045000038035030149048c9680d034101182504c0b01903800c03000495402d10000c24905100310301c000e40009d4440188030044160311076009c0c1c4840504040c00358040b0400080c007200c940e8040b200119800340820202560750b45009403101c09209000e886141820708101c1b034012621880070410a805014000544602c0c0c5d204a110480c0c221840540c09200c071040310b103401c0d84010f8648200c142c2c6680c0c0c1042c58030202242003c007003000304020042168244084000d00d020901008201410306040c140c64003c0040d010b605180c0c02410100340721840030400e00004c010340e218491031504e00703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 847884226 1250 847882976 847882991
    0x1140a0506091b0d0e150609040f0b0430030c090f0905060307030515010320100c02010e0907031401050901081c03020c010c0509120c011d0402130807030203121611130c03050a 77
    0x100288844143c030082c0c2b250160101103004107610b21032442c0c0091180e42840098285034006000b2110789040800e0701559003d43e60b800c140d018051543c40d0301151810030300880c100b211001000149024004000b82c0d120b0000c2c1660320100101c1000c2c2d50408225410344031020810b03031442c5e209000031074401500b030b206030200c084080380d4040d00301d0009006104000001c082158004c0072010b00307034100680c00c00c1980b02a2650020301c0c0c0100c0507a40c0104100e00b140040b9585008183c3c4000e0180301d00000400030440042201b80e800c46840c0c0f460f1a0a031300c0040c049000c3d009400340e041e1294642000984541d0700300005040c80082034544449007007a201c0c1007500c130b107014080540410000590b094442c5038154120604a00c0100014204203214103407403413400460f001809aa404103405009602c0d04109084c90550b04494051604081e002c4100c014451940000d28480f181010171243c1d070358a0090000b1144600010000c6e061050b000602426054039480c43c1540380102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 847885476 1250 847884226 847884229
    0x6060f0c02010e06070f0c080319020a080d090f0506011511030c060c0d0207061a0102161a13030816120f0c1403070209070201140a0506091b0d0e1506 66
    0xd4110340c49070142c5504099590580a0020542c42500b007103600100e98140c0c100014502c00e821400707047c031900255150018138494402009605502105650210901400094070703c07080341c060b12000707100412802140d1a244642041c40d1a00410740d026000c0042030020308014a0b003207940c602e690f22401c03d801d074502d4603100c1c403880203c00c0442d04400006800c2c682030b10010440070000704401807034009540c50711801c551450021184c020213a038828a502d6904015001c04001d008409200b1185403642441c00044190406042d5040c003050608160100050f24401103070003000040d41c5e8240040780b0910a20340c41012070b0201d0443d00321744040c40c03180080071103541035034640604506442d100d00380450f0300e52010383d0aa2004001400060300c602000c14010f40c040c0d0004a03007034115880d01b400700f00006020b40c5a80d41342c0002c000792030740c1c1ca0507000e4106000582000802d044440b12450341c0c450b40d1168090780b410000c2d01e10100c1000220180c40c06170040504035603448240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 847886726 1250 847885476 847885487
    0x2070b030115030e1c030204080d03050906040b0601020a1a06030f16090905100905070608060303120a05090a171b01060e0c0c03070b0106210e030313061e06060f 71
    0x50074401c0b84090990401c0d035800f030780c040d940200144040f101d950381c42c0002400400c050380c0d05080040e0700070400b04040c0c94204075651140c82c050405000c036180170300d10140d9070040108040e21f0001c01c100490940d9000b8000703031803219080340c04000241c84025040b00c0650064862900a00c908800c03c040c49002141e0030000c0e80a03450300340500303460001d00001400111000752114001e0b507139107040280f054481c10305450f11810240000a03e40701c00a800006d00420503030081d04204400c05460149400b21035000011540001c3c0d44d44400300102d01d4989450401010090a40ca0002912152a014009007624500c1d02d94109950715074460aa5010f4400c4010462a030804500d81010751000b81a03240c2c04041200d061000a84650b03001401c00e031702900100c1c07003644800050381d03c1c1c41c610800d0f220a40b0340c207002c01e01480b44103503502e1100030041f00981c00d98002880030040708d0340150144110140c0322050400310271080a0041441e0321540005c2141048240030890080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 847887976 1250 847886726 847886729
    0xc0a2a0b04080f06090c0d03090806090d0f091d070e130f0e07080a0b090f030a09090c03180201031a092509060215041703100906060c1709150705010b0102070b0301 72
    0x1740701904050a600c4180706d10444000412814000940307000b003250f510811040388203592042c0149a001c0707003e41d001d0820900c1d004503030100603010707006001d80c1c0c08561800c048a040313504820040e96503d03804035241d4204034201070f0300c140c1c14a20740903d42045d0304100410702e010700b4200001d41e940000c85564414034071800b9819004010150041110380303070026401644001660f0742c0d10b111000207410355002c4000d44020903000c0c2c2082c41807000340e11a01d01d281942d420200001d05070401203c92210f062640241016201c2c850140c20302182d43e540c0d80d00c50400b51480d101400c1c201d011a41c004a00400625189044240700c1d21682c8120261000c458464014007000c90051442c56000840240169607041d100d8540d0102c41b103000d40114411400150f910074591705000c1d00d18242c8825501007020004060500c00c0071450080d440b4403d018400d01c2d0554803012500032511500d0480e50030110450b0104d80c55090020640140d8603000b001d901356200d030ba80301d00d0103c0342404203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 847889226 1250 847887976 847887991
    0x106090f05090c0f0c011b0521060307080a0b0f0a0c080f07090509010e06011d1c14120d060801090f03030b030109020a080a0b0c0c0a2a0b04080f06 65
    0x1940c01005241001040c1d950070000d60b01c40c540c50200c42c803007812042d620005290a10303130b5442ca003a1707048111480300000d007140180380c03091809410309e0741384907481c2c011066000d0511869000c2856643d00b000200c0c002d054401c1038032030909280c180281d901c00c0440b0b44800002c0a1000228021028803541a079a02c0c56290aa00340c1c40b0551007038100c1c5401080c5000340099017002094030742e0740000c1c0c64001d004c103c2d0120200d24082c0300052100c03150201c60142e0214005c82180156104808400c3d00f801c04042d0249110031030070843c4000d21200c0300e44100c0e001b403044400380544a8002820400c800403000d10600f0382d00d0302c48a0803501c549002801c10641200f054000a2282e00100302100c0300900205409559400062444045074003194841e80000300341d104100820f54415444a154210141042c1080f00d50070b4503002c88940040500110500b50303021480c2c100b501085040644030794142d55a15840f071420564040d000710307001c5206060070542d0000c0d001904900c034102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 847890476 1250 847889226 847889249
    0xe100b0d03020d050d0905120a1e08180109060e030a0906020706020d030209060d11090103150e07050c071203031a0d020f040e01060b07051b1c150b060d14010609 71
    0x3040d0f0030441e10354010303c40c2c010300103489002e400d0214100f009400301651181c1c102980d54080054082d182c1d405800c2407103420008040f000145640001095501025032100030181d45040015603006008050004004601e031480200303139100000090a00f10015031251580c1c40d03180d40040ea5900c03102e01c1000b0040e032101c0d440d91005c138404d402510380040050312450402c90041003035410380341c1141519001c100c01050200c0d0300e69140c042e400c25058149060500c3d00e04001c6a0028110300402000500c07000040b501d0b40504100031820061080703400400e40500186001000f030b05101880c090702e120240e10329240ba180c81d100100f1240d900418421544039000c4c2400003a055801f6405055581d60704005009055800103040440c0300744060040b02055480d4221800e4000340d1550182c0f2041300d104401c85103018210403601d81200528887c50304908107e00a4444905000c0c1c0001d0f010a548402e06e1189d0420600354580c246042d4080c2c0c2c0300c1204490140d124440c40c0d81018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 847891726 1250 847890476 847890493
    0x80604120207230a1503050406110a09150207030b1801050f1326042c060105070807020d08040608041a07020d051e030f0406060509060109270e100b0d0302 68
    0x100000c2c0f44140d0000041d0070350600d03a40c2c6000a003492000d00e058030f00441d84039000c00040040c03d2007101140810b546009051054031103009240200038011a1059040309009086c41c0340200081c500a40d8000a42c140519007404107840070203042c400b412440d0300340804a00702864084425200f40074644400910380c1043d1584083e81c17100407489510308414032844208600f000b4018006419140f00017109100c0152a92a80d841d9220032505032240210034420380d80e910400310360307220350020180c548500b0300d4000030301d4521681d600144031480018000500a4100c004144101c1c041c0f01d03040c0800c0c0410780c5820f00340c442150f040f80180c20000040070f846000320701414604055640d6a42ca801158024103810760007540e02180c540e101501300401c01900e4050080035003c140c821b11031509240f40041d103030f0801406061140740740812030418280c42d6032462841c0c00c0705808140450172496070000d440d8031441e965020f81c1d82c20000000401d082c24010b071400710b0703403550080c000314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 847892976 1250 847891726 847891769
    0x901090b060f01181415250c050301060e07080906010e0c22060302070b010906180b040e060a0b0f06070206190507120f030b04050402090609070c0c080604120207 71
    0xd001000c1418103200d0540c00a4655801c90b000c468003822400845040b400051006c001c10079010b005043c031140c030b0030030880c0440d0a111407040c0100c00e0a00c0c0503102400e0618008a1101c040e80000d5010b40ca0001c00140310284030038011b015403010344a2400136112158155101c00b000d00400f0042c100940100343c0d619203480080c01c03031031308004810001d44590565924181103560244d00040d4010566100744104001014018010f100c0d00304410f07480c02e503841c0c1043e040c0c1c0c1020640d09a941a5014141c1c60715006281c0c0c40040360151055480d088199030000c0c900b180d0b03046c1c050355406103201643e082820031112120b400501d024100344009002e2000d51000e01d08850403c1030500011000409055560720001c10703980320070400c2b000d0807a0003000c03a4100b0420b1407060741882c05020140e290031041d250048010788d84280c4503030710355105555040c41014010f00946110781c3c0012101f41c0030031102d009500c50320600d1035071031028408070b90303035103050241d400000c1e40d14000300c106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 847894226 1250 847892976 847892989
    0x40b130e090d232206030e1b060702010c0614010305100207021305060f0a09060e0c0f1608161a0a02130e060f06030421020d05040905130606080d080901090b06 70
    0x5810b900c00c10a00d070404400001d0002e60074400c4c8035131061844907050145542500a01500c1c5076044010203800201910b1842c000760010241d50141da0001580f0003564856594036003825004603081c003444c3c41010340b110300501c0920094510f4061120300900358141c0f0b008443c1c40d0b80d0020400180d2801008000f001000083d0100ea0f01265203039042e05a500c88200d172000400725403000040b89880c0045100110400901c18a062902006118101c400410a0b10745248580d01c0a05440b83d561800c44924410740c1500c07030380340003045161810001902c2001c0d07480d0410a007205469115048650160f004020940c40614028202440314080c0301d0080359011000404d07512007144094003080080e802564140d03251b15104289500c03161580101e4214407405100400e01031103050030041190085011300c1d00076075252800b00d22145056201c0380003242d0004000c220517680d881d0101e540e20301d01c01d0b0202c04210307071200040c20500180305100304107800c038084218907a07409081102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 847895476 1250 847894226 847894277
    0x70905011d0f040e0712120807091511010f06031403070804030213110f0408011d0d030e0c0301020a0c0302210a0e030a050f07050f2211040b130e090d 66
    0x1003240c0d9413003102c0307854442000180010a0500400ca0304840b080c01c140d000740820090080900a40c5401d04c610355a00200400480f25131102407a0810b000380000c0f03030300444d075521801c90b039030034010003c111101c0c50b07010704c04907031040f01040200000a0010344e107a0041c0c100280061100b48030170809820b00b034550001040c3e03030510005114141180c03520040d04101d4010f807042c00b0103e001d202c0d00a0074410342107000c262822117502e56a290356420b9491070b413100864200360b10b42c20001035240082011003046200140207544034460318000400380c4281c18010380040c03107090414140090640e00041c5004000120300307142680c020002d075501204920000d42601c00c0c0008000442c1c41031140301e24403001200500200383c504001c000c11310242e07400d02c51049052a20903a6044002e81000c0072040140c0b0020401c01210303001c4c8240f600943d808000f800c1d400050546000250712080070a0700e00b000c01c0d404080c0c031001d0b1520747c4c44001c42213001c0401e041c214208004040d1801006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 847896726 1250 847895476 847895479
    0xa060903023f09031606090f05090f0723030103050f0105060604080a020405281b0201020a3e01020c010f020f1c0b1201020414030a0b070f1412070905011d0f 69
    0x1000782405e034962216414459103c64005040250140507024004071003c0040c502103030070801a04010003030540380e4601404d96000e0003181140c2d03102c05d60340c0078503204c040c0040c454803035102e44c1d403401c00544590f54615224803035480c1c01e000810615110782514165a094030041c0152540c56007440010900505000030014174086405c00903a401c060703061a120001d18040303850542c18092000801031011080c0559006101201e51140d00040348074003448c1c800010358054070036400020030b0042c48a01d030640b84074800030a03410420150014001081c00301c00801012000e1342c440c0040b4001c08502e444000c00400c1011040c201072504000b43c06140200021000b074403500144180c3c40423131032250350782d402150400c1a429a808101e10b401020f602030528080c650fa506500560028248805d0004448024926a2080c152441d0541401e8100717555408190103c5402c0c3e8411126500003400360080481c455115100302c038040020100010805013105081100c0c54284e1a0040d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 847897976 1250 847896726 847896733
    0x40b040303060906060c060c0509061e09060c0d1b0c14032a01031a060f0a030216060b1306031101030e0312010308070b090a0b01050906030a060903023f0903 69
    0x40f074814030034404c02005040310f40303d043d810001d03464060705495100100b41c087c01400c3c071098505803580022604100b03030a260207501071020b061600090300800400c0340d0080804240f0200c203440004241c081440d83e51501e8030001c074080f030804039070f620020004044060040c4100003a4071aa04240c908050042c2a80c4602c02c1d07800050b0b005411041d001241d0f0107080600c0b800079600f6206441071424280500d96020304100007094181c42440b50950550600103889148940320742d05403800c41c0b006d4110300284980303a08042000d4240104010301c503204100500b502c0c0c003210301c60f4504032a0701204502c0c03a139620300d00540040c1083c01e031610190000b000000214201c0100e402c3c06075101c0c10885803101c1c02410300c01c0441ea8002c1c1074000315130181e029500494006510141119000c44a030f80c034540c0c4110100342420b450400c01003c80f401c2111400c10160085003116001c03041000b003522400c00b01207002c0060b10791204141c106070600f403030b503808454480c0040128240c082d00310b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 847899226 1250 847897976 847897979
    0x4050a090506133219050c090d020102030f0f0a0f0c0f120c050102030108160f0e012705090c0415050a0512030c120c0d0302040b0313140706030e1c0206040b04030306 73
    0x3103880c1c944c040b003905990044d4040042c0d8050b004161601c003040c0d030404000901d02441203140a208220041d4800c44400c00d8420840e80708004449a0211042a050711224400d07403000e4290010403c1c00003040101c4030b02d0403128800e1844100450b000f100320030b0074414580712800c500e144185040d04000075a21004045442400114002c1c500c500c010003900030220180a802c2400f07421084035044000d80400c8000c0724111210706444009080900d4611881b0b24060448121b02c034100300700f42050100a2028404207020041140941c0c0030f010341003200284900071309040c000c4640c02068400e00740030781d00b40401e01c2000032003210100d074507044450000905d410090003c03e6005040000d0546a031981031044900c2800701d0309040d0f051608001003145130b4040100866400d440c0e541d14041407204502000f68110740d80e00545282540792400100a800a10b4145800d4130075411801540d45402c0328602500f103681d0302500440d02d45648600407840c01410a408143d05d4580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847900476 1250 847899226 847899281
    0x2191407150b040e0715020c060d0e030d060312170c0f0c01090b040b01031505040b0609040c05040606021e0c01170411041a180702070b0a0306081204050a09050613 72
    0x4c04550b00d4060740204030742d81c80d01141d1400a42030703034114001c5406c601e01480980c1c64080070350306124104c80340411490b000208052542c0918564030403c907040240000a0018a44082c00c18070070b6581c0701d00c0390014005004420b8101078802c5600c0680400100b01d1380203514028207440d1104c0c900200c1c02e0722682c0c9400703e0700c010542c0c0039209090100010410441c0e00c644010031100480014030251034980c0b600035140b00014032003800b584841001030201700400d0b44035009040000c00401c00d0030303160240259601c9450514a02010000d02c20584000000032401070041059407012450384480008807174103d809442100c050080700e0814213075607203d0003a410744510841d6130400804482c42084400d025081c60181c3d0341c003000090003915580030417004247d0382c04a0050380d4441d1001e40c104c00420881d071007009103005030224442090000f0000b00f04a403002c0b540010076503220302c03030b40d021180f06540c0158440084040c454a0100680147c10000726543c0311342e072103404241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847901726 1250 847900476 847900481
    0x1506050627060415080919020f1201050406270c0311120d1e0f0906050f07080f03091c08070e040b0d031e02070b1b0313080102191407150b04 62
    0x1300f0440c0f5040031841e20040c101c0e4040c850075400004100100250140440c1c180680850010003a02a01c050481e41905444100301c0380700220101008110b2807030581041ca0007000c1c548404441a020b80b0001c940c0300f246c0b2101008034079007002c4c10800403840c5030350b800e05800054000c0340d0030191041c006001102c0a2050401d400019125107503800c0d402e0707030300b10102c0c80d42907030840c14803188003441d00c1e80c50b900c9960740c01603c5842c1045a600d203a000b8030710300c1e24051b0060090500900165411416940e40d014500580042046590740c81195545420b10007406c14008006905100010006403080040924032036002d4000100354000c1c80210320001d0540c2c2c0d0076030110b60f000c0d11040e01d40c52880003901c1d521400e8070141003110300b40020f42405204d840e540d140030200ea2040110514014800c07102c17481c038100251040039030743e041054080e411500043c2c04001d031164182d50382a02030820303000c0992a1122a61400030580e8462103104001c03d9540000d99840040045940351071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847902976 1250 847901726 847901729
    0x310080d0503011a070519060b0a12120207060f0503070c060207080324010504060e031e10060605030f01030221011d07080a1112010908041215060506270604 69
    0x1a5030740da0303807036041c072071000048001038080990441c030810200d40401c8010400038254102c54205582c1d0040c2401d00401600000c0e8039140d21240c266000a036500109a5041c0c5451003550f40082c3d03030303680f150140d0311483d04d4402d0b24080f44070541361f00001da1046c001164004c0c1c040c00d100e90134680a03100c0d00103c0e00260011500b00c1c41c00800c1c000510b6000303000c15101030050a800440040c5c8000091450003644110000c4c000c1c0c025581d00c8594088c424000122038101c507252000c1d002001e040c0c3d84030401587c40c4005440d140000c030300588940e084074461600061009005e902e903509000a144106102d02c01e011401c40f048480c1e0f0000780524506000e09010305990080c413180b40908102442c0c0c810303002030340401004c0b400110004221010582d044500c201c4124400090310f001d00310b0140e0040c0881c40c001008200c505001d030f40072404601402485c1200c0580c841443e0455155001d1168030000078400c1142601d0884040d194480c105990035001205e400e0100d41d40340c126 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847904226 1250 847902976 847903003
    0x91709031212281128350708070810081b13050a0b0f0d0f2d1523010e151201200a0e130e03070f06051515031008 50
    0x41550301a010f9081410001816411080d8074103e0000090f081130003110701c240c042284100565071006c145191015a444600c5040c102d905e403859004200d018201c0310300000c1b690610206055800545210080e074803034000400b105410050044065a80520010782c05600104800d0000303119014490190031590404a024207128003003145046007440400d008001600007100461248100d02c1406908440c10800d2145030300d814000212000f04204d0402100411070301c204400400b4464208030250300c104610146a8404001e0215001508000d85c031920014409542d440541e96000f141e0b40d01e000840c0312044011406103d01016040281d9540d116441e5070701940220011407681c80e0030b60076240c030207a504040c04100b6910500c1d0300035201e030150a100080c249c0d020128186036501102d881c1c803841c0c0340c00807a8081c09041294030b0340c10180810400e44241c2014040d82600401155100c03a001d64814100c0c1c000170000e030200d0360103400000d00d250042c028113510052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847905476 1250 847904226 847904261
    0x30307030207052701091503050d080103060f0b0108040b0703061a09040c111023040b240f011215060f0806031209120109170903121228 60
    0xf415041007505202003041034092061240421865004140c14505441e0b46000000340d201308072880b66486462500010460b03c1440d604403000350b0806840c5040300d20640061000c41240710240c0f007590b01d82110640400d2a00020800040c4049080b6034880b204d49400613000d580c809001041080340d00c42c40349480e50020750340800d4101801203420951990400b00101454110301641d5141e10040c203624107540d40720283c0070141e01c1000c4040001d819900c4850030304280c107001800700c1094803881c9020403c1e02c01d194411090251154200700000c01e1604004011801540d050010a4034450065034400b540d454100612000c4000740c40f850b500c0d11211080200054540d0501900161003540800901101321408804440303d001c000d0710b100904641d00c0000d0790240c6568400107000d628180000c412541e200c2001e0301480008a00300c0d0600e14241c044000103100d20754183e00317522803000000d81811115062192a80d6038243ea8074400087c9201c00d40c00c49141c8000c02c50701c0305c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847906726 1250 847905476 847905479
    0x2030d030b04231f0b1305040c09030506010923090f16050616060b040911042708070c090f02030117030307120510051306050139020609030307030207 66
    0x1064841c0800008001252015095403418915110a0014100c90880220315815995014030303054020007002c2c1e8205907038a81046e458450003140541c01030500561404800b510740610490500013141e42041c0a030446909000480011340300f4125042d0314002807101116130211101c20b62841307038240c4005020000c9000a00d43e0030048005003241c85803800810503c8141c1d40c0c0001c540d000c600b02241540200e80e00c3c5030001c040c220a40321560300910700780b0200180b1103001e20040c10310004640c10843c04081201c0c0f04148a0903034400c2481c0300010b42c460000440140060060600600c0c03240c1c2034035942c210450641e0115403044402d60b030007000400c440070a401046094508810141d070a5203014100240140e110303500013100c254644001c42c5c241c107038035501390001d000040c2103888140004440c0d40b003d020584109070000b0085101c102c030a4041c1010300d45078580c042800041c11440051100d03481b143c1c0817050780e000b00b0401c1091500da03030070002014050b2081c0c01501da4107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847907976 1250 847906726 847906729
    0x10318020d12090503060c0d181a0118060b07140a0804170106090204031a0612030403080711010318030809071701050a050c19083607060215010501081302030d030b 72
    0x10580e602440c00f0740d000109110045015400340e9241348e1081d440043c515074060328488642030700030310280c00d20300101210391b0b07005680c00c04941030701c9464207500b480380c190b12610750448229204a0700e20440912115001603d00c100541094074081d0031110232032801e4490264552090b8450a070440c50551900c40c1c114084c0074400050400702e40441c1403514688074141c01520804000025100b0600060a165502051043e065000e2130071251982e0316032400d2011940080400c0e0b528607000e2440c9051907100340204a41c010644c44001039008240e50b0a40d8090340141802400c0c1c085c0d40320100b041c1c12400b200c200556007400001c61a400c05070710391411660050b0181c001010104a006002000075082000d04019442d000149075201d154840403101d910005082151036070032035075440203804c0248120205010700307a981240d45c0d0b44c816030b61904001812800200c0c07410040040f50b0060082d0b5902c2091500b9420405840ea80043c1c2414039190104c40860384c1c42c010048103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847909226 1250 847907976 847907987
    0x1d160b03060a18110c0114060f011b0804050d0303091406040c0510020c061305010f080103030c030305061315080c06031512030c070f1a1206010318020d12 68
    0x82850440980c80d508140d4003040841200d40951610051403c3c0c10310540c0907190f01280503548040a0f203a1544c562083c0341d406031022030f200d200310780e980f81c010902c0c07441c002158070004d2505848224601034402c24184000105040540311040700b48000151525104548021640300e66030005015402d40b4020324a504e47e0982000e580e40507400b004005001401c0180036101c003140c0c20041005480400c03442e01031003014580c1c101801040c0e4a130442084406007007500c3e826285d119420003000b104540240007440054005080030000c10007080c0030380c2c0070340d4101c03101411001d5a40805031081041c0d0704411480360000d20404420030118000b84003c40219408943c1c16203135017443c030583d074452003001d90385501c81e2401180c1302e150071b501041140c1d5064141001c1d107074001c0ea100000400707008184601d041042c105500350201d107918101304d0302180d184102c081c88549030348004500602180c07850b0710318158407402540250f6502e4542c00d034060720031031000201c8926208000c5c0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847910476 1250 847909226 847909229
    0x1050f18100518060d080c07030507031b06230304030c050f0d091401020c06030916171c020d08060f060706020d0b04110d020702041506080f180712061d16 68
    0x2d02c0d0100c01803281300e40c0c40b0710480c0082c64014201e5603c45070841001810807009510080080c401c802002040100c402c0c4401d030304400d08521f040840c4c1d501c3c4426100380201a02003526091041c0d42d40c002c403012403000d527400038080d29220188484503610f1358940a1403224411a903441140301c20041644500b400011700010742a41c01d4159000b00040c0d0744108078030105104100c080001243c802041140c2c1e481240020b440d04641580c1d80648110f0341300300404040e040c0201d04240241d820031403010260b25403154001d010b40401c11000f2640103101402440d404441500c01003000c0d0b440d140503014043c000c41005aa421070030311030008a4001c0e8920386c0c0036504118030401200c0d00303071094039011a144a000350791a1114400075005126680144060154811000c20f005501c0200700344501000003240700a5191800c0568042040500110840d48152418007040442041010060344100b41c041103a207600c00e000000a0005101c1003100d80c003404d070084400c0c603407695800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847911726 1250 847910476 847910509
    0x503091e0102120a06060c0f05010216080d0e070605030f1e0a0608010b09060a030305180415060f0c02032d0a030f09150e0402030403020c030607030b0f06040e01050f181005 76
    0x1170540781600150901101c204064404101c00007200f00707101c0700f0740468071111b894a90103020b5042902d4645029045100314010203881e1650040785180001488801d42da810344a050071030362034001445c08280024028096003103c1040b941121042c8048240110200d900103d1540c0c2090442805c445412004070f201e00e004a0a0101e1750701c84041c0507090343e4151815550718031190300b160b50000010310103c1d0700306140501121a180c3e420307000318217440895860f030241c002074544c00c48080401301e6021f90325400804404031334610404440030038880a546540c0f081141c0840c180c240f002c2000c050780403c00ca0140d54940d036074081250009000b559054002040382600010880d86d2a40b00c814022940000481d0031315000300036040d40b40100600710b868918000300700a02500d52440c0b864000e01020504422524014068030203485001d000c0b64400e03072170320041200b114200b804154000c000700c941c0e003903004003045020344601006e600801c0254600002c0c4542030207521000d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847912976 1250 847911726 847911731
    0x20901020a240b0f100c231507081b0306030109021309170c070608041a07090f050103020c06061e0d20010e01020c010f03060f080609010b0d0209070503091e0102120a 73
    0x16503030760303400e6118801703509481d0100b58503003103203411b0190301c2c8003542d4840642c84228094202650004d8031155204c0d9048041c0c00f07645801e0310580d10f200080c0c1d000a82d001c0c1964649804c00c000c840a181e000c00001c1c008200c0c4c85440e008616610f80301b44401c8410343c2c40f01c0a10341405981c03010000145a0341c21403c1c079245030302d61034544580441c0200c0f010401d550000c03d0a000028000e401c02ca0040819002c0034201080060464001c9105002c006019068006180d40c00713071082d500003500e02c0c1c02401680d910102082135080d250b25170640c620103000d40f0700b40f1944814240114071442070401c540d1101240c010b801e03107040d181007407504005440c402000580d9010410b403d11400c203080c0b03100c10b250541c000b82e014001641020702e10101c1d004001400590020f03005c0c1c0100141707802080795901e5482806244030f05208d02030f401498200102c2c017001c0c41140210f03032056418007921a001009200c04000c0030b80c0601c2440f0310ba4002c40c07841d42c0499440d604c030343c0110082804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847914226 1250 847912976 847912999
    0x70c06080c030a020a0507120e0907050405010c0308100306063206071e060509010605011101110a0c0302010b0a0e01060e0904050d200106030f0b011406040504020901020a240b 77
    0x40500c648401802200141d40214410f0081d074040c5041c0c640c01d40e0702848000c108c48040c9030003400c58035416a060300c540484000b050742c2a004104503819101e041e550068810300ca81c0b0240d820718030141140c94400c1c10418000701142c254824203028010841e01965403000c4ad151441c074110040381a0525540c07000c5044d4180d51310401260201c1d0b40c1310310800c04c012540c07141445800701c9204040c2c0140e00740001c110b09410103610140585400b6251041450320b042169400c0310031600f5142a540c404200311002c42d4000d001c0403192070b101b44004a8540a000041265103240754414a00da0380844014002640c010329640400a0159401c0425240c04d40b1410b40d141789103649101400198802a0082540c2e1001c10041619181c0203001c000c0e601c1ca0286042d1090342001e44031034603200008910503075203815494581d0002040d076806c0c5410a80dc0000070b41c0202c102c5030551080c2980d00300083c205200b075107220000480303101d5100c00f0441280c000c4d100100c000c1407055078050358 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847915476 1250 847914226 847914241
    0x1080a0c0b041203111e070825091d0f0706080a0e10020906070b010b031b07170306040603120c0213020a200f060a09110f090f09070b070503070c0608 66
    0x443c0c140c25a01460159401114001d080742001d4001150124031b084440100c00d82440c00243c070340480d200130003140c00960404001081038082961046601c0b291130004224000c260b4000c0c07000c005902c103102d10b10540b0000e12615041401140b140b0fa60010901001300380d40003188503a105402000a008022540761030a459140314031544510310381c08505d400f082d40f02c10041d14400c580c00880c0c1c0f04196100c0740038000c250401c0740d00c0c034010203018041c4010a01d20000b81c40355283e20415541811080e80c2000006800003403d240c0c000340d8070b100000219420702c0c103048400700c1c4e03a20f0319403508115006106c10003481ca5903c041c0e06004116241c00180e00c90780f400030001c0c0c3e03034102c0702e50200190081400d00c8480a52804540700701c07001d001c440c84941e440783d003201d1300c1040c80c070034001d201c1414040c51008207107d5591007281100002d10802c41d031030301ca0b42d0061121044e2600141c46407003100164200a60603a00b5a0001c1120020804c02120503006000d40c0d040001d02882c0440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847916726 1250 847915476 847915499
    0x911060901120e070510020609060109060e13170a180902180d150204230a0b040e3103030e0f1f09120804021f0e0f011701080a0c0b04 59
    0x40c20748482c0340d03540f0700c1050424018030180010300001002d401424040d00002956800f05480d140400c0c083c0c032000140c80c00e001e103c0e4404480102c005a2202d540c3c04214000c08680c10205490348200c1c080340106124080d030050047d400aa154034035100640c0102d103061805c1c980040b04040d104110b41036201402440003110702d28101d5407102010b034180350020b0100028140c86240380c1c00400c0118801e4100e5481a2000741840310040b1303019080010411701b50711134441c0c0c2e150528208818001e460304030a11607401004698106c0d01c0004100001449000040000c0300d03c0b12a0b41c0180308160381402203030000c4002000500140c4104118907846044290702307006400f10a10f092040311403990008004150030440500a421000314081d19403402103404078031900e04220074900d00c007502e40d48400d900a42e0b50312503a00b07002c410305000300c00041c04611414006802100c44042000024007030280a0080c0078000045980ca031540c59484203800440c407651041c8403e1014a4426 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847917976 1250 847916726 847916747
    0x6090b090c120616020a020411031603180305090f10051e1e130e07020a030e030a17032703130f14090a1113080f01111c060503100911060901 62
    0x2007400750565110307031300d09074904419002c0080d00241468001c038120501070300507620900750a01c240480d181030f5801102100d8610300000c40804200c031a0a000c00d100e64043c050095014103050f00a000c04400610b1a41400181740e0020b4000030342240a2983c400403040200385041009040904640b0380d270300700c41c00c030342c064412081001c030b00c1c0c40203201c0f40384080d001419240841621800d104200030748a0001285c00da020804507442c160060400050914000d0f07000b458548004000c40f503d140180d0000d080000702c141c0030041d0b0144451680840040c0b5803e400081d0360380c00d8807a00001c0750340d003d5400001c01d04448901003081004403c1c0103207906004540c0c00100f0394aa5040c0c170b00a184808100e0083c0070080382e103180c040c1e4050703403a800792164202140c0b416018080c2c42030a942c0100b400400c02d00d0107001141904001c0318035102c4d140380051700410990385800c040b0349400903007007030511195194201038060180900d1001d65401042d6882850404020000780211101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847919226 1250 847917976 847917991
    0x4080a0627080706050a1b020105040512071109040219081605060a0503010603050406020417030903010f060612091406240427020316150206060607030c02060a0c06090b090c1206 78
    0x8030340c000741c6e201040c0d40c00800801c03c040e403050803450500100a00802080b1000c4403503100340044000415500700540d8081c581c030004403005140041c00740402180d0150007241c1240841e91020400f80c03075514000d0240080c03e00510b0b0049040046600101041d448207025001c1049098003440d4041c0841c0e0644030705003404186a00c0f6498030900030700c52544443e01503c1c0c02045007030011408402401d1588044000b4480d90001641503c1200c0b154070803100070821100720401e0500c4950000d89400703006087e4127031500302c0c24a05c0c50a2200850380200200401c090700d680030780d66209907a14108085e24100700840300c1c80c5003080c0748080b1030484a02c17021503800d40021942c00304000e00c0c90034000d020582840390b403800343d00c140541c0e0041e03440c00f41c01010001111410328106961110b13805564020b000b03101a003d0125590203d03c9810410400101d00e1000c54100d018119440c0c1c41440c80854910b0b0200ca51410240840006403042803d01c00701040c1510004203950820750 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847920476 1250 847919226 847919231
    0x40201080c040e0412030b18070f0c050d0504061209030e0103270305090a090b0a03020907050c0102160204050a0b01080406151d01050405070516031404080a0627080706 74
    0x164007038071100741c0c0210ba0100540190990811040028940846511000989080c40710240141c104a03d4000002c00402844c013008000350001c0d20580d943c05c10740815080142400480d07845da1030800f6020320381c034404900c0006041096607070250f42c0c008103e2030420200200030140e603005014103410a0918101501d442107406204002000d05000c0291f100c000f0000208501c1e002d032043e0060103d95128400340c038000210004540103a03150714000801c10318403141507a003086100a009401081005024050b008180341c0920003844030700b4100340c07100385990306481004242c4500400760b85440c7c1c01c181240383c1036604590b031250030070351102c40414480c004240031060010b6907400090b10388101805447c00d4000011620b068032816501840240ea032140d003170b9020300c1050070580b028040340c0c0d00000420700c81d040201424426404e038500d040c0d80e03041e04c140f038814501800d55085658102540e1003610b00c80c00404131605012500385001d00d981c440c06101c0c000c04101406440c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847921726 1250 847920476 847920481
    0xd12030b0a0806070201050609011508010302210a050a0c06050c0c010f0509041103010e0a020708070f060612050f250905040609020409080a0f05070209061c050102040b0c100b060304020108 83
    0x684889003030018242c0c0310200e40003440c00344402030180409840c5203008960100010841c130000000740122a080c41c1c40c1c640d00750740303035600380724100000800c00326006494000c00c460004050108001c1c1c24029001171508034124284021000d119502010a105041001c60904000401c0090301d0329000d00300301210959000d4141d0f00c0d40f05120007150311600d021a0410503540c00700281d41610303404460400150342c2c80900204078411000c01500020b003d010040000e078040f0141d9102602c205400f188071640c4281512200c2e40024007143c16400c503d4610040391000c100790b8900c2610030002000a03501c0d81008400a405030158240d803e803a18001070910003075401c5000a254040e01c10801c0503d41d0600100c0b5802100c2e081d00081e07584099030501e030b407280083d80c580139001000f9500702c0e11800c003004100c000c0200c80c090b0b0130851204c1000850020303c0603000501a0170840b40e175030346071303403041500f4a140300402e100e0152420390940c07016103600b0f0640b07070300550a092084698 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847922976 1250 847921726 847921729
    0x501050307020a0c1712071109091c031a1801061d13020c1501030b060409210e030c03070e0c090a0915060e0933060304060e0c0d12030b 60
    0x3c0c0c1c542c01e010f020b45030080710001e004d07402054500031201d201c80c19154540b04030320081d00c4501c101d0301c0140c14980160310582d1246000703e80c494014402c94111150074400024101012007040403400101c2d6482040e141c840e07800054031080c098040368a0020a40c0040d2180c0c600702042c000c400030001032425a08840d80090034640d042c0300e000f0a407143e41d11902018401039400700400109500132141a80b007001041d07062107040e41c1c1d000310810b1940d650740042c0402411010710a94070f4242c6400540b201c4521140101110004c580d034107180c00782e882040c10706d01a00c820319240241c2c00550b08000031003540150301c1d040444580c1032a03661017540700242040174940c00440d295031400458040d540302001421b0700300c0d109074450445e400f5a00c0f0801c650b2400896220350a102c0441c840c404c0e80342100c01d41a06494090b070580310705503544010400f0383d003046404640c40355546051583e030703c004004c80017501da412030326081c06c594281d0b24140003071035040031181416128171010740d20317 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847924226 1250 847922976 847922983
    0x30619022106180c160f0b040c050f0a03020303031305070302130f0612050c0108040201140c0f15040f11030c04021c0b041b0815220c0f09050105030702 67
    0x800607038004601c0d45a1040050141008203442142c451a6140c8940c0c084401e15840b1911900c0d94032049400c010301c42c081c41d2130a10300e42004440440e055140000042c0741c11515034007407801344260442490500080c400103c1003615018030400e007804003000142d800004070380d802450410a030002c0718191030424503000d17250700000d41c480003c104002c100c5026034401c14402e07641410038003400d56125418840d6001040300030f1701642050b443c58000754029405260814418503003031460110004000c1d05a801417240c50f403980c0c0007040c6042c1066402c00842d148000c03001c0c0d01c4040c0e400c1c29518001c20880c150402000714040c400300c108140d4080c400401c44e600007400c155550380018405030840034400005500c0705140101d04240b0303042c540f05a104e81440c200707060008054142c0c050364111001001030191031070a40d0508516110340080c001a007445000c0680c9425100003a5810741b0034003105038040040c0f00d101d00311915030100041c1e00715082800c00966940795224102e06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847925476 1250 847924226 847924237
    0x160f05010e150a082a030402091b21160e090901020403080d0609051f09020c2a01092c06030109020a06110f03130b0319060602070609090b03061902 65
    0x1c20600801c040f0212900401342c1403007031084000f5046900c0c0401d002c894950f0440604003460132050001a0050610103201a0003403d21011400268403a0194000c2640402e003005002e8460141c881140800c0020258104100e0300780b81606959000300200b0f8443e00d070000030b1144580c2c0d004202000303001c0d4100c0740a181c00c900380b10354a0714002e54290103800303540701c0c0c065960b01d002d001406004d0300c2103034071010a810780244000545042c80b840080d4000c440030b00b105001c9e40840b401400400118002001d075a0ba21484200b4070410024140c4410341d80f00d940006d045048841d0301111440000c070b030458802903040390b951603142c0031a005224961000350001c04034007010610a030040c851001c1c0d50a903c0c1181c0c1000c1c43c07480390130f45a001e038451000c9804d28081007401080c0700308001c1c540c0184100e50030000c00b00c01c0005201a80c0d866800003000d60130611082c00a25406000e44001d085040c80600603060810003003907a400c17004120b559070758141f4203c0f603c0e49485070129170 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847926726 1250 847925476 847925509
    0x3140f1b0f0412110102011815140f011d2e120507030b07020a0b4b150904031d130618060e3403020903160f05010e 51
    0x42d125621808051083c90040c2d40603261480490b0300d48015610500034510400c401100348440300c2000d41c0c1300052823480382d410506042e110044814030b84009024107100b182d220744849443d500d00b0701e6040b030840d8806440035041110f00104948840010b030059511034420f540b0b5120316640b002402c15040c11034001c4d40c11141c00040da0020b01c42c00261100035039002d034840036503544071040280c0c0d8481c107040009218010744c1c00000c2840e421540f41d11032001547c1c4000314107a141c29a012035400b4015680030071040303102035015100c02d0381001c2651004c000414980724015410000b420702200400c01010498100d41c440d403460440c1d00409074041c00607011800399001140100003412036400b801169130030358600240c0085880c00b502003143c580582d83c0b24503850b522101c603c0e001140004400320901840580d403072003803074403029034041020b59005031121844400c050a000308440c103449410b00c00b071012f00c4541404c50501c000c403442420040003120703402c1302181030075102c10b4004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847927976 1250 847926726 847926757
    0xb1006050f031e0a0905070e150607060b120601060305090a030824040213031109040b0c07050111030a0603230706030f060914180604050d050d021603050a03140f1b 72
    0x1c000e000c01c4e034000f00324030342c4102d050300c1080341c44178014004400101c5070390001e44500b140d40c0545051420003882000d015600108920801d00c02040c0c4600003d01544000c2c0d100300010440240d140c0714140d0003d030007001070030b901d00140e00e00034000c0d0700c050440b2944603c64882400c9606101d440d1000c0640c000e8070641d1120003500d0400d000585620050320542a0070320030f031465150015407544078503403040100c012034640039041d02003030f00078030700440c0c141d0b584403c108410740b60507000d584240d68403e8041600e90a500e0103007101c40e55003407440c48401505e2032081c059407020500c481514400c0c038001850700c150444030406402c440d480310250f180342c9007941d003015010818035445440d45500c041074001a40080554404040b6806032054104107041c2c5203640c403a02c01403401d003108110141c01c01b891400100901f20484600300c0206600040340c0c0000d80e050b0042c035100300c6000350082e02602d8403041000394404010415032201c1d40301560706081a11b4403082c2e070320103907026080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847929226 1250 847927976 847927981
    0x80f061c140d02010e12070618170304030306050423061c081201080d090306020306010e030d0903050c041a06090307080d0306051e031e10090605040b1006050f031e 72
    0x1c26803521804515200154240000d05440302c1001560140c015800d201c114a01043c5895600082030b03008d50b2401110780c01184800800c1041c5503448501e60b10990356944e906092030060b0899030158005801035003003000682044815140e40c500c81c0d6407400003014159280e9000030341e45501107072000d805500003196201800103020183ca03a5102c0c54000910b1a40c0714600a40d482440b085031600260460b43c0a10005a058028542141040c10820420303400c20000a0400b00c038100c00800182581d041002880010007002e2170444099508100040c0c01e00c1c42180c00708a101c00c99030284000207103010258504000200c0103000300e40036250381c0d401c2040020b01614151080c5032007032486800741503983e070f00528064180c0c00c0003030050820410310301144400c1c0321204041c0c440c50003480c80040c8000f40701d0042c24002481050002040d240c5850031040c019809010403c1070140c402d010b10400d1380000c00c4504c0800440d6003261a6500e101c2b030140e44861111100804160a005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847930476 1250 847929226 847929263
    0x1091502010e0c013015060807080606090303040909080f040f0e01060513060c020301060b0316090b0307080705031f031103060a0b090106051312031806080f061c 71
    0x100d848818052070503500d15001c00e0004454050350a5840c0341c40e00790700484540c02d89060b100316569219800c4001c0303074a06522100006e1006554000c4021031209010040c80ca6480b820a941c80300c000c4030000e0504080c10086941d0f402540281d0b03056690350001ca009006035003003552200507451a00594842d115030400c01400c0c1c2034412407106852010000c10720500490030303070314510045c00c1c4601606241a5086030345041c45141a81c0656a031140030880006079401948545d2480154401c184405d03000140040103940c8103c9181c1810720501820aa2000a6036040300c520310b4120b44070740310500034031040441141304a404800d0204000300f0400b040c10b1804c01d00b00c00700c05a840c0341c1e035000b01110644581c1caa02c0307a4481c0c503800c01844114007079005449000303004082d039131000e500d5066010b2491000e80050303001c100d0104c210015103003480c11038009040c80e40340541c594201620a0b544060001d4070784c511541100603035048511407041040c042540000700508100882c54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847931726 1250 847930476 847930481
    0x309010f0201110424080f151903050601051507051c140a441f090603110a14150c0607080403020c010c0b04150e0a122307110109150201 60
    0x20400100c030380e088000364500c46c01150714521690080341c2c074120304c0d41e03500e440011003a03251007242d61052500341400a22860203042c00042c5200f04000c00c0c455040c00b0401200c00741d02c210103901002d003000520001840483e01d107010703881c006126001d41000180c2610103081c0c000c600b101c00e140208074509015400082c14200450060101d481d1044002e00400d401c0c41c2d10411000403e501e400104400c01516051940003040c51a5030800320400720501c00300c04400d521001020791146014410f00402c8502c541e40d54000b01e03480e549040c5091b4209541603006000f80d486a080a210b41c0b0824100c8800c89066480039400d40d8094a80203801501c0b42e0710a1741d0540c0103105805128516501031810034034119002003020300280c2d202c1d500e01c00c040481d548084065601c0311b04414030542d0800c020800356109006110f80d1075039880d4010402e544210045503841120001520910300100846071000e030414001490303a01e5610059442210f03551041342884081540c0c0b014266066 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847932976 1250 847931726 847931759
    0x506060f0c030712050408150603100603050a1a071202030603010615020303070806220216060903020d020d0f08070e010e060a030603021806010806010c03020c06030a06060f030e0309010f02011104 86
    0xc448219842d02c044c0c1c000c4601d8040d038081c1c002c01e90310175940082c148025080c41640b0502c014125141903130103040d81001d481c0a5401200c291740b048012204110242d00b440ca0165041c1962080300c1c58a40401401025500c500c204000e0340003000c188503031001e4014001600c00068203441566003940001d550b540210740d448001070001010413404d00e0000203c02c01804160748150039044020068802944001c040600c1c90322602280d0001800600848071000e009401602804c82070386400307820102d02c00765420801034000d196030300c3c4a0b0440019500200c0615001d001366075440c0050343c0c1000e1280400d82e0180d0041880003209038150030500540e403080d902c1a081166490115005400691325140440c02d10400144194881c074042410240a481212020407201c00415031a0344150784441007240c69800a000ea10b0b04440c4d2103034040c140303240410070f118500c85e403542c590041809580c1003020b61040120141e1003508480d8403002d050b2485503403207582e86c18804540300384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847934226 1250 847932976 847932983
    0x140f030a0801090b0a05060d021605010c20010b010807050f0c060f0a061e0b070c0b030a05060f030c030705040c14130501080915040f0303020c0d020c01090f030c090506060f0c0307 79
    0x1d1000c080c54a0505e050584211800581028107100300d004800e40070f034009d050344481701d0040d1088a00402c200340960070321035200c1d469003060801d03180311000030b9005800c8541c1081e81000400501c99a000d051f1036031100317a51419507120700c44040c0d5492117201c0e0f64011116440303101c0074441c1040c003c0c034869002d403000000400c0125511404602c4038000202d0508041304490010807801701c0d00802010300380c2c4200c0d0f0580030b05403640034030f07050368005603100100251b907072041000b203080c09001c001c0e05c2c110132801054101c0e810000690b480351680102400b80f5103d40c10912098041c0c40781c3c0b1308000d030340001c454076800110010002100240b00700f0740000c41040118500312000310340001c5502e0f025a810b041599903840d14000309404010840030194208203180700e4400510900c034684070f460307015010000c000000100f061201e500705880d48113894000b0030001c4c0320780c04100222a042e15000c122540c405c00020b2780c60103038800301001520001281c950306480800284100c80c40f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847935476 1250 847934226 847934231
    0x30a06080613172a06060a0b070809130b0d2a0803160f02060324120c011d06031003030f031a040b0a0b16150c020703140f030a080109 59
    0x503002810450041c903020301502070801d0020404142c42c031400100848200d8460b1011913110040b10f02d0440448400c001d08581c100105005080c0b8001100790010048056040d080230f8240d00c450a41c1d11a03040d003103220307001c80840451a69520b8100c00820280100a900c3c1c15102d800e00c0306034640203a1541022441828200f402e00081a41d22002c1c1e840d148021414055141c2c07003c1c00030b05801c08103a0360a540700c007900d00107079146001148140c004ca0004031071443c4003034142d40fa10841c10201880b560409046080790b540014020940f64000d191055004c0c07003a03540c1e81c0171100c0039880705400c142c00104100c510402007071000100c85c0b00b0385d54510315450141c022002c450781040380024804451310501e0740351629410100c0d0341000104022031495550110b660303250f016590302c0c210310101c842d2040921600141140c5600c0e034030b020030b0118900c202c42c000d440c0c40d407501008000304000345030350300c100100700300c240140c0c02d03280100da07039407100144080e021800911500840a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847936726 1250 847935476 847935481
    0x9240b0102010e031218010e070603020a020d020703080d1503021c03110109030807140d060618060306051f1110270f03031a03011404060501171b04020f030a060806 72
    0x3d0001003110500700144a5000c034541b150b1400407140070002012424030764850008074500704042c400074000302110f0700c0041e507032000e002000c0e08000c044071401045d9004a142040480c0c42a412100c5080602c0f000050095101010341502d554542003c0c0d040494490014180d8400524a070322150003612240304504028048a00740c40481200400240140021400c11030042c5400d0110b18241034145040050000030ba078122086a80704100103800d01c4c0002e11001103150013540502050700d4180869410070000c60704804840a507450000c0720080c0003202d040c80340450240d20b0425506580e440c01b11400860040e01030414051560114090182c22541d442000c0c900711690040c004100342d15240c44c1903006000b92160000080180d811180c500d41d400c1c441d071840c48801d4058000b00d4200380c01d00340100c500581040484d241c0556401c00e171400005103800b54800380c602100c1c1d490f0141c0303001c07030007a0080c0d4150f075442101c01700520455101c030303800000c15200d075082194000d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847937976 1250 847936726 847936751
    0x200a2109081605010c0303060504180201030515150f070f030e091005100c110a09140108030f0d050a060504060e090d05030c121008070807150903110409240b010201 72
    0x404000303421074030146403034500700f1036940254100c4803510b00a00f03001550130360b030f80c0104055940b20041c034a40302d1418031040d1300710740e00342c4035181c0c0142084200d1100c1c1c142050108800c1d40a84004d02d04650011070074001104003a03044907051644840f0701112803100b403501414000354601514810054080062104a0441c642000b2103100501c0d1302103003515034805a540c81c20400d000d903000500242b030001b141d103449141c0001041401c00000d65084109070340910ac40c010f8020265a0b001040a1210021150156100b0292890001a868450031045e40080250f5030115411500340000040c44072080840144510b200f081a540b90340c40742c2d0011521307880203d82c4e103841c0b4601801111201107802c4481c50340300004880407001981c950200710710341075070390348044a02e500ca4607003030041e00b401d011030615004950030000a45400c617622120746460740c801c424042e0303544040100c28003c80e990a84401c50750418554022542c65021030060b000b01c0d00d20368050340c00d024000a01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847939226 1250 847937976 847937983
    0x20a05010c03021809130501020301080d0305360709090f050f0c060f091507050a020114040e070f0e19050a0b04050f150d0204080d080f07200a210908 66
    0x44c24580e02e1282c00f8401e051042001000c406082407108610300c503c4c140004401744011070180c403c0d40c00802c030013640e00740010f040c1d440007050800721952010031a03080358420100b0910800002c0300c1900c3300405113424038070340040c541c000810541410101400d1180350183c60075500c8c02281034842e90354883d14007554902496043d0780d00040c0402c912280d0501e05809828550001403030a501480010702c82c21381a00282c0090380c0a400400a20003103607003007401d20325040b0910b00454109846d043e60185403800040c041e00c1031002007840d8040340f5100c0c580709031200c203009095000c0d0f40008002d1000340c01240c02198003d0019a002003600b01224050390103c5074005d040300a88000c03c0240004080300f821035000c0210184400c0c2e00820312800500040c2100000800441c0c151040040c40000f0141c103c2d010961480c0906c448103500002416008040e0b89240700441c07010110603280103203408010300540d034401601a040080c500d42c44100c0a0b03c0d43e40d00d21032a0f120b007082c58a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847940476 1250 847939226 847939237
    0x3030f010b0f120c0c0c0a0303052d0c0604140106080709021602120d1202030405151015030633080a021b031b0607020c060f040f06020a05010c0302 65
    0x104048100401004500c0402000341e110703940b010300d0410341090000d01c0a4841a640801030800206003500210420002044414000c84d0550000f070310f55100a09180708064208d650f0700d820217a920420885441030102d81e0440d0140c040c0c0e1840000e02c03540d04d503c2c09640c2142c200846140d003074005401400b849041e50f00301c2001d400850b141262400095000340012003508501803e03441c00b60780c0d178050500507000e188001d025040c0740100002c100940030341c42c0300c075502c1c418010301001c02c1d40080c00300034001d0401c2c26514292030b20940c01c1d01941840d4411034a514080c0b80070015503034180c20500858503500760b0128400e1801c410f59440d409204035003149000000c11400b072561140c0318550304030b005000010316120011034a0300441142c2c1507050155440003030350b0b410310050042110544104880501800d06003520000d403618400844903200c1c88010505d4000421110219001403480300c00000c41c1e16a51170303000e5103c00400c4020340d4030354a40680c1c002ca150090084a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847941726 1250 847940476 847940491
    0x414160f03051b18041514041a270901020705010e03070209040305030a0b0d12080709080709020d0e0709060f0909050303010e0705130303120f0b0a050f0102030c0109230303 76
    0x85070b40301c040f1411241d81010080c4518601441c0000700c240d1104c0c0709820f1082c0c00b40340d01c4a0b04504080481002d0b405c5503070b40ca07006600d08025000414200092030314039a1086412540804d5005c030580c410700f101c010344200e140404028000d01010540c0103055651003140240440c044501409440b40140240a03422415100014000038030074002580d0140e0611000240114030b0740100d445038400010445420b64046000ca004603007003010320390b000c52030b03141c075110744c80c01d0001c019140c2006110380b000c115004030744500000300c507400a9003103034800b81c00c440100baa0341e4200d10180c00305200340100c4621030500800c1c140d0341c500900509580120042d0318503480c00b80078000700f02005000784200b05040c0b000c0300020402005250003940203036102216000c0031848071040325100f244c0781207201d250600c44615070321040a01b600719103084802800c2c265074400140e0a52251855002c006c4d440d0910f8081003110f424400c552130a0504040c00c1141c16802080b983c070b00c0141c030f106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847942976 1250 847941726 847941751
    0xc04090209070c0f0c06030609050c130905090a021203040609171b0d0218100902041805060114030103151b0819060b180f0f090a05060414160f0305 65
    0x703403085005205048500f03204200c5500500350b0751300c5d40003585a154202c0390000b510f90104115000b254081ca42e0801c454426291828004143c40840c0b541a445910705440e201c0c400101c4840301400b003100c105402a10f80b18110741130072502a00c076403060140c480490b01c070850208220041900c00400c441c071520041030300b00341c0000301c05445904203500d580c0c0f1201d102e056800680303408000e490406040d00c01d903c820300740392090701030030344454000c0b8002d00d04c148002c00031989680c520750f8403682140c1d00017a80b603c41d80c00488005841c44250041d80000000010400c08e4a0ba0b00211000c5507060810014845030220005440f0394130250b030000c0d900710003040c039030010004046880b603003040c40003c01c642c0c2c642c0404030701d40008041d10300203150062118914140307640c600086110455110001130704800001c2c0303420f2005450100f5a07655540080c0454903241e22a50350384030f603491400f41a140015144501113180e90602000800724014100300358000e0096038021010091075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847944226 1250 847942976 847942981
    0x10050702210c0619080108030c121b0f070306050109091208150a2c0708130f020a0315150303020606130207201f02030712030e16080c04090209 63
    0x1ea014800a40d0107100709400782000301c110b65640d103001001c01c1422110050425108040f010701100b10580c00300803640c208100d402c98103e0080b44445001548820381c9484000703440703410b26803044201191100340701303501265040078030000d101400c0703d1252200f0f000b075070f88403840e45c402e42e52607220062001c860680200a9507016038400c0b90702040c003043e04e012130905032000502c55181c5a001e0103414104506020306a924201200c180651080c0c80f07440a0a00d620f00034a030903402030070748200801d001d086c007040060842c4440704130b540040114905548031f0810f043c030340b0024184080204e18000070034001c2e080da0400102140d03055009810b0b9a60f44005000c00c441d08011201030081e030030064030700024038252400f82e4180b6804010100c003e40441403000b40031a000380d020030300c03100f40180981a50700008494480744d0007484500c0d0024250015006000c1c00410b104a41c001c48084102c8444c401007064101c070f8100086481d59480c0300140012906c0144000c2d400a640000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847945476 1250 847944226 847944259
    0x1909030507060c0512010f050a090509070501030c0908030f031632070f0506010e090a05072c0a0c1806050d090c030b010608040506070f0e0d11041a10050702 69
    0x7144100d0301081c18668608092143e011039541001d81105900c40d803001f00c240b00070308000203070001401c0741800800407418100b030543c1da980d03a00e214050400d510b900c60207110a2203030558400910f5900d08032922881c205800b05c056030800c0b1343d940c1c000302c0180e00b000f181e90700c255111180c0003111040400304180b0b800d6809100d40104400c030680c80d03010040340001079550b20721400d400340510003815155040c400180003046003c0c2c1000c81c6640722007503250200d035010680e642158880302d103006288403039208085c403610500a8624115083e2420481014451341244c45c080b601a65105104502030f443e54054400d58010a00040c00070702013800c3c2c03c0d03400c1d8002069140180d0400d40010740d00e942e1400604002d070417500000f8030f9035043c0030800c2010820340740c0007101414119064054040b00801001100500500c68102a03503841e083c00302c69080300c3e4030028058014446c039940d03c2460b4401c00340001e0442d001e15108030102400c3d5205000740c0d0f40b21540284042c0d48404401c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847946726 1250 847945476 847945481
    0x311062d061203040801020c0706080603030a0318061802090f072a06050103051510060e0f04150b120a02030f010b0d0e01090c1d0606031602070b040608190903050706 73
    0xa140c55008000c03080e00d0a002c0030108081c00060400c0400940e5a03800c0c2c01265003421070a5000006010361070040c025156400310507181100300030302d80003942014004022040d1104000301030000d501d030081e0724403980d41b400d4500c65140d0007500c0010f070a482d0713810b04004404003202c501001510506401d00031403801c0708042010200a91401603c009035280d8908803642a4400c81c0c40364000224504601d0780c001c0c030580d01030303510210040081e1a1590103001964510368181c840d5540395a07841c8180d8465000909000303148007203c00300f0361901820b50a1b0751009407100d00c44141500040c803280c009000b02c0c4e1003103400d20040c80c0f41c0d034a8405030150b1900440b030012201d03611044025401d40c000d10030b40424901501c1c1484a5906c1c10713484980040701d00c0008020a907207001007102c1512140222a00301480c0b28840c1814840e0000403418006946c00c0711005d2000040d0001e41c940e1b100c843c2ca80605030908030002d0a542e02d460103011034000f10300060110b0341c28005c0d4401302c0c1d0940d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847947976 1250 847946726 847946731
    0xf061603020307051c11211c050106020318030f120309121204110409030e15040305030403050a050d020706090504020f040801050a06080d02010b0105040302090606090d0311062d 78
    0x90040b41c0c103015040ea00da5040c80307070155070040c078043e260340c90000c00c0e94841030680c80700b0342c041d014000304480001c283c25040c02910095201c440d00050801c645a6a1190344410b5140e82104100e2940c42e000d00030344990000e480755840c0541c1000d00044c5107804074019042504050080c0b26000d44070030115000c1e00700030981d02c4a400303030456040c108200f410050001080200c00350080b880d06160810034042030510f903500951600458000080c0c0050300c1c6c0f82c54400845041c04d6012082020345d11501c6241c000801e039000204000041180001303039664824421801c1e61520b12020f40e0403640c0c0ca12606c074640015440c80d804000700d003043e0b070040054680e4aa48145040d4903041914259041543d694808a5550703108101210307003480240081c90306440203003c0344082c0710000b08140503c0c00060f1080e142c66000c16816540c0200f150090000601218500f8426060142045058003a442a14050480081c00d40546488008204078100d1086140003d0381c0d9501c11300780760300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847949226 1250 847947976 847947983
    0x5040c0b180d1b0e01030308010f060509121e03090406050d1203111209060f070518012d09031407030b0f0621070f140a030f0f15060501030b0f0616 65
    0x1c0a01400c5a10803a00c0c3c8801401c1d003190440041d51461030020043e5005078400760030000566001d00c01107600c01c0440e0012407044484a4112091240090800c0c0755440141c03804101c0358000c0620000110160283c0001240c0c20410140c1d1201884541504640c0040c0303032810521008107618029408100c4050040c14070340e003001e415508a000d010700c242c9055489501c0507042000c03201c0c00000da036900590038600702d410b00b0702c1c44190010071708007980194181b004110801801c0b41390b680d40c1c940b0301d0810101d100d141c01c0098902600124050005503511060388913011b0002ca000901341003104e600510034030b601e550300b10003401c0d0a500508031036400485032000c502c0c0121070a6004076502c2000b005460030711303d0070341000d4072059940d11001c1c4041075110002c51645e20940904105c1750001410b0f96410581c0ca045054007481c81c80040c9081d1400e1107941e81d02c1406c0d407141d02904c60a880070410710703417414100b0004801d60700e40305901602c2000018200c8a4030203032000e500e0311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847950476 1250 847949226 847949243
    0x20a080708130209040609111e01050912060f06030d020d020c060304060e0d0509131a090403020f030a030c0305010605031003200618010201150f0b0a05040902070605040c0b180d 78
    0x40d6000400c40e41003a40c0a4035047c2e1612200000d01c0a4404141e400c800c0488500d1000c5212100341c22181c4043c02c03105040c000003041042043d2554104524164040300658031149002c07014900a1001610880d0183c4a11214102910300010300c84910300c4481c1c0041c090f901881b41000880c2d400100110b400b80c0e140d010001c0d40400c1000580600816911070b161140c1201080c010300794102e07517003510103608065100e090020b000e591210302181c10b4900000556440c02c1c08d0303141008006000c043c5100005a0b2509140c2c142e210224081107580c051080ba40d0742c8008407410302058501d984a4034208c002007001030002c94024a1484083e1001d804803800c440004920360044444100318403c480c100d803900d9a03080c45840061010004034060f01030810000540c2da03541d40c041c4c2c00307414800140c4190080c0c082e206881c0145003041c010740d41c800040c60041c0c080e1000f9541218451811000468415003010a0707901140400004008001d81082040008840301d40d06849110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847951726 1250 847950476 847950511
    0xc030604020403021002011a0f0607060902010e0d12030c050301260c0303180901050904051e1207050d2c130f110a02060c0a08060103050402010908011a040f020a080708 74
    0x2264100285c2d04440d0a400020f0440260305416402c2c9040540c003030b100f4449961004c201d41d540300181d4465035001900040c07403c44c01d100503140030200002d69944552402d80d600700700202d25465203000501ca42e01448186003a4209451038042030041c070729010001c0707a1001000d00000390a018498903002200d90108950020909580c4010b83d940212044031850904a0528548050040030141c410180d10700e426114035846804040111400300403e074618042410108102c0081c00c0c4040716450341c03003005281a135a10f01d030140e148008608144011b88541c40e400b101e01202410040e0105d40403000340040002d090712440443d0b403041d03921000702c2c00c0444103100b180710070540500c1c04d582d5801301400117031402000a0011181010400c8600c2c07081d680301c2c0b0031607023001081c20086001d0b210303880103070303031019032604040c040358640003042c0072044181200d2906054240c500300041150000c140c01644242c0101c0d101050551005c43e078001d00c141f41456005000d1452841c050303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847952976 1250 847951726 847951729
    0x40803100902030c072325030519020f030d230f0408010926271005130e011d06030319030501050406060806090402041a06040906031103150c03060402040302 69
    0x20703081520003110b64940400c5c07a000b0003995840c1304800301079861200409100d070305c1c20255150001c0d1080c0c100340c56a911601c5280c04455607400145038040103681851991074404000b51305605003d034803070550303840403100b541804100e4403928400f541c0c582c0044140c0701040003410740c6005090a85030b104000054242d02d10700b01138000350520340008245400b44d410700c2c80f840c02650081e40c0103810107501c2091a0450501201c0c0018401c00305100b5940d0720701814603507921021030540d001084503100e02c11840c0d00000501910902d4103040210b10303202c066400d660350f024002c0c0c46421818114419500c0701c50101c166003e01d000302100e01d4400c010650212122440b0711410100391100700502503440c041c0900000b40002c1d00d081e44551402e10005101c01e200030304080e0280e6a1030170000880a50245034603403105010300380d43d80e295613800340c0c8402042a403005454282c101c0900844515001c503038842ca018010024201e60f407128075421460741c3c0050700aa41c081c0d404c10002005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847954226 1250 847952976 847952981
    0x5190902030705400e04020d020d060f0e010c030b030a082d120609040f24020c0c0a05090402280510110d02010c020d0c020d051519060302090408031009 67
    0x41c1407003044c0e000b071130410030480c1d01c40803078140c001d503401c0140380041480a00544071282e540309804a03070b00320fa0040300340040384148103c048003030000c90404134861320708000d540000c01030300306a50007007007807030804401241204c403080d801c00d52542000c4407080102e454100540b483c4210986420151046039008540320901ca10b00100c0d41c510214844640305003800c0b009500100079280e00da05c524240c0c0c0da5a10b0341c0009500100700140b0403030062121304148185244801800c0002c564842c42800b00c503907a0804204046e00c40d01900e1400324141c180040ca07075010300c1d070180030810401c0f823424001500500000314a28401c10511000401d5640d60907610700f038005940328002c1c007606004000f401c2a120410304130070b42e03050400c0d01104d203078009010086001e8034545041c01414610009103050004400074080c2c0c0b01704103032040c02414041ca228011080d0501200d185050040c0360000c2d035442e880042c0d80702c0036990000c0c1c0416a103000560384a1898200540c61585a18503c004c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847955476 1250 847954226 847954267
    0x12120702131805010e2107050c060d06090506032116020d0c03030e121f0b0a031b1403070302010c020d0203060109061706011a0a0c060c020309010905190902030705 72
    0x240416142d0384001800000e11421800b29401405418507039801c011203c403c01d0103089441c145040050340c5c0e4207010702030142981003c00141a15a64a0703a0444280541114000c0800711407a00001c00c19524000800603602c0c0703844600d9030f10309042c11045e07040e19040340750b01c030740d0340380031588182c0040c0c1c0c0b0511500d2041e48600aa04019402c45c10010041c03100a42600d0003a44a40c0c2030400540c00040d205802c0c2a1480304240c0e80814014082c000c0c0021076162600940258008001c201c1b0062807400d01490300c410300800b103030f950b20f10444a141311204054268200350800e0000d94428090090010b00151440d103082d00140d001c40d02c0c06509038810030302250340760b0042c05413003c4403048014000541000745a0365040c031210401040c10b1341c05e603800d00180002e281603c14000e46140541942110040110580b1400c000e0b4480d44885001ca000078443c0f1404501407a1400445550085103a0a0356419080c940024001d5001030042c04c2400400d002605141072503165102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847956726 1250 847955476 847955501
    0x109090c03050a0b09040b0f060a08190317010b0409023403020609010b01022a12030301181107200303040f080c030102160f020d06020a02010b0f1212070213 69
    0x141841c283d008070302200d820300c80051060706044188804030b1050700e881608400784d818149010388990700028074280695200140034082d00800740040d600015075034003458001d41303e1044001801e0f181a00ca001c0900600500715402c2c4000d001006a035406440321080b10280450904d052000918800c01030f10100d50004400304a00020158140070480d00125820000d0144d80401e10010f510f9014160944035108100020310001c0603001628203005a805000706601c2d114045500b03031a9842402404c460064140403c0950051407240095985540c107000381400360a99980480303608031900a4080308001d0040c0c9010380d42440204020003401c8007100f07000d0f240c00d60150408044804642c4070303074030500001d80d40b09490309401351041c2e03203c04410841c00c41840021041c0384899809007a2520201e039503504103405500c00c0110883c1299008200030500e4100f1642c00d0300e06800c158070341c01c00b01d10b90f10028211000703040ca082c4010500c03140b5824052464044984050010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847957976 1250 847956726 847956731
    0x60504020d0b010e010302030126032101090506060702060a03020c1e2a10140c010212010302010e0411040605070606090203040b011802070201051e0706150f0b0408060c090109090c03 80
    0x7600e10340c1c00407601204c5507400e0a06505540c5040d1544400442c900c1d035002c210071711400d10303900324402403040345c0003c000100c820700e0220064040050181c406d00038030020510745004a49240380034000e54591a90081130985840c501842c210060b4200c2d0011100512400d521080721320280d503500e0348580e42d183c0081605205002001c0c0b181e410300c0d20059182c0401d4a81c0100c1c5032030784241e1510a5401d03091406c10302c104c44002804500c2205e6640303005500c00b099407401c1d05034486007641200d0007661055040c912440401040303c0b5002c3c900544c18604002c20090207000d640a08840c0f809090000385480e5034031100b41c03d80c0c2c4101d60480b01400c41800602528004c480c0c12035000c40b410b0000c60810f00e40f540007a0440c415100003000c1c884d2080251340c20404500103d800c0250b0007001400750308040c0f00020001c20460042e03210346840e804021505500c00410b5504036a0302900604040c0c550f50b40710092030380302e42d801c1810844e503007001243c030f2803040c01070188026195500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847959226 1250 847957976 847957991
    0xf03080a0c030905030706020a0c06062603030712051308281416020409051504020f0609030a080304020109150f03060609030b07081f03051e0105040f15060504020d 72
    0x52900319045074100300c0601d8501103107203010640003c1a1044543d0020300145e0ba042c0c1c807401500d011311003400084c803890030304034089616440f92188801504c1010010740c10041c240140c2a207a0100720b40ca480014204c24649126000c0da800040d04403015030420f901110f65619011031355801900312142005400c0030394440ca042d080d10a65a050a52410f1110344000d50f2500d14180300c0e108402c500b2038045003c80d170665442d0ba11205400d80d1100c00c580d00540f2035410094008411103080c2d1207104000d08004582c107021084031404040100903100d844003941e1010302641019005a0400091010114185980e401d5042012055440302100b401448600805440315074200104110754034a00708001070a50014030707040241030504005983d1803414041c440030051141601030504d2080004c1444004500d1050b22510b4003080080d014503040d2f00c5003601c400b42c03001003807013a42001c01c1011804040c0e0101008801400114084d5550b000003404c2e80c01011020410965440c0b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847960476 1250 847959226 847959241
    0x31c051927111f020a2619020d0e0d0f08070b10150302130b1806030c040311120303180a0b15040c11030a1202040306022a010e1906090f0308 62
    0x18090911021041c030344410383d0701640000e450f2062904010400307400140f00500f01e000400005003a006800300e455120b020f0404980c0c6101200c502d40b8001d40140c0c203081e109588281c82c00c06450740050201786c036507011550344e009a085482d80c06e540401c018062040014003032070b05c150140c40c10761a151401406c2c00307141807a021214a48030b00b858410803c103641510140b80007401c80d002440a20b0311404005401090604110116507110b08000200f01401d560135000d0425a07004442004480d02ea200910400f54101102827040d54024400100070300b03191100d0000d584a100260f44003111150703202e1100c88420782d103011000300c3e940b202d004c850416101d412550303606413818841240c60041e50980328442c143d1400c0c02c00c0280e445107800d614140d01250300450740f000c8115503603038659903075000c100500c20001c00803c4080003288201c02c6c05000e401030b5011200c000c3c0038040b00b40031003102144024001200d000c1c0c1c036000d8072800300e114a01591002c50007500c0d8688141303420308 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847961726 1250 847960476 847960489
    0x80c070e0709030308090a020a03030302030a0b0d0f06110418140c090d030e190f050301110c12090d060e0a03080105010309030203120a0b090405031c05192711 70
    0x411012210a90900700070070260301560690031650103082540707030b98607100825801c00030501c0020307400680d040c0d4004101507241c1d00451042d1100f22080040291040030024840500e06018018400e028038030340c0820703200e40c40004034440440c0c1407850250380744030110040000c00303070120141d40c0e0317803440c68424000c000a0300e500c1a152403240707140c01100800209a00c20003c0702030100501040e100e401c0ea01c0c1c0405086c0c0344103414000c001800d51b203980181d41c070320141c01018021750134441041403400320b440c1030325040710b40c203400b5000b407401c4078a1440751604141e520b90703032203030400303400701c02141140c4115060f0b0704070480900340c2c9410500f00a44000d0301a4000e1b810589025610008280c0c00f000740d030352101c895100000309843e1020301a000d4101c101d42c0036404440d120600c4100480000180f200418642d0100b45044850707440d102100d6045032982d80500c1015000450424207522410342c15400100c0340c000c0c15003510001c02c2030680c80320b00f114502c4020a00d03c080703103000c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847962976 1250 847961726 847961729
    0x20c0a141c210507260912042d0e090a021207120602180916030c080c07080a110714031e030f0a0207050d08030a15062019080c07 57
    0x6040403000c0c100d40b402202c41500721490b41001c12a03864000c9030502d4800c0591980ca40500140d014034000ea01180040b80002035454810300c0c4502c01c140c400401c4004140d400300c500490002289038030f0b850720025170075040d5400d0440d800705d118010400c2002411070500540c0e03c00020312241c40d142c81403013104082200038080507232100741e081101804101180b00495444070001d1f13165402107000780d004540c0c891416501c004418100032495250031641d040039041c40e1707414081140821005d58075801c0a803851240c140c002c01c25040821051401003020062a141101112044402050904119400203d07403403440b25107101040c602044403850400d6852119460175414140c130075034038400d09860f051982c10203d08410214020300441e8002d20b00940320500c5d0b60740700d2501c4005030f882161100c480e145000200391680040c000048141d0f84a0340303445078009001d13410607030030f81040702d1100064401c00c1d400708072645040c0e200c8014076100303440c59503d1b9406401960300f802d649 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847964226 1250 847962976 847963033
    0x41208041503060b031b1c021c050f13141f0b0f03030313081306021f1a0402030a02040906030c0306050c0f180604030519260d020c0a14 60
    0x5003c4240060040c81d401c40e50001c1c500f038400310110390382c01c46030711480c0200041d500d801c64200c0411034058515400800881240192607801ca08600054000b160740648108510507040000135001031010356106058600521b140d081c80c2840b11005440e0680e0404411400c4600804485281d0070320b01500d13166602c100c400751203046580d00403030383e6800300800c1a011346030004080c0c0b06001041d0300300e5200781c40d1120704140755a12844080e60319058400c000d000e8400303282004010300d41070b1254001d0319403c4076102d001c0361101d00402019401c0a044c65508990802c00020700102c94030840e40118450f0703010a803043c2c61818008100c440050200341d810408002d01c06904181d00c2c225581103140000c118100c03034194020595030b00881d08018400e101c2c112080716001000343c2d001340a18454400030740c08034a0b118a5080951100a804440403000c0c0001d40120503150003404800350050205c516061803605e41403079004071081c82018a80001c030080e001c50007840c0900e1648800c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847965476 1250 847964226 847964231
    0x6120a050c0918060a0b1801030501060e1605031626010f0902040f090e0703150b040515010509012706110d020d050f03092d0c031b090c041208041503 66
    0x2518030300c81d442d600d0080141c0701d542d40c1c030070806c4d0305540c440b00d424070304504c1d204210080f03684a02c0c01034001c2c06a40110350803900d041d800600308499080c01940b14140f56910750341503807140000300b01c406882c803482ca400e00100001242c02307808131111511a10b1340341c00040305c69500d49840342280506542004805500400080c003086218414200842d50104c0b00007030440040a0014100803041d04000e140d107808894124045c802c54101c2c4000610884040156403900d02c0c00e60146001c1000184c04500c0521005406602417001c004401038560300c001400064011700745040c1d141038001c2c20208c2c41000c203000c66480100700400b06040c0300e000800507502e16100c040e195010306988440300c0c800c00400660814018069194200340c1075a0180c003244145404c0c26080201c4460043c062103840008140f82c87d0010b20040030b6403042005400304000b16040c010035000080462449210400000404006d0780d9850407640713000d100b940ba204c90404003010701014907024420304060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847966726 1250 847965476 847965511
    0x110304030f050a1e05180414060f0a09020a0f1d060715182003070506070b042901061103211819020907090f0b0306120a050c09 56
    0x9401c001c0040c4540c086003031181c0c03101540c4030202c5602d194101d001181d00d0014503d00829038101c0d02901d0000d04901c18004002d820a0500013101d17005199240c1494444020a4860401c07180400e245071000e0000042c0b5a00c5041c10341c140d13403000420b500003910380010180419484500100702030090481c13060130458100005aa0707020701c10018043c402c0350490450494080e40c00620702020031a818000e07400642482440d442c0310100a110080801c4c6204a040ca00899400c4c250b070401081d40b4100010341d11401e200726070051085070480c0206c0c10448200400340340001400058000e182090b604101c4000c094450b0b1990910f0340354000d00c8a07201c0c880c0c3c840740d1005160003a81e40c12400f66940c0300106000d410384000e545e1503000e0f0101022111120340542c100041c000d4602001944502070102c5854409100b035100c0d0f00036015051100507190f03002142c010b000100048842580000e800c4e0030001801e03c1120558481c28000d00c960801c40c0c0c2d01c5510000301100e211004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847967976 1250 847966726 847966733
    0x12100f06090e1312090f0b090d06020c120301090501050301060e010602030306010c2103051506130b07080904020408010f0b01111513050a03110c0d031e121b03110304 73
    0x2070040d801000205070751480059489010907246480d101e40006540e92500c44902000d8440290350207030092104410300302007003040f0440d0072103004420203000101580c00c607444050007500309500e0112075000d081c50248078008450050360282076120000951945041c04050031241c180d404040e00c148218010010642c0100903640e0011003800c003281032078041e1a01940ba0f000104007101118880003880e2080d5505504c0540306400c01c5982005030204003040110300d01a100300f41070b540b00302c0007040c02001ca0b0076002e840c60500c40c82202c4c1c1801e440c503000070282d800540148085a541d01c40d07444007004503008018000c0b4007800c1050b41c08880084142d203840d04a03c50054801c3c01c48041001c652090850200b060380240aa0f4000e61107842c000309040500c0421070803901c900840c54904d8502184142e10103a0b040e1661100000c00705440018130074030b40b10200a00603000180001d883c03043c020744000b0440c203045203800d91058240501200c40a0b8008519140c080c00bc02000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847969226 1250 847967976 847967987
    0x30b03160303030b12010519050f040b1810050a020a02011a0a120201020f012a081021060e0c19080607050f0d020c15060102010c020622060212100f06 66
    0x99942518010404e04104400300c0c21000c219401410698689010840114000d50014011208481003440b0301c2c0c0750102c04a070011f2042d103024004e221640e010803030905105844001e024441400d82c1c243c0c8120100120490b038007146c40d500e4135074000420f512890760a214600c030b02a9502241030340c8201c0c4801181c0a803684d4003c03442100c104030140c809582c000c01c8100d170822130003402800114000714942c0401c0000c65001c076050b001007180f800d8135500812600d8410450285550301807480e1503604c980c1440d0004101d202d880d90a0095008111680100c0f18841407100c01048480090320601c1200740d4000030260201c0c0c2c0d124000d110700e0601040c0c1580010035403a041e0380b54108040e50f210309108040d91500203a2001410512620008c01c3d0a401c0311804158035025036210401079090f07843c0e003000074005800000003e196514010f0030030b4205004100c1902e00300b1026a10b4004907030010891610b41181d02c420410000c0034900070001a0500c41e102030101490000003400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847970476 1250 847969226 847969229
    0x19030216140303040627060e12130905130b0a18050d0c0c05030a0302070915050607120e0117040f080903030708040f05010203090a0b0702011b030c020301050a050601020d122307030b0316 82
    0x12523440300d411080c803200400207540404030000b0000e40c1d80c45000b00c1c1a5480e4164401d01c0a000c0c14440040d649c000e042e0b03900c3c0c007869042030200c1034035a41c0001040041241c612261142824030442c1800310300100400302c4000c1c01e0741c03501c40991100e81400714009070140c1c0924403a5102059800c0025070102c0e05104603542c002c00400c09411494024180705100c0e04480d802010102e03003801444032108440c07a01020303e803180700245184100454401400441c000100e548007004140001e00300f1244100050003140c55600f0301c180710300024196030103001c3c290ba200300c3c003242c00e11400400d071410b03e00601007400110300d41540e80c800325064450078070a441d1074210104454056902480c5100600e101c981c000310010805e914000d40b50110304c04082e070003586050b000032280440707845643d01448050f0010701202900100403034074240070402c461100c0b501c1d0300c0e504140042854074090b01d03403101c101ea454a441c11110003800c4030285d240542c4079a11a800405201040006480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847971726 1250 847970476 847970483
    0x30a0e07180e100c02160503010606050f03040606090510090b09040309231809010f15141503040501050f0c0301061b06020702120d1419030216140303040627 69
    0xb03408504042c0b101e08080b0b10300aa8040507013820240c3c0042640800c581d81815907103071002280945038802e2601f201c100b405485e001c40c40411840c0f071068226000380d42d00600c103c07004203080e034849030740e2000d98074103407958245052069000c2c003d9406174020720703201c2c00d010b44444004d071406440080c10300005205503084800c01c03d41d40c8140e0305410010700764480e170203002e07c20004890301171a2002642103d0360311140d4a000c0c4000c0c92148213000340480c40c3c2c0c103056070340050f40c24400d8080e010003c008201e070740400d480381a10700030701c03103030002d1881207000300000561460568003060308410010310800130150100014411980c104a03402d034044d00e045418101d1400c1450010028801c00c82d0195000d0322000b45034601c400001540c02c8182501e039500300d0210004803500400303000781000040340204020b43c039100c0030304c031743c1c041c001e41320700d009e05424203080c240c4800c0d8100c01c101c40c07201d0b41d5420000c100f20522a0500a80e60109018645003040498100800d4228001d000c4002d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847972976 1250 847971726 847971731
    0xf02010302070215070c0608090f0714010314091b030d09290c07050a0503010207020a1e050d03170606071e1b0b031602060103170c120f030a0e0718 65
    0x14010f54a61880c508401519801d101341e60760388a041c0240c1d081100d21a910010f419040000d654210101c6c800c070041116031f00419080b03060460302d0511100030240c1c18100f6130350b209510070802498485074012800d032009000001a082c601b44140303180c3d0b8aa00d4002e0b40325183d10030b89194001115012a1540c1c0c145100981c650401c211a00c84130400407151908003150031250044045800400c44d401154a0329a07199074030245130a034010210040d50001d0002c5042019542c40c42d00641140240b000f10010740752107400013104043d00c02016000240000d80200000b460f0002d00c03a000101101e0003400d0180d05c6d40c40d1140d6040705401c08140c115100c40203401c001c15a080444804210140f010b00303141c84405c0070200307820880d5501081507904003012046070000c10f6440c1a2030f0001e100075104600581401041c3c4e2002044076540e100e102c6070264102240d001608280c50413107811340c0d49080604146081e1540000d0410f042e4118040030090f500c3d50084403200e5441d000c401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847974226 1250 847972976 847972987
    0x50d0903171c11090a050f060d32010603050705160204021c0c03150506040b04170307080315130b1f230406020f060903070809120d0e1201090f02010302 67
    0x555903903002d03107010855a241030002e40000d4441200c041e000c00d44081d5868916a03580b181002008015140c41a07000034041000400c000401c1c0c12020402c0035410303642d1104c054019000c41400000c10450380909105d4005200c0c6541c10701803581c210401e03140c15410007a00c94002c07540c01e60100e000901c110340c0095800804414114404880369a41ca01002406881e070303c0600540f032910300c481c1a81e02408800300e090b01d003a009590650351104000781c1000c1c24120a4001d151024881c82c20b2848140159070006039a85e004520a0f02420f00c424504c0f0701101c140300c9600c0000c07600b18030082c02d04801c0d184580720101070000b01c04075805d14404540704180180d0741c6a440001d0001c44a0310600800c1d40d40040720010411140d41c2d50880c0d08079000d100030983c40d008150f6001100b078000300110004038081d40301400da5900001c01c000d62203000c00203024a4450442003d9011580c100c0710441d42d4070700900c0030f41c2c1501c1c11400a200d40c2001d980e4101444c03000c041e000f414503601003a03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847975476 1250 847974226 847974247
    0xc0d050901090209010305070609060c080403020906010203040b0406030b0a170a0314040302030604141e1b040609050a0507020f12160f02090103060b03100b030c090403032007050d090317 82
    0xb0507400e4010300324074142d50712814195159501030041d1808910390040000c0c03a644a548074664041e00508001d003050b055500304140b0400c0546802c2c114130050102082e244601c000130401840c0c551030014900074045c05120f803589441c0d0080300307800b82d0000e440d10b40c10030104070308000c1c90b4140751070003038000c212000241a0060741c0010790107124174010002001440c1174550900c030001c0c0c0031038400c903240080c000301590b1307100c1e4000810b030810550368181c000e08a428420102000344003040440d00c1d012210112a4115450030110b915038051011150301481440e001f83d0303d031005400c00401e80c08441840d88070380074841320745141a042a03814010164842d00807564024181c207000c0d6500e0400d000a821524240c503c02d0042580d5800d90039030038402d14255070000b402070441e882612003007180001006100742c0906446015403080c03925101180d84a90340c000b91070ba5291501070500a1030480314411403000d05c40d130700c0014400700c0c8480f00c0c1901c180110501c41965200c1d1010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847976726 1250 847975476 847975481
    0x2030d05060402040807090504020424090506030102072901050105041a03060f030a03051201300302010b151b16030215040f09050603190b0610020f150403170c0d050901 74
    0x28020070441c02441400f281181311030300223a00490089805014074001d03c42503103072003680501e00fa1003070340071b10000b0441200c00c3e40050703030f010100800042c02d00d12140c070ba80d0300c5941c860301f140b0003800502190b1200c001808480c507016003001c0c605942071030706000d0b070011004c0320701152003032003030b40030000848503502d41a1a41403a0300c06801c0e0382c00c0340300c2454098050b420100d030061241d0618000401e011048518110700c10704407500b5100540e05010b9515080a0005000e50865403100214052b0303441304426903101e034030880b0346141d40d01c850807801d400c007184121080c41142c10442c5100001602c450142003038a80486200000c1034110039180c80700e2140d98000325500011010000e00590a07602c858031400095003500c00c90380d241c4050b03000e04c013150707080240b08003e040007150050030000c004c0366aa0200c2c1c0100c511020044880c036290080d0899412020222502000209039100f5034040f0f10350140e880321040f070300f400c414203a4907026400d0f01e10002a560300000d2040e41094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847977976 1250 847976726 847976729
    0x606090204180c020a0b280e0c270105040f02070515240d03081017060109180b0109020c030c060c03090d0c0c0905040317090106030201091d0f0a091e0204110a02030d0506040204 78
    0x2042c2c03c01000c0c4800e2141e0340c9900d00025270a10880d0550103c401c140c5141d0041034031800c440c0308002c5103038206002c2000501e402c0b0703181c081b601c1d400d0120500160080040000c8560626549a41c602d4101169183e1007040c88049241c10410030300440315031103014003081400c0d411304101e9195030720b02c5590081120103034401c1d207017101d4030300c1c40c1100d10b6000701d84141640c1c0b841200384120a00b103a10240c0d111002078004080a040d1001001100703d0741e800303800704841d0101628509561150070524009090ba8044051080041400002e020810850b107080c002030520080c41c10490b100c1a41c0c4004601c52a040c050b187e01c00101003610600c401c4142d02080c1d50282c600f400d00342101030090010b80001c90104008010219211030003074084503132035852050128080e030780c0e400e8114401002502e540030194035800c0400026030581e115003002441d4070305011043d440c80c010003080e40c03c0c20a56100c160f20030403001c00c0042e0301000701c402c0484100c00100e030030b864040119000703100782d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847979226 1250 847977976 847978051
    0x20907020307120306290a12020f070b011e0503060a050601021501030308070f020606030a14030f030403050d151401180302060a0207081e190606090204180c020a0b 72
    0xf0007141400960990700a0781078840d0502d6807009104054940100400c04a403010714071401882a024800e104060504200c0b1070f1400150420070000b41c451126081704004490701d0b0b04407070041c41140008405404042e07104100070440724640300100ea21541c0c080c3c002c82c45943c0b5030b400204d81d0390082041312a0185c1c99414450507607580e04005040700d100360f401e003001406210464104510002d07042d8011680140540060301c030550b81c0405e680c1000100c01d849000c00e100340703004540b4280207103120700d0290315000e41d1103604280e05404c903640403002d5007594001200078410580d50441020f01ca560a00704402201c01c1c2c2c2c40361018070714283c3d00080d4030020000b41842120341c04a2110122003400e4222488211f94503c40c60b0311400c0702d140080a40d118076101100c003008001105030050040310005605511140500c040c0ea0040d080303c1003251405008480561aa2003800c0d209005440642641c41891742d8109900f0030141070500f20700003c07640200103a21199400e0000e0a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847980476 1250 847979226 847979243
    0xc0501140c0a0c060f0e1c05071e051518120a0606180b011d2b05010204030b09061b090f120c010e1c0b07030b06070303061406040b0403020907020307 66
    0x80c00d00d0048540e407868014100010760125104001d58003880010412a40003419030b841c014812010030980c031414141a2340354450380d06c0014002c509020b40201c800c85090201080600f44130903c1070706240d920310300d05202070400914500c21070924490a1362030b802c032691040d112400c0c010a10b0044152800362865244c800001207180b0364150300d80c810b4226401c01d0010a8602005540c851202e0440700316040785138140c40e10b14a0304145a40c2d4140780281181184109500c948500031800c11040b03450381e5000070203005000c415000190303c0500c5000070075540c0f03042e0f4911104030340407031841c81418002151a0620366200c540224034420081c11107015910324070395990f65601e0180045000c0741440c000c848042c10008060700d1190405111030365185801d03074801c00311590081c41ca0080541c0ea01103500c0c15a41c841c002c0c85000c1c0207950101d00c2d94103240c031042d07109520849291290dc0200010812410b0034030030b440c101d94049800c0f6105540c2c9800c00e070309501c21600e000308000b5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847981726 1250 847980476 847980493
    0xf120c0308270d030206150d120203030a0f0203010b0d0c050d181202010209151809011206050a06150e030a0206280c02090f060d0204110a14070c0501140c 68
    0x4160380350b4403040181549070501890000240301d103040440f50040c00581101c4000707a40107010350b02c126141400909030154422081d140c3d00e415900c00e800c9640143c0000007403003d56800745c000d461260103003150440c555490103816503031503c254240c1c86012900c070b0680c4a01180950240ca0a101d00d60702e007030100180702c020712280104010421500d41c9039407505506403c0c41442a200005800f80c010102e0703010046680c030068009086101c0000300c00142400a038403901074042c002d148000b0b031340c0c41c0f641003490800c0580c0c030010060b845e528640034082219455178030311150440080c3c2454401a44c014001c01d05250340840081e421040010b84c1c400075000221121110b8490864841400a56101d00700c0f0031b40f501d28000fa600242c2c5c10040340c0c009803103980c03d0b07401440041503e503000071658007140a030703402250303001c950400c0400d441d82c043e074122020b1402d44280880452030402c003696003c0f02a0100d0049904000100d10b901c12034000b0301d0700310307800210748004440405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847982976 1250 847981726 847981747
    0x90f13150906030519050a0b04110d080c0c030c06030601030f180804031401180b1e0708103201110708100606030207170a031d250f120c0308 62
    0x2082e441c4030844080c03068080011071520040319184805034042c01400307601c0c006448804040501030802d8603107442e0907816803202d9840091402245109103242a210140764001d11f0401c0b4101c0b860724025040301014054560741e281c1102d900c40c10034280020383d03e40301c91070000200561841c1d105582d14400741941400801c0c000f0300100c1c1d1040000414411009600500380d03802c881380b03600520301070f06000000611005405c5d5004465244841c03065040004000c0c0b9034000362812004912041c0901045900181240d4050b00012110303c8800d50a0558408050301c4824161f00e1103003440c3c881841c0b0703803183c81c451810407010011a07000503214000da54940c81c1542e0301c03034a554648280043d8450090080c0c0e191940c1000c911841d0600e540c051140360fa00c00025402016034400300c1190608200c802040040d91140c002c0c2980c80040f101c0d2204088800d85003241c2216202c0108040740300403100c2c00c00c0d20f1044100046011603450311201c403002c0764000400008010a214000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847984226 1250 847982976 847982981
    0x60f2101022a060c0f0a0309110405041b0602010c05071b0f17010b15070323040f030209090c030d0c0302030909040b06030d053c030108071406090f131509 68
    0x191580c04058550f50b4641d12404034031441454a58140c00c1814803201c00a00d0203070f440002614000d4040c482e00b0244040000c0c00c8800c05c450484012920900400142d40c43342101c4015002d64002086284841e0764050100e0084280080030110f80e208004849a2140c8044000b492425400031800d502c0c0d151740e0745145c440b0b4003d80758075031070075030f5505444c40c100600b0f4403041e1113900700529040441d2802c80d04110070740d041074500c4800220001b2540f4640340200014650884000b0400e42144100211704102806032442603100740c19001c15954045082243c040341414a00e940c213003180303001d0b411401052501c541c03007000441048140280440d001c1d00c2903008800b52031403513a031070700b00f503519000712000040300070440010300040000b290720b50000c61040980d11034414100105035015584260802052600b0a05040102c000d0b14110486000c60464285013800c00340404558000c0c050b5034550b2165040e0702c1440c016190a50010582030f94a80c4200d00c22921180c0c034a01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847985476 1250 847984226 847984297
    0xf09060f0c0f06040f0327080d030b04020906090607060b1003020c0118230a0212030405010906090e13060b0301050a240b040512280b060f210102 64
    0x34000d4055004111002040451150b80d105c13940344248000d0b0b841c100d8171200c4205030344032285501160301c4007078401c05042d00c00803c3c3d018000c09a4600800f070040598224210840c003d5005100c030036011768901040c1c802c07410701514401c0d152040f6040040142040d0000030750400460000454010b5040d0010860302c0c40a070000d00c00004924002d80c81c6850411018100c1003120885140703080b40e400402800c0701083c0200e45554200d5000140002d4289420510640c0009403c0040e542c01c200b5403001442142001451a80341c00d1074000b2681006020321901314aa0b618101000565844144600c5c001f8008008518021500500074840c199020483d04031100c46490780c00080c8100e8400c1c1c070300d142c0c403041c1400d10304020320509000410300103025000300d0040107401301c691418031080054902003241099a1810003d07264070024000358024008440f4407065a26121182c07160154075a0010310131600c40e000d01c1e40203000d210f450039014480d030b101000e00140c40759842c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847986726 1250 847985476 847985497
    0x2030d02031e161403060a0f090203090c060f09060a0c0f05010f0b04020901050909100e0702030a1d010e100513081f2d02040906060302070507090606050f0f09060f 72
    0x240e12036003c1c1c03000d1081c40600b00000120514000ca010f4007100c400b56070402409450071921a032120400c1203d003900703070030201074190301101b01302c0c24110800c48942102c1c02a01c0440c0b070039445a0141825109030b41c02580601d2000035240d1525104002020704030b0380020f840d40e22001d0320301d4401d010345440c5614035205800c011f541c682c00d1605200b10703600000140c550301d00d000c4a201c00c0c0442c801000388a0f40c1c2da01d401500004201c14112101407060141354080d503036031064500042c146422000d2036180d030b05020309080540380d800c40504800c940301101c0c1c403110b03900038180450381341c81404141c0000e00916200040d034168002143c03002c0f003440303540e06040d50324410003950444d480802c444020b00d1748101c5803006135942114207000350300702e28000740c6095101c0400100383c80d0303142c0c48040081d40c009100e105102c014855403002e8981a201070041c90324101c0000d140740035503a440508590002031450480099000b141da080001a0886807134500700790412905070401c0d6542d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847987976 1250 847986726 847986781
    0x5070e09040f110a06120c03060501200c06070b100b0918091c030e0c04110a140702060313030e010804110f010c0609030c0b010f0501120c03181218051c0302030d0203 73
    0x107c0228000d014007001c2d144180d4542034001110019800c5070703510511300c5841d5001d00c12020f8810748503c0010506240286a4080c0c3e5041014100b1280e24155000410010041c4414445a55400a418516203666820a50030388528050038145900c0180501e43e0f030300d020003081e2540c2d070103400991440708400c0135214101d42540038002691b6581d002c094417608200800141503014083c880b4248a00c24074080c10190103a010130440d0f4402d4840c000d404d41c21000e05400c05500a41c4014240000e180081c01806c0a030307101c4401c20b042c02c1845108070f41c4640c042c071040c1d2040031000000d039040b0200b0300007100700d402c0151001040d440143d680c0560310b000410811240080c0d0000c035441030b03507090702c1505610644002442050b01d26020075171201d08103140a070300e620001c11100d0203a08910701d010040d890291107030000c2000d8011400c1300b0340701080540d440000494604181c0307031440e09015418030301203007188240100d10b50b00300c0c0b0100611008401c6250756548074154450032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847989226 1250 847987976 847987991
    0x3161701110f0405010305100e090c040e01020a020a02090618040605150a06080a051005092404060303170a1b0806010f0806060901030b030c04020d02070605070e09040f110a0612 78
    0x41056900c00c2d800d40e501d40b5402044108a194460f900c4182d11016024406d82010340b80e040c159111030054600b4401079018036044003d43c1307018442e032440d1a14541c000c51400b914054040d403150400d29003c0e21800003a00014042c0c1c40390039000f009141080c005080c68035062820b0001484166445000c141000001c285175082c220040c000366980342e124001e003075850b1034a4801400d8000c3c00c80d00c9000d0922400940c1e0344414101d20b0146c140d1042c00e41c00c06100304c8414141a8900080c2352260b4185002040071175040001c600c0c1d8116101c101c2d0030320742d64142c10b032806800b070b10410561205851411000055100e04101c1c05400300760390301082000b40b510201d60144058a499910540801504201f903000354021415040c0140507214070b002901d0006080360441d5400c040801e8000034280d007000750f42d01c51258010307600d04001c200054110042003050100800046c00d4850001c00c04052244d03220003003030052002440310a030161910401002008003039900031150317050014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847990476 1250 847989226 847989251
    0xe1002100e101a030a120e042f040b070b0405030705031303151401050f12010e01020913020c070b07110a14040f0b0303030c0f0c030d06031518080903161701 69
    0x5046010b10003030080846480c1074581c030003000412200c1d1b10a200d10880d84501e503442d580030350030314a100c84541d01200c070306401000100707260741c015038020541c8c01c010a00c6240b007401c0c2035480c26130700b180703000c0001e558030305d0401c2c40c0d485030380c0020346284400f082d02c40c403001c050403013042500d101e018044070741c2049024540688244210110070b0700c11003001070105040030030b4841c0408a0003400034801c80803280303074982180c8286654850341e0350005191180780c10282a18010207039441c0e0111700d040b1441940d5615010a0f01903c00310342c10002c5d905050120088040c2001400100707520505a5101d84a507003200d600b2011900407030518075140f42100891061074100b03840900510319503910102c541c0303565840020101e40c403400a00010761210300400260495181d003043c00a55103045040c81da600403e491602094030381000303508003c40b5425407086d104180d101c050b281d00e03490704800117410b1804070301c000d4a1180725020000382248030340c1c0700740704080c1503440200280110200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847991726 1250 847990476 847990511
    0xc0305042d08191403070204050a0218010c0218060a0e0a060608070c170901050c060112140f03070b0c04050306091c0c0305070818150408120a0e1002100e10 69
    0x41001ca0001d203803e103c40041250900010090a035001c2528034001e000c1e4001822500241c510100295002c550710703111840c1e80b2164183c160003420180707005c00d81640000c141030300c441c07604403522040b10041003054480a161402a0900c41408941031803d10a01001800ca520410000640200108002e02e0040a411198507048103038a80d14054030400084254040c030300450402104000c04084900c017070224a0180c5a0081d9410202e0010301b03044140340010412103d076500325100c0b0443c030400020031208100e60040c2e0203601c5507100c248030765090085e0361216405000328020800d4a81001c50015623898072000c90b8250f40c05142030440d014880079900a01003401000801f0104103850b01401d80740200c01d49070b42c2104541c07800703c1c80020244c1a00003181501080901c035240e0284010014070001381c030014100504400d008255041503462503000d60703148200049203071710912074080c08464032001441883c2c1414101e41ea10003c0400c0303008264501644441c4800540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847992976 1250 847991726 847991743
    0x110705030403050a2f0111030c0109051507090b1b0c0d1101030f02160807021f0f020601140604091509020412020f100512070314240102120a0c0305042d08 68
    0x40c04601c5405d180c00700192124600c1c0141191241b20601403d1a8a8000d018001000d4869000380c40c01606d000f29030f44030180d010f4001c03818403041d29410320030300c04000306446a01c2001410b0b101c0e403070410010316003000c1401c0c0046400000d40c1103000248500c000c0b90761140242aa0100912141010000e049000b194400300211808100d00f90105054001503c18039000030f081500c0380040c0c0d0450304810540309410700108119030568800c26070144000b80c010a0b4540c07840c030228403110001030140c46203005080e0718654a030b04130012010800c11500c090f1940e0740085603510b071605002002950068401c80c8141042c0e00011541c1c1019410709101040301d071a40b50500520008080c10440010301000803da03550005584800c0c80042c031500400800301070304605400c00406240d01440c00070480d0656114020002c401120782c001c4414911582c5421580d490b01f61408642d140b00d2644021207040040c1c00755075002d094480400d40141c00e00c440010580e94401200f40c803040c09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847994226 1250 847992976 847993043
    0xb07110606041e0b18010e0f0907030f1713060801210b0a050402030a0501240e0405060106050c03220503060610050706231005010906020307080409110705030403050a 73
    0x220322886200f603d60080740868000030140300c03c1001e24200c50400403800d03445008400d941d0420b00c00031003134000046800c0503614014210850464407403a40085a9250080c420031000d0080b010040c0300109031000c400c0d01503600c0682c0755590800500c00c02080c043d42c1c0743d03103c403036151002621014982d088965400482d802c01a503803a48508028440140241e8060054808141c002202882103040c4813141c1100d60b07138120001264008048216007100c0d071030300d800f801400045480000d245046030714901d0720780e03580c141c01802141180501c600e003c1d014424182c0c174808801b03000d84544142d8609900f2a0060b42c0ca0404100c2c26402440070034001c03500821155000c50b00304d0300b0260040d90364210403845c00c2c2c0f4682d0320001203441100d1072802004654400e01c403a6901c078007594000e104c61b100640c103003411a00c84034514400da105920280365500b101341c0034041a03405860b00380d42c10a0599480b5a540d060440e00d80117001e0084a01090b03080744040d005d011a85c1c88020382c01d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847995476 1250 847994226 847994261
    0xe090a0b0c0d0908030f0403090f0e13150e0312070f120c0203040302180406050615090f150c0304030c0503062404090c0f06020f1c0810030b0711060604 67
    0x44a0303240742000e521075806081007588074440c103008980d1400046008100700c4041400c0b07032500b400e008009000c03640080d40d0039110310342c04104111103843e409070040346c0040040407584070b41c5002010300614000c81031020341001106503060348040007500081407190601c0e43c0e596039881085a5401001c0c107900c0109442d1301c416603015036158020340c80070b000e40c011a4901600da070000b071001c0400c0049030103800c444070b040000300850760040a82200041d12603004600003901809e841c0c0c051103010394041c228224520390255940d40004121074070112030944c2d6100343c1c606d03050720790b0321078007003500e902600c100f001880c0c0c100040d01c00c0c40b4034140b000307186c10000c0000f207000c44268103007901070784961035020400102c0c01000da1040100841078590111900d092006818000b9151449600c0c0d008000105032203a40340005085e88800d41c608110255540141e4003a10340751a00043c14110000d02041440e9402509100c443c7c0d141c0011510b19603074403c20007068030005480c0e1000c4130b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847996726 1250 847995476 847995481
    0x602070e09030c07141002070509070c020f0607030503091b0d030309080c1c03060605180d020114030a020d050c16080307050408030f03060a06080f28150e090a0b 71
    0x310a00d03100703410041e000c0a0743d14107180c260000345081c481780c1201402506192075184103291003c2d2450300c44100d400030705070032480c1100256901d080103201000b17003c03189801d0307011940c8034844c0300001d140007400b05444010394100203016030001c039451001c41c41391580841008990641c03003503108900801c100b080c0c1246642c1180a054020b208491107841030280207000391052040c00b800c16041c100042da040288140242544c0c195440380050040400005000c03010b102004890303a00c064401d0740540d0418401240c40c02c01c601030041c000500402401250121500181000e8900c40d006000070381f12101c0c184020310802044401903c03c0b40300d1034000960400146a00087e2400d0140c20140e0b101e500c5030441d0300480120001c2d50000080145500c2c0041440019002e9403400c43c5c600d281c02e4055600340400503341e000050416000340c45081e4540280004c0f41010802c1400380e0304c586200c00700e510820b400b43d10350502150780000c404003000170b40594003e400c8030640c0ca564 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847997976 1250 847996726 847996739
    0x40302041509140613061a09030f0303040303230105030616020f2410051003020d0b040e0a0b0c0f07110a0503060705040e0901020a0824040e07090f0204060207 70
    0x1018100100700250700718180c0040c000c00c10b44240b052914010610900d02c0c903102d002c00a6010580003045545482c0c01e400b840302554414492030761045421006584504580010380344c455000481007103444000108403c0542c10782000050b1050002100340340c034014810728050103803d0054a415521600008042210712200da2100c0b5486005441450048421460428a80188040981d01000b040100001c244505560300001614058503c03e040c0400218101640742d082c000b0990082404c0310701da8031039413089544032402441000070345503030401980c0361883d14100740c2c5c5044419000451a048102c100d035030f618002240d05182211a65940031b0120942c9041c0d81c0110f0445400304090701e080007454003d900603101c2a4460f40b601103c40c2e00014024200340e160390040c0440316060760082d03009508440508003c00d107203440315001c0b42c410404105410f500034106a4650384c18403001c0b03000000da9000c00c40c1070207218181c4090800344d100da4803402005030702200081201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847999226 1250 847997976 847997981
    0xe090a06080304140a091803081008072c0106120207150c111b0a0911220906050405060603011511010c0e0a05011115060613031a09030f04030204 64
    0x1440100009556a00d5407070300351650304641c00551401810307a51203805450090501d070014010904144004500441d14095030b0031561002814800440c010484414160800102a000c01d9080b6503506580ba1709140f80911030340c2d1580400c071101c4130034007000401010300030b06a641a0300c8214901090718a50802940083c0c0d0654402211601441e140c6200d401011004000d82d43c0d103d80281c940c04020341440d158000c01002203a40d980700580300e03192401c81204403400444001081d100d01c07042203840784200c190f40700c12100b1600501c00046002006042903601d1154204409510351061100310355007511030702c2e40b004042c0300400030380001680d101e001116034980340b9540000c03010346e9030940350304410307100100360107080000e0700e4102180548003c2000b460525a400044c03038a00791111042d92000c00712403e5103002a0315a141c1401b12a40c142084801501c1c03d0780da07040100741c842030752880144207192000403d1074004000705850524000d90302082c6403500d1039081200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848000476 1250 847999226 847999231
    0x191406072012030109020912030a080718080f0717070303021f27022b020103090309080a030504080106121a060a09111206090721090b07050403140105070e09 69
    0xa0038850305184014080010000c0c44c000d00c1080d5001d0388419082c401c00120307900c1f40300750790f51660052045020140d40090b200e0741001d01400d12040b250311840006240f41e0f22601310880038454840132074204000003c0c148100c60510301f01586d82e0307400401107500c0d0042c911000e00140d01510085442420210600c41882c21070b0a00050440980c641c1880c81c0442881d06a8800101032424043d410800042c0000c2c1d080450041d6410004001048031030219802c007038109a500c080c160101030088007410b02074070300710f000c4414643d9240f5004280d9802409011202d50808c20001031030841041c0f40101c40303601044820781b0502d551403000300500c00030b081561100c41204001003e04443c86030060440f00e40480503680c2648858242d5100009131501340078100900030442040c0e80059a2011000905000c4028210302030641f07001d81030401c401f0740001074441c00c0c000800c0d00500240704492007026802e6148004039907c1d4203ca03000c07100d48000c564000708220300e600d402501240d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848001726 1250 848000476 848000537
    0x2c071b03080c040503072606040b0f040215030c0c15010f0b13090603060b09150f060a03020702040501060e01020f010908030703020702010c0c091a06041d041419140607 74
    0x342803690310000179140840300d5200d0512491010000041440882206101d140450006000d1b90900c0e650b20696503030010516113074260132402080441d603d01950244408001455039168205013150008641c00644955014400c0704100550307141044d007854125103ca25164440034a464200c80c0e8540c0200031503240203654640124030301c10307a071003003602840c0105800200d805c950800d100c01e02602501942081240048080b0b00b40e807403080d0260585030aa80c1c0307548510111800f90040d00400c000290301a041900100349180d1061820301e502009908540c1600c4650700c0c69401c8070780c4644090300c1c040d410800940c100340690000c0c200c0500c103240100001c0300380d485148502105400c00300303000d505c42146808046400d00e00b1002444c1c200c460514092074440702c0e0280d500504499401001d048000600303200140c440000d1014010003a02e205c003051004244800550300411605c2201310140c1e5190820001022441001c0c0c0380c4030004000c447d60707450b82080084d8001403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848002976 1250 848001726 848001751
    0x9040b060f0307050d1e12080a29012106030b070801150503061504030b040b100f050d060f14130615080607080c1e070213110f0c072c071b0308 63
    0xc000191507444010007403a060783d00c42e13965040070100001680e00c01101000d03040340c0c1412041c02400e602000042403402403e04c036024a331464102000b00c154280c0c00140780f07180640000c2400b16240d000341c030603801640e81c151160780311908003588840f50307880d40c000580c040c4000351240c248107584029119040b60441d00b021ba490740c0c1c107202c41404031000c440400d807400034071142c40345284200001d4004200784541e101e0600003c90341030341005e0806040961100c00520120105a11140c121141510846070f6480d00c001242c1e508100d0500c02c840c500d00e001c81d0b04014140f600200d034191520790000e45101c1d12042c0c0304441c0d844000d440b031003200e8820855492000580540f5107008856010141d486007414010092840501e2244403280c41c10250303000400350500e41101c151502440406840359451159149850001d400216402ca076000040840c02040d81d480711081071031a50107400c694072128100c03002c0311142881c41c50000402d0120002078051400c0c90780c007902d04c5020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848004226 1250 848002976 848003033
    0x12150a030f1112121c09080c071406041a1b0f010911040905070b0d0b091504050a1e020706090611090909010626010b09040b060f0307050d 61
    0x60380d00c0300c118280c1c200d60303041c5801040c0c8454106042d5115036118504041c00f05182202e081c615148900303180130a004908402081c08a00e00341e0041c5184d07508a004a62100203d0b000e1507030702d0300c09014081820555605401031441c0038070442c1e041d5600000041c400038100d056003111500325900200e0110040000d60029040c204400005203e8400c0041494500340c100b240c45d620304400a24029410164008007284000644500f08c488143d203540e5255880d2070342800824124070502c0e4401041c0e0240030004800403a1614504422501080b840e19154210b4089400d290381c60428040c52500320f001e5051303e540909001405000046900785540d03844000f00d541040740411652004500d1160318201904e1850340141811300800201d400e05c0c01c0392440d8500d0810303801c00042d0882400c1d040180030b4001c8140b00c10041c0c071054807401c0c5464024500ea60840f1350601402040c01c4a100510300041d4400407104050310218584140e6240d0b07095500521f41030103820007041d0030707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848005476 1250 848004226 848004233
    0xc07092a120516120b0303071106130305070e060d02130506010c0203070f0602120412020d0215030f01060e1e040b1207030b040201020c0409020907030c1112090a060512150a03 77
    0x445104052824060030700040101025190744c80702500d032a095441e10401508503180041241e05661308841070018841c40800021100d100326000c0741820300e0f1040c400020048001010310a40700401071282159995801348004036018041c080c1d88030021004452000f074440d404035400c03010616042102170342a0b000b00e490049264841c00901ca160320041180c954148603288490784030412003440c3c0f61401e0f000c0c0c00a8450500042d02c01c408805400c401c643c3c604506418080782d44000300c4d100d140400700144504002d00c90000030854145420b156480d0516043e00600c2190b440c480401595005010080c04070142e001c0d001600d07000040c0309100101f000314000d610404c2d9000440c0f50900c002800c224084181a029a0525100078010f998be245007907800405843c0c0003900c0d07200c484046420030a4041917400706d000390031306002c0a59140006190101d005c1c0c1d190842c480e69054210346500c80c0c000d52054a034020740c04280c03060705a60f04403418400007000c2d920020f84949 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848006726 1250 848005476 848005481
    0x618010b030d02060f0105010801030c210f050105150613090207171306170403171003140c151305130e101b0e010f0f020a05030f0c07092a12 62
    0x1681080503030b10001c1042083c0a00145d054050102843e100040f5451587c403d00c9045107401050b50417000e92000780c1013010802d803070701002078000d500c400c024020790500500819040d55850900c03503007400c01d1101800c201c022102034502d00841554503510b098516002034000c100200d40c0014031448a2058080799000f41aa090094103001186803a00700007525074850b00803000398140c00304d000c01000c603820034090180d80d003001549402c0d5503684502803076003d000d6040100481141d40c1c14520103040080d4034021020107032020b034250b030b030780a0401c901400ba100114010240c0d00b0824031050030311800d01071884015100104086200a9000b8101050042c500303001a503168180e00c00c40004111080e5440300318145402c0103145040000d04c200342c880062800d000c002d1002d030070300520030410310310155040320569484001c02c003c40206c503400380700360039841e1058036004140c40c40c862281c400c0200840c10114040b40403810010510300401d0075110600c224540c810494144070b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848007976 1250 848006726 848006743
    0x30a0b130f0c1101060f0909030e09010e090d0206060904170d050c030403030c030c080c160b01030b090c192c10050a09090f0209090a1a0f1302030618010b03 69
    0x10021034000d200180091103d40089004040713130703040040400581611a510702c041e1a02c0360404030310031015081c1a141e140580c4401504064180c000164a142c0406002d0040c01101b060791221107208a08070398569040d2006a40f0100c071801280014030066191413285811864003802c103102104000b0444604851100c1d081c04008100410990706120302d00e0071200ba1b080070409000000700081a03d04010b010918400e00000c41c80710340d280081150079840c7d40000254000d60b128078000e1b0b814101a241c0602c40d01c038440080d502403406140b0031084190000204208914140b2080c01c40550040041c00e01d420030480100c001482c04e0520384101d8134208101d2149c1c0c586418090295440da00c0048030900d051100e000254855440e0004aa012119142aa00c40e44005420030990400041103544003158000d4080710384131400344120858000d00b2056500c1540d408804481c1040096241d00b011000400040205070b90010103403404000042207120140071a00d4010345 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848009226 1250 848007976 848008001
    0xe15120d02071a070b0703090804080f160e010b07060209042304030908030910050906040e0711010e010603080a05031e010927030c02060715180201030e0c06030a0b13 73
    0x1014140302074080d6030200611403442c3d554640c0f51403801d803520703140003c01609400416440700400c0f004d0100c410250b4020704061000c0d11040c2c41074101803542c5001c0e0818003070049400380c00c0091182e8199613414101d80081080300c2c6889a02e544080083d031240295a0740241d54400c080a0030740000c1403d000015607545070302090404d03080141800d9400c0d8030012030b5600420400003a0384034106550301e08004d07800d01179200d007640c0b80000d440380510f0b00550f504003449410013007050740c0240d42c4094846042c0080002135040154142621421300000e000b80300f040003000d03001e600c14402154810484050001300d00e003419034a1000748400c2e030158821984800c0c5240c0080084814821003d803101c00d03504100f0101d540291809080c40c00281c8500d501040c50010300210705000c1c041070198500c1003200340c10070100842c0403111044160300091510101420f00d10000801c540441002410142555103c0b003142c1c0261900d4801c0d540c01606d207510180100c8842d0040b200d50582 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848010476 1250 848009226 848009233
    0x1e1605070611011b0f050c0109140c1302030106090b09040e0607020d0e0a0e060603041403130f060f080604050c0702150306270a02090d050f010e010b06040e15120d02 73
    0xc918100781c0c2134412504c03100c0011011500c0c5902c051790000c0120300d6a001500f8420f8854115000f400d00400c50700070090607105036131008440603c40858440445001143c500034225000c03460303d4102d01090250a020031916842400120300701c402600700349900600214101c0303042c602c2a82401d00540f00340307026038014621031809941000c032450308020b055450841c01840c101b45502c43c000d01410b241d0141030004046400c0c0003062100d4540e00a10104a039900e840741012400f00820610400b0b0304407044240220381c591041900720340442c0c180c3d4030440e440e290042040010704000c1c200c0c0d001d41400300f08090058445982c902003800c0d5407400551070789080740034054034284a10074102c1c440301d400c0400c11000031211a00c2d4011042100c0140c480c04a4004515881d0201700090b15601c641c291f0504810300c1500043c13082d040b2038000348125082c4100f4085913024a002c0e40c03c010703140e400052640040207601a0480100401040f6810302d0040b0650a059070100100b0041c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848011726 1250 848010476 848010497
    0x20d021c140903070816110a0b0301091515270311180103170d090c03061b020c0f12031315081302010504050f010c020a09060e0c1e16050706 62
    0xc0380507090039030010b002c00280d480c169aa0b0f03101c2c4001c1c4201c0404400f140080c120000a010100580c4004e869010f0b224980280d2501d8484265030024440d0a0180b820520010400d0a0921164003255038014204801c081c075040b042e100c0413652001280b8100031500c0007280d4140c5100445d0085014041517010400090144503200001051030716601030340400400004920030344214266050b203401030303218080d00318120003401c002e100c083d14002420501005020303196211100e600c40c5101680700c074001d0076100381d8640e041d0000440c0d0000c103000b04001c9074142100040d00d004582400e880c41e0201c01c180d5001c400d132050b0840c140c0200c2040c001102190040e8000d030700b05804a00f00082a1403a500082191140c2d0044c140681070080d14040964002d410040e4204c3d030040ca1003400c941c0f1244001c00070f0000c9e1041500300f4240d02d000c903c41000e003030110b6481c180c2c1c0612010010001002d4803036250311140a03443d440b00102e0040700801c50500000c8040c1c11760ba0f99501404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848012976 1250 848011726 848011751
    0x1e060303030f020c031b0705130507200309060c01020405131b14040b090103020c0a0506060102071d040305090a211505090a060f020909040b180706080a020d021c 71
    0x8038440c12108030500d00c10404181e885a001003506c1c4852800700864810031b40b05400313039081600d9640310a802804401090b050482d90380c010038400d140030f40c0c0b040010743c180c40100c0204001003d0035078068104001c150398906140008003985c0d2a000c001501c2c4c240e40b80e0203d0a100e65440d40540320740c1d07580d00c40c0b40800034000081455441c003407408082084902040b1101da120714407801d40084000a102c5181c2c0c3d0298069030000f80c01d02c0169101242c450034010b072944021603026005005141d80801d142d914088c030b84150f00a0780401143d155075a5034144c0b01c6900c001c800b10382c040303c011000507483c100040078a003100c020305990f001450b5580390280258004500c01b541c80360038442001039146000400359606504900041a18001d01000400038451060304a0b0008403c07002c210a121a4502c1640200d0303400103c140140345400d5400e455004901034040091802c01c003141c28004160080d212545c403401c00149004031504400d4510b01680804103900f03501d413114045c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848014226 1250 848012976 848012981
    0x4080d060f06090605070f080a0908010c020f06040b090c0a0312031d37061a1008010e07020c040920040b0f06180406080303150117070e041e06030303 66
    0x1484440449025241002c002a108140c80d004a40030084080b6401c0c0520440c0e03001c2060082d0402551a5189299000103250b13a08a00502406609040b28900b40c10710004072a5500b26a620241015403130700d595000510102130080000340c400c1030104074080c0d50300300b4503000a6124101c0c01d5102810340001500355120b0b03006030003c00c891082d0100000e0000b050321842104080c01c1c272003480300f204034940042464038618030804900955000208446603012500300c2d007040211540200544042203a480b40862455002076a2500100700d0003d11500090300288140191401a1600c0d0081001c42c0c0c9547e03000d6843c50f68403070144a40b200707040800000d80e0001d46090200d9840304010512000040d000e1a0041d2400a64002111640c20071401503520090042c4180c6642d2801a9503a801c00d81c0c08071b02d080400880f80500c1d6002d10b038040e8492504414401c8030f0360b0385203c19950280260100307500b0a444075000c9401044010740b00b10f03510400e0700c0c0007421a00b1410001c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848015476 1250 848014226 848014229
    0xc030901080a06080d0203250b0703200a170907030f0206070c05030a030c1412040b0a02070f080a1a010e010b03090a060509010606020d0512160203040f060e0f19060f02070e04080d06 80
    0x800701072340707800c82000c01c84800c0000e078851402d040104640c517031940185c0ba60504043c007101c25000c0842d00c144040d62000d4115441e00018084020780c2d25072000311501e03104144001444086081040c1e0014149900a8101540140d5041c0401030741c80f0017003401c02c00070039822000264022000d00401201e0121030707000380c214000a15034001c0b010701c08010f03881380d40a00b610004020910000d0588200031080c060300d00c1000030b11400d940ca9090a544140c140c00c2210001004954480d12100d5002414100c4540b01c1421180342d2030050100c0b11341d030010344044c125002d811703443c10204900303004080c003d0003201d000154003440c0107002800c0102c042e00c01c004114040000302c207611300e0f40405540000c3c1a0004490304e07034226409a00e940329940c4034050781e08880600050164205441d40c010840542c1c550100030780240400c8040c04600e4088645a40420010f200d1540b003800d601d581c9040c10b00494122303688580d0036404c650003c440c110b52020000a280d103130200d03240103050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848016726 1250 848015476 848015527
    0x2010c0611040e15010e280b0a0e1005040909171206131104170a12110c0604060f030504060b031b0f040c021e011401120203070b0c030901080a06080d0203 68
    0x242c03500400340001c15030401c08807000e2185401c055040c14101d40e0800e02d409545600701d10794503603a1340e401e400700507401c03070001007011078114ad501100500700340200c520304019903517549191034240310b8000c2c020540f0143c1551004403c080000f0f580780303010010700c0c0e103010207400603440745050810445d124103020700a101590410041c0c2110912940c281d130140c44c651441d0721710b0000813011070b51401b003420340c01500c542c0120260032485a0443c04101102000740140c45d4032908100030b01c01c00740300303512035070000406440c401c8100324480c0d4000d5420a10624011840c0310489000920b410840701c0700c04041640003025142170700d810001f42549440c184c4062241e0075400002a403101d004919266040b245070b060340307400070800e43c05134541003480300b0400000d5858100c12840121074540485c0a0704c0380c000e0105078030301c5071020b6600960030200210300d072a50b44030044603944070151070f1140030303500e488012650744024800e681b030300d1003035074000d5031039030101001100b0418100d9440c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848017976 1250 848016726 848016751
    0x2d0203121e041b08010b0a05040b1c0b01140105031b162003070f0509040308180304030b04290c090f030f010b0a1215020315040e0d170108100902010c0611040e 70
    0x81103191071f01e40c00d00080322402c58002807180001c01c0440c0c500c00c4d665a44e840160006040003007003001040302c880c180c44840c10b081a0344003001005680768407085d203a00c819108032002c0e05a03c01c801e00003e241e8030007000a003a0b010722256a5103200c004003408000c804003202440e82c1520b050400c0715400410b0b0500080c1a9546414085150424040c0c409420800403000050000d402c041c4028600b82d000c030203ca65407030340c3e828882e690010550301201c040b42c00ca540c0c0b02c000c01203021000c04800520604160700d8444042a0300c02d54030814509421a0504008691542d0180188200a80c3e048008078200842c2000c100b241a191b40050700425905036049005c510701b000030b0080c8098180300141c2c0c9445040440311480801d00c0c80591140c20400d450074852000b142c00150340f10f10362214040c131141791501440c031003024040d01001c6d82c4403130654044030026821100c429401070421583c101010344510702540c2d0b420203038403500040003e00704a4004182e603280e510100c000102d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848019226 1250 848017976 848017991
    0x23160201051308130b0f030a1d07050915120f0111210408040b0706060303140a0c0f0317070c020f1c03210c2d0203121e041b0801 57
    0x80c0c91594a65400640305050100d0300950302c80c0110071041c094a17240e034020b500c800381a00f0343d1215074811281c0406280c00c0404594001c41c078a0300103c441c428000260a04505000600c0740000b0002c1c14100014400781c001095521505e26100c00100382c2c1d0050300910300700b41c2c8541d0a40c0d190b400c194005c803100300305094010042001c0002e2300145604481915210350a04484c81d014682058440100004201081100390b40c080c4049910070f0b225806403c1100700d92008601403401003e0100b000c1c03080c4c0c400069080b0300c0d110912071103424542c0b280d0f14444204200541300b03c0f070013030200e40f120701c402003035142c141003c444400080b40d14503080c4c0713004182c003103006caa659001002c0c07090004034034500e118000100c100100d480c04082102c0d4414500040102e1050b16007911920400c0002c802001d0711006a00c40c80216500150314020000140d203a41c041c00070205000b800250412280150710308000601550081c02015032034103d01c045c0b1007a0040300e03802050389a142658 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848020476 1250 848019226 848019241
    0x60f0a03080a0302030606071401020307090902040f0302040b040f0204080d0239010e1009031103070806061009031e0b071806050a020106082b020a0206070809042316020105 76
    0x886002401c0c1d480c0c09a140e0301c440303000c1240348c001c4500c003e100c8440c60f85150314034801540a18071410711503940390000355459002008a20a034002c20001c400404030510141c00c0c0b9412680e040f04c40a00006001440e64127910304a13040364100e100d654101100c015021581000031b8104030003070782050315a2200782d0008810840c050010f8405031030b04035020480c680c5c0528110b440b82c11002c4d1080c806003910500042244015002c12a2030507094241d041441c14000307101c1c410b41f00100001c10640e1a40010400b00e02c072500c513140d08000d60b20740d0203c0018996176680c1840326010840d26203522262400e614445401041041000384248000c64014042040007041368984d040042d6600c035880e80480c05070505810151042c801d4207440070702c00240c4110400075100c0d4920070b0001400c030020490b02c03005444000703544070760140420004500c250005040485000b00000cc1c51405000001d03402c0d070201900c5e50300500b50030304028005034284042c44900038188020003007444d0480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848021582 1106 848020476 848020493
    0x110109060204060210140106050f07080d140f09060103030f022a0102010e030f3a0902010305010602151b0f03040c06030b011412041e0803060f0a03 65
    0xc0250f1760b8405036204242a40110151560180c1d00c1c0c040111401e41040030101c11200f000c100c1d540004403902d000b0990344920240103e080c07101407001c0703100654001c28600c002140c0c1c504022910402041041c19130f81d01d414600d41010910108070b01e022034500c400e01c1c8401600c04800e0704030f481c00c4511511502c00364028040102ea00b9503442d1240141c030490403100006001c2a62800300b0030303021032a10010011540f10f258610445245040081001c0000f0710342e8481e801419540c2c51b0142c64090034041c0003c100300300c000d03e00342c05440401403941458640b0445e100c081c080e03802c02151a03c1050901d07c1e03440341801d0038545c040c4601c0d0f01c14400820f01d02441c04026502030940310740c402d00080c840a00b418101500c00a80d04c000400c1201c0d006060254002c8803041c21040880c0740d8001c2042035280e141c54400c1c012049803960050344102e080c4001000000c1150 = true := by decide +kernel

theorem cover : BRFrame.Cov 847841726 848021582 := by
  have h0 := BRFrame.cov_init 847841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 847841726 ≤ n) (h2 : n < 848021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
