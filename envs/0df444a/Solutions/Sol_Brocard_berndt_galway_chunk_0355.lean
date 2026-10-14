-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:22:54.752621+00:00
-- url     : https://prove2.me/submissions/b7370cb2-b2e3-4f52-8a60-6c96bc00ec7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 63669067 ≤ n < 63848923 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 63670317 1250 63669067 63669077
    0xe031305060f0307031d0a030f0e040902010c0201080c09030601090c0807090303080402040917031006030c0c0201120e0106050d0302070509010501140d0e0f0d031d0607120c02070506031501 83
    0x140d6241442000d11400504115041d42400030800d0a44650803694624018a030442014150307903602900f454400007044000c90750705885c4025142c4c00c045d094032900d1049400300085503064001030007035044504024100f01441b0001041c413407100054504d10b01c8041c04841096031684015802410380041d52804118840300151203184584045001e072649691001c00e5602d4603400c0c48094140e0480031070341421a1049440d500e080348014510031481c0e10002c44101b80341900160484946200e0b07107080004001843d80580d802c285a401c440305954000200c00000c1d8006600420b229084183d12540c4080c500c0180341e800103524003511002c47d6080c100d0790f42e540040d01d040d200250280c5155406010702c04180426034080b0b4000c13801e650580c0d034003401400005085c807030303100341d0800469541c220900840d03894505440149405600a000500700120042e1a2000c011345220380e60380c88d5130700644030718424002e01c0028a800f82c409a1241041c00042c2d0321800300d4204140010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 63671567 1250 63670317 63670319
    0x50f010c0206010509090c0d1e020d150c020c060f0c0f060108070f0801091509030201060e010b07060605182d0a0501170c0109060c0c0509010b07030f0e0a0b030402010c060e0313 78
    0x700f008074032603030909401030082e007904c1e102d55105102280d80d076444003040c0d41e000304c0d09e0740580c4600c91551140b611404001d10400e00801c4120216144440100215484441c560340e060311918210340e1202098441c0f141c64010a9072118a0460300562851060140b0720000501c0c840004524080d60701012101c0d001c140c43c1d410740d41c00c903400304001628140402180308407040301584000012406071001050840e1079199140d6804001e9001402003800000d12605101c0701d4400c0c4400707004111144988455407115075040c510000d0020805506110146003482403010b2800c0003800c0c120a90000c1e03072805000c0c02c0001e040900c039210103580c0030211002c00031000720b8080b81e012016196103c0080c245901110f4034002200220386612580b01c000c140750359102078443c02480c602707102c941c1da001c4503e0001c103913141c0001140140074002c100010b1503540c190742102601c0082c01110380366900d40c001200d0343c029420014008624007110980e952130044010050940140c4800b2001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 63672817 1250 63671567 63671581
    0xa0216090b01020304030303020307051201030c050f03010b06120c0403050109200105030702070621020c0115050604080d1b0f14120406080610030617030702010311030103030e040504050f010c0206010509 89
    0x903641c1c8003661030060b0001c000500009000350b000d103070484921301e03000e4203042c010266092203000c2a041580d03451018a004c1205c1c1c64190300780040c1490a40c000d010455007030380403d02174007513101030b01701329107688001441284516050b076000f50381001c002d00910101e4188042d081420b0726070341d280d248081c02c2c611600d5000c1e0b0112801924035074004c0880d0303458203400702c2d440204150101007428220130004020742c400d0003e4170320301d40403400014440d1007844c11030803048030302d901940c000c00090004005855010840d01211000c0f4205007844200c000c5100c1c00d5280030500c020102400d04c4031080501020384941005103c00c40122440e140e40810740740e5190140d44140000605032000292150818441100c10842c90f42800f00c1c80c6910340680d4803d500d628450303a603080d44080382440c1550f81c180548000101e40360981440d5505584005200810752445c0c41c0c007507074403200400c08003d0100213174220400a04000c1140b0040008000d40b07400c402c2c420b03c1e10848412000c00d0074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 63674067 1250 63672817 63672821
    0x27040506061509091b2a01090302030d050c09090c07150219110a050a05030307030c1803031d03030301060c060e0606010f0f0302070b1503010e060c160c050301020a021609 75
    0xb151a044820070300740f078116030400c20105002007041905003c804e80711094510b441020f040911242e07082e29204030b03041c01906600050103c240d1078070742c1c14450684042500402103403a02c0721000e101050b82e80d00e00d0f19801c000d124a1040750382041c944820041896446405065414441c8004c100c295000b50760340d02c20b0340151f01407405088810314100706018090100310031940c10072401da0b17507040b07500e44406040401c00481654290000401c010845070305100e00b00810800341407100383c244502d201c00d05100041c3c000101808103014051060054400d800c0c012074000804503540e039a100c0600501c1d40031034400407560681400c2a1880d0316034041101c03441990306a450685009440000301c038512030b01d64a14091581c00c11844003c00e0119031a1445181019850b2140074420310a141c210342c421a0003030710a8208a090051042071b5600300c50a16910312004011004913050841c0c600586501259156200044c10350f01150045401c1c5002c0388048020849140d6604a04007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 63675317 1250 63674067 63674089
    0x180310020a030c080c0d1503020405100501021203090d050903010b0a0f1a0705032505030c01060e1311090901020c010204030f020f0a06080a020d020c012f0909152704050606 76
    0x1561034402e0200c120014482d0340007c103004054010032216580d40d07000701301250000d0398201200311041000780302d03550301009021118403c190802c0d01c1c5241c210700d0f007622110034444c80420080c001508485980c3c0941040441d0b000c02026106143d80d03a41d0704d400214103a10030380181495041c102d10b9000b031401c0907210402d4100c80a10721b0240c4031841c2c920550354801c01100402040503a801c0407407400c2001e03003018442c4100000d440d5003800300704080500300402040190026101101c005250704200c030740d07040425541c151680d250080034602a0042400852042d840031130300100b40001e908036807100c14025240b0104101c1403509111000006004041c00710b42e02da00860300f0010203600624820250303800050a00440403402d03402d4407482c0510300010f090030070041c103450030003031300e44800702c821580f80d986032052020115410a60003400d0041040c80c3c286096625141c0c1c01c207100c030f03d400740555490a0880034032000d202c0a01074800792894410341b0000703400b81c148412289 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 63676567 1250 63675317 63675331
    0x605060607020a030602130b030103050f1b0303160507080f060117010209060a080a0906050406020703020c040501081203060301060b0307020604110f0d0602090d020a0603020a0e0d17180310020a030c08 88
    0xf4041e5003182ca84034045d51059045164072507483d00c0000c0c0c0749907604041e602030351044c4060154054401c070790381e01d049545001900184290341d00241700d66000000c0b1041c0701020782c01c0b1901c1d0440342c01e00c1070901c0c0444d44810101d0044151400209901041d1641039030118800b8030511010b40101600702e0203905040b80d00020100071115465010302c00d0aa880481c0030790104081145941d00c4003503a02c1560b0031102c1a40202d540c2e001c154040c008044050b0054500300700c1c540c50850351030b81d2280e80b8110394008090020206449032002c1d040280501303a441b080580d41c3c282001c000317507600705c111426690301031a1440070410b0314191030352014203440145426040022600c03130341c00960018080f907500011194000005071a040e040d540140300c16107005803502003c200140924030b55040441c412080a410680020742800034403a041c2c0700c0120003610b41c114100350381e1b0b0150810b401541c0c14400e2444c1c5200e80e102c50b0b0014114800d4942e001d0000b00e12224040d14180019903040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 63677817 1250 63676567 63676579
    0x9041103011a01032406120f060e0415050c0306100c0b16090b12010e0c12010f0f091404030311120108030304060606050a020703031209020612010e010b0705030a0315030203100504060506060702 85
    0x101b20700743c0b003884d84030000d840c054000907100c9411403940c4101e9a282d406014800c00000170803090181c2e200d0001210040c096043c082e5103861017108180e031200502035031041c08a00401c9840f10300c00c141c0030365a0741d407001e00c228441c284201d0b0038286085c44181000003802d5840041081034604042d1802205030b003c0700e401c1c9909006160008600c0180701c50780c01c480900618051081c0030700401c0c024841035412818503410004042052000c54200d20705c0d2904026210643c000c84044680c0d1090b01407030b0000b00d00c0103080d03128a140c49030f5482e00c004802c0b108004100d050b030100086005520440d0101b015541c2c80005440902039a4030000250300a82070800101c0d0043c107036070380b00c038282030310000e1305d91811b50024403142c0061a100350300c050340d440180071000c6142c0c1100c0c09401020f51443c107040b0325a81d0740d6900e200e01c40c03e880800d6100c00e0491040b0b468500b03e0400342d5401405c1c2e0300c90441c440f80300001480c04444c10381d603141c20700f80441c00c0c50a0032802c9404041c0c0103080c0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 63679067 1250 63677817 63677819
    0x1051203070b0426130501030506060711061b07080d02010f0504050a03080a1d0307110a030206030a020d090f0803100e070c0803041403030403110c01030b010e09041103011a010324 79
    0x51a115484130400100781c126020080c1071440b65103000610b220210104040300850801c0001000c858004103528040d4108120010100e040c0000a1180460888200e0b50320050401403c9442020441540f41842014404500c1c00c40204080f010900d081c0c1c001c0100800e80c4e0b000c0002c2d10010354010303240313810680e40300c000b0034403540a16900c004626004a40c4225060502c089013820f07811840c0181c00c0440c000d0100000e868280314503c004603040e410481c11500091340910028286445141d1300240084100c130541c0c10131085940c1040c04495090380301e007080c04180c1c0c4103c9020700205010300000c21005862011240184001d9a6440303503014169540c05440d0b10140c404d80f420382c1d00041c2d495181d8004c00082d84500d121b940c0d2440030408108105103130928003c40641810b0400c1c91403485641d100214014106040765614416210750501c0402d0103275000f045134042d403c08098441040b40c100c0d110114140c00e0380d04000c0764180f066031050030a01e0001424400c8501c0304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 63680317 1250 63679067 63679073
    0x3110d0f020405070e03062d0c0406120609050a0b090a050709090b060c0a03020705100509130c180303111501080c060912070f06030506010503070c12020313030b01051203070b04 78
    0x31045902c07101030308003a035a00c018000040d151001c00c4825031428002d107000310489403913422488d4035980710b51440b0f1841e400d0041c00140c00e07001b5401581c007000006c52504000d110281c01410007081103000c10041c0781040c7c0f0505020742440103141d4005c40440000c01e450700d50b1440345074458043e5a075040015818528500003800d000004c1a5003c4020300a00548140c00d00900001070b100e03800070070140b4500010b1200030103000400c070041c000f0034030480078180c985e0b140e0f0020310030703e860300020050060f0005445121780465520780301d00210101104140c0c01c02c0c0014100f880702e10465005620f03902940f0864002402a01d00b036400c0301100b904030381031601c00390481e2803005041c003007100c0400c05200e18048003980701600411030300c201045059094030039a03401900030f01c0e11901d54903184074081c002007003c00e00104050420b881103041d030703131003442910400c41c070040f948007800790349091503030f0a20820300580d4480c494a0f0301918510358000704884020b98845140e01c000d40d00c6031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 63681567 1250 63680317 63680321
    0x12060609010f0810050303030a0c0f020a0c0b0d110309010c03060f03030c11040b09090a0303060f03031b06150b070b010504020702130e0102070212060403030506030607021b0a0314060103110d0f0204 87
    0x141c00a400000c04e514081103e03030b0f06102461040b0541c00001486900d00361004018142e41000b03001550450305800010400001c0040700392601c0840a90b81d4114080e00d0034002c144000d15500500404414008a400190021950786a440c1e505025464448940711500c0d58241720080102d105400b10400003803044141402100008100080707980b0714801003074410b02c04550003119500004045c804240c2c0500c10702000d84000c141c422840750560760f0140120039444815920500e402080c0c00400005800c01c0c5003842d80510710442560380d941e400d401a4014160031580f0140400010640b410648242c13980709400600e030142c4aa44403140c07100070550950008a1950204404005030700c80c1560100c44c1c5082200400d000d05c0e0a040040444030042d01c3c041c4a03403c03120078807603815400114009002e2400f0310407902c642d00c00001844405e49540001d101c0e00b0802915400202c010980c03034104d07170182070311480c0408802e0070004180d0420030010448042c0e11412809800c01da = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 63682817 1250 63681567 63681571
    0xc0108060f0301020a0f030e03030112060f091b030b09030a0e010c0305091c05010e1b041505090702030304120c0302031b01092012060603060403111002030c12060609010f08 76
    0x103000344040c041d200000c6801e84e8455103d1401098555003000c1c08903a0520a8985d000341d100007031811541005110035001c1a0740744060a69911b80c0520301070710384554404129030b40e00403e0010b180c0d0700c1078800103400c3c9641c4010b8a001c180c000000300003540110494500001c1030b6140c0b062210f9010054035513a01284050303080010038040f0300219210b000840030014080014401c005a1600c0e1540c29141c0c0114040d0280c0c0011105405034100150b1402d4441d90448001c600020218010080ca1a442d484240c1c4610100184505281c01200642c000c84c0500701000401351440d806451020312420000c00680c020000e41600c144424120a0394040785030000c59101a00d49501d0389400d641c6948910180030703c82504a00d1a00d0b0003600c880d90590307406480c240c07400c5000240c44000041014040c00407074002202c02d070b032052000c4148100c2e1842c00f151242402244468580c00024605105030b8180e40801d0162406209440940e00705030b4403103200f0946208101c581c8140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 63684067 1250 63682817 63682819
    0xa080a0207030501050f22020a0e09151501080907030c0302060a03020405040e15060f0d060203040302010209031509010513081b070f03031125060f0219060e060106020d020c010806 79
    0x34801c0007000280c820301500340038444501800c64070f410301203218150781e074070414584624a40c0e00003902c01070300c172410300004403120005085041e550b9a001c043c10404081384000c40000070508000000c0707840c80202502c11420781c1c2e6440141e40341413010350340f1b4206010107030a014a08008100628280c002400514940e113000740c1466603038400b1606403602e4220340302c00d81d00045408001030300c0e000386aa9000904543c0c000484820b14089020440c500d030300500120b0b00000010241030003501110350400000d0102ca03450f203003400c070f1600c0c4014207480c450001c0d420180400c0f800c40705a08100f20254128841603e0401c0110781006203004012150f80c3c28041c441002510701b40c2050640d0023503029032640d40150070380b0391071541010401800c2e400e0030541000c00503405585010100d0075a807003400c1c04801c000780218282d1070110a40040d020001d6106072150402c096500710f250b201010071300b12201e90b600c4000507610fa00c03061200c00c0040e805008441e00642c89408481d4100034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 63685317 1250 63684067 63684073
    0xf0a020306060706230703050112080c01020f0f030108070f0b03130201030e0304120b010b040f0302060307030902190602010e0c0619090905090607081003030807030903110a120f08090a080a02 84
    0x50190340d00c40a448580e4069030968400c00c980e8003425910030003150f4011b20a00d4100300740d42c14040410728209001e403020340040d4000c46e02c00010b403800d5048a05515103c40d05940b00c01c0200500e0805034024062045c1501503200009140c401805003030055500140f255400d594810644890344807a408041e81010345414000c20208010301c000c1c405440d24040442821072075090280c003081040c1d1186034080d81c10030042002e0210b0070018000e40350304940d11380c0d603070700e070210304601070035242402a5224101000340c03241002e60140c21130860b44590000c0c00358201750005a9180c2413035150040d04900d08219500c0f9040e0206210701c500000360900c5240c003510752600008882044800c008e140e0300c1042444841600b0140d00c65111102c00b400b074135154116038009105400142c002803e00d80c4402c041c40816014200b0140c41356010421900811118140362184000310001074000c28117070650039130224480c62000d0b2140c02080c000b802c06800d0341e900d03e58550311842034041140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 63686567 1250 63685317 63685327
    0xd03030b031e0616020c21031b0c1201140c0a02010603170301030b010e012d090c0c11012a0807080a0201050106090504020406080612070803070c0e06090f0a02030606 73
    0x180c001800400100c0c0c0b404010001454500c1488115030700d0b0003004d40035544094000b46207580e94501e0f004240c0032004042051080040361146117001d40e4880c07084404910200c05030309500011102581030013218550000168500a1801c9400141d0b15000076001c0d40002403e00b4070a4000b815402c103207200004080c0e549403224032a200300305400007401d8800000404c00e00074002415805000c0e500304030300c07465150200314881882030701c014441c1d28007030021804004602c070050341d00400501390140080b01c2180e10081c4561034410044816006003845468a54450700d00c0300360b149103248112242190301ca42c1c8560148070504101c0e03c81c20100640000550041c01a1031242040c2e00089515414000d0180c08001681c10080c01948140800c11440383e12003001600840150385c48003d11108020803414002607070801075092100080d03240c20403030b4600016040b16510402c440d850b40340c020411509178000d941c201b05240480b030110b03180e850709900468103c84001c01a038509 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 63687817 1250 63686567 63686593
    0xc0415080a0c050a14010203031302010306031a07080708062b0204110d0509030304020d06050603100501170105060a0605040b0d021207030504050615091605041e0f090501050d03030b03 81
    0x8411540303012144050505801c00c602c0c1424143c00000c1c0c0002c17001078208101d0100003e590380402407516000303c0d41c0400450540e40654403040285402842d003a0707482e0008042e0b580303101c1c1c042c0c45d100b0000c0c1038a00042c0d5814480d5101c0c6009440c001d1030040c10300c03000300c851100007480400c102c54400e00202c0c420010b07603403807051500300d024441415031541c00c0c6105000446000800071b1311203400400c20000182e46142c0b1070022190311513800969600d6400110f0b01d070103108075450f2111440d1034004130310480e401091880c40e03003250f0003d101d1036441c2c001303010031801c4a1180300c0100700140803e01000060002418100761102401414180615040052040305031006800310f56981d0600c0140841840500c1d4010a80b0312940034607101a004921310326401400060100540e81d90420b00e2442070080703e0040a50f000b014400c0c4240c480c031003e2003420381c4a1004920350704580001c0b8840300d8010f19040b83e1004000544040300c54400783c01030140c452a1a0b4103024082140e030130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 63689067 1250 63687817 63687823
    0x819020d020a09050a0e131709040903121d0307141207030e2e11150a0c0f110c0f060d02030403020c0103060914010504090303061a03060406060906020c041508 70
    0x28801a03443c1c1c40701500e800300303100d20108650031034585c21900504010b22140b06152050780c0750313489061091481c01940c2510858010101802e80c0a41030070310711014558448142d00c0003c0c076000f4104580001162580344010301628403092030b0f0020700620000c10f0030b40c1800142d442081c81034515104c020642040c06900c4403030b088010529104900c005402c03d19141c507582140c000a51101c64030f050070120404034450f06d513600700140700407440300030741c0188201d40701400c0300341507030351182450030000f80070b401c001101c0c0000030441414205950300c100d6001407000640d0014220490021091026800b009007440760001000c100303801c00f11450f440250321480c02076001c0c122400100d0300040c1514583e40c400502c81f030034107203c0009100d0511055044400c11240050103d061780b800303401401d50f99000900c40894088040701c140035031402103115800c211400c02149031121001d8400c0e5550340209801a4044500044a81001d50080400c00d1525110b00d1780300f680c070750200385 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 63690317 1250 63689067 63689077
    0x90506090d080c031f1d0a05010513200711030c0306040317091f0b0102010e07050616020d0c03080304030e04060e0402011115090106080f0a020d0803100f060e0f010f0819020d02 78
    0x40e0306c0d801c0550801050560210060304262502d906004d2545014005484122104041d038241c1c0d0752a078210b10140b444a2040d03100c40c000d4541103444144500706003009410310070704140a8004d60360305898900d40030400c07521881c2c0c1501d850021203100110480403580040a0860510820f0901490500e18589421840c2c5c0500004607400700ea1000080c20b40c0d0703400e005840d0350391240c50140030560740d0320140c6202a000c0000035501c000640000b5605c0906207101030050312082d94084140500719000b98415401303030300c80201403180c035000d12044880794802e8081843c03070200850010340c0301c0c1100c0c0200c588404210b4049a001a15409881c01c00b96460041c507075440074200702c03044080c0460b02802004602600040d001d40c1c01042c03030103c42010091544c8000000502201c40080500b406030403441c5012904544858018082000341050107110f0038001c108100603600c42c8106164544455548195988800d01c004543d0cd80403a09400720079002d1208a10300786182c40948 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 63691567 1250 63690317 63690329
    0xf13030f08030610020a1203020a0201090c03081e0c190201120609061a0f04060c0206160c030204050108030c07050906040f05090a1403040807150c0b0406090506090d080c031f 77
    0x141c0d6414a0030400c490300c07030f03403c200f04151b400840201000c42c8594504a5601e0305504015a9540e04100100e0040c040303110020311401d95403501205020840c0d014022192a0741c00c500f1204500d604025007130b000b50400091958058581c00707110079000e01c010a0058418100340480301203084e0f500701aa00329030040c04585641c0e180c10008541c0d009a110700d410356504195180000ca42d4105d2180d1280e40212824402105000c0d403c548403c0d00b184c1160500c94507040e810031142c0f500c1c81c40e8680610083c0e01c04d9003014000b00fa0420040110385200d4400340044c100c0e00d10348000d00844840080c106644035a80b003600d881e4005c000c3c01040e00c02c05151000d89043c580c0c629114100c02041c0694149561040c807080c0721800c00041c0c950162054034064850111401c08212034031040f000340241031540000612080000341d030442d0760551721500540300d0310764500200645d80c01e52402d01c00300181d80a0081680d09500600544c0c0049241d560141c8803c50100b4694103070a4a52042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 63692817 1250 63691567 63691583
    0x330405040b0f07050a02030d05060105190807081b030a0507090b070c0e0c0703090b22090b040f0b06040b070c0801020c0a060f05070903021009090c020304051507080f13030f 76
    0x100100d5024030303640b907105003c4c0c2000d904214004c0402580c1c0c0c001c3c00d6035040c150f65103001040090f0301440c261071100d401041e550500101c524030003841041c05544150202d1a11004500342c8211082c20b0220a604a00140c1c150360f55042014085e18010b4290424080c090340040b804040c0340d0010101280146599001c081c44e20511035080000189010b42d0701c0400e1121400080d0300541d414110f600e0a00155151a035113403001101c0d00184000b00056910320000003400d907201d42107036064080445003044001f9011500c4c401f55120244102d900c400200f0003405555890006000740c18013030b1550740390454a9901c002d0881c4c1c0070010418803948001050010441076002e4407520b0242c800e01801103090502e0041c02c511500d0000910840c00c401100341e0442c420f00007036000b8520902c05004c0e0b4440407101071f4032a405405003502030241200d040400503034080c11106040d61102c20035180404130480c04009800a00c02c901140404050010200d0209090000d00d280900c1d80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 63694067 1250 63692817 63692821
    0xa050603150409051006140d051f0e010203010306270c050d030e0604060207031707020906010c050a0b0c030901060816030609081e04050406050915011b1a0103030e010503330405040b 80
    0xe842058011007401511402020a112300003400c08141000c42d40391010360b018003001c040c240b42010304928040c0d21b20700c0d803002c4000014805241c100c8400c0d40300107145a100d02c0c602846528082d1040c010180075130720f030b03180108038a00342001031341e1501c0d000703280a0212014080016001d580181d02640050740022814000d02c21003406c21118126a0000c4c03d1600e65160701054000c00000e20042c1442110400441840824400042c40d41c0c0e10984c803507200e213440125940240c10588503480c9544ca41440456460800160319100b1040001ca5128035803860b81c0d0a07001c0e02c04002c080307442d8182804071540194100c0f4100f01420300142804d0384450401060000311000c81c2d0003184a04010818410f00416045800458031030a00e00503c3c000c04807101024032080745c6200500810404401d42d07580d071007507020241628405d07503404080000700c4c1c00440e80340c0000d0307070368820f030032142444401034964075020402401e00f07445190400381ca28038002002c48500303c50684910540000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 63695317 1250 63694067 63694079
    0x3060b01030605061c11070f1208060406081e07180c0e010806010503150a080d03020705070602240702070b07080a020c15040515280e0a050603150409051006 69
    0x207030788080c10041c0d85032820f09413030f02044445016036179600360b0125541d10102d03890103030190443c0c12081d00303e0418103030004240b81c0b00c0340b4448104090400905a10042089490300340607080c111201c9800801c41d881c08030a03489103d070030b1003030450040e114000f800a070300401403082400c140307101d620002d060450301101a00307818841007241c5c10013210034100096030b07070440b0540303800040c00105007821782112008102e403185c0c03d80000c03035580f0071088194000c0381d05030000c00300c0c0c9102e04252000155075441c1a40c0d13564410390090741c03849103a41c42c0720340c00352401c101c1944aa528030403107246d2a500d40c81c024081d40081410340303208500164034044540c04000015452800703440082a802d0700420842041c019030041c0e5228103119866042040c0d1110290f440020080c620642246445d040348010174901c00b01d04000305900001c004000e15020301828122940904464916039420080900305060207070700640c49952120702101082041100c1d01c584412a0000580642048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 63696567 1250 63695317 63695321
    0x1909030c0b090a030807030905070f08010c03060803090612101d040212120d021e13050913080a0e0414010b0a02010f11250f06021e131e0b0403060b0103 67
    0x304240c03443e50122100c500020307482200f581c0c3c401418580001c5501880c601142898102d60182c507119440c00400708501c00107500c030407617100c4180c808108069440003c0723a200e0281600e51584000c044c004c1d824240360342c120040d401440d001c1d91400701511109144445109440b061b0580c0c21032070200070442c14405240546000c0350b0340100b040c0081500c030500a4490030072400400ca40125031001c00741c841e2404032003216041c1c060251207244500500d580352086e031051500c01c00c00d10300440c030f107101d0b103050002440e03400c6108140f40016652040e20754101c41c04c0030980090383d5400041144643e12061806408000704032507817202c280500030b00790f444185a200302e042c542036001c81640c081c0008c44480d00d040c2403d0800c450b00c8805141120380e00400094086036100b01c0503001c1050701d03801800c01c101056280c070700046581c03500a03c0d034000c1188070381c008510030005208000c1050403004056000315420800355844240c512100d07000795000300c4510f600d4400079041d40d81c02d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 63697817 1250 63696567 63696571
    0x504031101020303131211060a15060512040308040807050607030506030607090f18020405120a03020601060801050d02041a060d02040302030105062403090307020a06050c1e07030204051909030c0b 86
    0x2403000f5421410055202c9032000344002008100c2117600100d1003006000b01c013254580c0c2200c80030f4800d83d10b0a0208417000e841da10300d0700c03010041c4090001c91094081c5041d200c440328642c500c808a9500c0d41d8096600e004080d00644507080c05122041c000760041044c94403400040d94003080d1400d00341c00345860000d0242240090014a400074090580300a102c80f08a841036107031200d001c054422038038000c1c031a941200e0340182c940040148103140c001100301040e4469401c507515680d03154402c0f126242d0a0240d035520805016030400580380c2604500015400027800d6910003940c0b100141244d800210b22120080d0017107002c0007545802c0c17164a50180d0180c03050701812916142d002d0224681c944c500426420204c0410303603c050410507503c840354082d10456040382ca440303025120390480a00080c841c03090301c1f900310102c00c1c4c9a10707501c148070b1454000d00d40c00d415075081201602004000703c6902041c00310070300035262640100c00c41d5a001e519106080c10550914002c04140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 63699067 1250 63697817 63697819
    0x903041721210c090609190b0310090b0f010302180405070903020301050a0507020303040308100537050604120213050a1506030213090905031e03060f03071d060a080d05040311 77
    0x12941004030070a030000031503904500c1100c1030783c3e5400c00240080c41640c1c00c14624a00c0442c902408034034208c2500c01075000e50310341c8400390112030340c8000600603100c080d0003082c9c02800c241032a1440d5402900a8100c01c00c41905850352241c100c00481d0498404407003680000303250440400070b508003071046d1a01f158034520300f844203141c68100690760b84005040181080504070016100c4800542031030043d18009140040504c071410b940800e010380c40114400c11894490309100c480075500d0b22004540e030142581303082c5842c245d609075180c42c00e07450598103c1d1300c03602d82450a0006100c2e05118060070100014101d20282030640720510a80002041c07510401402d81c08105070b40251003262090301011521150f50f03d0300d10300314010707075016000341035a660b0704101d040e2002019521400c0305864281c580c81030201010b503610300902c501006070103c80d107109107030344841000700d620100c0503100e541040d81d42c00c182c0d0301e0207104103681e00000d000402c0a0042107101030b40d09202c40c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 63700317 1250 63699067 63699127
    0x906050102060906040b042d1101030c0f030f0f09060204080c060a080c130b16120c020901031412070501020306150c0c04050712021305090c030903041721 68
    0x1c0c00f03840c1e840e03542070082c001070404620200001c0c03c00210721990060901a170078620303406c0410f1001907441040c8441c00311500c862240002c0c200b03500c24070a640030840305035684041000c10708000c0c1c006169000021802584403500844254640d0260060140c4100c400580d42e40c0f030b00030450304103007001203454461442001280d01140c0c0c01001c080d00700340f05484040c4d81d0700300c4e440103050100c9142d00c04046450081110406560310002d41c082d02d0707001b011080c2c00d081c0c11281c11180d000c1c3d20500258031401034001400801c1c0c5e90720b0000540030242c070447d1404601c407015400d05402411048419039000810440d15052600d0740b241c06024240350305042c0400556002e45440d5910b0f105400346a5910000740c44c03521500e4203000e020400002107580d00e06411800e10215850b000d514007404110b80410640400b00088a00c1079140e40061402c060a1011048400241b020320203114814854100b0424890a40558400082803889540c80504940400a03c40320240b6003404070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 63701567 1250 63700317 63700321
    0x1c0f110301030b0f060303030408131a0904050a0b03030a05070c05090f040302010f0908070308040c0902190201060503030a090e040515010605090316050114090414040f03110d0903030509210304090605010206 91
    0xa14000305903604280c0c4410301e540c4030b807101e028003c4cbc00c0b40690700000c4c000414202d5452110440b40060000f014160740078001c50713880110307e80580b040c5100081e01a441007043c03810030740c13244014080180c450429011039542c2c071000505410340545954a98900d0101488201b64091080c20545515486c0901c10040144c0740e43c41e40d401015800740501c00980006001c10004102c000e000d0030030858210744400300b2078070301080c4007904509407015620b41240800e403403800000351403d07078a49940700c0e102e450900f0a04005040050002c0b1224864520702c03440804450740031a000c0d18140d910503440d00c03200301c00c062902165080d0028180c10050040c809641d1014004410703400e01070f0700aa5440c024401304e0300500140c1c90704507030038181e40d050004200360b20340d90f50040c602a507641d140ea400c103058202c0c0c480c4042c9000340c0103d0140380007040080d00400242030300450051440d1129601c42401d121381a9505801c40b960750000101403182101d5482224007800007072005003414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 63702817 1250 63701567 63701569
    0x607020607050403030521090c0a0b03012108160605150d0b010911090d050318060f0304030c0305070506040f03090f0b03010b16020a090c120207081c0f110301030b0f06 74
    0xb91240d8007002e03040180005540c42071700e405804001e03d440030520480d1103482d1800c0901d0321611035a010030b02c61000001c5c001040340051058070706860400c540074800c0111000c00c42000d051b6620111803140c4107114000d6100b0720700b981d80c0d810070b015200208451400ba1440d035031b800b00395030703c491144c18440012401b084040c114030b170654089400000e038450902030b050025008240c0910340c030080d81151582005800300c0500b000303601d403529401c1040302c01001c0100768040c010024280c50002d01c00180402d02c01d00001243c01c0c080c0c10060314202040d00c0b01801c00358100da056800e4117542c44440201640444640300400c82d50315012400350400000c00301034401845000f622903004203107107100348020f04103410400c0d40240300c08009640c0d00c1515000d4080c198403480843c0740f048001e42c00c41564021190500d9100009074074001d40049524605102d6080540400d81d482100c0646e9a80620aa04840c1c2d090010030340c4070340c5907281413000d000d4001d04000d05000503006100c00303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 63704067 1250 63702817 63702827
    0xa060306082b11010605030d0504090b06040321090317070b0c1809041b0608090f071202060a0c0b1311030c030703080304030203070b010621090201050327070806090607020607 77
    0x501e1161900b24125600310f40203a014102542003a42e02d400341103a101200380e088002401241d004200901030b009602080001078091444003402521003401d040310718500322108428150041d042c900e03100c036141c0e15140c074a8003550020b00e0300c45400003074a030180058140815409002d0070340c840e1400040e03c0420000c0144d0041a43c0510400008201007100c100074100040302e04403c0c0300349540d40d50300001e08400c401d540d019540e000b080007410f40c0d50400328800c42922600c1001c0c442401d496401d214455100e80d03421400c00c207421400c41d00140d4a5890039028040381c82c0f01002e108000c0c24510601d0f500300d2402031181d40128a4004103440100e010380031690040b54907600e9595504060b0304610030100001d04041488001150080d0084200ac151040001c907510341e0f0581103006000b101c146071006800720f1030a00005a00318038461017a10808040d0092600750b101004801d860900039811428581c0c02003c10045020b83c2000b20b603910241520060420303040c00c2c000030301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 63705317 1250 63704067 63704143
    0x3140c1603020309040509070e10030506040305030a02090a060207060311190f1103040f0e090d09090f0e0304031a06030601061706040e0a0c0906080f0601090b01030b0a06030608 78
    0x2101826400003201414002d00036510380302c00280c8240002e1510310540ca846001c0350081c1015841d00390045185031180b800040282e80d4804020050b40d1540d4606840580000b05904d490319001c0101c091192989800d010040c03203113400030041503003406d0025094070401a4080e9440d64280465075880c2c0c070740026900651140e0400760001140b502003245c3d81c421030520519a48030028000403600740302072050040300c2c1c410318441e00c25154451402d49400000326200005910710b0400d000310780c89544810a208010000052507040700b94800c7e0640d0055071065903030a40701d0030101d85440740c2c0e4040550040d002c40190641d58100301018007000071804410030580d8103800000c0300c17505c83d60f0000000a8601c000c407500315003a0318117042481c4047c044c11b0351145c00c0807400034041ea000140d800c2a07650b24400307022103a08140c25000108090007a840c10140c4441800202d910f5800c000409442c03160b4000c100541008251807030701c0405681c10848240d00c68650303842c522038181c404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 63706567 1250 63705317 63705337
    0x13021309020102070f0314071211010f0905030d02061b04061b0206160609050d050903120d090b01060914060f03041e140c1201061406070302010204080303070f03140c 73
    0x64003211400103d00d00b03030903034101c05e09980c4050404800e000030101042e5024016908480c0141d4441c94145082e040743c4200401c0742400c0304016110350301469041324940c001b071424540345a40d07a00001c4c5800900410781c00942c10807411300245210782c4c070800b0170025032058803a1074075180040041c1054145602d118020480703046e43e504541d100300c00c0b1410b5a052a001d1102e40000d424044028028200100d54900c80c0c0d03281c0a10280c040c1e01a0784401200802404030501e0001c50001141c0c4091040704240c1c0d500c001c400f0000b00c0d005156400303880c03250785404c8028180323022407940500114950384181da0034000155540012800c41b540b01d0740c4905074140083c4600c1560459208040b0018201c829000075a1080c14000560b4850702d0400c8444840314182440c015080342e03543e02034000030034883c0050b00d0141c10583c0041c5448e5209100051406555100d01c60554106840f0b0500140031007070024050717035050045100c0c195407561540030908221441501c0c0d1b01c245010710b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 63707817 1250 63706567 63706571
    0x60b03041716050102190e04050c09040c0201020904090b100906081b0310050a0b01030f0603050a030804080415050a110309030606040c0516140d1b020618030a0605040b130213 77
    0x31180241d00312510b040607580180250744801829100c074a441c0e010345c0f80c4000080d07202174a060a4a0680680c900803c1da0f500142d25103000801840043c000d0486284199034003041480101d446601c600002d0a000d1840e4a0060500031143c3c0105d03106540103400042c00c3c2002406022030110702e280501921041220003500740201082c10442c0805041a8243c60310040201400c00c03604842a1081c090380c04000883c00e02e415032088414500015155030300ca031002e400064000c1540640044c0284022800c0a81d919088469101119118400100013158082070b00c1e80200301d400310400c100300518245005680401d90781c000041015205035190340c6400049402201100d42e0306100515040400c21326081540b1034241181c4201014440c0c116403a421a1003404894100501041c6d903c0c80c81409800300000c540041c150300d00c01d041d821864242555041081e56000c0c1d111348000b0a0314a841d04015400304001000d41072210005140ba40041e0342d4011680408000c190b80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 63709067 1250 63707817 63707827
    0x80c0a030b010903060c08010905090111031909050a060b040b1c111306090e15010602070315060506030f0403021b10121103011212020102160803060310050c0706060b030417 76
    0x490300f64040f07600240c03000c2e00c1c0c49003d40d0141ea00504483c16160186001d111541b222880a4206c41e01c0301400811050140003241070301d4000e6600a4140d5408400424004850f44880d0b060004d145000c561090350b034100d1100784d007800c2c001d00d440c141c0b045499807040710410140a021036241403009140940309003000d950f83e550382080c0ca080440201e03003080066114003680c4018410201c25540510a000807198034040c00a02c5030305031142c40d07028245541c55541c4820041940020b001c850300e80703400011940da115a03001d544036070440171801d9080e0820b0b080c080e0402c4540c0032010444508034044c50542e485074001d014003d089850004034940138008418003d005d0b5005a00700710030004000104000c21440c450400c030300803a29040c130750720400c1050b4202d102d0046211b100111140c0080003007640c80018681c000e0021701a83d841d00c104450910484804465104d401e00001c2590003d200fa02d1044401038107030103000510f103050036191900c0e11a00d241c0c107400243e00001d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 63710317 1250 63709067 63709069
    0x1202060a050c15071706041a060a030b030a0c1d0105090105060c0a050a080a02071401081b0903151005010c051018170406080c031e071403100510080c0a030b 69
    0x10a60320b0443d003d50141249040849000b000183d06818050082c0304001c0071400c00c0c9401d204405035200c5400e107040e00c20141e4800e0120366040140741000f45691010b00704241e803024005040703c24844d103d01c0321000e0401680300c1c2d5403042c40e21451451143c03d0014007090b2078800e1054150f40049440342d440c1e17003003a00c1045c0303401700700e000090050042002050401c402d42e0090074501c103e540958214a0301d030046041101c46400c4980e000641070f4010400000101c00d200c840821510461450300e003001c00403070728150b582010791662040d90000c01001040b40e0250300041d140034686441a680140c45060365202c2691030015069a94107210b24503024640d500c50140e0362203628485078180d403406448481c4c00c03d03c0344902040c0d0050004081c9022081243c0c0b189941d2414031010605040c6000012040140030b10203000c070302c01c070501c00d0382e04800c003562240200034460741d0002d041c02e0912030b9180e40304058205001c101e405210b01e4250030303000d503603141c80e45240024100701468 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 63711567 1250 63710317 63710323
    0x6020f12031005040e0d02010c1b080a121d0c0d0305070605180a06020715060620071a04080c0d0f061505040e0a0b010602120403031b05070e01030c1202060a050c 71
    0x243c403090b40103280201c0d5098405000c5110b8a54036042c3d0001c02402035102c40944100704144207890103445100c55404c00100c009016107650301140c980b0f0342c90407961010400c200d5401308201001000800d500c0980108100514040070f5400e60703115006098036a0058194002c48138002e1aa5071034a000410324105154000f451100d40012200d40241d1424010025030006806032034008400724001200e03426406810100c61007540c40e000041d00c0041c1503580c4c014407403880300c11401694800a420241c08101c12043e0034503000e400d0ba15490118454075244001c8210f42c01881c6020990f03001c501c0800742610751940204002c06d00407001e019042820b4044d0b0009980f0514050000744541d4002800c0401d403481031307000b2142c603600c0340403d82c3d480e0451864402041000c000a000003807207407000c40300340d074003240510f070b516507490351080d00300510742c0c12128816000c030004005218003d403a0100a256000e0380504e490f178a9000b181d018810728a4010a021000800c0071410f04c0070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 63712817 1250 63711567 63711569
    0xa060201290409290c09060703180e0702070617010b04031401090206070803011d06101803020303030c0703020d0503010506250b090106180510030f03120c12050106020f120310 77
    0x4d000c560130301d98140441c4802000a0001002c034443c80004546116240454059280040c03546040130110380d811159a8007602840090b80c1000e500052004180c0350030901480c140d4011742502c80c2004001006818003211ba80110382e41c0e0300041001c010503100315420303690880020042e040541c4030983c050445030000039003048000030303140244811800070303505a42410741c40002402e00d034610440f1610044c3c5036181c0c8220351071406084d045c0103141c002c41d00580d4501000400350759800003400c0d50012a01041c140d07000050000030180c0c10b00040c1c01c02452424031900f9135060a002c01d500340100c0b0a480180300710b2000300342ca856400818010100c0d80044e1403076851070304044060282007648600e051103011211781d0004400c1c4e5004140c81100c181d04101801840d40e180c000410a00c440d054050018070703403a01c100404180a54039040b0541e13100c0888240d100e4883c0c80468070b05034003000440d00203601c07420300c4d000080ba0f400a503c01d400c00309526600c5003c812041005a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 63714067 1250 63712817 63712823
    0x1111203010608070e120d1d04020417010b010801031a04060e030d1d010c08060603100312020313050609061215180406140615070f0b0103030804020a060201290409 72
    0x800300002594540c0704504510801c3ca0740c1e9880b00c0c0003820380c00e008410a02070a040060f0b0864140c0c680107070f1241650003001e01c44040d041002404142c0840c00300d034050380102d9445001d000c40882c801c1c5090040000d02c050031328040601e5803458540c0c1c100700140304c220b09550303005a07000c20180150740e000304140d004034506407980d80148440200007400f0284844a40488020440c1608071040c4103a00100041d0b4541d108190344440400045074002046205140304a842c0072011500d825443e0f4441c1c070258008541d1600000060100d120030340e448540710303031000c110000c26501c801c410364101603143d4480c1072003511841000603180c00b0b8845648e4100c0258a11070f0f140c0c2c0040384100e8012401105c0800c6521302501c07150400080c211503068020450a04100b0910064401440b400380240f6a8103480b101566500943c01e001380e005a000074441c40901c002e500c0c1c0b10030000c004055600081180c0c244207502e0361a9111000c520005603141c0602c40400c0e500c494010044143d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 63715317 1250 63714067 63714103
    0xe1005010b1308010c021002131517060a120201030218100203040e06040902060a0c0309180b010f02011b0e030708011104061b0503030112020418031e0c0b0103020111 73
    0xa100c0801c00a1034101210810010075840400503500c0018030078086840240e03805001098502000f400180d800042c140c88202c0150000140044c0051220003410b00d040d039415548800c001e10031074031400e010704541d2007801030850412900e4111056403041e1642800d000d0785401d50002902c7c2e60350300049040e500a21002048605952b001c00140151581a01803407110b071110824042204c080742402904180100101c04060340180c0000c50414840d161440034551a411070140503001c2040220500303803183e04c4a0081d6030040f14a11b10f8820920003080f050b0305a240c03480301c000c50f5115031010301003048407810303850701c043c0300080251403088020300c01d000481a091200381e105209410006100c0504c1050070b101c00b117040a20140c0200055055034200740700c0403003d03a1040e00807640702c5d9448080c0203911b44921034884445000c0d40301c03440d90b0b200230440d044640c41450200d400700401e0140e50b00000c0c40140401c1d0540790207103032071403400c40001d60300c519029003042413248800e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 63716567 1250 63715317 63715319
    0xe03090d0b06030f06130201080c0d0603050102040306060b0a12020901050912030a020c0102030406020a110103060815010509070504030209011a0c03030421051c0c02031c0b120a020102060a0e100501 87
    0x88003000110b4000c0d4020fa0884094282610010352103120544580c59480015009600035601c903c004a820960031070704540313031005621003a4216000d0360300c1251039075000b01e420820303c0441d205541c010b04441c640c140c03918545c0312004200c0360480002440f119804504a5081d034803c80c00e50351022030240c0101c1c2050076401000d40e1744c0d0010041400180304100414645510200075242200c00c503030000c0c101541c1c0780d0740d07142440d1282002c02d4101599650006030014040025100c4035003420700c10380541d410002400100f18009084001b8804200300800041e00c4d441021411030700d1075918001d00d90303450311a10119100d40200fa0b03810384004802e04c018820018410300d1215400031556606200c1a072058480340500304491780b0340c00c0c003207000d640c500300c0e1504206010b860f90300c160303807408914650810250705000f01501d1071561f503030032848890501e154415240c2c1d286c14001c042045140d40000d40d100c030001c11035001c00303481c0c030801e0400c00300800400704941c1e54184140925 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 63717817 1250 63716567 63716573
    0x30915020d0e0d17072330070905270f010e06180106110a02060f040e10030b0402100309060c03090302060a0603050c0d030c06020c01020c07060e060a030e03090d 71
    0x40c0240d40c0d1420b030b09009051400d1200e41c003c0103800031001d2007074036001559890144c1543c201e00280c0600c28010140c22146030003403040c000400010030f440c4094a4541e0410000d81940d42c8440c3c642c2c0802500c1806104003e81c0209824049820880e00c41820001c1440c00807440b612111400034031242c410f00b41309031901d0350000341d0b0607100c00340280341d015581c1104111100f42c4903c840042c600c0343c040184a00b52180d5810002c020015007110040c8203160f000c98015400a41c41c0d2046d060045030501000405141da40d03000203449400e141410f0850300c60a020a0002e04024821700c1c0d42c140111006000380c000c0354100c0e801c50303410404c00c60706813006006040302c020210018058000000e0041c04c40e4811001542d811000a1244440b190180100412910010741c14460310321007076800554940001c0800c801e80300000342e100c102220801d443e00071190011001e020000d8001c0340e050700c4410030796100700c4e06880c010414100f0880010300f940314031641d080d00070280c16254024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 63719067 1250 63717817 63717821
    0xc17010306090b0916031103010e06040305030610080603100203060111010608010b01091211060a02030c0a0f020f0a0605030f060d0f061d0318040507050903072c06090601030915020d 80
    0x103501e000307000c0a4802d91310030742c45580712254400030440c081581030003400071410009081410b40c001500006901050450b81407411404813000c03800281d00000708002400d0a0000501c02019402d21711494207150002a4440d0328001e4030400b07441d8040300185803a071007100c0491064800200070007100b85c4400809010345a181180380c04039000034400250314070000b5880c1c80c1c20303801c541c481c11559504800c2000d11740c40031070007e08501c014841008900024080f40f04c010344200ca800050b51518070500001c90f140c0c10300a44640c14018042200541120480703610031a64600300e544da0740c0c1c0c600040e08400701c02078060101c1090a04000c2002000e07842074080c01c03a0100e04030100c00c20003205035643e00c106190b00b0050a4642c6102d4518101070700800d40106442c01c0403420035500c0c20100c1e25240300c0b40c0c002e40c42c40703041180201a4000d03d1242c0c6094a0000000310510300c0d094011401460740500054101981d4141980900042020002c0700c015944002d40d40c5410800c3c803000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63720317 1250 63719067 63719081
    0x1f0201050106030c050301050619050904110301030c050f030d0305100b0c0d0e0415090b0402040b0a0507030f0302070309050d020d080c01020c0f07030506010302010c0c030b010b070605061801090c17010306 90
    0x400319103001c00e011040d43c090f2051b07904030384006140c0303490b100288480b1252110300c2c4803400b003804801d1142c54542d030b945008d4001840ca0fa003242540700d41c51402c0c44000f896442e07000c0b42c05614a041111500e4034041002ca20039000c904010a0b962500310500d0304901481d40b0001ca4003d011848a80c01000414031710f000084507942c000034400100108412a80c0301120240c0f9000340d0401040708200c242c06c1107500b0b14004000600b8940d4a507c072038415407100800c900000c00c00a14541090340003040146a01900e180c1142009945d640241252103035001d40da11820a0302e0700c1e1400c647d549141c404c0017903840319055440c3c5100c1c010721070103900407950180c0c0c18040c55030360309810340d800034100302165004401041c80b640b85030015510400050b00995080490b44404008a106a00d00354006c1c01c1031850300741e45146a052520441b20060701c01442446003451007440e009503000d82c80e040d2102c00078001494640030034181d490300c10320035a00f0140d0007114000000e100e800d601042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63721567 1250 63720317 63720329
    0x1d090c19030b090d02061801020f0403060603020a0b091005091f020c01021525090b070305040e0a05070804030e0105040801050405030d061a180f042c0a030507060203061f02010501 79
    0x49a450b00f851168a41010091200c01a0322a00c00504220031800c29804040c2080000610388298079040402503030180c5c0041c0e500c81d4840a04004608040d0780010082441c043e140e41044003000003c2e03050200740c0c100030300b08000414641410341c3c90442020050280220130100a00640700203074071014120703a43c5000d40513031203d081807d42c0880d849441000c1c4140d181216200b40301c0f4441d688902108034001f0405042e01c003081010b1100002d00c502da00a44078503860383d00d440305074024000014641140c10342484180301c2034940081136190415418144102c04000d40d2004844d54091359000100c19803c00042c401400307804402801e4002101d42d060005907200c141c0d405911031280030651600c0d00402003001d800c19003101300407140f000203050005200c14040042c054450703040c20740540c0c0040c00700521500d070070080b480c1c1c0c0900000c80940841441d58034090214001d50130050300740e6800200150301d55a50101080310840c1003138200ca030f5000d00d00b070001d0007004240615 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63722817 1250 63721567 63721583
    0xb0d11010206090c0d12050708120610030207030206040204051b0d020c06130203070e060109240e190605070f0501050c0a090f0b0d0905011d010e01151d090c1903 71
    0x2180f12000702080c4406903941c0500000407503000d0b9541c01038003000384803402013040300501c070960024400100030007122540d0082c3c0b00c0c040c14200204042e5400c007114040034540b04008580020b40c01040301980a5012640000c80e60340c0c41c0420380b060390300c0400c41001c1510001d8060820001c42d409040c5072903c00040380c9441d51900c1c80500c65050300b0401961560000b8000c00084462028281e0b0002040c9050084182d494254252000301c0c0c0b071400c003001d42501c1d441012107502c21900302c48080201d400d462641e0700c1480240100c4090701522081210002c1d030401440400089402c50391340c000300800080c0703401c0f440d210030764012181c5040001e08501000030b11000c04184a001d460320480c0d0b4603d001542c030034510051802ca2000c8030b4954803240d2003d00e03040036044004000c9407920022651401e500c00311030864039281049200454424014003102c21170284684400b150302c24241c0300d507115111150715064100030410340c4001014550500d03091000340d10b034116407152070307a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63724067 1250 63722817 63722821
    0xb0703030b040b09010302131416021005070909090501060b2209020c151812130801140a0b0325030606170a060507210c02060c0c0304060309060b0d11010206 69
    0x1000156074003483c4481d0700200d000018805403422460700c00600e05407840004c0c1c0c00c1240300d05903500003c220f0718645e1004007041500c01c0c1a806101084040798011400c110300d1511107005031110515000d080344090761400c259040120950005002d4201e02d509581c69102414203940c440d459400c1044249406120010b4080b90500a803000082c0440180841440c1d0340320320b0094034002080d01300584c001d29034124034488140100f111105d0342e0015145d403503103a10a9801076500542c090b0245a14080582402c00300503800d0b103400552107040402d012007040b0000b85009902c0c1003080d201c00502e5142044620090406401c482c80303081e09101e080e42d0b94a03020312001003203c1e159131a400c000c40d2000014010b034483c5034069464202050201c1074001d01c4040315508d86404400503541c0c0e140f407002c0e15010024140c0c4903010a80e150304e018402d48000c0c2e12406540b256400341a290010001000902c1e08000400080a03100c800f44c1d01c418201804607000c001c02a90150042c02c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63725317 1250 63724067 63724069
    0xc010b0303070b0a020a2607020d09050102120d06030b09060402010e01030903020a1502040902041413060302060f0a03020405130b0907050f160206090312041d040b010b0307020f070b0703030b 84
    0x640d40b02c250030182d030303951503650b030707800c00010b544035040c40c6081120184004210b00c3d400b0703180d150202c980406070310346858042406031030801421400300c1406004070007080036a0740007501030700009442034203d13118001c100c100c201400c080d0b080204000c42c00d408001c01074400088403031046000b40e031804100c11080d4015011507151800140068000e42d49650110b469083e8030107961030304c0d810052419a840c40301d10201d80041c2c103c0e0318160b14980307a042c045c0c5014214180705c6581200104203080c9180d0001c0e48910410038282c80c880000309500c00004c1c020b44c140d5006010152501158415a0707903c2e000070b1010b551440c0c8910020800f240d68a403141003924035440340307210380030f2a0440035104032a04000161b4102d9000c0002c0103071031042d45007403081280012980d035203da11035050418003078000300c4240e103405d0000400340410001c2003400b200c13241158480c2d883d403540d030384502c0b0089041c400d0009031078945125101c0000303040c0000c0c00040200307034002d40e010402600b01d0303c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63726567 1250 63725317 63725323
    0x114040c0e010e01060c030909050907030c090c09170312010303080a0c0201110d09050109080a0809060906060303090618150c0d020316140a0606080d0908011506030c02031606020c010b03 82
    0xc01002801420f03100141320060040544608543c000d052443c0307181e070342c2c203900c0040e00c4080b035810a46401101041080004050040c400341c40185c0043c400c9040c585002024245136110b41d105e002c044001c0c0620240c1c040c01201d074550b800e01d0b5215120341e16818041c19410054030600344141c9070115040100c0d1040c4501c00260701440307021481c0003503108981000d800044802c3c1c40c907558030318a60340022248402003507280c3c00c5484d40b036010700d42034089070f0900b40c0c014038102d080e401c850708204d140e5501108952201c0d508845040d12620006808042c2c03050f02ca45064000031703507590104010311241c01801c00e8080300000c803241080712401c01ca8590081c0030b901010302d868010800c0000b00d09a0407507070100641400c5410f45804c0d5181d81055030115400b0800a41140d6911005194050785020207084000000e0005103c141400c0c083d00f03081744203030006c043e600c40c0410306042c0b0034412990443e885048610710340c40c01c0e062801c020742c80000c107039995600e0b0440340280c1d03003004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63727817 1250 63726567 63726569
    0x30f0a0e12030a0f0e0c150408070308070f0501020a030b030c0409030e0423100e060108043201090c05040e0d080712060f0b0c0d05030907030f02060702030114040c0e01 74
    0x303000900340e40c104881e001001c50b00040e1081040c40d449440100e001002c40c0300305101034650074010000503201c0c03014010004804416004100d404110500c654440020082c04072030307010701c515545036568180310802c1251420020207035400020040b071141d601d0341104050200480949a00341d6241c8101b204a6080c07480040200310010000302080c83c4c1a84014441c0c05041441c03a03810031241d662001c0048100d820a10004405405100891200c3e80700d541c090020f00b0201180d0a00d07455003c1c028055048042e01300200c00740303644c5402c0b103d00d060746d0300e1a2000c00910006003940341c0720640002074000c0303a0095141c60b42d003035100c00340012101e150103144e880e02085c980b106503088036100e00000080c007010f80c640600052004541007210000d10038401d000f078460203011445800c0c81c1d2002826410000e061040c85070690300802d841d003c80b507005185000e800d41c20f1001c190203009541019600d1352130480030003034400080184600c5a803040714808009911010030703041200003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63729067 1250 63727817 63727841
    0x907050d05101d0402030c1503091002130b090a030501050a0f0e0601050f01050c070f030609050105070903050706030c180b030702190f23010608100605060405090601030209150c0102030f0a 83
    0x12071001c403d095000c203140e90424006010b862400410002044142101505090580c5800030400407440e4060100407040c4107400400d500e002417035a40c1082c0e44906000303c50506100007280c000980c1c0d01d00088000f0340e80407000740100c1c540656180010110401d14001e55420b2043c54148a1000b01d280f41c180d480c014545251600381c10b004603007036000961515254810050041030409c5203504801c0210301c0381c80041044c80842c54230f2402d48901620140a00054401c1070002501c00b05011003540d29529000a0b8001c0c0c0103401c42e61003218414620003955444408a002c0c107609005520540d8144c084034810340aa0b2401082c61003a8003000c3e014807000c010f0b0b07038001059200d070039200b000985d00003011903803100f00c0c0c1c1d8210b82441e0702c00d103100e0744581c41c1c001581c0041c1c02a10000c0504070761260804c0c0c68030000c9113070050000d058034101540010114030b1580c40801e05070100315035482060320b561660320654000d500c20348000d0071280319640041e090300d00d2170048420f6051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63730317 1250 63729067 63729089
    0x100b0405130506031e0607030b0102010b090c0d02040b0d0603030908032104020402090613030302010501050f0d11010507050a030309230a02010f02010b0d0308011d0f0c070503090907050d0510 84
    0x10181c07409800a100281074981d02d0f00610028001c4c40c44021204042201014081c0000b81003001000c6c0840f0400d200042c15a41080070101c220703a82c5400040c5d008d410302e504160f86e0440220040028822074018402d00c07a00890a1148200c130350340000c060320b00c20b855515145446496956403801030b2088003011b4042401210340340030341c501c2e1041d00a88058805410880800c00044094120417000340440000b0442007090550900600740140300a48020314200400c001065038003221400c0a081010341480c00703411a4403030801c503800c00d13030442c041d500034008514004020300040e031825941100c9400403408014400724a129207144001c0041900080550040d40d40c0110325501d0b60643d540c8021110007a160f8448000d9448d10954441c0c48641c1003041c01d52038440003250400311010385204002c1030b003086410090b040012000070765101c41480c50a58510f20504c2e01140e006100d0005011a0f50340020107010410b400c0c2c00107000c5039803603100c0943c04103814802d031a00e0b48 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63731567 1250 63730317 63730339
    0x6030807060c080903040306110f18090703061202061b15100b031909020d0215040501030e030f090d080c01020a05030105130e030306040207060b030f0c10030902100e0301091703100b0405 82
    0x1231040d034482800a0b580712070460401200b00c1c00c40b0341d10740001745103c0c02060b5200b0082054540312815aa1040035403d0802c40e130340c1802d007a40503990034250700900500c1d001807070303007440070a841d01c0e440209840300456508081c104142003030300c4800c2d140c500e01b40d461401c0100d040a1004241c1e8880c85051a01040c020600f00d00c410141846103816a0041140303480c420241e103561841c4442828100c1201c0e5a841c40c01c000103003210200c0482140d250414000e0000314144070301141c440300b00c104c80b540d035880098200a0124420070700144240e610010700b2000054100000d13504a60f811905980100d21900900013135038012841142c0640041000403c146490303070161250501a010018000a549021034505100c0820362191075000880306495440c001074420310750181450305100005080d17001c620259070151441c8140800b010240c02c95480c250b0240e0310300c9070000310348402030400241540d40b030313403060303824640c1102062404580c590055003200e04441c0d01801e400b03445 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63732817 1250 63731567 63731573
    0x1c1d210d020a0b06012a0809120102030c070206031009020c070518091510030f0b0109050c04120201120207080d0b01020705040c120b040905060411090a180209180106030807060c0809030403 83
    0x1ba030685600d0f050407100344040408400780b035240320845c51203400350580c1d41c00076a0030800380010b000200c000300d070300400c204190407062000350348095a050342c44a403692588003c0d0b11401249402500c2094030100b0315600c0c10100244070011160251107a00c80940f1002c481054140c0c01c680514141d40078100b6140c00040d0000420f921002800c06003e2070707074030f070b55a01d0f45c2d070003d0080aa4030b000381f5000500ca245070324840c07190017804000686240c54503081c5240041f4011010290500220f04400320f04840c1b01d80440e07554961019045030740c2d801c054000c0c1d0040504079070190040c80748a4000c2418209840f4000000180381c807400d900d001c002c0d0400e005840b0060f2425001510740d622640080c00400c406c0b40030714030444a0b01000c07141c40c070a101802c0310003418100858202811940c0000359020410386481e01621526000c0da40c03400f0605100723200a440035210762070070f6070003c103005000d00609a40c921070901408440c0300308004a440c00025a101c89894208000030400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63734067 1250 63732817 63732827
    0x1a09010c02030708070603020403050c010207031203092d03030506030f0a060515030703200312070602070f02130903030b090615070c030c0906080c031c1d210d020a0b0601 75
    0x481e100808440358a81c4410081d41000059449800813907000724061040001c1400300148008082c030003815088d01d140c031245a01180c03080c881c1c003815500d249031000d200c54245000300360020300c004507600c004400101460007003d800e05400107842d00001c110a0314022441f0840142d51400500c4410b141da1100f04c010b01c0d0140c1141c0d8110811314022108c1e4406102d044011401502e031070b410b100e171030a00e003643e207070303200500500c29002007030440d0b14807030307648155060503401803130060700c6a515103002c0e0100c058911000e540076243d01c900042401c8250410107565100e076a00340515540030090040c00300b015166503500406902803448510070080c06410300034000c4a001d01d945540341c50300c1c011080b06800c680c900d80e89403031060105040c01c100c1d040728078a00b50300400c1801c040040580700f00320380460f80c00400c02d02011580d034107280241c02001c02c07407004118181529109104071181c01090f600b20703140f805a50190303d101400491090000c0c0d80040c8019801e903500001102d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63735317 1250 63734067 63734087
    0xc0301052403010b0d030503040b0f06010c060506010e040f05010503070e0609040210202404050606060307030f060b0307090e0106050301062114010519210303230609011a0901 77
    0x340640d6130704401e0382550b944800d40b0320310f50301030307180e5560f03904060929400c1c092008082d450b007201c3d610b05228550364084101000103412140014084d120b03a0012201d41e10007500380c55100b0308101c4016034120003503100a0484404400f04c807021547d407032200c0c100e080c085804c1d640c02000b6a00140160812519400721840d05d03140208803104804c3c407480740001c10112046440e848031500751104040b4405008401d04182049000c1d45882e90f5036a0b0b031000003c0c8074a028250100c04030304200c0c041e42082080f101c1010f4103001d6152989005101038000711035000004480110001d0310001e043c000743e050360081e0b50303003626507800d0140c162002045c624000d26000c0324406143c1500f82d55100d01c0c002001e1500d801700041d4940420071940d80c00d03844c0ca0321011003004504110000305c0c02c0d09891503008002d5540000003d5080a40041060f580c0400865005400d80c04d01d242c20b00408a1103207200f11680c11950342c880507a17100c80391031180c80c9000c20b40300300400d9401d0741c0039140340700f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63736567 1250 63735317 63735319
    0xf0f060621110301090603060c0e10031109060a0206090105060d0b0106050906091e0117090a0201110703050f0a060f020f0405060d0f18030305090a0c0b0a14040b0c0c03010524 77
    0x4a1402c50103180711246030f00980c0000821943c90343c0a008101c00303400b910b40341000a240180b8509128400146400c1c440002e100034103035501e1958103611041c400382d40c03030704c24002c1c8400c2d22150110000f035251310085a82000a5180c100080d080340f400080d0490310b1074200094044d142e0070a10196129408030184961210080c40f103002c10b42c2d076208100001c000301d0181c0762000b810f408005800e0091200c40702801c51840e07820040324480018180702c801d902441c00c5018240154400d030b0800b029604041d1142c003500c104241d4020002901300710141c0b103441c04001c1c450414504030224000c13404124a0384200308003c000501e81040500112990500009a0700424603280d00440705031045001e07408200c0071301c0780c0c103058041c481d16511007a210050a240c0c100b03581d85560203100c60040151490010407011350a5201e8500c034108070409030000b5130341e20748903050001150405281002c0307a20a40483c3c00d070301c1c1418010b80707000c1e00c02e841071f55810040d1411041d428000c3c800c2d8003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63737817 1250 63736567 63736571
    0xa06030203100b090f010305030d180204020424020105040503030105151902011a1c0206030907090e0c10030c120c020c0d060b0a08061b0a03090b0a0f0f060621 70
    0x21025035002e1058a124400031100000d020310510140211014002c0c040d0040502003401000402c07070120489450a600d50000920400d40c05488001002c2e0100082d40051010030080b40404403480c003100f01904103d0740e000e110b03a00d45030407402c0e208111070041c05500180700411290500d1101c1e020f80e004030035a518203141014001031113812100d10303000010b039103400a80342001c06050f2200304520b02694501d10680f9140420210040305440084c06804000000b820300603040c4201d02c0034042c0301d1010302680008824081c1e450407041c1030b05116040d41403600311000d000e0b20451020740403c0d12200651006180704000501180a0388030940c00f07550703c4003440740d40359981401d01d148194000200c4004410a100303100e00d03103400c205165803180c0300780419a9100030342c1410112080c5541c5030713500072090b802c4001c1c11100c50b00511418040c0240401003220741c0000c4801e18500c0005c0158107030150700402560352a1190b02c0108951880588100300c8146440907024000840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63739067 1250 63737817 63737819
    0x30807060b22050c04150810090603170f04170a0203011b0c0b1b0d0509010c08010602120d0f09051005070e0a091d060103030f0212040e0105040507020109021c0311030a0503040b0a06 80
    0x101d220b60b407080e40c6c04000408180410460a800b100f0210117007074a40403c2140c0350a40d5948145a1848004030002e04000708200f1011840c0800315030103048000c1100040c10f0040c8229981c0d1846d5103802c0f4401c0d4205004003010180b100d806003449001d036540d500ca02c00071034540000c1400c001e000810440030300304036920031200c0303040200b030341c6400803100286924190b9100b9007100d80f90490901049119801004141d40c00240d05218036030030a0159502d9a00904900041c03071070400f18580582800f5a6400f030080c00325507140c4644150034144000e0340c41d441700b01d648094051885900c00d403014424802075070a81d010324400e0402020500b5211240b08000d864100261300440018081d91084007540b03a0501544002d404210f40d890300f024180700154032707194014040c2a005585e500c0025410714030075004000019000b030130300240742100c4001c6021032800700c901a0007042004195120710345000013100c071607402940d80c1c40c1c00c5444965401c41c9603c40582803a042d9920750320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63740317 1250 63739067 63739079
    0x70803270610061b0302030a0809030c010504060218120d05090f12160911030408070501090c032604030b040b04021f03020a17090a02090604060b04030807060b22050c04 74
    0xa81c600030750410418050706850218001c09442c600c60041000740090b481801c00280c00000351130b01b91101c3d04001b0301c2031343c41065403490b6014400c5003501303941c01c14080c4001d0142c5c0b68000c040c91a404003032215800300350010701400710004e001c010000d900610844050f03900c40c1001d40044d2a0040c2084040d00864000030700c0c1d800500c02000340340c1c108081d04030702c0c01141c202150042007003440c2400b2015130141da02e1264000144054a400000901c1c407041003c00c0d0f00420000f9030000e41154860b4a908142120a114840300049400c9680c0c48001000d075500c240e504803640203073b03000403996581d41c5862101c80040c108076000417289109a10423081d80380003451030882a0f4006031100001c6000804042000701900c2c00c404030801403013000c0f100480d90125040e01510a80e41c2c2e0f440384008034004196940c05001480710108011080010120080c200d45002d44014042120040108843e2040903086000054040c45403040408503541020f680254144501d0b030402e983c981d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63741567 1250 63740317 63740323
    0x61b020a0e0711070b0d0b03060708040209040c0e1003171c09050c030706020109030216050d0f050c040905030705060a060f1206020d05070e030607020c180907080703120e01030207080327 82
    0x1d088170030019008942e003842e0000b18072031b000402d08114010308080c10451000f40500f60b029101034010715002c0d00107010b000344c415081c401044021400031407480d00006d505200700786030204a80d01600d00d12141d001d801e5030320075201072002c90980e0b05c503e00d18202800c0300620a0f110129014010f445500300c4540e0144010002071441e40c0002c266500246002418803245403e03106118a0355202844903407a10954100065806054084044400d0515902d445200c10129a2080c20200401f08000340071001c0c1c810240f05404481c0c49072a061f40c0c0205464040c003921011009220b41002010080011f05034101d00422005242507162020007060b40c0e000c4944030003003001c40381c008486003400c000f40c40d41301c00301e0300c0a8030070801c2c4100040c08491249210b51910f03401200071030403503001800503030010704264040b11100c941e01d2405250341c5900f5008030000c51f240410180555002e402282c182030340c445582e83ca5a580d00e041e8502002000070035095100091040085840c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63742817 1250 63741567 63741569
    0x10e0f09010b040f0801090b01030b10030c0611060f01080309010c08070204090b0f070c11010c03090e0403020609060108030414100201090c08060603190c030605060d06060f061b020a0e071107 84
    0x25880780d507680d500f062000d6011003203a52181815038034207c0303000041016030421506495019540034007a40b682c042d511000304807500090140e00000000185858000481881440041c419074583ea500d901c0f054607050024422806660410444808a5803241c2e40040d2140d10a204d168100316058001c078045400c9420226040300d400414481c80c0846950455400002490908001c2c0d54540d202d000d403042071051541031146100d545030806001c1c0d0310034005801d10f800c02d44554502410025560241501c2c072113aa13009007000880d1414010048409485129400303070b41d058a06001d01c0088005031500f00111b550b69564000001d03400903021006000b160002d0440d03040c80710805007005203040801d02e5241120314003800180045c42da203011a03800281c00a030705d9035210042032080d0500000184030701e00d843c9002ca2031078078420581050313620550340d58080006c0b0000c54508004551000b9522002d4064108488000804c01170350004003458031901e901c6950024a2400140b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63744067 1250 63742817 63742829
    0xb030903070c0e15040b0109050103052206050a14090c06071703040f020103051005010c02090402030a080a020304060311030105010c060b01090b040b0409050a1b080c13030303050601080612030405010e0f0901 91
    0xf4000901c83c1c04855101050402402241c0405c0305402d090000707800028036100d041c0c1410f4580c00061540c0700c5450710311080c1e4011004049603a603080c50001c00800341216030240e01c0d031428554110490b04554210300c514600c000904003046240c04000c2940c00c9107a00304d0303040d8900e604120b21113207240007440c002c0b4400d080da058400010b10014081e508000c0100001504a41c03080000341c0e1b200020041c1250103a0316012240c9039400424117041062a024080ba480040c0d4038814960000c001e10858206580800c8013100204005190348002e00c2114001540c01031950003144003036000b400400300505110900b07694850074004e45c0d4004e640100390409001c142001f650401c0e000d01d0798420030a080802450304600404802e00c4601d5204204214082001a070091030400841e14403407102401304442a41da4a07008010700401c550b0346000554060203d440c41c203001c00d030004029044c8002d0b44c1090705001c011500c0038019406a9802080e000c4038044540301c1d0f44a003806068 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63745317 1250 63744067 63744089
    0x305070b0f090d0f02032e0f02090a0e0f071407020405070309150207060b040e0a1403040f09061508040503091905090403020106060f090509060d0602070b090f0f0708070b030903070c 80
    0x807030b45c0101820400c0b801482d10801003d03100062100c03065190103003032461140d4002480440e00300e68400240141d941150300300c4c40c01980030070716940d012660b07441100002072081c80c0355101c0740200c4280c15800c00041c01140113002500051405400c0b2661006843c03500003541d0740b4546031584980c00503040c408005500051031414071205003d08061800c090f5014000f0500450906544400d1880064015500010701503000703c03050080710028405151001211a124500c1c0001046130b4410b4803030140c0084540702886005a130920720494102c005542494001d4080c03100c00c0040310039000c0c084500b0300e40800d0030790300c24000600490295000046450404c680640883c1c1002d400c402408210001000956940e102c001d42c000010781c0e0341540d0b01c1c0103140c1000179004002c0002c1540401c403041200c04800002c6951541610700115800320440303e00c0039031240c0c014003d08410b0b801a440601000b40711b040203641010300e52041b03034508002d94035061440500c940100b11801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63746567 1250 63745317 63745343
    0x207030206150f1305190e070509220c050108150f061c050405010b0a050102060103080703030c210e0d0c02090402060c03090d0303140a0507020d08041e08070209010f0305070b0f090d 80
    0x208a0481c8040e04c100058001c12200001f000300319520120380c847c1c03134440d000c0c400011301050464480c40f440b00c4610300221000b0301d42403610040c0c00e0718601640d400500030300005240f010112110700e1a8003c0039000441e07500d0b01006100c0c10b94807044802c5401000b03041c420700459002d100b000e1045000e100002582c8841c0020040c02070080d43c001411544403000610200d040f0504450401d985401c001800d8102c1d030f802a80d0f100324a910980d0b61105410744030200c1c2d02d250300301c1d403945400101034a54502c000c4009490303d2104c140e001e9000407980d40040c1c0141890401020408200003c60303003040400c00c002103440b0680c94044001030b4584c0d0111102000f1000e10a40117190083c0034400387c601034800039a9130f0b400c000c28404010350301c400704091000620090a101c0ca411130038514208040c100a0740ca5800000124041c0e00701400005060007a00103041c00ea907480f0000c1c0048900e8010a8001c2d9004031107242da00320820058800950380301c142400201d03114000180b50a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63747817 1250 63746567 63746581
    0x80307031d01030b06030718030c06020d110102030c09040203090106030f0c0f0b0702010e2403010609080708031323030313050102010e0d080106050d06090c0e1002010207030206150f1305 82
    0x1481c040c2000d01d05140c24aa950f610581e1800240c81c0d00c460285403050f02a00311109000c0e1070642540003400804041402007003490b03011446040d040c0c5c0c961a941aa001c180340c100c0d00701d00c03080310710308d00b064010b12081105143c943c0080d0303000300190001040340d43c0c994442542052b88200201c54011a00804001e0289024042c500505000420b80d0a04050b40c0001e0104440740c1d071400e00c00d05000c8050036225120360100d403504480d1601c15038880d0f86845000e00455154001d580f2103104102c1d0000d8000000002c8500341e8440c40b080e002c22502c3d0040c0c0e0043c010ba40200b5492908101c0114045a00c0400207400aa02c4c06800d09041a103418006800c50b41e4068a00f10359030000004c0c0743d06603401245150440300e030ba29045a031588003401c400003d0965403c110402420f181000d0710640d4024100409001c0c1142c00e000c054030341820503402c034440d21100a025802c1240000c2d40b044d103107691280461405410080300e0802d4900040905070030361410880a03a2f43e505001e48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63749067 1250 63747817 63747857
    0x1050a1428020f1b0c04150b04170708030c060f0105040504050d0e011101050115140c0d030c0302071b060905030307020901030b0402010512040b01180b0918010608030703 75
    0x41100709110407050154000309090260082104801c55000602c803540403081c1d01c11143c104c0d000300c40007800d240c420200503480e03079610700005100320f00b0444452040340c01c884002d0121801c0259542c07410f483e08110300f01480521032949000d0040c10000201c4002c00c1c8020468400302002600b80f510301000c00c40000c2d54180c0203523003c5c82c41c103010800056000a00305114182600703000b19440345840c0100c030b102d52120034550080d42030800004507110a907815039101081516900f0340301504000c2c00206001d842015042503001000c50002d02d8081d0b4001c0c1600e008901d4050724003071301615003207820b110409a82503200308070803007001000d83c04400100a0581100907603c0c0500c19000655007000601000e81500a20741c00702c2c045a000d2401c035002809110140025480c2c0390038103031002c280920401c40c0c020f034103a490010b000028429180000700c01003010707610b0b0700d401004007030404800c241d90701e00d9980c50001051000041010b012130911a940d010b68100d03c0301c180a00b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63750317 1250 63749067 63749071
    0x17070c080613030e0103050c090d050609010c02011b0e0d021509090114010c0305160606030c030b0a0603031d04090c0f0f050f030c010c0602040b0403030302030702191e110301050a14 80
    0xc0981000e000e110002c0e901440d85400e44c082441c010a150321100100b0a03144500c1d209268040591179145007003100c08501c85104424107002040640000740f010b9090f50040184450b50181442c2c044103841e010342c400b041500f10160000200b542c0950101e000102c43e2080080d510001143c1000107142914007240900210310001001d85045000030340b8003e5240c6005062240102d82c1000007a0701e0540c00c40b0003504a0001d2040ca039884c2408102d0080a00082d03c000f41c1070000101103107014010b907412a941607440d000c03000d40ea003280c0080d40d2800c11031143d0142d00c640906011820141030300c4050880c0000783c2c6101480c04d140e18003462916070211340122408070034840155008501251814802e00b080c040341202d030b140140007445103421501c462800460b001c014550302d80e002c0c40c443d42d21038081311b500c4030403505007244101049800034010030380180c0b920b03004201c0c0070324483c0032446041c01800440b0443e00181c2503031003c45506443c255544184070368044210b05441d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63751567 1250 63750317 63750331
    0xd2d0b010305061b0409020a050903070b0c0714180c0909070819090c0902070302030408030304110109210303150807030b0604060b0c070320060d0603021302040e0f0417070c0806 78
    0xc206803903240f02211300ba015600c6070b144503940c049629131100d806102250350420380102990312150322048000450f0308404008080341c4910680400c03000d8294850741103405005041e001c041d06020580e1003617100042614810200a109460b01c03506c45540150041945444081051400340d082008421140c1c0c1140d6102d800e00e1055004103c6803072000041c1c4800702805a170711521814180d00e5841640e1000306e503440b0000420007880340c1003c24405a110999070040085d50b00d0041c050401c00790401344a4004000d602d10740024000d500c1100301200c02c101c0b100100e42da90784946c2c01c054443c2d000f9651061400f0420101c2d1500d4401c82c00500308251500b4149240f20a880d6906c9819010050101e04161925241d4207900b0043c0011071200400b4140d0b5400c1c0102110040c2400b44402c03805465400c4030358070000c2c418002d41b020390389180d2003400c69944034080c1c0f03234400c6009407040d02c11580e144096000048240001d01c0100e01400c80350145501e080003a9140c041d00800c48 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63752817 1250 63751567 63751591
    0x1060603050a330503070902120105040b01120c12020c01060914070f0503040302011b180501090605090f0a09020c0a1407060c02130b03030a0f02070906050d2d0b01030506 75
    0x20700006440c500607805060f2200302a00034034403000440f0104907401d90881a41846102400580d1100070780007400e8120b11a0b91411041c6d990748140001e41b15103202c4030380800c901c5400070102d485107a0028103401d200e0320700104414000b0580d1000c070313403000c420051b9a0351030320801c1c011020036014100540040c03112402c460300c0c250f41c00401c02c0c0094000710040080000114092600c00d410540b550f10040101450350300e03001101800c403420b15841c6514100310750000044540c0910b900308221229500c80d64600703030f207410401c000000c030300b5074035540404440c6c0081982c400d1880a0203261480500400341981142454107603017101c800081103982c0002c0c402d003c00d82e8099084082e455064403550101f90750b85201001402c2464000e941510000c607200194644c85005c844a10645400351054a503c610703070760050b6006030160306e03001461180c0d2800010303050344010001110001c2c45440e0303100d040a4480c501c400b1148182d6610400200620070b0000500c05039801607070900c55 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63754067 1250 63752817 63752831
    0xa0204060b270a0608070c0203101e0e060711071a07031209050d030906230105040c050c03091c1b0518041104050703060515030a060f08030708071a0901060603050a 72
    0x1d03a980f1a68001c0c0740030440014042071040c0d003e000c20858856008068410300303885801c4210040c56188846407888800100c1c41e10307603030308078441c0400110b0941e0261185036034525042d1010b414134440086148200d01000805c504411912400740c034601480c21354803005c604005050b20180f50a20f8100c52601c86200700041c00000d00307050b0341120381404103030308005040c039000230040807503800301401c1e450310180c2c001540350654030705079807080f28100003aa044900444036800b520303000003110b40c010404071580c0e1400c2c1c0001d60340a009036802590702c803240d940d10743c055000700808440443e0034040078012440c0074282c403e8002d00d406001c07103981c5025110959507015190740c45028564900104907540d1190300b001010701405003100308041c562100400c50f951044400c81c9640d40f4042d0082080802204400c08540c8448011030400c0075980390600503602254040300c400c02c1c8003840040c1070045110f030500c82c00550b4000600d032481c005000d001d4440062040b07070300d50b20307000e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63755317 1250 63754067 63754069
    0x606021204080a0f03031404110102060703060509010e04022b02040f0203060108150a050607030c02090105010c030f03051e040609030207060e0a120c050301020c0615010f1e020a0204060b27 83
    0x141203c101c0303810058440e014031a900b01134000340000d042842e54540c9000401007401102c4820000302c0400381e08072801036480c600c1c01c804443c03ca0080c40d40c03051440e00100480d507135041000360002e00040850000680720450440028040d4112031940071032046181d082d0b00c0d181c80382c844003822281041d49113203402c40c0000c21b880c0005000584040070034582800c2030301e42946407400340501800e400d5849406040c064100f00c603480c0124405c8803164004104cd5201380c0000b040c19034183c071185035030800b5500640181100508068030102080385070305522007450720f01130140307000f10000140d080c5103080082c100720160304040c040c40450301c110400d03515500301d000c0440d10140e0a000807006246850000c1c4134840d80040d900d507001040d040300481011a0340c81c0500040d002c8079101d840404015580c5c1da44115064002c198001c04482403035038400c0c46104042e000d0700c140d50940240307500050456006070040802180007040c0d00c02c0c0c1e98980760740e02c6a642c0d2952081061514250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63756567 1250 63755317 63755323
    0x10315050603090c220513030801060f02010902030111070506100e0a020702060d0207030801080d0914060a26070201140603030d090201050708071109070e090109110c01060801060602120408 83
    0x4800c150056200000054100c0c205010300c0480c030f20002e203100d03101c081410404480480b42e01611008600e800d0104060860054510100d258907480708034031070b03181a50039201d03103c5118042c400c2d0754035040c100c00140e8080c404d415143e030b515800341d91503040301d0600c10316000c40108804c2d0000c06401080c8102c1010b104203981c440f841d2440540d50f0421440450035900410031507210075400807610340700b01504034203d24142c60780caa04031201940c003d80200e801c0c0c801803054900750a1071084440860500700001c0030302c058603017020481c410030303d440d00d034501103201c11a90210005200b40320300741d5030a014210b40200c030f1070f10421982c1000000680c403807203003d4030389410903a00c05030541164001d106580703c3c150090245ca8440c501c9042110543d075201000900c6903110000152116009002c031a200b0200640400444e0703003001016001800310100032504100107005140e20b10340240941c0f0043d04400001045c42880d104002c1d280000203014603800940c240010b22440c8000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63757817 1250 63756567 63756569
    0x50109030809030703022d010501141504030b0a0f020f0706240803040b0304110a08010b040f090f02040f020904020a0908010c0f0503070f030609020403030f122705100207140c010315 80
    0x10400640c4000d030041f00701c0d12611450503001d0030350a2400015034140e071a00c0c540011401503c00301e10f0110481252001403045000c000c0920000134040b802c24684c6500510a501407242d00610307181440d0303d4101c4039049101e04813003030f41d103c600300d2200b80100d00034040c142c640c814030002c0c8e041c1402c0031592a406540070f40b40840f4000710003d000d0000d031410b20044454007070030f001300e900e460b0646580a0007401040e076000301d003482600d0740c807401b030783c4100c42c01d0395040100740340007078034940c00c22014011444503204019003d21612065a443e8801407801642d00d84600840c14a0280003a0030345c3c44810002040c80841035035103c23101d81000440f940302103946410140d8810021058008100641020000074804100402050341100c24041e90b100c094903001040c4c00ba264000040d1005403c1c00c0c1d9005048813550581c00105400c41024107200d0415075517140c4921045404903001b808007500d40b0143d0029070741509009100c5100211400e19082c0010015864204000344075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63759067 1250 63757817 63757843
    0x60109090b0f0405130605010e07050904090611160c080303090a0308180303011d1005282d170303010e06030a0b070807020f1b040506011101020705010903080903070302 74
    0x607410031030956502c5000341444500c000300100a40d0400c18048410000302d40d070100e03000f910f030000102c3d4141402c081d680c82000c4580d07030300b8a800403081c10b005c050321900c00e003254056298018081c0c403440c0c0c20058010307528200010503e40c1010f0904500b030300050743c07100c4020f4100b0000d0050408000c20314580b0150117040240458807640013144008003405c90100d807900011001060500e114600c2008080c08000100034607208d03200c00b12300d5520240f043c80c2d404180b011900c1e4800300c5030460001c5902d40e180c049001c26980d0f40001080c40400864800c0304660890140c582190f41c01008010308165118038140140a242c080c0e40c9110600944110440301c200146066401b00400705905034003150000040c18408005030003c40c05803206070160150035540c010060002550702001c181141d03000030b04c0392020b400c0c0401405c01424180c100116109041c455180034001414250b219500000c0c1409890400400e130000280201074581c004001e46004a0f90000c0c0c494180c40e6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63760317 1250 63759067 63759071
    0x15150906030a080304052b0807030509010605150d0e03040f0b0d06090903030e0d0e0d080307030e0307050604060b09010b09120f0a03111005071d01020c040204120212030306010909 79
    0x59400c0080d14142c00390000070002c0707034000104000c0002c0407030340001e06100e5450010548104103400350b02c19111380032900c0028942c4000400151081e0003643c1c114a0324400002c1194554004c81d003c0c0e00302c8161103a4150300001c045100a64030320801c0385100c00300b00510708050034000c61040011080c440c000c160703040030882c51001e00d410360001004101c22402040203940d00c2c90003401a1080403806041401055820306203c0e0059503280e0380604020030f4100241e202d035541400c250406098079007016a14072404480c144100010000d883c0200020b00c45031800d03180103030685803240c41440c0a4041e41d00108401c1ca110003c4e165801000c56404040f5661844210b1a1911000014100b44902c281d10414143c020242e0014140b541041d00c5210310302c43c080301c040d0b034803c0d91100d000640088070741d81d1442d2505003607890b80e42d051040d01e0040380407000041c1a40c00540049041e00c0e24541d01004600d0300311410303480302000304091415441c103203001800c001c03114480c8084041d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63761567 1250 63760317 63760321
    0x2030412030e060a031b08070c030507170a120f0b06040302040507180f050117040809090408040e010f090b010215150d0803040303061502030c1e010207060518151509 73
    0x1030040e20b49041c508809404aa22a40d0b0110001c1c054141c0003956821004905100c1101c0c80c41400c0540c0310b12038030b4a0710340100350181c2c0c08031520360081d0000c0e43c800300c0082104140e0420500100110035096852144050701d0000842c01c45404100c04014146011031b0f035000c2d40c96080c2501c00300c90301224000758982d50101c1c103036404812700002c0950451425000300e802c0c2800d00910003591000c1ea11310700364030380100e1061b11905003518081d11082c0c09019001452a00301e41003a40079206001e10b909160741c1d40c1100c1c403041d0003a00515401d40807000c003444411085c1c80f8a6954960910041c40c0e40031040d08401050000039181c901c0d0000c2c2d01c00320b9010b030380319040040a120360088280d65030780390600b00100105900c0c0900c1d90303c640c01d01c000345821031000050303503074540510014040c5007503042803004042e100d0f04118400c0395000d0060501251052146e18400e600d161003045200d10b1440b00d0b14248608883c40c0c4480c000c0e01801e00c0f00e514800c85082e1070a00c4140d078540d41d65 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63762817 1250 63761567 63761573
    0xc0d0302010f050412030c03090b0c0f040b120a050c090109090c09030215070606061701050105090103180609020a0f290403020d0c0302130903020303040f15060308120f0702030412 79
    0x902180c2402d40900c0d07041200340001c000c0f81000e00f100088041d45c08002d4070f00d10ba88100c06642c42071802503c1d401d022004145404c4503400100302013140c03c0e802c5441e10f40e4403810300916070810010003424680d40000c20042c55850702071940e11424004040c1d181140b0200080c000815501401e00440c1d603400c0141c0140b8040e984400256400401c0f6100e01d0512550b00101139112840840b400c3d800c0560010300280900044040ba800341070130312030541c7c03c2200441e19500507911850405454110134001c40f400074510a090501030500452855500d005010005569900c00307403400010840c100100d05408400000400e0001c0b248a0400300252401c1c000b40116000a035004500c0704583d400c0005800e420011a482074644490001031003c403601280d0303030a071001d0090303041000060002040c00641c401d00701c0c80340002403180f254441c021801c0f180c0700d0708100c1e00843c00083c50750246482000303155010008460005503440d04010094880c0150b2049440d8024422120410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63764067 1250 63762817 63762821
    0xa0509160e15040e0f1e0c03030a08060102070306050901091106090307030f02060403050d0503010602100902090c0307030e030c0f061303090b130801110a030c02010504030203220503031803060f0601020c0d030201 93
    0x400c3d280d1308448201e0780d0302100310b45601024400c015022100b440e0084803040115980b589840d0040c0518200341c00c0d01300a60314042d0061046045025071400800081c956124140c0250040000000c0c820307000e1038030b00964003c01c140c5512032001801841392580e8006512801e490b40116184580e0724144089a0340d0b00071500000d0080c0a02851800d4031940807014504a5083d582100ca050848031049421039841d030201941040bc96800220600351001c01140c100d4080e01e030008400506030155411504000248065504002100140c601c130400190b900404d081200c00b000154954018009807840d1007801300200d0003050145608030809000b0380108440c4c4001c5c400302050768840710141c0d00000e82c0e403020901d08420114002d00c1442034611503949500110320f81001010710880b0000d03000a100e540c180803200128280d1414000f6007100341c2d80c0b1050480a0321414201401e0080082a0b84440044507007040a540e80c0056504002c0e0f605486e480b000d84003e082c1240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63765317 1250 63764067 63764081
    0x60706060e040b0f0708040203030d0e0f0708010e2b080c07140706091d060f030c040f0605040509030f0702040b0609030d0c12050f03010314070302090a0509160e1504 73
    0x1c01040310303108000a000c903a80d10301c0e1040d00d00d0340c40c2c401d45607504103003910242e2068030082d4250b80240300c054100c1c1c80d00d034440300c0b042803071100b201c80c03407801c540115140c50039a4021040507515000b013100c41c00002c00040c00740312545000407000e103001800358042076079020355450802c00300402042d01d440c80041150700300d94000700380792070181d2402d0540760381e00b0320b03885079400244030104006408580680c0328500420046408540c580718101040688582034038a154980940100e1070a603a94600c592009005c9080b0080303040ca181000300800c8403002004000d0b560010841012201a00300c101c0360803d47c100c50004100000f4404202c2501070030705400d802d8071503c100f40c40401d41140300e010307041c0d11412400140080501084a860040340150007040a09000500018640203c91104003004204a444440c0d60f0740028404170b0041e01d207242c030503070780700300340000070a06000403150403601761030400c403d501d005120700a511009110b40c0034000070006c2c4d24035556907500141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63766567 1250 63765317 63765329
    0xa21031103040c0302090f06010807030e0309181f0312030c0509090a021b1c1101020f0f07120504120b1b0c030c01060504060608011a090d06140f060603010506070606 73
    0xe5120310300707071804560b480403901069106400c5080080c2080b084000104d00c10601030b51081803c1d2542142500581881d59036541c0b54041403007500510b0320340c0c4804030004c00721b0030b41051103410281342491000f08462425a8900440041880402c0032903080000b40c4801c0d184c00034034800e85c0036040703a140c0120b6441c2d03a4081c0c0010180402e076400c2c0e401500d1a0840320306110715250035000300650b150f40703030020342003084910382c0f182c042c140c054082c1480055030103001501d0b0401341101034040d54441070550724104404917584003446040001c0c07498050860512030700e030500b055000791165510030350082150300700200140c10b00300040d8440300d50840708030f001703501c5100d06c4451544a411015202110390728109001440c2d103410700842c02100c4a589a0751460790031300308051900e914410740084076140402840c140e90f01e91030041260107008500000300500401041607115401425401c021180501440f0540c0d0350f90301202d04540084640580d200c0d0a40703480307006071400343d0043d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63767817 1250 63766567 63766601
    0x60f09100f0603060b01030614060901050712020a05060a0e0c0607060b0414060f09150f0307030c0b0a140a140912060c090f090103031209060b09041b05030a2103 71
    0x1000001c05103402000c01e0701d1280c101440529500c0004400325240c0303100d104410388522207455030b1803c0c1b0394003d1070144418035200e03191184c1612006a0404480b240d04016841100e8140c02c2c0441400002c0c0c00208100040c000304070b040d40c10396a40c2d0f140e100201d1141c40001120380801120742e00c1034003880809001805007042400706001007640482e996400f88102900c00c203214904040d503a413184481c1000d8a640a081c40e01780210800c42440700f507010301c180100800401c1c0d942c441200180407003c1c48503502d0701c200c8402003049014200740300c03511030103200039528183c11481440a1400c28041103869022201c0004c41c1c10300440c00c07101c0280181d50a10640041c0d040007880280e5041d0382d0080c0c04c421103400c6c003d60f400c01340310241c006080c219240c001c40030756801c172242d036502504000c17504000d910000707400407400b40c3c1c0c1155540741c0742c2c1049030920303d4a003c410040c034088014200d200c140e030311001142c03488500801e200300e03942c1d201861780500a510081101040c4440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63769067 1250 63767817 63767831
    0x30c09030209190b01020d1e0507020a0f030302120304050d180b0a03020405040e03041a03130b180124030f0501021e0d0501080706050702040c0207030b070903060b0306010602060f0910 81
    0x8034518007041c1d10b0f4031074583c40c1481d00c80c600c5540000340c601c15070011640c0722000482001e9050350140103c000d0300301042030800c13240e409656030307182c0000540304c11041284900c0c034614007c2d14220545010341c00001d41402004085040441d8001e44a9807a0405010303107881050314801109040d000080c1d000ba010410841c0c0a81c181d01600685200b03a030f04001250320009902c1d541d0185100390440e2210b00350f030005080300408040e5070001140e00100c484c158080c0d0f100c801c1010115910382190a075100c5680c00700009004014242d440e010f81c1403204009107c074040c13402ca4900014116001a0760b50b0003c00009504403840d80c0380c80079046400b55800101c01480b45c1c000315281480724208000441c08000108602c1c040307510350f40b106d0340340411070782c00d0002414400d103019095002d00380e0000003040d00c4460843c812542e5035500440503056107414002ca51741e1403812030180e80001c005001c001c3c0c000032202d070001070140203420f40303aa03091001441e01883c100101c00c2c160500071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63770317 1250 63769067 63769081
    0x1030b03070906050f060403050607050a030207021507020f040c05030a020c03070b0f01060f02010501050d0609080c0610170102070503030a051312080709090203100312090317090f03150403030c09030209 89
    0x44102c05995048a1588503445c4030380400c00140540e00021309581c01001c0072a030039500903070045c0806425400c1c050300302070076600001c0f40110901c00c4035828010000700001107140c41310852074542c40442d0104030b900d49a1030700400c507010040c2000c041c1540000e5001c3c90180c00c1042d60032180e4094900300d8185400b00308040005003c0c400c1c10003240000c016440585c0c01805080e05965019143c44021511500c5140103085840c80a46a0050801240642003030074410944161259409205400d151503a051190b01c400d0003015026407040c00302400055001c0212500710603200408586038079949a480b03c032040c13000000b044503103001400221f164010401134070804494580d404e10943d103d00070f5003688001c5403100303003641c6540b60520020b41a0350300c15040700454036140141c01c3c0c8036504c011562a8081c0d15200c0c0c045e0100700101e1038948903020f5200c250081d0081c0011011860748041c0c00c54020b80000e06258540c20190034291161000000a50700100903400d113062100e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63771567 1250 63770317 63770321
    0x8060408040e0606030708060d02061b0d0207090902010c0b0919060b130b130e0c040204080106050307050a03080d2003071205071b0b060a050414100e0f0406050601030b030709 77
    0x8807a10301c40b04650400521180740c40000d8074822040e036107600c4444c4d0344800030040103009401c0c04a030f0020007032020351203e10002c6d891a282c190840007c0c030760749107840d00107860603060703911028009040440600060364000c0301320700703995070eca60308400c5611140c04040c20960b4402501140c00c10302c1301e0744003d01069411983e544142540e00945550300400c1400c00e84841401207500041000390100c2e140316141d0052079420551000e0320a504010b2002038240da1141d4888125603454010601181c50709001d08401400c0858181949a196035a1420b0707500130f640c0d107080c1d029507400314525010200104111010000b201c426507030314129802074502c2141f4002d030901e0750300d00b0002605050280a898184501341e500007140c0000c50f644072014544018a1142c004000741000107a0b62514060341c042d50907103482548030740c81c100003c000e110307040354400c146444485042c0104000702c0321300700b50455049240810035075100300040c1d002d000100012600f521403200c000071817078629 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63772817 1250 63771567 63771569
    0xc03070f0807110907140705070806180616090302011202070b01060c060f051b0a091503020a080903071703070302070f0501060807081c080402030a050a03080708010632040806040804 80
    0x6030003c14a0388090001d01100200855080b80802c2030003131241a0a01c150000d04a02803140b011a0425916020190300304203003500c000b039081e101e60b0741d0030000e030a003030201e164040421050b6495200c1c1502004040c8003c070300c4041d060108400301180100a01d0701140c2c406074101c02000740b156520040280290f415190a4910510701048c0c540c9640542c000c06006a519003074109000c5000300407034145501840c0c03070b0b00a00c00c0e9080002252890108078491120302c03502c005884242d000030145c0100401400c030710b015002005150002010005061084c100c90740010b40c6a0b500e40d20b0903130007480340b500050303c40714000d0491030820105400c00e10648416009a8031090b5541c502143c1d1829852710610030b114002c44403140c042d00c41c80c038040d4028001030440f8018091604c9072824040004002d0b800a402c480030007403480d0f00710914a0040000c1c0c60215021030103034404124030b5001692a5001191940003c0d201d0300400050300c0241c0031850030b0710075900f000e2074041029486 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63774067 1250 63772817 63772823
    0x11806050d0f020f060706060e04020a05180a0f0f02030411040c0e0121110c03180906090a0e070b0a08010e060105030906070809121b060108011e020c03070f0807 71
    0x800602150303509201458104540e03025440c0d610b101d54550800011070700c00c0e2150341c4c221405010b00380100c2d8841c050785004209001002084d030402e4010700c42e02c43c04d56001310b4000c0e2849825a06c6004540307007441c0e40000e2844001808501245400f03014080c100d0b40c1541d00d80c0040184000d1122151034103c1080007140c2c200b0400b0b116200950799010038085a0340030900388000c0203031800504505080320020701d140098030004040c080c000355004103008040c2039101140c88180716200ca41007101e0407400b1500d601803440c000000502c007190050010804944500c80b00d4180340081114802901c01c80a41c5030f10b5003203598000340a000c0034403c1503041e42e503010110710316502981c00c40780100c0e407881c06051a03664024003070303815080280c101c45040c45648100c003031113417951020f010040c0c0d0f180300c8a0790541c2c00300d0341c01f45082c1301a040705006d43d241030101c02120440c20407045c50154642009600c41440d856940d0031070080d29000382a03002500c2540041141200003007009501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63775317 1250 63774067 63774071
    0x405041407030c03061503110c060403081f05090403051303120201020c06102409090203010909110108060603060f0105091002060f070c0515040206070f05030a020d0c21020f01050118 80
    0x3c0d040030100d0a0390310504c5071584c40c4464075501d0181c0c6110784c025040ba444d1a0205038900511404028500207044074142c0004503d44244080c401c0740884442e181e100e04201e40c40070908010000c0c110110260004040c4800001c400300d00910000c1528021900001d100300e0b2041103140281c080c3d44008501c3c903490092000160414aa82c8540400d03501c400712007881c1c031a00348044070741c0d028001100c0024003805030f000140500b0750340010341c003a0031072400c00f080541013442e1040d00084031031903460502083c0c0082000d81c4d129282500d038040e03412038126050820002c01a5914461100816004002140c001000540004180e800b40807684852802680c40b0b034412514400501c0c402481034204410642d1080070440055030058002001180340104e80c3d612406004030003a8100c0d201c2e000810305100d490380600200300942c4940c103146071990103030f5562000124103949640104480c0b0204260024070030003802c058840030340c00821113540c45180502c402d0408c400b8010b0b11174 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63776567 1250 63775317 63775331
    0xc0909010e1e010b04060f06032a0207090b010302091311120a0c0e030f030403150209100804030f09080c04020315061201030b060d03080a0506060c0102070c050a080309011b0206040504140703 84
    0x108180c0300f0340c1c0446901d181c2541f502410010114054800702d10841203054040b45024003130129100c034414107006640081c44094603101009059403105441c1d00d06040c81030084c101d190f01e44280000316030001000018080fa07040c1c0a0000300e018807144459545100c40070081e4558182c0d01c120100d48242d29505500341e0f005041650382d201c011a210101d42017401308000040d0030a1483c507443c1e0301d44401505103107222011078100032a00d0b42040008031051300384001e058006240c1480000c142c50942d481500780481c1c1903841c41020402030280f0341c00400500035108401142100030001442c0540c1ea151401030096584003c0c0011345a0040ba400880d84500d0000001545c49516445903180c998541c0b08010003401c00030100c68016004019030442201c0038402030030070314842d81d0039165841c201814490b40c40c47c21340000005602c20010300c0f40070fa030030100780b45000d50710b6280e10024500c0c1e440811341e00c0c0240e40c04160450f080102007192400c0491819119150b640e030100000307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63777817 1250 63776567 63776569
    0x4080a080c06010b0a020a1103120712080106020106050d0f151404060609023c03073902090408130b0711040506100e0114030106020d0212030106020c0909010e1e010b 73
    0x161083c1702415001d80e00118121001880384410b04041040c024199030740131041914160980d0300081085959100181e0708000183c3c011100e64050841407008200c8141441d001c00da0004171240c3c09002c150a4407450010499010121105104280b80a1000602d050703144005030505030f030103c41d00750603c0e1002c00c48140170310a955901802c07024114034945008802d15008407001c0603032074200e108010010210203060020340c00b0314038940d940040700d500000e1101d80000c0b51410b64100e0b01c2945007070510304014849243d50070307404483c0f40c035540c2c45524000000d40700d5603c1c0c01010520803200021011200400740c4800e0f03004040a5545100400401040741c0c1d08950850380308802e1701400154601c03900001d0940001810322203925011550701c445a504240d100e000181d12240c0c0314100294148040c000ea50200d8040380c2c29075040500c06074581c00000350050041c0c0b0000b00003002c2080c00d4100c0d2100070004015100d144c04441e0282c2c182c428200d00034606036007412081582 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63779067 1250 63777817 63777839
    0xc0203060a0c140c0c1e040b060708030106201203160809070e060f04020705280c0501080c04170105040309080c0312210f0609010906050f011404080a080c0601 70
    0x40b50055a442001440d41d03000e040020760040e148002117441003284200054903040c80721190182540180e18a054908041006903141d5405150180c0300900603200068280d00644c1d042d50f600d800d01c80060304280f060798000c4d203001d5103c4452441501c5021650b00ca003000114010030411810348109005a141541d10190a6030240b819a010301800c0203c0c0358007206007034008400418480b49030035214006001e036004000113495a4100c01c801455403040c2e014400880007150071900340c281179903200c1c90710000c0b451051138103104404000580f07003502881118080c02040e0003800b04266544400c5000b40400c130b81c101c0c04034224031008101d1001c0000e501120107030045c02001d00000c00e0031021400c0c0c0040640d02000322070307840e180f40c2051001e06414891810b501d00c000140c0b81c4502008000e1070180c0c482964140b6018003401240c481031642c14102100b03003003500c080c421440f08581c05104540c804001400342d40c0c0143c0c02c12580400409a10717100e41c041750300990301c8100201d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63780317 1250 63779067 63779081
    0x8030a09030f0f050d0902060d021308011a030709050402031608030901030f06120602070c0509070c050d0305060f01050912190213050105241926090717030d020a0c0203060a 76
    0xb0100d0005e00000c02c08421a400855981d8800f0785800e0609a07400000016608240070302d09051403c0c3d5000e0040300400d01c6400b108110a615040e14036416802003525039034030b8024000d8a40e1242d0000c0e0030741d1420001441d2a00c5082412100c440c0d03503540141c0c40781c02400c6070500003401c6c20b80d40b40d100d204a00603841541e03220280c00307a6409907551550003d41c00300710304482d00703c01c80c00006110390f5000907480c4100030903111001417010300e1500504115200044030107040c82e00d0144411500c1da035180096030102070034640c1d520b4510388000307140c6005040d0401c08511070004c510b00d51100c283c000044052080d80ca03042da650280200b041138410900800703421802100700300d8000c00c0310180c2c10310620b208040c0c0c02e00d848509441c0d0b01c2a921000180400b182c6000001c0b24844100c5245040d0154540c10000245c1015540c2c2c42c0c4078000352182020130003407134445244801003402200c01e20f418111003190748104012010f813401041150991090180e900041c48032281400362107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63781567 1250 63780317 63780347
    0xf07020607030c0c05010c020601050a240503070e0306010828050c091306020c0106030c0503010e12030c1b0a0b07020706050919080105040b18071202040e0a08030a09030f 75
    0x102941e100c12044009210100201080160042184020501c2031041d85a01051a800f4000541c141000e00c1010006640030410a902c01c101d2050b20ba0302404c2106440c0b0058a0b10590301c0d1101101120400a2602c000e641406044d000144900c0c001070b8001d024491a04042c54469901d084241d400c1d05100c40642160440740000b00e82e4078100da007850b8003400984806d07030081201e441308412a00003d0009515030f56540c0203006100201b0030303203001058110000d21800c0580c45400741c650b2050f0442c0c00303000102001048030701d400c1c00280c1c1d0041401c59001200711114400c940e6641e043c020301a02c0003d034440100c0c02191020505009a40060700d03028505031400003230084000c007401800080d08000039002c141520203000300f5004a010314012596420550310450064555500b408060751042408000010480c08010703240c58040f103001404186000d2581d041c070004c0a001066620300000300140c240340d550002c406640130b65179111101e98140411781d04042e55541c20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63782817 1250 63781567 63781573
    0x10207050d0b06120f15010504051b0703030c0e10020106030605090a0b0705090d140a02041a0a050103020706020417100608010c053709140a0f120f02060a0905090f0702 74
    0x160b5982045030440c081c0400132401c071021740c9200e0400c0360038003150f100c1711904011000010045450140621900418800620004122052284407541c8a0351308002e050549039442c0d03044107402102c0061070181c01815030700d030503144060001d00802040c0011100d183c038000c00f00305800e40000d0a503d5045c3d114072307124a0358990708401c0d00d1641100d1926035012082524100c0003c10b06010302d451003810000410140c0320501c104801d5800b0903144550082c485041050140d40340c03020700046540c03c1c200140c0c0c030105800c040000e80b0581e00400c81040c00758141c0c00405030000b076004207503801d100d82000000d845e0b400303803130a039400c22001c203000807418445221850601403088621312008000041c00254641031030903401022036183c008070701944030801c14542011001c590442d811100e034054113041118a04080e815801402c1008206002c003404000c810f00788201c84980082c5000c1c0c0320611090001c012918500030a4024000c0741e010074000550351280314050f0110f0303000303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63784067 1250 63782817 63782821
    0x30314030103081e070203030a0305090d0825090801020309150a020301030809060918010305030d0c050306090408090102190606151d130b06040306050703050c0705030a0804020109090e0606010207050d0b 89
    0x213000a5100070282140c0d000d001000050700681d8100700501c203440c0240c40100e054a000a21981414400c00c1c04c84140001002008502c08604c00080006000b131a0540110901c248085070040d580b80c1100105620001c117002080e0000604010050542000300510307a03176280507071059000a120040160341e050000c000c1e00d02e00b21001d01883e8002a0110792035182100500600240070b902c259110703080007607400044602d034092110380714200c2c10550f02c1c5003041e2012035002c85004001506c07603100030802800790384c82404200d0081951807601100c035841c50803c80c1c01016240310f24405446400340000e01507000d0a40c00e0016010300d0f00b6441e1a4554a00b4800140f9411003c501c006541c0c007503848080c0c0e18440644003460298400140c43e10b030611000d030031290080d0400890000c00e2103c0030018800004840100a03103250521041c0c807240f0042c0c07859100c6400841c6039504094001c406410005aa18440c2209030308407042c2d29a02c100784226607848000c041c10021100340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63785317 1250 63784067 63784087
    0x81213050304030201050d111303020906042304211107090506010f0c110a030506040507060305010f031b0f030f02040b040203011a1303050307050703060e0c060304030e03010608030c030403031403010308 89
    0x409071482c0d1f4460348000c6420340342880c0c90091580100f5500064954038101031095007171844241d07620440640d03041111f1038040010011079030094280b16200c42e011400138003040b011624498100c0401414680403e841c80f901800f0141d901000c0c8805215590b400211454070303005075806040103844000c544010401f0072a04103144260a42e4503805552a0314440c0d1200c0341040000d500540240210b030400340b9080d81080398592010041504000c014412100c071030044c80102c1ea4441c00c42c16603200c80402014100910b644030f40091100a580041030061203640c20202030306c03c440802206220104010072070000b0700400240c0000c00d07507400034aa01d00c1c0002c090301143c810384c1c400c00e107a90b0741e6024038540c04a001119560000c0704200108500360160f44024013a02024200c1c2001000204919010041010702044668428103403161030a42c0140301400201c425a0ba40d1000300890907030300d5005210440028040c02040612510360340203482c140d0b50b10004041c034003c01c2c0d44d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63786567 1250 63785317 63785327
    0x2031e0304020a080706030b01031103090d0503130c03080417070608130311240a05010e0402040209180a0507021009020303070f02060409050a0603020f010309030c0201111603081213050304030201 86
    0x70801c07600f2a41507030000c240f8403002c011001c010101a0b4020070084031800005098403e550890405a0414010b1100d60000402c0f003007020105468a10b0322030352680c03080c041c0d04600b4a000340800e0180362020050017408001001030f00c82031852a0740400c040e0590310b9440405100e14400141d040011540c8020807440e13005009010707242484081182c07030fa0290a21031030790455040c20340c4440207001e08001602285610807240b001c1040700e5850103000b40040100108024417660b030016403c1e5040e5104001007140c0031f801102001c00d13140c0300340301c20020201940c03810098880d6440307003400d5020341d010f03d0304d402d075001d0055400c3c21007550fa03110349004407444c202da12a00501010401d42c080d4841d0520480c0c250001240451450040c85141d4107907001c040d04140c101540080403a8002c001900c020f80c1c280790020100c0035605109007490030034014141400d84030340c000024010004043d00718008481c040716a1904d50100004200740401300c0102103810501c003c1003d58028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63787817 1250 63786567 63786571
    0x114190f030603150c2706030209120607020610050a030c120302010209030a050d08310816080405030c0916050a090b0a0f020c040e0309040209060d0504120f02031e03 73
    0x1070070003080040e141e50b01d290140800020000c40d490fa035002ea200c40a602000019004104a4410400101a0100f52940b05041c0604c00615800150880c03450322100d201c6e040c00d000b400c00707440a40c10203540082d16050300303480710396040c5901c0502291915018003503500301c83d40030140038030662500080d03e0415081c40c0342074066560034461444d403174a06005100c11148114003804492484e554050540350f03000d400c000c0388079001c0ea20a1050440031201d200b1140e07001100c0703072040b0b00c01e24080329184201440300408420610303031381d020400c240c809407050340c3e0300301c0a44a4811002041c007804243c100e44105e0020014000c00d1762041c092002030400d04490b2604034141605c41800c0d1541c0da02c031042e0340c0001103d91640b20340d040ea060060100388a0110b400b84407035185900c1e2244d0301d00540d00414845d50b40042e40900c9a07840c1744c1101c0518042070350602441c5014203206000040410107080400d5805545181061012045605803001c2201544210190714501c1241d9080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63789067 1250 63787817 63787847
    0x4030810050307210c0b07050d02060f28060f0906051c0318030b07080a050703090201020d05090301090605011203080f040503160f0b010312020c030307020a05040221010f05011419 79
    0x540042032021800c1d1000170300c00b401040701c00c181d460540d40b80640c50515841045021134106405004003041490081500b0075031884140c03801060071050946040c2a802162a590b85441c0c4c0c00100c0d400004110300840d500500100500c554607400e2011120a41d2001b40301900b00648400000b80144224615403001000541d5680c0c0c803543c48030300d540340580d02480460b6048081043c04038013070088960000144c5004d000c1030110740e00103580c0d03420440c0303204184000491000b0035a20254054401550407550030301035965500031100002244e100c0c1580040d0b0171900050011501e0006503000d035900ca401546072005034803201074025420310301254000c402c40d581c980443c5916070042d01a42c003c100e151003c0c07180d00c0d00030f864000d2035060f0078000d4009015030000369a0f4007064104984042da0050b9440ca01075108a02440c043e00c2c0415800c0d06840011507151300c24071811064400c00c2e00d49800164050811520390300601599004050481d10500112031190b20001c10410f5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63790317 1250 63789067 63789119
    0x40e0f06010306020304060f090201140309010b030604060902040c0c03090e04060b04140702061b03010e0604020c030705030a020d090b0a0c05030d0c08060f010503010b040e0907050d080304030810050307 89
    0xa81160018100502a031080d16039036000f1061100340000c61145441c04100c5040030080903100350b001030700c0c1081825090884c10000700019401d00c0081d0810498440000d00b038a40e00d00e800e15040e4010010b4400c1680a1f5180559100b0018003c4c0403440e002038040e180c040ca070514140200034a41001441180c850341c03604005c2c281e507141da000f60b80131680454070071016460003400c0285042d00042c0042584c051801e035113155000070604a0303040d152401c448482c6503031842c1c00702d0060b22032032040307120b244800103c02c07051160200103000801d01780c3c0c2c03d0f29084605070704c013229030442c02d00503100f2411081010814043c060600d007110301c0d10442c26603003070085500d0038030304943c2c000030444040365003242000864941b0f5080502850401d003081819541401d019410b40e0241d8000e00500c0d696000108001100c10000c1000409000f04030300b405035554030745402540c0003138504901050030070010481310301b051000c1d1400d882000c0d005165051501d41350011305543c0c0304400d440f0007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63791567 1250 63790317 63790333
    0x50a0c090501060206162307020906010320030a060305030403050610080304030213021e0d021b0604030206011e150f180302131d030a020307030f0305090a03080606120a050901060803030f06040e 85
    0x4007c10000c0d00d00407030710505881d00c841060040c0306801e80020240381c105454014000351a05240c0019440c0541801d21544c603540e403940448000c1c0140d8001500d54440070400200b045400100a44a1501148420f1903903994403403943d6a0f0246000080d404200c104c241480b6030811b41c0a4840c910340b00742c0e1000540b10381031400c41c1651250024580c0030707800103581c03a03d0703101100c4801e8005c4c4048000388002c0c503254400035160300048c05501e680003031508410240e1480c80c0f2803100034064800c4040c2d0002111400500701030700c83c0e9a403802103400d643c28140000c0c4000e125030f007205e401820418031410348049080040c0544007481002c4e500002e040038580310104058001d80d015900116560802410060400304040000900b098202401c01c6400c01010504412059040c1450403103600d4100025041d030188007408600300300c03071104020310403107a40c0091b8016061003000300107403074441050645900c02102c4a020049200300800d950341003d40c40100428081e0041e10118 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63792817 1250 63791567 63791597
    0x2060c010b0a0801020a09080a0c0e070c0501050f0402100c0507031704091415150d09150c03060608010f08060117010905060403030b1e0319060b030a050a0c09050106020616 76
    0x5503203608038403c00e0b903010030030460280d0807000b084090140030004124000065651403080b4105000b0070b2100d1074240081784000c1d0203070291f180c04a900400078481d03454050500800d0100c2114160b20842090640c1c41d0020300a40c84003030840e401c0f5016045280c1162551101d0340c0c0d0203182081d0ba030004100015450220b4811f203400b400c0303880c5111400d802c000140240f200810342010748240801440941103082075401c1390940c81c10b00703030080b8111041b03042c0110200c03c81d8600e03d01c00790800540030804e66041c2d122005a6285846144060341c0740e1600722002c1045014400042c1e0014006011200038003001c41d07942e0b4020400805c01161a82d2141e041200c20754007103010a45039864520149005c02e42c82040341582c5030100d0802010400290fa40c00042108840189440c1210000d204070358000c03200c2081c000d401c80d20361010501d440c99949001d160103540c0821340c0b98010510420328020b40b4100c600560041045444507202070751006a0041284280b1511001309881 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63794067 1250 63792817 63792829
    0x30911030f0105090106050f0a030b1b04030b09100b01050a1d100f0e180a09020112051003061103040b06060d02040f0b070201020c0108010e0112080409060e1e06010c02060c010b 78
    0xc4544104004501401c10318803045c20344c0c0050304910302c00c04264a01d01c2c0c0913111801d04008498101c074101456441d0484510001600300c81046100744002401105001e01c1d40c1129000c2e040b180308035083c40840c45e5001302140e641c0009123000400810200c0e80b0305101c2e641c000900c007800c21102c0c1c68106001c0004254108000c00c5c0701c0030425003a030900c8515081107a504d200f10003527924150092040d2100460100010244c80140b9500d0311903000390f92055108a9000001c47c0e001c10490610503010003c41941d44000c599a9007007803035000c1c5010300e401c10b580c06580e0101c00b031549500c0301c20402145400c1103401e9140598280000504a481d0100e280014070188040340e03031b1b40106000080c14032031400042810300c00000c004000e544005070345181102c141c160700079a40300302d42c601680c1030302c02d82d808190524180303640842c0c010047e850303050045e0004080045198154007181e0380d0201d044a100380400e14410103600503090040081540700c8140340002411800c00002402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63795317 1250 63794067 63794083
    0x1104020d1b030c0f0203090109090509190b090111040503060f04080c060a1e020304050c0f06090406090212010509041101030906021b070503010501170303060d0c050d0809040605010f02060703091103 87
    0x40001e8641c03260720f4480c0e07001040003580c2580d070b2000d1071400c0514800681044a68451040300c141e50f2800560000c10920000d20078410540c6c840c42c080300da6042201241e00c040d1031241003546420010b840900314801218101c0f90058060405036680811500045200501c10340d5a030380d082180b548410800e1014a11600b800000050781c00c1a0840d58000c41030011038800d2002d10400605c80402c100190304828405c0843c0c810f58015401c10100e1100e0003105c00c610303002030601c403001c980303441a90080d00340005201102c0788180e036560304000320341500fa10054020040c68a07141441c0d44a604800725040c050503000d0324040c140e43c10749030054040b00e141d2030030f40c10102c028000e52900380510360060a18040d00c1001a03090110561039210180469200c4d004000e990000c01000005000040c04000c00034400740c0d800c1c1c200203070702c0e60180c4a001d03c00c0f03140c00d402051a6004504016151307045a0080c0016031727603220160010704507070034240c401043c0b8100c00e014070380e01008a0307d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63796567 1250 63795317 63795371
    0x906040e01030606090c0309020117060a0b0a0806030105160f05030703090f1a0907050a050d0f230706081b0c0109080d0c170903121b03181501031104020d 68
    0x300c1303610740015013045402c0c15040000b01400c141c90240581e03840740300c542050900c20070b00a040d07207480000950303a8a40da804205c600c400880e13010300242d0400c010909c2050154000d000950701e0465000f140c003113a00078200801d0950110200062280b270241d580142075060008029645848500100c0c40f4003a0495203c1c080c04006d81001000813512a0444607038002881030034180710028102c84214003130103000d601c4403400c0d101401800b002c00c22181c2d8006a07265204088050b00042050a0000965091044200c0094194840c88031540300c0c03524284100b0300c1d006156007841c55644920001e18996407a03030420b00101e00d0350350003011a44907c20740081c406081c004060070400e050303c10012828800c0c0d0030040e902101208540740c4040c452001c5100382da40c102c000c4600e00d035014501210200100070015403566942e0003104d5010250100c840c2a8030861440c03010440900004050f0b0485a4004d41507042c190068400441390401c04550f1048440c0d1401d81046440c00392 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63797817 1250 63796567 63796571
    0x6020f040311042f0f03010602011b020307031b1a0114040f05090c01032301062016030201030c0e040203190506031b060d06150804030206130f080906040e010306 71
    0x410401004008000d4582c0c030554080c060341c1c141112103c0c21543d12180d40c4c000803407500e05240803007840e4046031840d21744982982d8036940c499800900a05008000e05850050101580c116134000001d42d180f807a85a40e4a0032007044612000e407007503055072000c90b01000c4204682804120b4010380034044c000e00d240d000d400d008684200400e4035011685030982c1441c007030034010520004640300704905020f08012031081801e15882c8001524048a04007000c40e1038000310b00700390302015801d00d0750302c0e80d0b2307210940000a844007900d80d854070341d41003c003950010007040107501030f030801c516820050401080e03c01460020a0607130b8000c5590100d506001480725013580e83e00e05c074054005034161700410944618001c00c0010034002c9200070302c2118041411480b0001c175400044c041e141601c100f4a28400d43c040c00340181034151812005805048000340482e807145086007026500000c80711084025074491f181e041d80000e4096401200402000c141906142c9a071030086207c0ea00c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63799067 1250 63797817 63797819
    0x607080f130503072006070305031902040608160201020d1109040608010203070c06090f020402040b09010314130213020409060f03060501090209090115020a02030d030b010e03061e090a06020f04 85
    0x240c1021400c00030141da0900034850448004980000140c1d4104c071344c804111803510a0082c0c18203020840c203c0c00e5030748280d00050b110304050f0301030069406182e200800d0f084140c28100348500b40d0166018000005603a50b0002d0181c901400c0f4040c00303091305000042c601030321403809400b61150191f0140c0d915000040146150401c5d02c0b8410040c10b80d90b00840c06c50910040007400540380c1702c0701030480303034480c0045424040000c90941109500070011503445a54400041080c1c020b9a244e5000c6031620f010340702c50710382c929420341c402c1c4080100d40300d054510398200100b8001034441107074050380c24000490603034514821000506258450560183d14510340141500c805802c461a50381c0103008850041e02e460004505617900300804504c3c84401c1c3e04102c1ca0325240c00f4001c1d505204a0048a920f248c041d44084021413080c0e88418201c1055020300d07a07140400c0e10740309261454015650700c0140c1307400d04075807c06102d0042c1d0302c204959841d046c041c0d030881902580c0004000130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63800317 1250 63799067 63799081
    0xf010605030616050301050105071b030b010303031401060203030a0f0219230f0d020a3605180601030903090f030510140601090b0306010203040906030503040501080106020a050c01180305060708 85
    0x4030b49507000b91001e07001d83c1c101255030001070181c00b042c07051030706001e001326020042140ca108080080014a07882a01455032402d095075091028802075011901d400540100b6084003440c481c140d40164000790321b140c0303961003100c0041410400c6a40b1040e400d100303510564035091a46c81c01c90700990780b110b0924000105600c5c81b4480d0b55607000420000704017001411070f055058901c018060a001616050058020b480e1840301150303d1a02a00d20166040d00610f07c5419018250f2035030070005004e5200e50a101c0c4250411040149440c5e601c400141c582d031198002c44885442854000d000588e075440301240c08420345c000f250190081c8092101c207804521462011203c6400046041c0c10010006840c81c9414041d03116907480010010f5003a9008100326001080c1800e0b041043c035503a401c1c210b41b242c00900696000030b20003000021600d100254841c102604400601b0000b0f50120042da0200211820404a0030726668000007103001445514815246a100c481851074a54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63801567 1250 63800317 63800323
    0x60a0903030c1715010519020706090b0405060d0504050f03070f0201034703120702180106051c0b040e030a02070503030301060f110a02030d11060a18060506040e0f01060503 76
    0x280840400001d01c0f0301e4005544a110a9034200c094000280c0340003500350700480c0c0d03610800805507041401c00d00303140ca48036030001b41003007102c0e101d80d5400c07111a12984c0c2518a0b110781c0c032850781e0014081c0440311443c05103078060b076002841041282c1d10203400e1048281036820610b010b4940c40c00d04441882956058068454414409403841811900318a0280b100752503203013040c10780d0603001c224144040003011207510f0740d400c020101c400401c040d0072604c40c1a4062001203014011452403a64003a5a2920083c1a40e416480302420b1035445410341d104182c0c0c2e40c541d1803c05072220300c001c0351a2118880c140710481514040c1d5070342c01c01c20304081d2400f0003e60116020398002c20040120580c442c9090b51000b060f440c0043c0c03100d400360100b82c50a0340c02c850296160013401d0b0b00340030480e006200020740f070b02c40b0f8044d40e0309680e8510514080b58002d0140490148541074102e0000d40b00d58050740d4041002000003400c120792156592034001070608080300c9a64456003071000d46410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63802817 1250 63801567 63801581
    0x306040525060f050702010e1c03031406010804021c02060301030308010914010503060a090c030b0108070f1410030509031204050105060a0504090c06030c020717010c14090a0302011202040503060a090303 89
    0x3601081c000340b841c01d10300420f6184444034040c10044085080f0f011603200d4503103608403000c010b120345140d0401ca91202e18410055104901080c0b0701480b0000d0b07001194002c5124410503180c030041a0386076001d00c1800c41440041c9029210318450f01d200590b590030140d400f1354080d9441e0b03031466060490071411074915100400d900204e0400400c410754000801d140e0004003400c6c08100040180342c00d00c4243d460b80c00040440000100102e552080012240d0403a4a544244c1950301e030340b800c110400580680340c0980000c003006c005c9140381d020350081c0d50040c2c80c00b01180e00d040404548512150000e48040394180d4480d0103200c3d183c500000360380007800d403c030b504100c0080b480c2d442c080054994440c034000c0c141c440181d041050700900109005040200c3c0e4400003107584440c15009150804121010a20100c42d0590306107072041034520300386018010000e0641190010740380b160001003483c01c00f80c0c08000c00315403030f18140003241c01600207010100741070300c4030310b40030341a5021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63804067 1250 63802817 63802873
    0x1090e0307020a06052203050d020c010f0e010305100e04030201060302011d060405120a080307080103020301110708030a051f0b09090a0902030604080703020a020612150406080d0503090c03060405 86
    0x140300785005a03650019050445201e400c00350f981d1913042c034006044007207070a041d500314000340c84c00100b8003502088048416019030b09690b458118000150b45403258018600c00040440e58126095402940425000942c0c958807110503943c540484050b244121811030040c1d444207000c1003196000038003980c10381f08284006c8416071008012800c103024a00c102486080c10010202c0300c10f40c240b004000d00c0c0d0300507010699030b2600100150201c0ca00b0311040740a5072070aa141603900c14481c003900c442907400480103103140c6079044964050f20014088502e1442c50a050b40503100c0040e550307030003c100d500c000301e40b240541010020f040b8001410000d0240c00c000c800380042e81c1c0852400d52095100c0000354407107000e401c04070300d07005940300300070742014000842c4100005a0080584a034900c129805060565102030000703032000762041e400f595210a659060b4140200d0213540d105075134100702c0b5100094040003c1c5844820340d4150758a41000d10352074202850030440c0300348280 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63805317 1250 63804067 63804073
    0x120e03030c2a16080606030102040e062806021b040b06070f0809090f010312171303050d020d1b020a050a1218081c0207050d020d020d0605010602030301090e 69
    0xa0181007070061881000d070b0300c6004074003032480076240705a1000c1255034011503100f12102c0e00c1c0003103042421502280618a828800da10028506c3c3c5814001c84084c0c0b00000c111081740d8603443d040c8102c131074180258124030b00c192108540900301c0904080003e2101d0390050110b0140c4009207405681a00d1000c1c1c021828070358529030390f03102d0008841d142c65104254600702c0f020ba0400c01c0031030140004070341c0d00041d0032003440109102c0c016918180c0340100242d01c114103040354161101c0300d81c6d0000ca00582e41c000c000580c000c0d41c0600c031045441c002c2c01e055242c25040050b8030120f90002c20702c40544d03940c410501821040091074034000720380d1400101264903694441a03070b07800080c1d800404ae99202080420443c2c410800d17150b64003102d041c80c0501d2a00c0e20015a25017207068998030416202c007500800d042e10000b41803003164805490500c40440b01d1702882018044a1030070307604600c4801c001d01c0004d100344140e034000c11141c4d0142d40c40354102142030064030386151803011903074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63806567 1250 63805317 63805321
    0x1003050f0f0c0408010f060603060902091e010c020303030901020d0b03070f090c0c060c0f0315301a100501050315040e10061404060b0a0c030e01050712120e0303 71
    0x100e45019640261039840c000c1c200c0d80d01e210b004002403040d034010008550902d0800c0b503804e00260404400c1d02d490383c4092026a0b101c0d10381e94103d00a0040b15a8461040d07401c0007031a00a0b030b0050b461094062400b910740c050746402107403455005139048859a0750010b24101141043d20880a10882c00c4001d040d58925046807806065180e02401089030b507200010450a0b000759020007140360b02c24003d100c101c0700da04000d4500c1000c120303000c01090501c040640c4041c01141c03a001030750702c000b01d2124500c45079450076203030724031400c10704051008102c49500480c500103081c008078041c04401007010300d000c81e501114030b05d20780e0109050080c14414400705491596004174403003001d07540040c4411007440500d28000404e004920741c4e034944074000c14401035101500c07000e81000c1d1010b1048980d204403000c2580b084845a00c00074400760644400648034001c103c003410340524009042c42025290b40303010081540c9503001007103c003501541784a95a0040407580602c044c041c5042d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63807817 1250 63806567 63806581
    0x20f030103060e1f0f18060203040302010b061903020c011508060a0608060403170403020c100e01030b030304060c03050d02040306020a0509030d0306030b1f0b030703060611211810020c100305 84
    0x2c244e21400103140c143c6650a1119220301c5a00400f0101c0100c02c1c00c0c6040049420900300035030064401364010350805907044080c0c2043c400703c3d80c015507035009000c01361001584c04c90007508902c480c0740095403580718100d4034031181e41c03140002e03011140c040d280d5810980045030850705568081d5259420a07820000440d40009000350341c40020b1003013030115501c41c913040382040d407d00d1500b684410741034006403244c2c2d4860619140510280c804001e000038403020580c0d280214841d46000445035070700c0c440040e20a101610310356011031405402c1c691240e441d8401c1c1d0700700b4916200040d074042071804040c54104010103004d00c0c03030300701005901e045071511080110300411200f4035604403c514a0200f40d148900c078020035480d409291207040c1104014090005403040301c000405c565030340c0c4168000881c600c106000215162105070000c0040382003d030300024441e0400812030032060071251a038021509000d8010350107888204185c07400c1000c0e40444d218007900305481c0100704044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63809067 1250 63807817 63807853
    0x130e1617070f05041109090702030310050f130e0709020f070b070302070506010e0705070b0405010e0c060307020d030b0f10020706080c0c0c0d14070303170106050906090d030203040504020f030103060e 88
    0x9490041e20040365180c0700310b074840c1c140c1c41481841a0040e111f90b04020b2420f5020002d14003c3c03418548031090241c2e61030400c0040554180300c55031100307140259031440306641d80540b4405120a069442d159540d56403c0700302d80202101350208e83d00080c2020410480c0421140c0c40511410114101440b81e16002d55800c1c05000360142030b00c8103000300307440d54001d20a545003c3d600c120100b80500e400d01d80356000e8140e1102840403841781001001040c074101080d00d00c42c1450342d0061582c4414180d00b20050403510044907004003c0c0c11616589403115280e01042c070141d9001045a60301e0001c00502c80d10005000e100a180d050049070520003011030a61034000302282c1ca1001c0d4003140c10300710303825071170204191818410000000102364200b0400300d04281c07a15210303001680d030f4080c256030a21440240c00d0380000708101e010402c0c503200e41e0308004c0d98003e1040381c0c00c2c20785410110b01240d1120103600030f001004030040081102c90b002d602840890324005d484041144210303400303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63810317 1250 63809067 63809069
    0x809070e0c0910050f070609060c050703020d031802040504050105060909120403080d18050604030f0215010506031806090703061b080f04060b04050f06091b09130e1617070f 76
    0x2204071541c00401c443d041c820801d0b207002c0d80c030800030a680c3e40c01d14176000b001000e00c0b1a089038901c1c10040000004c070700580982c6e400741c0d0550080c24000c030303800310118005d040d0fa01000080300b1054810202584542c810076118501c230340300015a5003030120400c1205480207062402581c1720000100891103050280c1381104e51140780241c42d201e00746500710184c44106242d4001c0c9441e0b904042c01e004000410f240510b0094651505500d15020100d07292521006180700045120004100e00d0504200543d40000040c248000482085a103e400c0000544074132040d41d010030010300601189224440c1800504032001181c620414000f03040d0080017403642e9001314880c0001000d00606412444049000400130803062820a10403802c0503401d540304e0780548440300000e0502c0e0703515011809543c40080303416040400e400d0030001d0040468002e001c10b81c0d15491080c0d0010020010700103038100032040f5101c1c460910890f8074141c48180000740c0d1a070f0051104015800071164018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63811567 1250 63810317 63810319
    0xa0602030f090a090212010518010518040302190b01050f0d0c0603090305040909030c0b0108160b0a090306110c01151401032307090509070c020303090f01031401060809070e0c09 78
    0x5842e080d081c80010140d003040e600ca0100f160002900307004040000940d03c1c180c520444042220814414415030711100134010f0540260300c03c00d04110444008101d130ba4071522a01c1219600041c101003001d00340e5614004032404060140140040d1404c0c010780046800e00707642c0440c23000c1c065120a0826a480c2c81084185941c500c2c4000600d440ba40c100c4000e4000c0038024041c218a902d03004240f02910407041e5200000300e000801d501c2c4c00851803041c80ba40c0c0380e00d0b601c14541082030804269001400c074805110b410303030f00040012111701507007607079902009040351148001c054080c02d54410348808902012862014001001040300e081d160321401e180005100e801640c0c14002110708071b0810400019410811010300d5100312004203541040d6518465a15040000d5a0484100b40300a40c16041032064618508100c031842c1c03c07000c0c0501d004034140d403645260b4126510300b80c00c8071000820320030410900c074130100041c0005045103801d480032450700e107802d850540240c81c10780d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63812817 1250 63811567 63811597
    0x130b27040c02031e070c0b1c0c020c01200106120501050f010609030b1b18010e0603062b0204050c0c0c010f0503131a07020c010e06030c030103021003230906060a060203 74
    0x5100c071a841d8010340d50703101c3e4003000b51902c003500d4071614030342d54008200446500c2c07030b400885011000c650049d44000f0005070020709c90001e0740c00054402c40f003401d050f695003071041d668801c1148001d002d160000e2114420b000d4920a903402d05500b51400200800401c00d2408010001076130700050440c00c880d0402e6440e41980c5542082c80c124420020081d4402603012881030780603900e00d519168039203002d8980742d040c03501100601c600e80c0000c0ba00c0300d902154003000794403504010b0b1034450040c841d90580c20850750b1541d0000d001c80380e05440c01e00c01200003046401d00c01390300b0001c118a011090a10082d01c5071201c80c0240300d4800100400c1e45136020200d02c1c801c0100302030f03102c5a038002c06d00c080c03111460007070030096507103001408a0380011804140d003007450070100c048a009402d015005c1d4516030840e028000e0641c4e480800c00101992003d00304810035842400c800b100343c003d041081141040011075141c000c010702020701c2a0115007042001e290000200d03006c03491036860b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63814067 1250 63812817 63812857
    0x6010f0b0307050d0905100c020d02060412030b030c030609010519020306090112140f0d0201140609070c03020f01050708040b070203091305100302120a12020604050304060302130b27040c0203 84
    0x10801070032040c11700400b54850704061a00f00d07809500440d031b056449038211003c2e986e031900200e9852606680107040740c4040c981040103544030350000341d4403040240881c1c2030b50390f0038800f1a00c0d10104940c400000e0350f40300d0a100c410000480d540b400300d0b0034441d00394154108400060f030f1331034041c03003160310440c3c1d40034001d0104011844200c440e03803045819250300c492420036654444d010003902c0c9005500c2c02c251240a60b040c010081d00071500540080003ea03900c1c1000c0c4d4503000d4040b0198194420342466101c9034109005440c441e01d001e564400103414540703032250004001400e0f00c0e0640d0000c0c092042552108100c00c10303003d0f0080e40c0450140c0310b802d100300c0110081c0e003010390400c0c21444240b5480d84001420207580307102e2405284052080d04040341c944400380c4004003240c02c10401042064802d401030320854920b0001000b01607510a0b1003040c590103071811204401107180d91aa040018401c00340030740d4400c2d1001d00a040480ca0002d40b07920460002d80003940c960a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63815317 1250 63814067 63814087
    0x206011502060c130306020d0506090702031315090e130c0608061c02060c070801020304110a06080a11040f03030e0108010905190504080c0a0803090d020c0d1509080d0e06010f0b030705 81
    0x8000d00043d600644110f580342230580703802d000351004440c001d015404403400f0804651000040f510141c00c2440c01d2040346040c0440400100c1004c208002085512000840c150148510f251b0058090101e0403440c003000c2c1c0307070041414807158040c0b01840080c504015080d00da9600361840d11500c8040e1070441c01d824400a0554000c22800328503600c2214008280301c0815401940134074060031080310b4882d608c1003000a4641c1c00c2c0640f000040c2c4000105a041c0e006801043c4c4c0c50144c1003500c1e080c1915809080340c4d100c84c5900950020701d020320300c40303c01c0d600300700b280c0d014211000c4280700d645804040c0d810814010045103d45540e071314005403d000c0c1040c00e4500c01c400040560f074600086042c842482e0300f060707030101e81d24040c4005102d05039000081c1211800c1019042010580b103c2d2140f9081c00c6500c42030785030301c1340c88102032030001c0d13030750801001342d01c0000c44000ba442c0382032120140b0301030050300504000c01a400c4107000c000340e0201070340ea00c511549406591529000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63816567 1250 63815317 63815347
    0x20304170706150f0314030405060901080c040302090f01061205010f14011809021201080a05060a050901140a05070f030b1e03100e011b08060109090b0d051506010206011502060c 78
    0x40102032030754860001098806501814600b05d078002d8007103e00b01c42995880b203899100314842d00354010300c04c1010180e594050810168042d605000450609503682c000c1940414122110481d0f20342d00d0780107000309600302d83c2004100c0760210b001c101960401d0301c01040c0a46034002d40002084004403900039078070032a8a51241142d41d03103610a615a200d01c002c0294110b49a40d41030754140900100d0788107000160144500d80050092100d601e4003e044c0c802040003500605407035498409000103504407940341400fa00501000103050f11b4800001081d4200a4046004041c2800c0508166699500171003250510070b08882924410071000640b800c030a40c42900c140d00d08016020107001d2041d4402881d030300f8484507002d4100d42240007103402900480d8510301182d4060000c3c00031800a5018200c03143c0064108003920350340d03480720343c0f03040901c11144400c010fa21040010700c2d60306016803401018500d82c4070601c011000c1019417211002002442c1010f00400e00c034423507903500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63817817 1250 63816567 63816581
    0x105030603120c0106060e030f0c0609041b17090f0a0b09030c2406040216060903052b0c051e03061906081006110c0904150510080709020304170706 65
    0x2482c040f9500e80d422210640a0b003440e124030404148100e00c02840c600380880c01e82031007000d0710080e0402c04000410000ca5410a880c00d5402666424480c6001c40c50281c032031000c0f80007910341002d002c452000450b103505004000412035080401c945107001c00014002a0180d0711140b001c9607907484166071403450044180484040c8100d00076614480140700310902c0010b060310f40100d4541d140c01c03e0001fa4402c01c241c20541800010894000c94a17550004c05250300c24a8540d10f006040e00c1008a00c0d40d0307200d018008a62440c0040400c03200038801ca0380d50030b40c942401d504010100c1c191041060581001c50f102940000c0005e0507641d42c10f01c034070509005540d445e4013a503200c00009000c400f04454003180d208103c02d01140641c040c2665401c1101d4000042c101c2c0d032403000034419030240286c800c540c8422616821112008a0b0041d1071085001e071091071009840d003141949860460b5124125042c070400c107210100302c0020740587c1c1001050711440d80d452851800700028007030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63819067 1250 63817817 63817843
    0xa03050c03130f060207090209060a0e030a02090c0c0c0405090c0d050106121202060609040203100b0d0204020304061509050708070c031b0c0501031d0d080c070501050a0504030f0507020f0105030603 87
    0x110410200d00c2c0110404044143c40d04d903421103080c6629100c41e81c080b0b11420107a0781c2e104030b0511400382814800d0020a07000740d4041c1c03e0303d070148030b1580070466400e81510003030350031600400c16001c03d480402c800000660103c030180058240b0507001c50b101c0501c01c40450003080003810b0031090103c25040140201208240080d0f46562401c1c95601d61803207584c00401030242c1c002088003840c1180c2040e00440d0014041c098811041c1e440400910402c0302c0d160300118a0a181d1015941c0d40c800744d0b01c82d40c003982c03000c90100546401740c02030303140316007001c10130600d00414422042c0d8040c101d15404403003401c003a482e00080c1d0a0603508599040300d0003c4080d048500401003103501d03009401150806c1e2410300414480310302d81c0840845604202240e6404203601c800e4035885a0300454004445076280c2c0c0c60b1038401c0e02c6032801e544c000c4840360b01440c0c0b05d10520040560000520814000b00d140072428119154001514828200b610a040040c0400841c115940c01c0c4815220144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 63820317 1250 63819067 63819097
    0x4022d0c07060804020f030a0b0a05070e060c030c010c0206010b120402040b0402030a090212030901050f0a09180e06010501090e060909250f12240603020a091416020a03050c03 77
    0x42d440c50020001482100c4c105e000380801c07802140141000202d11a0031031740400540d1260350f510b400c680007014001c10000c20000350446030700c0c581d210440241048000a4059a90f41486003c558203640d1641c01c942d00719401240100f140c00340707150070b43e10f80840d810310080d032689480c00014058001c880310f0551061001050001100d4194030481c800b0788241c402600ca00142c0c1c4010343c40e80520301141d80464410085220042c030580c0090882c0c251304c0c2000c1080a03104c0a100784001ba10144182d4110350700d0344c401440d00340400c0507500400c000d2030300d0124130782804072480d00310340b0242182d4019082040444c010a60038460100e4072140074018640082d06880304203007455152141c40c0044a148001041e80003400f10f0f55658590480b002c0c0a491450340d40502d070141c003a21b40d052155503070314000300045e03a8100c4100d00801e003200000c80e001b044002d500e45c60050141a1082d40c540642c1b84035a81600890006025a014100795444580305c11080c1d0031032241140c0039000304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 63821567 1250 63820317 63820319
    0x30f060907171c03020d0f0c0e010c051c0903060b04060609060302210c12150f090405071e080c0409020310020a0509040f02040e180a12020f0d02010e0c04022d0c07 72
    0x10703030560181496502544047c444003074100824000c544017002108006a003010007000d40754000c82e0000340182c0315400301e0316000e002c402581014404c80d40658000352030b0302c0e0708206108150294401c640011101040460f25060024002000900c0750000b41500032481d0303030442005500541c0300e070317140c1d0f04689140c1c07402170001501580800c80b41c4111007100b0b00071683d540303007103000780541c12006442041a550804204000030344006d000325444e04c80d02c03002050070030303000443c00909190981c1c205030705418085540d003001c032000c5c2144c0c05146020301c4880541d41c0001c4441e18221019001680d81028480c100c1300380c41060350058000d07003801560120488550300800440e00d00c43c1c01da43c0e40317407178074410850488078201d40c000300e95014104040205500300764981241c8400d00440d880603090b200d5003410048103008071030143c0d40d00c4009e20a924420701c01407240c9a4101c40451400c2c036001c50055040030001c6018012480641850604070300000c100e416080c0f008048034042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 63822817 1250 63821567 63821623
    0x6140c0718060801050c030411030f030a0e0103050603160303030b0103020c07030c0905070804080702360610090e0c0d0e070902130b07030c02090901021b030702030f06090717 77
    0x400754409540562441c140c00020030b00010f21446010721030449289245031511b444400c00c05200d401d006a01d4091606620000b1030100010300c03d86c4015103640d0340d680080c2c000034045500043c01a0b02039004032190900305140b0b02a003030152645810b00164241641004030300034020482c0034402d41c840c0e24004002d0089600e141c0f000c83d4000d0a05004a45d50717404110b4035804107440040c503c0317000b80840c900600c4c10602c0c2c80e40310401410b400c021604c400084039a28000c001c1d42103001c00440f001e020403420044882c6101c00c0c01401d00c18145460010b0f8400c1c9024001c044403804030001c925200c502105411143d1500401000c0700d400300c4d10785130648000d45c4405050002464500346c0041d41403042c4040d0307204e039500f640300c3d405200000c1d000d000120388000c245071030a55080190309074501050150641600c40750008503242c801034410300d858800405c60450103a03000908014425000150341800c0d1003004004540e0140f4002c0c0c941e107090710350b00c5020910704041d1000b07892 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 63824067 1250 63822817 63822839
    0x1303090b0d1b210203060f09040b0603010e0d02030909040c0b070b010e0a060513090f0813030b06061201030f0501020c0d050a030f0905102a17010f08060106140c07 72
    0x14100e4102016850310102c40003c3e541c00c00c84202c001c0020220103501981c40da155405107500c500b02500c88844c58a9802c001070f958401204c048034424145030602905040900c01c82c4503080e130000c0140000c0a0710070300039550340902c081c09440b036828100000c04006d5204c92030b200a01014420b030703840e91075900d01003a00d4074003401a641e9440e030400c0083d11400d5140070710012a0005400b1004440d81c001d1802c014217005282558544e00001911000800d490300406900a40c1c1c60001002d5046140c0384c0d2003058058520b41c8990001d100110328205100801411250b021451080c41420703858001e0283c01010707058a03460203003100f0910b080383c008000f800752880982e41001000032942100d0119040e8607400707011684100c112001c40c02c11948541e45415400300e0b40c4026100b6250300c4c1c284014a0144540001e204081081c0400308007401d070b50240020204401036503080c20306199941c00144034400402241e1740140960b0b054010480d45403560346025518120b031502c6890380 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 63825317 1250 63824067 63824081
    0x801030218040b0106030513020310050105150903120c100c02010b0108060111060708061c0c1e0b030c0304020a05030f1501090c0903080f0f130e070801050105031303090b0d 76
    0x30207610070081d000c580c2045020024401c583c007212022950b401d0203c00c800602004224054400d150741030f400c05a5003c00c07108901c400c1c40300c00850652b04110030b00074011002c0780000601402403051601c0b56401085490826800c0c010340c80d00e0709405810b542c580700c4c0d44c48040304101c0c60074629070754041d0306412200c00f070102a00c3d22180e540301c0000450703220140c8035105207940c200c0e2001c105498800c140c02074104d40000c001c0c2c1740310b6403030100200da4004141c1045076018400c4c00200181c007494203101c10800c180d02c12200480d49001d4145882e8440140803548000d0000006021940e542090034060034010f4110b03680e102507070079000d940d0324039010340003410340540c00000f8804503039018140102019a4820070b210b4595a500100368000c5a01c036081ea0505100d0901c481403098041c100d0709105407401501c0c64508075121aa101d030141140c1e0800030b4140040c0078a0b60440112600311103641c240d54505441c1d4142100d000f0f221ba0012084044009010500c10002e0b8011503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 63826567 1250 63825317 63825319
    0xc0f2b020405010e04080d0506010e0402040f150311040b0a050403140607110c0307060507050102041d0a0e06040f0305030603100c0201091a0f01061101150b0a1e120905190308010302 80
    0xb8603600c484100c40302d0706040728000d00303002e010046010804034640020f5002103040c10283c007981e42c281d0010b0140c0e003040e00f01600c144c1e00034004001518107055580c10064540c10700b04002c81c0560b4072550030340701e18003d61150100000c0e1003030f9414407038401c5070000c64000d40800d910b10400d452031901c4043c140c88000025000c0d5040c001a4600400c0040c000c00c1c00a00031b001d03041ca410f80590300754008580564440d54240b000040d00002e000c60442217200c25455080d65150118445040340c0991880441c950701100400000421149001c0b5080381c040c2003480d166554600024905001d990410001038240036200845035015000216218407803080d4065503000c50064410700001101c862111644800040007024001c42e99070140c2e50302d5034004280520166a0b02c050010b0650001519520000b0003020a41d0b002108003d1500c2c5c41c1c6404203000800c3c00010051505900101c085a5840a15000300f0004000b9415100e10401d064442c0c54142e041c0038007825402d110076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 63827817 1250 63826567 63826571
    0x1003060218210714030f0a051c0309150f0e01091212051e0405030c0d05040509070806090403050a0504030219090e030408030a0e12060a0f0b030c030c0f2b0204 70
    0xa5035111401c0e428110502c22000140a59468a22584c0140780411a001d030140521804422400c209012652465009100800701143d851140c90842031740310360148201458038001034000303041036400403110780301d094002c620b4401c40010309000f0301030b40c4210500c6610300308104042144508821202c66981d0710741841c0c101000006c5010b4400c21505040c0321165001c00ca40c8081d019500039070003a000300102c90408072083d51140c0f500581c2c0d1000d5003c00c03000f080c10000303032400d02e580d1750344401e0a10744080d45080c0300c000328a41c010b020f04010203009000c0fa003040d00d46c0c0b081040d20001c0d0380007807202d80790070301840500c8058103090081815680c1044040713080c42000004030340c1140e0440e00294540011820704a98108031041c606c5e912440f80c1c081d21000000401080340280d0204000142100c1c0d0317292583d085a1403241480c0c003a030420520803035580d0b0045421461200151a410fa102c40708000240405806080d1015141e44040304002410407212403200c000340f081e581 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 63829067 1250 63827817 63827839
    0xb010e03010b0603010504050c0c0d0309020405060406060e310f0b03030f030103140a0204020f030a0515220213150e01020c15090f1203070b160f081003060218 70
    0x1410300b41d444502450b604a1001c10041005040030743c0036940c030a041c1608541801c1d4100000c0381804900c50200340000e844128080c02c0d071400d485110b411420032076081012914200000d407400c079912600ca8424000c00b90b03444010a03103806d400f0f4504242c03010321501c05181c06400c80050945098180d91a03203421402c8050b03080002c210f6441d614800240750442e0710315a282190307000744000b6001c082c09002c103400300503110303800980100561480d1040d02c0c0c0c074000c40b01c001102d20080103002c0002c21104030001c40d4907030a80c41000301201d030780f601c0340c46054000403201078882c1c200140a0340340c4140f0001503824207980b005449031001e2f07a0303aa1400c030b840310049940309040000aa80500442c90f50021030005000800b480d22000d8059420a20050b0008403c1c03018120000015007001820304200704400c030280b40e0000300e11141022040b80420010f0610140d54602414400360f04042103440b00d0300da00040081d98892015581c0e02402d134110401a4003082c1c5243c019800030310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 63830317 1250 63829067 63829069
    0x3010f0608100e071809061a040e0a11060d06030b01080a0302070e1015170a1b022404050a080d020403030306050409050a020126040b0402100c03080604090305090607060b010e 77
    0x9101c9484080f0302c0149401401c1c2a40102c0c070b40100b102c0100500e9540107100005142400354090358156110001028100e0304180000e441c9c5040e1000040d070085992200020203400031030300d804509650072505d400640444c24000c002c9504054030108500c4000100c08500080c10700100c0d10075030036192002e50360718100d0f42903101610114049c0011003014007481040f400d01c28980d6840c2d14000b1000400031400d01d91030401030b12054860340c0c4840300d06183c120207204980034401b00f1320040441c2c10240100d032400040c0c2c0505540d404071110081020300c9002c1003201c0685030046541740d0f440e1f000061940c008d5029100844c04079051003000107043c070b0144900d200040e00103000c0d08211038960b004490a20100c00e10b400a044001c0400e0402c044401042d4422440346d00102c2907401d050041264111140ba070703842c01c02051080000000794010f40c000d0b00280240d41c049841c00e801d10b07003590795026a0100740e8004801088001c140000c1e900102070384d4200f0f807918009410b40c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 63831567 1250 63830317 63830321
    0x30d0c0c0303050d020d020c0c0a080a0803061306051008070e010c0b062b0606030c05040606140304080405041107030305010b03010b071104020c0708070e010519030303020d0b03010f060810 83
    0x4100035004210094003080402d015100400300b81d50713203040040c68282c0310640d140898005400306c182580c441c10440005041c00031000c070103807003c3e80060458158641c0e0700102440700410b91800f0703107010202010550891f401c441c010301402080400401505840200004002c440000c0055420070103c0c4155014903120140241c00c5580854255188000d02504291250315079518480b0012010514004048642e00c5144580c034081142851818044001c014980101e48140e00d000c0007080040c0c3c00502212400c10000c24158136a41c0f42d082001050107541d204942190400c0c005a0340f90b03180600038501039120b5103080010740d0301c41c1003403043d83c0024018100140420060180410445100341e83c061900500161400e0b4007041c906081030a158054000c99101d00c0c4140311980300c0004083c003601080d034051808129041080c001141c0a10018080c5540000c03030b04140c07401a00400714458002d0300070f2108804260300f080080c80d291050540c0b50280e41105240c400300c034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 63832817 1250 63831567 63831587
    0x3070305060d020904020108091c0908070f060c14010204030f0303020903150408091207120c060f0203030919020303090d080a022b14071406060109060f170601030905010203040b06030d 81
    0x582401c007503039174540c01541c4405026040c849580b09800700c6c1010440d1010b1120300024995403841034981ca0108020315010321500b00c448400790b07411040c01110b074414121004945c2108890004d200941405402403162b90805462696103020b40014150103800503d0f1802c1c09a085800d404804158550403120948009001100800001a091400c2401801003403c01c0c01520001076a4500641c004440074038120740000e000c2c0d1003041030704d40003030b404a0762100a001840c81c43c542040b078039488100c00c8450f540500640391007513055440c100207407404a140030b4103240d80176189040c03440d165008008444010f2042e00903200c2c0c0c11030070180840e0011581c02164050740c580349010346d000003110103030101e030303007018403030380e0040f8154500800189100202501107802c000000420000060f04640207012640c6400c0000b1540512100752243c0080443e0585403580030040b409040100e42c05020303503002000784018070401e8012103009480c202e045400940c44080285c41070381c0300b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 63834067 1250 63832817 63832819
    0x5030a020108190e011805071211010315090c03060e01051801120203010b0306150109060509030a0308090f0d120501091506030e0a1a0403020d02011104090e03040506030c03070305060d02 82
    0x148011595000c142c91000d2500d02c01440b010031540b2070211045d003120f00083c4c00030804a40b1a801c2814858240b050b60003505079440b0a4115018980301c0505100300d01f44170070304040e03541f00c004082d0f4400b00320701d80180c885800140044412008000c0c05040640102c0d0100d400d01d01c0001501c4c9030118941d43c08180e043d5510509070318010f1915041c1c0090701090ba019501c901000b8882ea030305101c070743e10030042d0700240e28041c030051000408080103030300801c00b41300341001100d05070f6400040c91107415038149428800341c0e0ba01c4a02904041304150003001ca88900e18126281e19081102c021410141100800c501e81e03a603aa040107030b40044000a00001c0550028031106100b40c000150350001c80c01150b0108911356203851460b12030310951280c0102080a1104041c1d0504c05002e0190311440284440f900081a4030901c0c482e9100da20324450ba620f100d8a11040140140c5008100080c03d1070b4030b030700d0030513440303102c80d44110b90300e40021b4503000000b00e107441d007030752903259030b5070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 63835317 1250 63834067 63834077
    0x1060219020d020d0f080c010c030603030c120207030203120418020a17100e0f180606010806100e0a030804150201020703020c0411090a0308040915030f02012303090303040c05030a0201 81
    0x940d5000c0c407a030140c005400341d80040b20360000d4008a10103400d1442d050b0b00c2950031503511469540040d0031100780f000c191040504015080010a80c80740d018602180c1161142410b620780308016880c140003944000d405000742c0050310fa200e02524040c000f00c0c0c12240100c1c0075030344d40c0b400200c00c92140880342c43c00301c0c034003080c80c44070314a4007992180d0040d10350420040898889100c0383c0034880c00c96403039040901c880e0400400e00c5c0026909203841c20801c7c01800e07103080200000e05040002080c2d18095200104151030b958454000101000005090b09030400d40780c0c1401c03d12a8030a010f40d05081d944d03003000d000c5039407051084a00c0c090305603015190340200720007044003a16410403d0842c1d800306101394100b42e0341c0c203403100004501c034214440d0344525018503c0240d4034400000d2102d1241950b00f0804100306850001410f03a0910f0f002c201024548400c030460200041031000280002c810071036072807800070045020b01d0107040c400e40350640c1c07081015500c020014009002035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 63836567 1250 63835317 63835363
    0x201260106031a0301110f07030909090c0504060509130b1902030405010b1503010f03030e040b03150108010b01050408070317070b010e06031002030108030d0510051002100f0c0503011a040e0112020306010602 91
    0x3d47e00c019120561103450101461a5203078101c2040e2002c40c001511200c1100d2020411860203210384001400141c0f6107403080c2c50035141220044035000c030702800500541000408003044070010010080e0886011034481c24181059030003403058081080c0108030f510070044c14071640106032412100b240c44003014071420341e40c04641c0024000c0386241c1150f1250030500031aa002d001c3d2100c0315460581c0500d0300c1d850010130b2402d6a6411070040d061040400003400101d8000c05e200003079a40008090002424054160056201e1998054900d002d0180041500c0b2840c050190040310102d040311201030003001c086040344000c1c41042443e40c4100400c141601540d084581e02540007040400c116a80b2404144424040d114070710060304001c08408010015124814202d5100c050802c07640d840120050410310060003903440151140c0e001c0c11600111404480203011513840c080c1155079a061502c2340c05030408802c92090041000119800e44001450881c070604003900705044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 63837817 1250 63836567 63836587
    0x8030a09020301150306091101080c0f07020f06040b0403060c030c0504060c02030f01020a0201140a0e060f0a0e10060302010815031e0304030c080c0109080a0305070201260106031a030111 82
    0x301440081242c255480e440042c00501182d03d84c00011800b90101295661091519144e41c5050032082c0c3d06000402d0f080c000c5424480055450504405100981e60035840c000641c03440707407004806e58804000030340030401d1952180035104a0307108039030900c00d40f40100e0055090b00c000040010001e01c003484100b103064032035011228014000b400b960802440c00d100d00382a680580030000150b034403031180744814903008001d903a0005c6102003c001c2c00c4010071103d84c843c8006800640c0c0d18080e44003045215090b5440340010340f00300c000302d1f050b42003218802005460749100580c041204a0000740040d00951258445010020081d1000c0310300352598844d00e000e03e404911440c0710501000c40001d4104000c5405001c400380140402c10111000502803019034211404d50340000078600c00103504841600e0b1480e80c2400c10103c1003c00d1000520540100600d01c928034080e03e00020b080350701980041c8071100002003000448040400340340c02c0c0d444018a58107070502c100240320103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 63839067 1250 63837817 63837821
    0x608040605060d060c08070e0307030209040305030711030c060f0f090d1103120406052208091c08070b0402090c04050a0b07020a080601150207090c08240301180b01050a0308030a 78
    0x70140c0001d040f1400225039840392011205c0c940c600c1000304c1c035104140401341c0c0d00803048000b020001c0b0000c210940c20340d404120700c0c0f000030340000d090007004400300d841980141c0014111102541c1102d440301d101c2ea07011a550032080d5040701d0607402c6100442e0404401c02c0c50180b00d07400a8008040b1401c416034102c660144840c807111007400140408004c1611302d40045028074000c0b07201282c14140030002203401c1d0003040100e5100c106245030007000407480e005803100142c00f281c4000f003072110030180360030a0780c2d049401003000340c00080480801662a0103140201c1c003c0c4c6001d615549c1d190f0021441e8400d40c011168440c104030010022410200002c202c05d074405011700704410341d988041c80c50288203802002c0311001d4100c7d4502500e904102160080c40019001d101c1040041e00181c0401707809441d40060f082c18861107883e0700b0b00190b140606410140007000184040c0c1c0400040d081640b40c110781368440c4400000d11850702d000d0410940c2e420900c040d24640710300c030310180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 63840317 1250 63839067 63839071
    0xd0b0411011b0b10230f0613090e07091d060106090807090b0f0405010b0a02010b0603060d1209080d050405010e060307091e030b15031005040b130510020c15010602070608040605 78
    0x4072000c465005c210307400318811404800082003400310100c104a020004a411036015190050405102403c03160351612003000441712588000100d801160031400d0504000b500007038280c504040f44130f8202d4031444006000144000d094032410390f201c003030407612807409118030045079014135820b00040f103c81c0c1c0710a040ca0720003841c40c0200004a4049400d80704d0992201e02d2150010811070310050b020700a03181e482c003084071800d00c2c500d05040010070b11542e41001a0210a0380b01c68004040d0041e84030b640582640022280801070003400282141d001d802414009035075404130058030704160059074000d824585401c0002800c0c4094420b0010341c80740321042d40711446100001080c2e04104160007550038401c0d0b1008580754005142c60440c246123044045407410081001003021800d010f60002d200085d02500e200003800d001d0300d0003070394040000d03002d440001c42006c0c9040001c2e0340600c859002c0140b05182e0398802d020b176110f800324800c81c0049012013002400045507580055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 63841567 1250 63840317 63840331
    0xb0a020c0c030d050901020d03020702100c060e0105040b06150f0a0f02280c05030f0a060b0402040305120304020a0602070e0a021c09034103070e0d0b0411011b0b 71
    0x3020040c1c1c44000a2401803407020307200103c2e80000d04e41c141940d041c81f0100c01480641001d5180200c9a404942d0911040e4080400c00038008029810481103400602024000384000d10807810b080c14189401c51064402d28413510440780613a40048030b080035603072069180c100460400c001c0700419200e41400c121550114098078200001c051030001003414101c0401000c0303902c880d0640343c5107a4401e00764100701d1083c0e12035000805c0700100081d11001c200c1c3d0200c40400c3c171808580100f4040d0007150070041590245800e240000c00b200c07070185100e5070007100e400c0302c500d40d50038080e0384404444c05028096440c0310005082004907130020035a400c18010b03440c0d09001c1240c0300e1002c450f48404201e0021b2040241d04d462642c007016281d10006d4402c1070090200003d90608100f01c40480704a512200f01000280089007e40e25904a5500c05001c55001010503c0d00030296503040b24125560703001a40310001c81c0d440303000711042c031400c010641c1c81040607075118a258000b0080000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 63842817 1250 63841567 63841573
    0xa0507210f0311040e1e01060509010909090210121b0822051203101d04021f0507020d020303070f120909060e060d061b0c0302010e06060603010509040f1a0601020f0a0b0a020c 77
    0xc0780303206281d001b050090045580755038079800300e880018003148960b40b000c07040500b44904500540c1c1e45d854008445441030801003200001204a4405440020710b282840030b01240c90340d414681010700c0ca4802c03051601c0c40d154941016208407901803040c1c1c000703020340e07100054195401e01500021034102403204d51070005940d450300407036102503842400d10281600a001c0c8011401d0418800c0c07019500428140c01e005d00318840103002c0d000790980a442078108036284070035074900341b013221450303500701c036182100c2901414645600e150079100400080e014840000b0030440f10721408094800c4440351174141d803203030b108124124a440070b06a4982c1c0e03840189580340320081c0e000c611182d105484461008405007006400c40d0302c45007c40400b900715000b0880d0555808003201d064980c01c03030f08810300b0303102c0d828a04c0c604075075444014120b0000b030000f861000c500901030781c410034090b801c4a6511031200a00740d200d42907201c0040c40da22050020520792007164001e052241072400c01c17 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 63844067 1250 63842817 63842851
    0x70c14030409090b06090403020c0f0f100801031407050102030702130e1f060b031005010309030c06050c070c090c0804020f1903080408060709060c06020a0507210f0311040e 76
    0x45411940035030311040b1166a42c90306034003084207003900749520071012108481c076841c050300c000c1d450396118540e1070700c075000340b4441039040e80d11040c0c03402102001524901c00c403030003c6009403040324280000c0e2072000c1d900d07034101d600040000b000e07801c0c2d0707806a003d1800d00c0700d6a8284160400030b01d04491145456010640e40c50300100003209010301e10028081240c003007030a21604840ca690042c0c400c100c001c004020140c00385d0441c0c14100c490070310f07000031099514102181c0d1400c11885c000c02041c140404e100303400011130040c1c102c0b18006c1042103e816a10307048034040340c900c40b00300303000710356418000390240c0751080e0708407020403014142c1480c001c0410181450090716400c00c07030310854007090501455100300305059100ea09414041c950740c4c04d00c00c002d018000741d000001c1009030000741c1400d216204005031041e0b6a4031a11030080c01549440304035942c81d0308190140050f030411822445c2c3c42c803e000d2800020500405246414107080340982e15a500520b035005a011400f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 63845317 1250 63844067 63844103
    0x60902061207120c020705010806100302131e12020d0201030e0c1201090c06020109020303031303090509090a0b0601050406051606090503120f010602030f0a050d060f120302120f03070c 81
    0x4529480341c1c0341607030f80085210b101020340044600c890b001d4411036104110512040c0d801400b0507800400c21600068100b140c240304901030300c84e1040001d81d6045000d800101143d00007181c0007e00300780540c0f0f002240c1c07900d45408101c1546100650301428040c0b0050240d40030b9481003140d5410001911500c0031040007142180c640f80c02003006a03951107050000b802a01e05000005c1c003128030007440595000e4001036501e000127012010f01c1e445800c0140308160184003003900800d00506240f4040c0b410615807234903424a01001e07100703081100d00080b10703984034108403401d860041d1180f41c145a00b0318400c5480c0100704038111903055446140c8004180c00700007a0000f002d1084071304405103864002407041d440c1c180d0100701990302c188040d09901441d282076441048052404940b52610400c0c0d0901a00c81503010001c90080600c021588406c40b00b090b04065001e0740071a041e2175007100c03119580703215500841c140580180041007002d445110a80c511034081e0006001118100d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 63846567 1250 63845317 63845347
    0x207050a0b0715150e130c03030c030f0915120f0609060f080106050102100504021801080102032e050402090d08030f060907020606031e100603050f1207050a06090206 73
    0x500904032a40010600b501000260300001031400055981070000e86501400c0c101048428019a0301c0a401c5178002040c5224040c000c0031516006901c5c10030302aa40e0a0107884111803040c10f5000175241c00f50b0a00ca140130301038600840d883c080e0b5001d07440f5581e85d0110340000000c0a40030034242c42d13032500c0b50f19130660b000716000b8158081001503014940040c2d0015890140d0103081e050341051810402603802143c0d00340c044803075500100b400d50b141e1001480c1d032041b90000a0014001400104202105501851040800641840748601c414107020706001000709075600c04070201c3c1b020f210030300b056005000010406402449126038a90340c40b41b258200301d40d00454004000301b00025446d0040089402c00c5180c00078245504004011a407503085420104080d40050310581c40c81d20000c00c01d035202d11200d22000c0040f103860380782c050303201c04801c41034881c54441c000003070040d800340034215100035a00800401c540403096803000301905080340b003681d1100060068a500318900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 63847817 1250 63846567 63846569
    0x70b03090c0a080601121e0807060b040c0e0d02130e03040605090a0b0702010c020d0c0503150603010506190e06040f02040605070515060a030308060303251103030703050406050a0207050a 82
    0x4400740181c41d110000b4096810080d6003c075030190702c403c00411040740d0800300d203111150000070a482d4030701c00004030310740041c42e00401807043d0300000e101011b010039a4410502e101c41204d092003482c01d441d40c122103001a40340915480614000303107000502d03040202480d1321064600125500d10058000c60071134005030701c0040462000a2501258503200c0000d0340581072007100d6500302199038000030302c12102d550300207000e5100c4043c00818440710740300400c000d000081c200c4090200000b04004944400d40e01240290309003030209115261110a41a01911840c10242403520b0301d02d240c40305940182c9a250003e035509082000350100307000a2010305819201c080d8be4801c07500d0220f01c0c10a542c000030f004001c1c03c070180302e41d41c0c4d01e5203072400440b07416151102d06904d900700064110301c100c0108444803400b01e145280b200d12245024401d00380240d261682c010b80707100905440c2c1c41400d10007000244104024030106000d1806050414050710440c0c1001d0b8403400450300d02c540c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 63848923 1106 63847817 63847831
    0x3080901090504060b070c14150d06030b07081f03050d21050a06230a0501030c0e031e0c030109020306040b1e07030203070e090402031c02070b03 64
    0x4a14031400c082c00004004008056480400d00a0380c0c0c894a02210103581c82c040000303078001c180310318160b03d180207898944501c0c0c0d02c200820782c030b51100340000e0603599549004000300d10364000700d602c5240359031682200d90170310174480d010b0400303a928040442c0d4242001407002400c042080200c003501d9040803009554400b40c484111102040c40c444141c0c0b618080101c0401990030100488010005000522901c0301d01020300030122058141c21241245040219510079404209003450300d140480302240c4510010742050703464500300b00e80c041084e5a00320317890000c0c0100c50483e00c00710001c00a1020030350209071500d20085c4041c2101201c080084c105490240400340400e1a0f5100d10fa058a0b04241c05070003500155525400222203000011180c00d00162260041d60010001c00342c0607211460055043d00c1c0c183c440d0b0442c001c07440000798005c5008042c50050030 = true := by decide +kernel

theorem cover : BRFrame.Cov 63669067 63848923 := by
  have h0 := BRFrame.cov_init 63669067
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63669067 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 63669067 ≤ n) (h2 : n < 63848923) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
