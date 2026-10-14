-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:26:43.152581+00:00
-- url     : https://prove2.me/submissions/49776c54-b267-4f62-a0b5-6826c9cec99b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 240107913 ≤ n < 240287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 240109163 1250 240107913 240107941
    0xd0b04030f18090506060d090b0f1b09130b04050c0405031216030c060b092805061c05070503030c0f06071404090903022103071d06030403081015030203 67
    0x9a00240b10140e41000201003040c1d00c600211100c83c440480c00f95240400728040c0e0284419142e1481c1c107098212040141200000c0d10560003030042c80b001c1c0e0341303003410621070700041500d4609a010412091200381400748402501c1110881d000c90b920030004017240459000b25500303880410301180c2400140b4040c8103140d902144024221f08001441041242100c1d5a05004050000c11900d500403c1443d8101e02d801e04801000ca2a240c0350001050b5a84200000c1c50494002d0700070004031003031428402d95005000140c2903090740004443c2c00940c58180020641b4248109100000c040d0307010001001e030380c48000082c210b032404441400386400400350a40052002d00c648400300720203a40181c0b01110701140000c81d241035142420b07070070000031400d500c0c030040038030004208119940006501540d10740e9114207044030400300d04a81250100f810a50003581080460042841842450703003103140d81000754901c0b030b56400f00361040b05003200450042a0048204603c06510b030360 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 240110413 1250 240109163 240109187
    0x1050903060117010b0109050a210b0f0a0605030a0308040201111002030a020d06170307080a120f0e06161e021507020c0f09041a100503030414030601060e090a090201030207020d0b0403 81
    0x20407900d818107000010f40c070389c4414000d40804120011601512215210581d80060b0304410080100c1c02c0011880c56a1316040341c0d0215031a003041c0380001d09040008070001e510b5015540e41d10340743c075103500448101744001800031441c41501d2004200003580e100450080761040c200507901c9aa50300150241c40150f0710a000c012a188580d4480860100850301440d502214550303550004003019a418440c0c0c990213001c01c1cac50201c02446004051740074245d000341c1c40040306d000da034802c2c80c0c01e0404642031011400103003442070210750081440c42c070f038058031000e4019200d000361401281032045104854910040c0d0203410402c0ba01c1c2003051080c03803903120948580041780303000d88400311200541a001c0310071403803180000396408000c4041358080c01000301526561a0f8800100b0500541c04060512900481000003040e40c0500c298503006003000e00304141a54401c0b900800400490f80c099042c990200403420060340c1d81d01450039000e10404040c020350429040042002102c1c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 240111663 1250 240110413 240110417
    0x25020a060b0d02060703080921030703241a070512042102100507050a02060412061401121209050a090501090c02010509061f080f010203090607140f030601050903060117010b01 77
    0x708101003d83c4035003080b250140d4250034258855260074003028a00400104188040c15000c0c0c40b400314180108002c50180032141e40070300191a901c4400703050300221007d02640e003000d0303070810024800b0300301821860100c045111420200561a81801c00500c20380c01d62030745500040038805054205507901004e01070040c88000340949a001c02c009195110024080c040e01140020400c542006502081c40e0702825143e100c6039180b0a03c21804a000c404445141c02c0450000042074101020350498000c11841850707102176484482030070403811040d204210b001c1e034012440d07440e8209030000900422800080720b42c94100460201c40889910800710390400080c445482c00000701160480c03600440c505045407003183c40e904c0c041c029130041529010314aa80300d802d02044d0b001c4c500c82c0c030203c1d040d60010342d00d40038100d440c001c407043c405900c00400d0101141c031402038809183d000710306060182c5042d4030040024603081090b400a03c40880021414015030428003811100003028 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 240112913 1250 240111663 240111679
    0x2010b03160f090923010507020c090f07030908040e010b0712020a03090302060901030e060a02070b060105040320010c140a20061c02090d030801240806010825020a060b 74
    0xc02001407102c0d0481c03041145141d1298513040a02809464004882c4106080780881409009659000c0c0000300d8255000d80190300590340c41d81812200c0c58419004c808000c1c0003503446100640040c0303404071003603d026400384000304400b4005c540403406814070303404143d01d61850f454200c01e001070f00c000d04011508603880050010381c100701e0040940b40d048884640340c058034001200285000c110303400310b41c401d400c188101038100345c1c0200b4440b80145d04003916076407248015a194412440010003070015500951040c0c4081090b01d0150390051410300f801c05265107508081c1490701c03403040391a41064907464100b001d21410903111800c4511140d50303040400b40080c02c140a04088507140c205c1d242d007000000c1c8c5655040b524268401092468050317442c0c100101413034006d0140030018981e08408060b041403010031403050280f10b95070b0030715654a04004565003100900300103c0c040398070b05003400340c07558200308440840b9207034000c05c540106800c140d42a01c240d1980d49000b0440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 240114163 1250 240112913 240112919
    0x60504050105182419020105010501020d03051b03070503100e060f041e05010305030a09060c0803040f050a02030f01020d05010b1305091e040b0406150807061809060602010b0316 78
    0xc070040e1910055007803060159030400c0b0f0085000319209280d0f21180703001c80381e90f9603020480100a003512102102c0c03032090f1612290400d9080307420a02919002d64800e00381c1d03502075131003500a01d80c0320414540301039280905891910b000c0e0801d80b040d0307005c00d10120401283c10307035a0381008000c0c0f00258080540d81401c0c40031811405180602074010f64940d8008458071035249002050628100d104000c0d66940c2d041c280d45941018040d14000f68910800060191050765089070303143e04005864a10380310340d82c600b1903030300c01c0803402c46007801140604009079030180b00682140003404009a664507a8011201c1154016040603414000c1404443c1210701c0360040072040d00d038207807004006034440d8600070090f0216041d4406c0100b4410313007080100b048541c50180654490b8406000449000c43c1000750840315000e000c5543d40074100400c00503104004206110a10740e07030b46071a650322010201d027510000c1d0481c80160f0744901c1548172904041110100c07000348006c15664980c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 240115413 1250 240114163 240114167
    0x1201050c090d05160306020a080a14010e090c1003020307020d091d0c04090908130918021c08040f0305070b040810150e04030905150a02030708070f020904050a0c0605040501 76
    0x6001819014441d200c1001c003c0000030403200400302c01040311000301075500c0c43d104000e5030141600000180055010501240c03850040001103c01620800c8450703080141a02c404a4010b01c482541d10454484582e15115403072002d01909030344d900941d80e440c00c900064038141841d42c488040000c0d0100070032034115003030361612544125901d81819900c42007018414ac0c02141c202002552802d03152600700100000107008020300039900d2440180e50ba500d0004540c402c0c07200c1c1922040d06c400d824010b160003d41c49185a03011000d000c140301050b2640301064000d508514042c1c0300f110000c2c01030103000c1045038020811201e07a03620b803038246400140c80743d2000040d5001c1580f2102c80d440d0384041c8000c3d0720094800c1c0119100f151619050090000b402031003001c1c01841c0e40c880c031245291a40d001c9401082513900218981030403a030310883c86901c89078099038106048a01c3c0c10059481e900401c0c086c1d40500010711802d9950308000080024943c000000e103c01000204080d0b6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 240116663 1250 240115413 240115417
    0x4060f0e1008091e060a0f06030c06022b17070201021c060e01090b01020d030e0307020d030e0f06180d1401050106021c080f180f010e0d02010f060b12040602090307060503061201050c 80
    0x42c68070102003004035040024401501e02274000030004004207401081c00b5a0026100c6051100c3c40c82c0840700040580c1849a280c0007100c820000441d88006006401440740c41d045d04486c5600c001441d294840660400002d04170406040c902d40b112801c21840c5007520303215001d409030480030020142d50300c001070760703820b403454a1006041d00da0b074a8194040c024400d03610003580141110094608500c7c000f0521200072003840e10890f1410025070b503600301641030340c1c072441c0c1c100c207035859400e03840301048804008468200c54082a0490b400005031080c000d8a0082c07031190000d0100c1090040e03540e10070074505114100b00424a0108629500008005174000c01240403003201c580c048901e4500740441020351071815070030040c070251103140002e0b2004105400e0350081054448490200b400d5070028440c1c0c2c48681014000d80751022100003116420500c82c4c500146400642c102003410288241e000c0000b09801000304012824061710307142801da400e00082117a8a010280f042142c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 240117913 1250 240116663 240116671
    0x3071406071209030609121b051f0e0a2117060607030e18060307050402041802090d0c14120607090b0a052107170c04060f0e1008091e06 60
    0x1c002e80c1c1c082c0502590051042c0405150004401e2080d07a00d903040c604002054a0b000c10005101605046500c40541c2d080d0045658010301a124001001c00c01e041500206541801a40c0d0b03510003038207000c2400c2102c0c1d0010f6101321101da8003d200c051142505080b100250414041200504140406100300650b8808001c8620f951202c801d802d0854490140d403c50796040541c41c400f040c2980f49145407180708000440c04c5450160304c0d582030000740d004d1071050740c40401c10780844c450b250b81290060080880c3c003504074100a103454903440b80280560340070b134a0000c1d200f03114160b141840d84400d50501c070040024013140c00e2041d40240303c81a90310501800301404910426050b11600403680300e41c142c9105881003202e529003003001c080c001e44404011490064508000030b1324032000d14422000500d400741800d10707246090f00c10300010030308001040201c1d8541c1000f65a89030040309182010f540b0a8164236280c8000d91600e190240c141303200e90b680401210500d440065060380c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 240119163 1250 240117913 240117923
    0x180105030406020d0f050108010b030f03030a05090a0210030212100e0f040809130203060f03010c0f050a090e07030902031b060a0302071109070c050c0109180218130204050307140607 80
    0x169a0311802e01030001d010700c0c0a081d03e0f06081a000f10f0b5a1502c603003019060f51540c1e0001c001c4030002e4020036940b030308500c0019859800070b1000400c190065403209900440c450195080103841e58001040d10350040411401710340c6c0860883d60140825100c142c2c07050b10320341c810f03429904010b065044607a0042030450b400d44800005000c1082450030b0316112440500850350b804180642d00d00a904120380c221701582c0e45180c181050725050190880b12141c2c0d4444620301f541380c4804503a990302407844d060a01103803a00c0020703020403d440701c2d0710486051381c0000c1c0b9406103104043c186411182050000b248020698401d48d0b01c0c4001c9030301d00c000d5401c005903111001c0c40c088011448020b00941d0003640c6504204426410011040009200700c0c1903a0640055000544040b0700c0f038050409251000d0804a0b9042c1d82c923401400045407003103040103401c51034400225142da20f5108503808a801003000c004c00c0c141008042d019019115070460408103c402080b0540244800500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 240120413 1250 240119163 240119167
    0x30301030318060507060c021f024902093006010e150d020a06230f0403020f04020702190807090501180c12020403060212090307170d110c150c180105 66
    0x700c214001c016100c10070481c0202741d407010022030f5001c00290030605401019803c0403480c6440d16801c0303c00e80950340310303585994403840c0711202075003040d0320030b540000e140d81d41c00c024a481550f14403080e4208202280c860318040e4140307000c3d007680081e0368411071500f94002e200601070a0032185a640c1d001b001200440c0c0300271803400020f090f41000001c00782d0001c20300c901c04619107074040b200300da4100000c020822100800e540358541c0c0d125078001c403031261303400b030005000520340904850350082000700003500b8040250002032000e11170840007240b181c034238842000380302c4090100000400e500c8804208030b40c03420f041c801640300c119244611960782d40038110340042c0110b000101c160b0003603800b19182e54485c41c182c4001c2d406180314203031941d4007200207449040c00008031944035074071014403d070090154411009642048101512060312001510042d04500001d8031100380004000e000c5586100c2c0e00804c1c401014104074a2840108080c0b801c0301c0c00500c2e8103016140c01c0c40c1140d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 240121663 1250 240120413 240120431
    0x11100c030e13060806071e0c0b070c152a020606060f0408030a080108010b0a0602030a0c05030c031c060909050a030c061419050906070e130605090903030103031806050706 75
    0x146002d11010440b0b240619002c40800d03d2840007078603510981160b00e403100c0c22207400ca040154035440e1000c440000c1e20205100001400105086401c0010340c00c00c09409207003a0b90720487c10031051050103001d90394400c55499403004c050b00c2081d01e1440c0781510038208044c032000b9141c10340244058000d40c8005001d032206c490540c03c031360040640805490f191040100c0c010058202031280240f19130904902101c0717440d00c0c0d00903504a644903001507190801604050740d52a510f140305907018003041c031100320b5517130703051000b0080710307260907a0465200e00c8141d5000c00c0301d1300381d004a41d2040c58003000e00e000501c000307411480d02d605818105030f24045454a60040c2002200c04040301e440300c014000c034056051007954880b01858020300c01590340303220711582d071001140c007080000d41517402c6031114105045050185110700310f01180d507546440100d003050006490040107640000010820b15a110f210620952a6450111901c0b0b103010b0005140b80541d040c050542d0b41d488000d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 240122913 1250 240121663 240121669
    0x2040501061115190c021b030321040c0306020408150c040609061d030706090303030f050603030a0309080d0228022e0e0a030206100503010513030809070b030a050411100c030e 77
    0x1132004215841c1d0705002840504000075252804a0001d00c0c0d5181009503109051402002365910f04480c0707000380c4110360700d81205d411055006841903a584144041c0403000c100c03c0c3c00144060060a00145051503130344150101e080c03030081040101040502041c40340562150b540c1c000c4038010300e40305203640c01c03891550800b2142c0c010320b02d80c140308a81b0300046041c2c03c2114a0200d034083d817000c2054600c584100b0701aa001110001d9140d002003091a520074082d620050030075002d0b01415050a201c0c0b440300040344e00c45403c2c610300c0408a1026040c056210000f01e2454a007840035000e0b95031f00500d202c008901104401607003502d113118588600344e00e9130001060802c5801110789801d12030502a445000a07109084401e104040c08074080c2414021103005461021400c101c0d09002c0d103044a03104805030081003d03000e11200001d5050040c0040c50040b124401c0004144c1080d15020308042c1c0258843da020b80810b031810b1050300c1c1c00040c186610758150501c51a01c0e4a49800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 240124163 1250 240122913 240122941
    0x30109080f0f0c0d0c030e090609011a070611030105030c0d051209120a030f030606021203160203092806030903051b010b13090c1a0711031606030902040501061115 72
    0x3d1074010712580c05500400c1e94840c1803950042d0180e01d400744200311030014054000e0045138440e81200c1d0500042000c0c0400c1c00c0c0e10000c4d420f00c20900707802d140071a904d03001038400710582d8023909000480148010310f0240403213070f445507048135403000421944d5161615070030610343c1c4002039000404c0710032864580072218980380b004c180a6803404c03030f138503c1c01410003042121010b0000b450b1682c0031a0440c0005072030131074440b410b00e41e24111b03076401c4000100e842207038042c0303801c500044c800032400340c403803100991310100565481a0f02040e09100d2060504142e4403160030507013410340c8100403179040780c11201c0200300c91442017606c1c41c030180340c54003420504200d55042098066540d801c4407603a40b00050840c030400100003225642c0b10b04202c0d03207140440e560350294007040b5403000196192486100b403040501550101401060180d01d50071b820380c04640442d4960210208500c0c203485294058465400c064072103103150444156100035003500c048510040002141c100c60503021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 240125413 1250 240124163 240124177
    0x708150c040f03062003060d062f040e0a0b0105190e030601060302090f0306040201080610030b0607080d0e010e03090d0305041a0a090b180f0612010b18030109080f0f 73
    0x5030044500d03a0703e18010b8001d000e00c0008294086105c0c0410522045c401e04032401004010400f200260031501c071400140036030041d103c90398007443c0d5803013020101c11441001280759940030f681c0b500e02d000b044480c1d000000744540381c00e51400c101c400302030307801005940c03203c142203184410080f011501514484200080c1681c540310360800010001d80c16001443c2207201652061220302d02a400c0c140c0d0f444003600c0007030208038a00001466070802186201201c0c10525011410a1900300415280e41c8116001d40d454140062b000c000c162075030088600500d5550000c004508074001c00d581c40740181240c05109004413085042818494030a8401400048504147c12000030013498681d0b0f0102c4040000f05000340b8002a41d07003c404140d442480701850b0011082c00c01e54100448406d002042c08c0c1e120f5002d2100382003280e48962080d010304201035502d030b921610040c82d8103204d1400850706110b130381014164000a0b501c40241c07801344074600442516106a65400c00070342c00f40c3c0c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 240126663 1250 240125413 240125429
    0xc0b09031201080601320f031c021e0a0c03080307030209040608070806010501020a0b0f060604080a0c051203040b0d0e19080a0f0302040e160513030507170708150c04 73
    0x200001c10382e00b030301140c164100d0704944004010094075401c10300c15203100c000c03400030b0700c0190008441c0038201100d443c40303500070040a440e400027241c0b0814040194a1180740300603400809480210710410b400280301e17150780e000500484040350354842010b181808014150703540030011600310f078020b8040c0c9d040503400800600c51580c9450040d951a01c0c24030a100e200d1081100000b100e5002240c92044150005003860503581d171415040c8140e98098080c81d0007800030040014052418071218580500c5900f07800f468034a0300d400c1103040401010580e0094104020401c039011185040703d01c2c441c8098000704c0c2c50b54205654504200c4410410f0551f1411340b01c0b110200030101c40201070412441d2038050b8040c4000c2d800b1000c07802a07010390300f840710b400d0001c00d010b030200340c04010b42c1103400c0c640140343c110010781940f1003d109a0085a4542c0900030520040460203140f54160300b008000302045442c10200c6a50b030f07079601d84011007242484012816007070003202100c021b41241 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 240127913 1250 240126663 240126697
    0x1501030c1832060f1305060a0302120a0e0a02040e010e03030405300d1a0a0803070209010504150608040f0210120515030c060d021606020406020d050403030c0b0903 72
    0xb0903140762400289821042e0203016204000c681c06800d00100c22241c001900490a00071181303070881e075507448a101c100075004207003070005860340ca020041031101d141e5600580c46005100540e90b00440181c2015445800c00359103a07a4903070002281140107030122070100c3d41c550038241c00f0340100551070340b4100902000041205000d400640d404088150318100a03692034407211021190705800d20301349200a0801c00c011211405400500440c0510b040e01d491082c50711002441007080d5a11160003a0000b040000551502c030601ca0f00505040da402d000c04810382001741011002c07401080c081c41050b6001c502400703404101c0c0f0b8421b03540606411540e03020041d0262916a03121b1038180c2090400b00040c1e034080c402c0701c070804018030240003420030440b02801c10599400103a0214021075003480860381040e46001c0454000340103080041e80d440c20201c0003030610300c0700003500c07007400420441000000e034070146070220940c00c508200f01c20b84030888140d0a40c45844100e030301c3c0c9020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 240129163 1250 240127913 240127919
    0x40f090605040311070b04032003010504030e0a120206371701080a02010f0e01030b1806010305011e120213091119140909030c07060807080f1501030c18 67
    0x10541c0041d019a00985a06840d1035060079040d6454801d0300400e403607050705200400000b044101e039001c0410100c1201c0068101c1740000c0f07030849004807800d400203081b41c01c4520709401e103000d101002d0443c204105840030816000301d42d0320310420343c1c0b840007081d149451080782c0001d4015221401200000380b848101e11900060001501140348440c3c0c007410000040c40200008261700e1a41d4180c41c2c00d803c0800302c0300161451000b0315000340c1896114005c00950b031743c0780010700e4007940c180d0700d94001b80c0c00d040d4001404c0700e0050708100d401c8100c0c1e032050713180000e081a200d0101c441c001200e01582c20107101190481c586107110000381810004e220041104000032264030b071209444100000c403072001041e00b8000c0621138040b580300d601400543d14201208619404043c4004407840c021a034880c0619220003540300c440065000c13002e000109911130465904401c0c1644c11300700d2414603d401610046904c030b40c0034185030f0b0320380010900c2801164200d1003084100c0b010210307244c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 240130413 1250 240129163 240129173
    0x115140102280b0601080105180405010e0703051b101704081c0905011a18040521040602012d0c17100303030b030303010812030a09060204060e01021e1209040f09 71
    0x21002c6040b10100407a0380001d0b1154842c00d010b81c125600281940c0350801042500c4007005005802501c140d501d072148a040c02d00100701709001144168020a118425059141462a02e1500061007001c84684001403554407206c01414020300d40d1207a005a02d45241403580c0e44078020064500078000800c40c1e80703c1207107501000009020704000c0c4402d4036214000e03806285009001c80c3d1000451054001081414030000d81c0325103d203080318030f011403485100e0fa20003401c1c0301c02e0741c5218002800788130480d42800383c2e6207051a80102d10300314080031600300d0850180034030b442114580c0c078040401c40c2d80c82040410081d0304101c0e90382440d41081e4140c01d5014031180003c1d4007180c180355000245040020489041b101100040c021016070029401c200394805808030309003903190790303081021401500c01007008000548030032101d00c000da00017908000d500141c410341d010240e406100c80c800c1c0805e464141c0503030075819561b100c6030003000400400100e21040d18480c608003005003080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 240131663 1250 240130413 240130483
    0x10b03160302030d0207030201080a0b01030f1803140901080a0c0e120106080c011704060b03100c03050106090e0f0604020903160f1409011a0a05040320040e0115140102 74
    0x20b070094090b50035003100e401043c6c2c1c2d40c01c036601c4020300041c500000100010460b50042182d410140346c041450044041e00320207560011010304860706d82d681c0e0003070400d03410000d0f80d0000100f8040c03250034072101d18000f0303002000080c03151a46548451b8100080b40c03080c0b80304e2400003c0207008409100081c030b6094024403c5d40a940544d1007448109495980200310844010740d02412400403503683e80d480c1c80240c80710b0064250584034881071900c560780507000c0c40300003041d185c1e0002500d40c03620000504190040d840152442a5182417090400011101c9940040b0503038003d66031300c680001203403601620943c140c00b2100da840380844c0304140404080c0c1200d0109500c0c021000c0c0900800010f00700a04c43c03c0941200d0040c440d0007500048007401c0d030140903042481c00c0603540e44071581072898030020b0300c04022602080000c14541413088075001010708008000751031b003040130f4030456242401800948410b26241181580c400c00a00502c0080c00003038a520650411401c0220 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 240132913 1250 240131663 240131669
    0x506240603190501081f0209030115140a2c060a1205100c0e061206040605130e010f06050102120c210703020c03010b010507020d171b07051e0909010b0316 68
    0x100d07003843e0000440410004400860700e281d80b45001c608042e90b948407000303600c44404281c00d55210904415801000340c5804000c140b450300040c4e103040b0030010131014000a801c408000805642c0303071650b0300c02c009803000c282e4a50791181c510580315640050400855980014209840f00351080c04116010500e1382c1e8030b109064040c0301001608030255482c41c808003059800200500000d0000341300100c050750000006003000580c00c4e210300114840c0d08400400708034072925503000742003100302442018000401c0c000200002ea00b4680000d417140e021307080707910f8110030210380040e0825040c404030380c81c0480407007a13410800740128620702a41010502fa009402404222909820107004400200e60169280c030700c2c103d481c0e4200500b11040d0002554203a0b4049106c2d822500c8a80080c44140681c50300e0103010303400c8800480c0b91200d01d80110380918548120580308054890305c0c01030100c000c5030902d00640d1101c0d090742c0185aa091050b9141c420ba449410314214061694420303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 240134163 1250 240132913 240132961
    0x90506010e0603120a090b121f080d03091415090d0c030807080903070f0c14150d0b13060311092503020a1209150507020a0506240603 59
    0x426a07880c220400c1c158001c44019800d80c00100002500c0f00e074010003004200350604003215000d07143d40d024111030700002c540d0b9640300108014003561450303180740103400045403c5094205800e0120321910390085441c404241601d51800c0f50070030424024081a1030201400c0701c0c1c8001c2c048401c1c0a42c030b101a80c4203400d80c040d60701e0070100e441c4212182e580083e0152521205900c88000803910401d0040c8652080c0c04240503074800107801c205182d9617180a00c10120440d810800003050781c0314013031020b61066000c1100034596103004000d43d240340c140c01c44006040d10407007005c19030f00c1280000c03141d20145001c10100401820321903002000005450142c03041e17a82e94220b0701810811440c0c4040c034220180e42d150168440e03001070130004000c1c03900042c02c0320881d403e003064908030841160240c0d40b0781e010f02c9a419151141319485000c0380300800ca4003082d83c49494540300302030b181c51404c040300440201c010040c40b0b00d640d440b2801418075903880ca81203060304890300c010800360f80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 240135413 1250 240134163 240134173
    0x90501060311100203041e051012050604140604150b03010e07080a33150c05010c030603080403031101110a02030706200406050c0f0102031006020c0102011e0e01060e09010905 77
    0x910b0741003110a40c100c2d5a219001540303000d0803e070705102c0051081d0301203107910380c1020b00070580d500d80608155402250740c0f200004130102e0800e640680ea03000f403486024601e8040e619072070415000700c403500320b0b10a803000a054202d481c01c20840103c0b9400600c43c020000000262000000f609140b041c415503441c000242c86101e104e4040e03c0c829960b06540c0c45100e001210080340040207010b0800f00b10a069115541d540d1059011960040c00350b0045101099840c1c1030220a02507010040441e1804111050440c1d48101150045000160810006030410308618000758458101103107180045134541c1d450005c000d540740d00404045860398280b000c100400074880b0f440440044400622a0602d414040101c4094004026618581c81944243e512820742880154059444a030301281030a041840181c40c00c0c80705c4080d581168545458401d0070880046001520035007904003007020320b00003185031702502803608004024488007091065404055008042061150382070352 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 240136663 1250 240135413 240135443
    0x2a12061504020310050105212701060e010b130305011b0e0a0501021b0d0c031b240c02010e030114010512030c030f03040512162f041e0905010603 64
    0x20090f8001031360480990301d81440c3c18002c66000c0c602030301d11084a22900040b01003924110749103004195002c0b003001e03c3c0006012261400c4031080c140302c00070707a0020b001d500e1609441c0912900d0500c03c07920702e0f42002c0303001841c031098042c0103c025500407000703012034070594643c04412040d0321210804140c0c5001039a09600740341c01f82d0800c54505030043c10079583c5103082e00502c1c400c1c10f0300d05613000d61002083c0d030010300e91103515006540540040041001503000c3c2d080d09030156009100c0041c8407a0890b05c80c1e80c18401c001214580c1e0b4607110709001018401a61006050300800b603243d4200902c045130200c940b03000d036048806c1180d001044c211030044944c0c4a214a107a50b18040d00100269101064002e0080d604a032061048400380e03602d80c0040c072901d4005a0a0040c8644618030b07001c10b104000c0c0c2e00034030198191000c1130344407100c0a08511200703603040840740900d4031080f10758890800007a41110914001d02d05100c9180d4503e031880c000c14441c0400c480071a06085a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 240137913 1250 240136663 240136669
    0xe09031c021c23070309020d0b07021e0d0c03030e0d0e010329040504140f0102031e06010e040903020f030403110301060e0402011d1f020309040501172a120615 70
    0x30300340038030940700c101c2a082c03120200d180c3e103c0180b25005041c1c503600580016180d1240001055014503a502d00c10f0170304c0d400c002e041012103105404064030038510f505100401140040348440c0310f003400c100c60034180c0b0302900640706103c0d940a581c0910844850030a412024050584209990403c05030900b1030340000c260704600424505000800e80a00c40384c03c055002c103070024024845040724009601c00c0a203002e28000465980365004020701034003e2030103840884a40c039200c8080b0f554a002e100080610004800e16482189c0301e8145a05040c000e002400c200d40c0103c09883d0741d01d480781004480f926680354042d000e0342c81e06800140d0710402c0d04055004035030595070001d42589030b0340a0400c0203500d49010790b00c401d091421001068035034180541e200b14075005152654180000c01c8200c0e44140c0c031032103640040110354400e02c7c802017050300d2040084810040d020903a81007206070f00180342d582c4c5070800400340c4401003500c80083c0f02441424054400355000c40103c0038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 240139163 1250 240137913 240137921
    0x140108010515150919061206051305040c05090c0a080c032505040506030a090605090606010e0112090210020f120403050a020d0807020d12030606180e09031c021c 71
    0x500d40c50b050038001c00c074920700100c40000a452401e15141814250400940311003410345221210500184003005401c0d008900041032005916041000b64600004141e0402800111201244e5504009010090b81500c2c403809804060079548040c03a040b241d00c01e040e4006817407800498501000150103106103030849120b5002c1450420618411000c1d00c2d20144110200c5018000c05101c0442c070340c0c46c1c500c00307140f0031807038003078041442c4601d41828000c943c409018200c854225204100983e40c000504000b4100c0a00e00200700108914142c0001e18254078002d60116101c3c403c20160f5500190040340035004600341d9514200c003240c0c0409611852000a0480c0c0107800b500016182030172403290380764002d00c03460f45840300c180c1c0021000120a181181c40c060058020751032107505101e10070260160b42442c40f24892598445444403149200300c404081140c800102c055a080c020b0368107030490440d01500048903200003c02a40044000f446d400456400440100312140a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 240140413 1250 240139163 240139171
    0x2061306081f230109030b0c041502011a0f04020403020a03050a020415120602030a0e010219080901090b010e09070308160615050607150e1002040f0b070203031207020109151401080105 81
    0xc607041075010f0020181091030408400b43e05202042000001144454114620601080014030741e51400c101c14400c4a8402c012000216890952000040c1b03064035108050b4003070489200c443c22139100c0000d006440755070402500080701000002c10440c00140451030301c0d108a4003801241003445202c0c00b03541c441c0c860b00034501c040319441000700f20a075000715008601e029000c0ba64005100c40903080e07a1264000030300c0d11110300d0081050360390102c0f101e600410302c14000c2c8202000713034507034900d44071043c0a0b101145e444c0e840400c0801504000c0580290b501c0056030303445014060f20100c40c2c2000e55410346441d42400356181201680c4043c0c00150340c4000c003c54100386103501c95540300e10312705440060741541d0f10700e01c11240c481003046034072541c4900b03400f6a5860508002d40030607a4603a01441c0c0e42c280c1444110010307600030040d103036500b010300c03800001a07442c0c80c0200d0140c02404400741c403d0f1030101e40e1800c00142d80e005441d00040188060f110307642e0304c0300e64a00300c6604071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 240141663 1250 240140413 240140429
    0x20f040516050c0304150c0203011413080d02041d22022b020307170f0309060403080715051302091608010501030c110102040f170102090901050d02061306081f 70
    0x1003000103018000c40107491141d03c404102c82c1031540354550340455110110008010607040000b4508500d42400750580500b446034030030350b00d401c3c09048078034a400c05610041007800081034201c2e0b08541c56055400500015903071140c0d61141c81c034400300c14141600c801d8442d10042000040d100c0340e03a030004000c143c0c080d00110309241c050b160403003c9c0102d51061201d012180b50448003594082040704040d00c00c140401d0180514003080501d001405240c0d07048581091010320385554401c81620200e941040201d6654481440c040e601140c2e00d80a001040b4948000d01407481036141d00703050061306c2519242856241c20711900051a1034a100d000003418410062142e54825004030383c51021500b0a0076680908071b0129099800039044010191903550301000210034541031014011580c4000b14501200100400e010078414040c3e1401131000a401104546600c02114a00c6213070040094a141d15010004d0181e002510701c21003e1542d45601c0d4100d8002d15000c1c01154081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 240142913 1250 240141663 240141691
    0x60b420318070e07170405011508011b090b070b0711030304030201020405042d020a03060302030a1203050c0703020607140d0905070f0f0b030103060b01021e1606030204230319030309020f0405 84
    0x80c0030041700f844000c00844465403505900c404221580e90180060000c0b1000810010000150041004202640c00f020030501c002d0400040501c0c00c2120300751508030601056903504c001041e150000d0590154030a48400410401030540c194050820b44504882c2809011400c070311181c0c40c240c001c00d540030307020300c10180310035401c015500405181066080100d0029941c2d00040c4c14610b407504252110807601c03940080c019498407855600c0764107500800d0801c0504d480007590355074010603103020f00c90035180c040d105031a03c0702958030303041c00c0703141c00e0100d8036052406984030009441803103041c1c168203101060980f9001000015100c001c00e40505517840e40d180c60000d410a4103046041d405401c3c142c0608102d0107190446680e20000203105c1d0700c0002c2844030500e0060f0344480109481070005200501e0346549144101c40d40c58012440b00d10360f0070000381030800d100c03516292100002c5c00801010f030590816040d60380204d5a51050810322001d000594400b101c206c0310f08210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 240144163 1250 240142913 240142937
    0xb09060d0302011b05090901050907050f0703020724020d020601120b040602040e042303090907080601020f240105030f06040b0a060f03030302030103060b420318070e07 74
    0x304a01118030030740070b880041a4882d10b40c03025003101a42445600c0028000503030803400b400d141e00402d00508069132040c181d490400e00080c4940900c0b10310080440c0000707950740c1410310030448d81c0c0181100703219408070300d6120703440b54841d5203513142068058003030903041c98842400070074807604071031203c0014605009142d541da403450310000c0c0100ca155509100203e02e01e011249418401e51060010032550040c0383c0d21440101c5c10fa10301c2900c1e40e4810084a0076640b10038503540d400035107a041102494944500507418101c81c03114001c1280b245c860500c0d0101e2000000388180300c0442c030b42004c96602c0d001816107514955039401120742c4032501240005849002e01a40980d0f80c030f80000b041c82c1c0321001d2040940c81c070352060300000d801100510502c40148141d00c0308550444d000311b19a40420711111403c004044901b240e5034141881101800303402c04020000006440550342d64a05421050303010001c5041c20180c61050907808640d10314542001030080e000b90700e03010700141d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 240145413 1250 240144163 240144169
    0x2011b0302070801020a020c0901080303190c021515010306080c0306010303050a05040f030b0403140705060c0f0c0106031208011205070b0f09120c09090d080a050601200601030507090b0906 83
    0x2445050440c1144200000001d18590a1003c1c1c840307a081c0341d0141091790a1103041000e81c0d081a080803001342c03c01c0041c0000c035406035101180741c28100340c0100c1c0c0700440d0305045e0b0414410042d41c0b485415140308018001084c00c12000c0d040ba401d8030200450385e100c03070310150b681d0454030b5030a8140c1d200c0001400824000c401800e8400e01d141307041482c0c82d40701c10460010342c4d159441143c0126410062008042e04043c0c070b040d0329140031494500f0105030ba02e0f81942c0c2c000141030302542e50b00019482c00d980c01200304490705030000c00c000780000c5945e49002b005410904804000285c0400004546003400c1c0300014012074110380140411410100c0540c01a070007400030040626080000706529141d201c401c040c4000e40740c000d0840d16040030180030a0b40b0005028070000d0b000f5020400d00c031900681c0c40340e0003405030a40052641e50740001030341c2c800044400310080400c010b540c032802e61400126a8142c905c0b0b1001d941c401c3c1d9550707007a50259850148125444508000060341e113003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 240146663 1250 240145413 240145457
    0x3110909180d05180925030203100b070302031c110c060a0c0305060904060b0607060501060206251418030a0503041403060618060102011e06060912081b010e07230406030201 76
    0x1541c3c1b941c046507549242801c01034130890760000d0384040380d00442040b40019100c49608000d221200f207581c0f8000c103030340d0300039100d220701c421803143c0000c510f4159603c0ca009030b01c281e441b070b80074070702c01c558940f04011129070b2464200d444800c001d00305052400001e100340962402804003904003401078030745a85550141c0b0102e10640c2d00310005106142c04607030b190089900a0059402600540c01c02c05940c030710041c015003070203003192a50a00400740704d520800420341c2621040e020360312944110703120b801d1192002041503251180d0295072051003000f0000700229442c1c1101101c03206204024103031605000c03100301d81c0c07100500c5504801030b080c403c40c060703110030148000901c09020804284a4411001510500c1c0342c0e0b50750148840e540040d9031070701611814100f240c00040550311101c0e2445038014181c00303c00c1c4c2c60240540301130250840381c92116000e05940b107441e00c0e62022080603185050414124105c80e80703500240c14244991800c0c1c9806a543e4038205a503414100040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 240147913 1250 240146663 240146671
    0x20040e01030f080715061e0b0414030705031621051b031006150e0411090111030f0a020a03030f090b0106080705070c080610060215060103110909180d051809 69
    0x20260800005000524021044d0680c00e518100000c86d1820a2000e031143c01d202c4801070302c2c40e0b80b860400d00c10100c6034420341e4100e80349560308a109440d1100800d040031001c2e40a2a018071030b803001d5000e0052446041002d03502414a1150f040045100d184810051000043c0c00c84e0484040c2036100c01115030f0014406402400710b4030700c4044040148111500307980008040c0b5200548403100b00c0d40000801c00b550403c070380c1400481100b4801f880300d4800e010001d0b0502c02c0700d6a6201160b242401914402040e29401c0b548400307005502035117407212024124006490017000c154201d120380b003050025500100402e1147c0c1c00c01a0603100204041c00d00414440c051108000081001d03192402500c4500c3c0904000d0030074140300d940b061500d0301f1140a6400078010130746000f08485603180c0c0801c0c00d190100d1400c00c4251080d03030a110f04850b89400030b030441c003000300442c01002c403402008040300c03c4600007185100701320754a0003010076440550301c0e41c490105113481c02d01c1100c1c0e08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 240149163 1250 240147913 240147923
    0x301060f051303020616050c101d12060f1f030b040609080f0a0e030606030d0f05030a06030c090509150709030609060b03031b100b0a0b210a20040e01030f 68
    0xa443e125000903c182d0042d8031031009a41c9140c0c0c0c600704009040c01150b040c698151402c4507104100c41000c0e024000d507118128049604070f41c03900310346e0f43d20078030104444807844c00d95106003072428000c03203505021180c0e011000540940790105280c440a060116074101c0300c01529601c850b580c440c06170000d0300081e10780c3d40c0148a40f0b201403c08800400d0100010f485160710304c1c00c2c910926060203001843e4074802c2e0443c204008501c0d4110300d100c00c0c0503407a803412550701d9480800c0b440041c101c40c0c01c0907000c1410280c0202d4030781855841036001c0c21611080314010001044c000c1149a41260307120b000504410040000840c03c0c2c001e00e01403486545c02080c0302c11700c0c50100b031840d0058131080192128284071445024010301601062442030a818010407014502240704164584511200386c400002c444c24480c4030b406403020454000440415035082c89d4450501409008280d415280504c41490f61440c01e0700c0b040390201c955150120903140e18584460840c4100307002e0030b1724 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 240150413 1250 240149163 240149197
    0x20714070e041218080d02070504050618040221010c0f110a030906051b030d0b19060c12111204050102100b15070c09060308070b01082103130807080301060f050301060f05 75
    0x100c02e00140111b4907091150703401061887d24050410095032000350006000b2850020001d0f243d5000000c105d50107a01a00c0e291080040300103c071b600c428801d0811140d9500c0c00e800042c15960042c2c1c0310307503c05060340c0e0b00ba108854401c0d9080e03c40004540081c08203800c85d02c2008128041d4020340060848444404a0681e00400d011308583c060141c01c1c0c0c01c9555102050b01c01d190078a0b8032422500e0402448000e1400e00801400d8142008000750440c840d800c0c2c1e144505100351070640300040146c0681e500d442d40c41601041c5a007080c02214054010010700c16103490300d03442604550b65008080300340000c55461400f031a076110200564894034101c001203900c480310301405009600c118212035650b40c4c0f9040500300920181c1100e64503402c140c2401340c0d000c248440016554248003599607030380d10f41d0a0000e6240c404124002c00c0c280000c11890280058a40074504a810075142c5c030308500080141165144404d02070754020602400f410307606244039801401e512509008155 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 240151663 1250 240150413 240150419
    0x405190207060213060c0515040f080706090201110313030f0813060203040302010207050406080c010e0a0f060809011505010210090615150f05180f13020714070e041218 74
    0x14180da0008070700355000c5400003442000007000d45250001000742d49408001e80f5044c2d0749441e01c03a0065032240e0781e60002e160104d018405e0008059420340c1d0b00020706c5907103400918152014084c1900300b82e01056030039070382100e0298040200c49452051510104100d802d540d02c54003003003131252003035882ea038092188101c1e111080e100440070f441990021501c0e0f900d14030009150007969000300b07004504003141048001000a200e04808200742044103d81030302901207840d00c28a81e100b403161058400300007801907001880c441c080c070540002886a01c44031030381d000103111117108030b60040c0d108922000d0b0a146642c8180c0010b80318080101d030155503810840c9862103141c0081120311960100710701d806420a1301003064042c80c3c1440c9042c510301c2c1801d080e00d80501e148103800b0300942e1f072903101203907100c0d95680044000501e046441e0861410940108110031051076210b115444020500ca02c1561115210710391155100396144803c00c400c8500c02031809400944088451000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 240152913 1250 240151663 240151711
    0xf0605030a0f0f0c27060f05010e0f0324010803030606040e0a0f11030a0e010e0606060901180f05100201020c1207051f0c120513020402071b0b031503031303020405 72
    0x1070130041800d00361405071204000750fa414007409071100300c4e003003a140a500700420200001d0510445809082c4501030021400209541f4550200441d0741801000400d144840c51600c690488000621222605070b032210740481d628441030310800e501107410b01c030800410b80704807110f45c1e006507418404200d1800329448a826a0342c900c4a90502711004010014035050034421a0346a4103a04004e1098503040170081e82c82d110080d01c124050000010003885990051b035240401c2c0c06240d2801600766650b200600300c81c20680200c900c41c800b811003542525105000b80d500c150321041c050701e181a9615801c071056031000200700c5007802100c0e078011080000490414111251040210b10940c0c40e800040000108103200c1c500d651900050211006c281010302d01102c1c5e05490040c8d0b40e100303d05046030780c0c42c0105401032602c0b40342040400d0030b829410103540540c01403452203078103004030010075403640140714450103070003080a410409480d141d00159000f08100c40f1280c8404140048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 240154163 1250 240152913 240152933
    0x11010909060807140d020904110102031e0c070608071b15050a0b01022802060703181d01050108130b07030e030f030115020604030801060f020c0a0e04020102010f0605030a0f0f 77
    0x10071a200e4000391020408a6a8001542c10013a81180c010002d1044c0d9030002d00c4144025002420486488218101c4c41e4001c004507100d80d10101c4104440c9a1500100c2c11780f43c1c0003d440e844c403402004e50016134140500100c9008200c10340351405405125403a500c2d802c504664142d41c038070084410074074103007628800d050080f04160400b0940c2d00e4608006032800b00101c410500040d05410105482c1d10b490a41158181c0c1c115625646c80d8114102180c00c0c00103211640542c20110341e0002c2e070354801440e210540911800400c4041c0c0e47c80b001903030680c208403030780708051800c0d195403000600c00700c800756445045e80c20001000500c00242c40d14680121410411100c00080103201c83c080a90383c41d083c4404520007000a4078059a0041c0646810710854041c007010b61850900030b4000e000e55488901c0c0601103020f903d0f82c0b1140401003500544090b40907502c0c04440c03c250417445d0040c041540d070060018000b00013203580b4240280000d0380d003a00d81d103c0072103100700041c000d00c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 240155413 1250 240154163 240154169
    0x1909020d0f0812061207180204050910030c060206100b07031206060917060c25080a120c090305030a050903070e183f07020901031214090307031101090906 68
    0x4060741c030707001500f561801203440074110300e20803200d500c02600300c8400000e61000713070340564840144100302e0b081041c020b03000d26000a54818a810100408543d80360341420440c3d01034141d045450b541c07060141d8513070f00f09640c0e158158881a000f0701c01c2091040080c8802446480d181080c0b0303200440d0305c000c840517034008a001824011040060245420300500040810707030140005080c000460300c038600c980625044512074215a0b01c110359009000750240681110680755100302c80180104000c850040c2044100e140c0b00d41c241109200f9641001a682d02c213008501d41460841d056510703400200d400795142c81641004940201c00d00d150134044c5441100400b10300398101c4501d07040c1400030710801c441c9086856060000180c603820520038458010707410700d6040510f0510078981c440c1140203500003950b100000300b00100d40c081c0035455000c6035182a000c290340880340d84244540d400c0c00d40d055010a00c2030011640003147c8070b02e0a0b030b05061018001c0d0307072640c0321820340710664 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 240156663 1250 240155413 240155423
    0x10050906060a06030203151527090702010b0927100c0219080d11090d0b070815150901030b0d05010209030c0906030a030305061c06060f0e1909020d0f 66
    0x4000c0c001d59060081401c000b8011900f03083d8250315041900d20382da264030b814030902c94000f0113401100000c504c822259038000003e00300100c4140b88914080403c10400703607074000c503034080000b0f030b040b4418401c1c008040b00c014000403c40d240c50000100b10315240c00c0043d4038060001c00d42207407050801c0313107030585070185001048030080c0040113410076034501da01c509100c6102d10b050000038114012107034001c01700b181c002007240d041844c0d102907000303981d0450740008900c29500d061003044c45074035103d4106a035555206545910f0044190f0b5046520716801c0000c01c4203d031144406103016000411043c07500180001251001031148411608250780c540d5002415210b03d040900262201540a8448001e581004008203582710000d50020b01015900c03004501d6035500c5002503010400c241c03802100c141441d085c01001841103104400032488000000114041c00c1d0315140c0c0f00d40392642c4d800007901d0490050f280600000003080768800344020140300043d40d09016900c0c410b00403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 240157913 1250 240156663 240156673
    0xc1603090512011803050c01060b0d05041b08030f0304022403010e0c070c090209040605150d0608060f0708040f051b01020c0a1811071406040312050709051002100509 73
    0x10b1102e840800d06078555264101900881914500300003a20760350341c1841e291b5900c0c060004103500500c1d2070b40041c555a2400a04600d503009550803140c0a9401100c1204505400c48038081c8910010b21407400242c10900014180b014800e0185600900207000300ca4007902801d28402012406030000d00c000c500480140700c81040b800324140d00030b0003400010301e88003943c0c89403080c260303140c49580142900000d100c400ca0321603070443c00041001030034450f940482200d031101180c001214042401f4a00740300003039410710004410f80070300c00d540d004005940781c0d440304461745a0002d009a03240300d8080040d81c0001d104100c50411000f060050401610300b600009040041b4616881d03c0342d26000000c0c0008074060545c16a400461100002d1584d02c14100200c07034040c450f0050a80c6d1001e014210b4054404a42c09111301e1181e501c3d070801402c00080c440450b1003e813850350000703007002e8062005041500311001d03c0c03038031030040f40c1e80e681860b24603005894003200c2c0a4059041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 240159163 1250 240157913 240157919
    0x8030103060c020d110a02090405010b040c031a0109030f0206070201021203040308010f171506040e031201031a0c09010302090609191809030203190905030604060507170402090a050c160309 83
    0xc10b00866034001290f01d0100051a000d10f44540e4841b00302a0191080c032400700800c040200950106900d035201034070921000d04101c90140c010b158403900c8124007501045080728641c41002840260f0754055150079481c1c41c0c50f02071126a4020f0003040707045d84100c2c151100715000d1174025501c510b01c030307a0319000d00d907051655094840311143c2c886c01c00010014241c1c03441141c0400c01492888035840c65001d0750ba903510024000e0180308042030064000007881c0f00703010104a002e9410b90b8041c900c0780403090640c80a17040007034401c607100d1203010703424850324200e503200e80c00405058000820f400d080040540000d544142818034102c051058100b04001102402105000e07000c07107114100729201c10f54402941380c2c840c909980c4d101d0141307030750b50405890003105910003512010b021a19149054a4020001c1c08141c0750703a80400c03090101c0540201281a00610440d400b42200d0f07440d4481c3c0d0303040800344c00082c2101410302d001340130f10b0b460000740301d41c64810640296200c0042910f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 240160413 1250 240159163 240159167
    0x41208220906090e03120403301802130c12050906060f040203070507060b06070b1608060402040501051c0b100504030b0a0204050d0311010e0106090219090501092108030103060c 78
    0x2c1c2e550b104084881c00c0c1612200c80c0f46000c070949030300d401803003181c404660b298901141d9852003084600751200c4000c021444a44000c010f0703001403074402108104510346402151a035600352400254007900c0700450106c48000f035005245400c405d4280842c2c808003280103501560300484068600d41d01030020070000d45448008a408550265011461414025801000740c0700d41680900055120590f103826521014112120950000840c51803400c6c4400080100d201c0c45a0210019035881d002c1b800c0c2c1c0c03500b40308440c02c407001616081d10700001503540342a80d03d8150b401c408032503601d2800070540d803203010000f50740f03420950302c159031642989086000c5010103403810324081d105110a02c1107132512821007800c5609170403c072f041d9011641299024105400d0600059420040005810802ca4000d0003d5800c0c807254428016818402261500a0361003000d00041d002101082a180700c200003110304580d001100980600035141c030100d991084e030040391400d580b00c42e54541c10b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 240161663 1250 240160413 240160421
    0x5100314070903020a210b04030c050f030a2a050a05010615080405070e04171314060a1403090a0c0b130e010e340f030c0201110412082209 61
    0x41e19608002c002c560440c2c000c100a0381890040390842248420448841d0300d150f01c80c0110030b94851a0300056180c50f142c010856500c46a0441d1903108142c00d005410380c002c0251202d07041c0d15030327581d809200c1d4001e03890007141c40d1050034000c80501030354007000b05009200c1407000301e00841c00030031001c0c0b41000c14929103010b20385000400c4011014480041d00101d80002180c050151441036a20340341000d4086148041d152181c0020000e40c01050110340e10105048810240700014198421014001c95206401c080c3c400140740001c084c40f80280381c0051074201900781c00f203990b084015903400f281110b6603001356084480206118249441c600c0404c0083c12a5403ea07400c1545031038248000a113014001843c6400c0714603520441d840e11540744403e51210504406a2032010b007400f4207103c051001d10740c00281817440141c045401402251503180140101d00e1a0a1500b51203009006c001d45c0111020001001042c4c02c4070311420003180c80030500405c0c0d00400e89025003101c112 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 240162913 1250 240161663 240161671
    0x30507090e071814060f030a02130801050601080a1406010c0c080106030c050f0d020d0b1f09091109061503090f01021903060e1513110a050705010f05091c020705100314 74
    0x52010380a24851540b201001e51b0001c0003280b00c969240c3d200c49160340045d0084002c0350b4141900420002400901504218029182a22480c0302a1100a250f1054078410300c0d001601407100d02c04505594820303518282c1c0a4002c41d10b0140746512a4019800d46000354400d40d00d03108121000d0009203041b4002c0321300381c1c00803105a0507422840c0d0115905070b400610140c20030001c5e50004451705600d004004480d0203000001c00d1003505c0740c1c1c81500070000c1c101c0a850304410150300303042904186201c50b000f040d008112348200200704d00e40c181c0c580e100503c0c2041d2030003050542020907100740042c0022000c4803550784071106120400500b290141c2d8040f14440e60307600d091080c4a504c0004d8610248025075885603d003070043d510700d016160101e841d08505000090007941c255002015080d614400e070300900c0203a403001803403010386a0a644140d0b864002da40901c80e14944030210050009803401507800c2035a07600000b6540c3c510411520020980382d05804049030460300129500c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 240164163 1250 240162913 240162929
    0x206160b151516050709020d0b0f090c16020907020a120201061d0603010b090103290402030304090b010c05070e0f0a2a03021e070605060d050c01030507090e0718 71
    0x700041c0240090b03240307002c90307214080c01d08000454007036071503d54040c1540c3d290068211807035655140d8266000b54064000e0455031031411040780c06a10b008181c00c080c09200903ca980c80743c0b112500020942c0c45190002284c80403032001000684804690f1031180040c2d07005071007401381c40d043c103040e004100b03400c11045901d411420308c00c1480075544c61548521403010794507141e89000219005110a680b560b621000c0135000008104070180902c03260210145400d001500b82c405903016071000b80d40c001d40c15001030005000b2041c095210140301d4805140c071214401c480e07120a414080c641d000074014041d40810401802484000160404100b18040186201245d00c01c0240d01c07924100c0c40480e070986001200f4188250141c03826611401c010400103803482036004001d86c010300084900d1818900007640c0c80c44d01040b000b2034160801c0261001548580044000300300040090082c0510700c0b002080024007001000d200f54000e03242c5145900a148820356414135991180103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 240165413 1250 240164163 240164191
    0x3f0c010e030303070c1e0614070e040209010e0d0204150603020405030d0c200111101d010e0304120501230a050a0b030c0d0c0b0327030301060c08030a090206160b 71
    0x1050729801105c494005401038004e60040407808034201020b100444081c102504040180300d084010a02e110300410b010340392021300040d8001032106902605038001d02181c0031104d00ca4003410240d030446511171005000003054222001403240d89080303a00143c0002e64003140034805410100080311100e801070410380c0440e041d9503034420b8404e110501c40d0711610403000000c9590390040c05071030142e440c56820790f2503089841008600620340c581c03480c2c040b58800440c0a10145040c45144003151500003e90714141c1003d404006111030941c0454041d0360340c002c0c01545c41c030210321000d0f0000c3c0300300c1011601e00741800d02c00180d4001510f111002c500d803030098540c81d60005520510b001d4103541154200c14207041c5440c44c2c1440368860304440c1c000001b04098110400352481c1c4103c2c03115002150b481050700d4541d0789001c02d0040d0b00200700c4980010000c0385007a130203581d001c150030f14007203807800c0c25a021130201d412815803050701026150b075510404c072041000e10ba0118100b60002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 240166663 1250 240165413 240165421
    0x1103012706050c04030b13060f0e0f0705060c031e0c0d080a05060906010503060f120604030801080706051611031006061206050603160e0d0f080307080a0207023f0c010e030303 77
    0x758210714047e145107110b800d4100b1010030081c2c03940000c407205044000403c22401804005902d82c003820008111502074900e01080514040040d6505241c1c030000450900307656510504800841c180c410003207040501014040034400c005c01c0110a1495980c00164141404400144d40c0301a02d81482401c8030402c01100b80d070f0040540b94418000c4840c1885a46c01401044da40441c0c1c5154440c035004000c10401815000b514080c100d91001d411174562690f21241102c0303a014514490200048024121020460003030203801c019100405423103010b00140c002ca400c8500c203a0024000c211441d000746604907091140c200100416074115142d0315001420b01c803002021900013090040d45d128111184d100d5011442ca901d901004aa01c0c001d06810290ad80340c200315030807000a120400041c56425041c020b44545a90140800c04103c44040c116075039201c50f5aa0082907030341c62012204100009080e250001d89081c020f0800c3c05210000148940140c668241c000d0340108184 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 240167913 1250 240166663 240166673
    0x7050a1a092e1815080402010e0d0204180b061905060904060b13090c02030418111603020307061805060402013212090703020904120e09070f080114010c1103012706050c0403 76
    0x5070303106d0350902e403503a01c41c51003000043c0c55a0030761501030341080c9050183d044000400d83c0c034800a50060041d04981d0780d03010200205202c51048110f01c1c1c1600720010030031801c00c0d4010301410320009101007030740b42e1505141c1c3c5030303034110000c0c13200068104041001400b41510411045130340c103202941c6440d00308440e01c0c40b0840d0122440d0f420780d54131f0710090280d4240b5010b841450701c1c2001ea08440902500740250f483d004560150b483c1450040d0415040c22127040d0030182d958402c0103802a9038841e00107544004001c0340250040a81001d48800041c0004c42400c2d6404407401c06612100190040d03814400d0040510f600c50344445000d002583d00c036560070b54429805081e0b01d59848a6100840300c022400c07550036000a5900c0a1084407504141c2e513007011406507075416221780c0e03601d080528850041700000d01003150203060780f000c22529540188801009800442c030030b410105952001c000c020487d03034151100c420020108525402119003150174409068142030440d110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 240169163 1250 240167913 240167927
    0x180f1a0105040213050918010216030306050405070c03110a0b01080304030302010e0d0503040f0606050603040c03290a0f061d0919030e09150a0807050a1a092e1815 72
    0xa03039104034003806c001482c0b071000701c4201072188410002951200c0162601ca00302020170711086000c00d0902a021a00f41820b00c00c5505c00c0d807660f6a03805444181da1001d4454054254049419008840903d00401c8036680054005c1c45020003c0d0340c0d481c40e506000342111810f00c640c28050700a05440d80d490b90340041a2604160800081603040b4010300e0b081e00140304551000b5001b032000720070401070020390102002202e008e0300c58005c203845030040070381903450900c110104910510003c42d218440a9200350030104ca4008000f91032915000800000319821440b031440700522801c0004c11402070042c042c5007a0154030010506000740d4015011500c16880b66004240c91070000e102c122490240220444c0040d00056200303442e0303a0200c9e01d40d8624011203004d60140000020b40c0780c992040c600080d10040b0595003005404410001001801030b00341302581c9003401c160203200d1034030401c0d602c0c41516484044540c0c403000322030303483e0308640c0e402042c001317140c061942c20a64000f19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 240170413 1250 240169163 240169169
    0x1050a060e0a031e12030924060b0301091b080708040803040602090d0303060312021501050603040303090209070806010e010c02031f020d15050f06070c0306180f1a0105040213 77
    0x144104220008000714010642c0c80d840900070208180f0801001e00d4000c2c2a01c100c64003942816902e42c28003401035040d00c3d0b8013980205a40650484130703240b11001c0120b009034a5481c20b010031116a2040ea1a80e65042030300000019030b80c61070301400000e0724403100c0380500f00c54140111146040c0202a1080400034009003001c000080000c0801c410341d411038695000041c1568628549810014000c3c18280411541172200c1c440106e1060300001e101050154030440075411a0300709002d02c01d5640020388120305040c0c4a810740c100581d42c1c6044144900c460303503500142403624600041402907107001c5281440303030488008015032008100f0060b46c2806244004100c800c5081590003403040c0008a40b249240c45d092a07812241c0703c0c02c0e0021600700700c03450844945d0580400006115042d0010083c3c0c0b48031000b040080d200f81c0000a116450085d881700c40da903503888075014030312122011181500c010011101c044280580070707001d00019102142082c07003038007085100c00c2e0540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 240171663 1250 240170413 240170417
    0x150902030411040603080a080a0b0307210204020307121b0c02040c18180b0a08030405010f050f120109180510110403060603060c0906030e0304030215090415080c01030501050a06 78
    0x140c1800042c0c040c10103018000b420410140781d072802c0222039a0009541c0f03800042913500400c04415140c000d401441c4030007009401003030b1074610040b00001003041145e07850304685004202503550362024501c00c0c0c440e500d54000c007032002c54159044400c0507405c5110184220010101c1c01c2d84810148036041e8195000a80513000280640d0000c803410705030714040384070a0010820f001c00389a9030803000c0304440309010b062000c01c1001135401d0a4050140c141c2e006000c10003040d8401c920f402c025003602c1c24440c1c41c2c2010601241d9950b0b0003903011010410f0701c0320041112800c0f610811814500400401140c01e0165403096100d04050607141c0c089529950428001c0840c03908880c0256400b80c01000740c0c0d5603915001c5c0c09880170390000342c080703410040002000b43c0a402124511000c100140d0314180c2542d003080748107204258035200e00c003828040c81c187d0341c496104556280203225803054065103403100300c9107040054100c8604040c100401001607881e0800d404095072124 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 240172913 1250 240171663 240171667
    0x50c1203071b081204120215011401030903050c0a03030b151314010e0405090c04050906040305030415061707081002040f090e0f0a11090a0504030509011d040c0305060a09150902 78
    0x140c03c001e50b07280116040f0782c024048000034082001088011140300d08056001d446143c60300c4821002c0d81007003445030798440e44003180316100030762213a4484605980300e03080c9035082c00035032802e079460314606e14821408642d48110b002d4062901e00007098814040004d0745141102c40c0f00701c030001203154815416848644200d40c0d045030700800102081c210041c0c0100003e02c0c14803045980c407421405002d000368904404241c0984010505903c41c07078041d1140352039610b440d03a80c124490040300c0d200842c42d90f504008120f9205012502c0c0c00b8695900041c0f10707176400c0401c140d040400d038403007196400e0f10411081000781d00c0e0b4603c8004030b840c0d8500024010011894a42c2040704000c00c5070018000c1e885c007102007294508046194030310a0390584490350b2500c4a82c01220380941d0042d002c55418000d40240b51b225200c10450100e101c2c15040c4180d0200c3c021406486014643c1804607854008001943c142002d00c18000c1001e21300a000240080000138100b01140c004d4800345a00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 240174163 1250 240172913 240172967
    0x12020f01050c011103040614070807080a060308070b070306050a081b1c0804030b150a090b01090f081f2003180d050d2f07060e030406050c120307 64
    0x550705490129120300c0081c001051003d90741a1306900440b0100d507840d1800004500c0082007170b140324881da400361030b426800e07225071409461407400107101c02e28a40d2952030100028840e80301505095214150b031026070b007010540a001e48001d5001107000341d610030802c1100d9400081c11346c60400196480004004821000c580500c034000208807401c0c03003003d04903042090610041c01220300400d805d06c482d84864800d110071144d03001e2440e82c08003084100303000c103003d5a400aa0800c0c1e05061a9030590f03035403400c0b140d4100c4241d220117102c1c0c000c000107058034500b0350003000020341a007608201c8941c10711103107403407030101446034094100088001102d420a640c032001c2d241e04540229210686100c400030310a81c0b00d1701c0c010345c2c1c00d410b01143c4501d100b0111200c0702c00e030405201182017184510142403107500f000005589583d29903c102c0b44a107010310082c0050611a030300c540c0d60b4005d1300c0c1a07a00d8040302d0700c4d0200e204081041003041c4107510684800c400705070340b035040c45a040703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 240175413 1250 240174163 240174167
    0x11090315070f03240f0f090b090604110913020a090f08072114030702010e0915280306050106020f0d050307080a0e03031509090703021e01021e0a0b0a020412020f01 72
    0x7000d5100300807000c8404c000c41c0a29580326031900321245600303241245602d0300fa604003642c40c5800a10307040720040011480780e00d402e410190f1420013907126541800cda41000501ca10b8025450803402039000a02401c0300d544040c106e00034040e80c0d90b01c2020240f038400705503500d085511803800303601c9206226003400f61008581c402481d0f000740030041f80d880d440041640b40e90020008a000c41c000385c0c05030a0508040d0f841901c00c004640390103004c404a00203000b200c0311007035601007040b140111221f8640b0301c0f03081a50003941c0580c500280c19070402038082c0c5840c00101d1000a940d100c283c200c0600c6034003008482d800081441c001a441e02e4101500c8040d2010703004c00e04c41400048104520384140f080106c82900d0304940b07021298854125280e00d0350b01c6800080d420495950144605581014100d004410184100c850341d4420002c01d4440404240018225403c080a03003402d0040c240207054103c680da200451900d850f001e41c20b0065035000a00038080d0014500100d41c0368 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 240176663 1250 240175413 240175451
    0x140301060503031602040e070f08010c0e010f0305060105090a08030405030714100e0303070c1413020a0509060f071403120c030717100e010b09010224012711090315070f03 75
    0x941201125442c0d40c841c4510780c0c0c1801e06014148ad02d42c03921554a40b802d2003459040c100c1130041e120004040c6443c0c0c8200d000d004010811030501400f00180c45460302c80065141c0101049070103552954141401c00d4140314070723603010803485501030240041503a01c4111404100e0901d0603c0400c40c00e070000400d09500030081d029210b4413030054001612602c010004840b480f00b11034016030305149209450881c09805207120000d0002e006c22510f90900b10000c0c000f05015080312400c110036540c9481914582001d406134a400200314060b540c0043c4040640040601020794254601100018226106140b220f545480140c0124103003964120716003015086040d6604000d40c0c4548a18042d94040300c202801841600702e060038840e00d040805018038150b48409001e6460000340c0b030f003401d4030011280740d02c0d00d807080440f9412500344600b9030b6120000000c01d403114039440415040c00c5441c0c24803660042c1074410094501c1c1d10070244500038100d070800103460103144138450858 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 240177913 1250 240176663 240176681
    0x30306090515010f02070f09020a0e031905070905061c03030e06090c03070f030b010902130b0a02011401141008180a14010501080d080a0c120f0614030106050303160204 74
    0x34503110034040c0c0d0424a07402d510b8004002c1c0c0f50035079149030040013280c2d90711182c03007451039804020f0310600c51401650000c08040b00c00d407606007418000c03400001e003005041074140d2640110304040784100300003031005800408180000308180d02d008800b1407000349644250f500000c140e14041002c140c007070307403000e580385032043c040300c11074074022882c075580c0c0c141451880c1c42840355910003d00303055814102002c2d40da000708000101d034a4070840c20003940180c1400242e4415500010030300f00707001809040710760201d500100311401181c0004d41d2200703060300001d594010002c2d0540c43c9858904000701454158a8003549540d00c0032091200c040309402124824002c0d643c1c120144008640b0656a80710858000c10071642e03901401c50f07403240303084408004240b44030b00141029034540d02c5620010300c00d05100d040002504402c4040300c031400c0100d0350071a40c0317150602c81030000741004100d03030381c040e00200405410540003e91324042d00e0040e403801c0b811140584119140c580044620b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 240179163 1250 240177913 240177929
    0xa06180f0606050f1203271203040e061005030402090a0b06040311040f05040b0f0406090b010e1506090d06180501020703080412020705060405010c030212040f1406180d030306 77
    0x4000520300e48200a0042c0b0710802d882a100c0039069203461901041d01542d502d20301d00294605142e8402d01b64050030101c19803809104503404440c40b94807050001016040c018001c0c55840e07040c12a544100d8101a290b18003855803440b051811903004000c482d0405d404468140391aa01c004540024001108146411100c045000000c003d041503501c122450219400e00080c820555940f044800031103000e841d00340300401080c41010b8801d402d44d001030040300302007440b0420307458a003407000c000c2c1e1243d00070744903540030003004204c0c039007800940701c904403502450503040d4400522110b01c0500301078801917488030350309a964152060404440d030f006009640301c00090502401c010002ca5003074410300d45c02401d0112a91010500c0426110700400e41400c0a0600004490400c4e02781c604405502c02c0200300c07180428a0000b4000911701d403100c90240f1400c1070380401e036289000e10380d50b00516040c40383d03190051115400440c2c0c10303070584800800c40000e080032405401d203944130241c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240180413 1250 240179163 240179183
    0xf0302090d170403150b10080a0b04021201080607021c05090402090a0308070311010908120a0902030708030901022a0d150f020d0e030c0a0b1e160e0303040303020a0618 74
    0x5004031a0b60041c004a03030141800301d050403404900c11050340c9000307400036804132408002030000740c020141e0681000401c40f0001e049070842c4041406c1381d1051140c40340350000b107401007025040400c071042c0c0c0302c80c0501c00350a032149500341c0003010b1140f203c000014861701140724071098650745c0c1078a0782031070300400303000345540d0b207041004c140d52002c2c0040e0000340300407050740070f9040d050140014141d4041c092034504004000c0d01c050107100909440466600d038000031002d40e0341048000090268840a59510358400002a280068121200740a0020241046e054012180300100040015182e0350714060f40d44c941807850300a114802a4654a00141c1c011012174581c00390041e0b0000034002c005c1e003a00d0068513940c034096910b03407000940c403446480d03000070041c10038160828690090020410003154000201d44011544150f58104060b10705062175440001c685000105030059840c1506545009454007420440030b4201d5480c0e64000000d0000c01c0d101c00303280342d00600105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240181663 1250 240180413 240180443
    0x1224030105041103011506020607050703110610051903030903121e02070f210201031a030a030c020f010305010305030304080703091206020703030b040b0a03060b030f060403080103120503070f0302090d 88
    0x1644014415407014065880c00c01c06d070044105c0c810040301a00c00c0c5400034445c07503846c00700440342644042d00c12010070600c0c0103519114101081228000d2064a03808030030325007080140040c1d80101c540c04244000c405104002103038000308280705a84e0400440c6800c20300109054034142d4410a00940e12405180e5001c5103a50225110007a181078141c951006a075131180e10302258591440b003190315041141c40c0c4010741c003d900c01090b013603e0389440310066080303100080c00c00031040c60540c04190300540d0b5000b14a01038200b00035800003420208061b50468440d15928040140002c1c00410001000360071b25001e030080400410040c0c0040300c81411600c1c10601030b4000001c120007190404241400a00d8103001c1d025440001400c0c281002d80355443d805c01a24031444040d405028001c501104801c4c10300030184a14060f40301c0610651440c40c00c2200c6030031000d03006040000c20b20600c44121342c4001907025600b07403803502688900340580098440225400000d05880e103000e124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240182913 1250 240181663 240181673
    0x40306050901021908071206140f030a1514060907140f0d060b090306070e130b1503150907020307021804110a03030f020c01080606090603040f1403040f0b122403010504 74
    0x1403040105a9503510150200c100e28010b580755809018900d00e16803e00d503089090244802b15008402822241c0032005138841c2041f030b40042c0d4500c1d00c4c1c651100c2100300300d10142e140a80d0000341c20740d203080c803900c0c01c141d004004c3e110401400917016030020b07190700034642510540e19110351050080010726070380d809012603030b401240f0542c028040c0c4000108054011504c04502c45806410011a0020005460000c022080405078403007228074030f0f81c403c540400701440c4104503210069034500341403010001801c0b401400d81007198002c00c0036000507150462030510401c4a0801002951035a140086003840c959003800e0300051141c00c0002450380c41a01c002001c0d081e902610b550303c6500c001100c400004495a80e000361007040001101d0400000450f40140203810039181f107802c59544a04030401410b41311606d03400401c05100c04d03565003852000401e119506d491078003c02c1102d012250000811282a082618860f218050141c0a99148000004000b0482c61600d450720b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240184163 1250 240182913 240182927
    0x4030b01180b0102030a1d010c0b0a090606050a14010507080c010e0c09060102070e01180b0a0306020c060c07150e01021909090606020a05070b030c04030c180c08010b0403060509010219 81
    0x40100c0360303402c0c1403000507554004801c848200c00c190355402c0c80080d07070311840b50380e40140111244c1081f0b94520700c000070a18002c4514064002905c000c1800740040c1000c00075200c450f0030103482081c18840030800c0b4034204040b10120799003801d0039621810386040c00c0c4010302903140400400e508154580c0000b190119aa420b40002102c2c200c100742ca84000490b540d13075943c0180d6100c0c054040043c0b055040a185080120040200214011000f24007042d41c0706107030783c0300b2a9051307008115403200700030602c11039074800c1441d803035581003101d03581703032440b00d440103001107403005a0365480010700c800290111188030143c81c6901c2d201c507203240130040c14444035100328020b052400501013001c03840429076070000f503000002414007505140c91100385500152141000440401c000400100150b01110081c40e1100501000d008540d50100070f9030b400890143c104a48000107018124000c0103039400d6a820030f6001a603a075441020a0083c49241c2051205118244840c404c4680c0044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240185413 1250 240184163 240184199
    0x14070503040c15020c130207050f0d020d23090409050106300803040305210f0403030b03010603020a090b0609040908190212071e06090303060f06050f0a1404030b01 72
    0x481c500760507544040001074450f12103606001604000c00786080c614041e180d41e070a40e03446200052501803a0f94a0b18a810040e101c02c10498200c15120070105030188004007030600300e41054403444040181c40082038160201ea0701802102241c6038605071595405421907a40c0840200176940d280c8101c421003404103202e0340480c1145140080c00101c00411551070242d10140c058110340300ea540983d99901b182c0f902031155031111004408c100060f42d00280210741c2101c42c1d80681c201810010143c9550070005c074000e80c10f20404100603258a4a03a104460001d040080c0b0410901c001035803170700c54540181d82c07150034000c3e4502404040c00c006c143c6010200520304410045030003d907101c40b0035011250594006118010214403010407000b041441014404811140c1d5500c9108442641c0c0042e4002a550b01d014801030303c03000c200c040a8421401d00a003041c0c010f1490440c43d220f000c03054010030074410454505840058280c070007a551000810b0b03602d603155941c24919010305d003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240186663 1250 240185413 240185423
    0xb04080c0402130303140d020711090112110402130f090c0e09010609090506040e0118050105010605040302130c0908030a020303071722140a050a11040c02150402041407050304 77
    0x40c80040945014822151680b48840e14500560325585080d9041c242c00704074800705400410880b4440c64040c4000c0a5244c414031080c10300c1c2080c0404d000b0b43d2941604140207501c1c50080600100301d0110700d03480c02c000708913005666002c010b203420041c000507512032805c401c014540420b810001e5001900500f0403940c0e2082c54605e96420002d29860a12510000c04c0f044203040c040c00030030f0340206610920161020410841455a050840b40110380310407503540400e4000007080340c00e01030b060040c046443c10904082c00c41e00041c408203466140310007030650b22843c4980240c0512000e000500e840401d4984500511801940f01c1d40210f940c03d0000d4030000300000c1110101c0c2800d80991203840180030065070358481200c10115034101503c1241e5010400d952880080005405982c4541e01401c00a45a4031b03240179543c00c2e00440510450600c3e107010540343e40061001c6008030300301c030030043d2521035001050081c2a00642503000c9201c0404010366560010000e41c003c45c810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240187913 1250 240186663 240186673
    0x10f0c0c02030f0d0504030f1106071a01050306070e041a10050406030f090f060b150d02040e0c03040b04031409060403380a0f060f0e1927030c0c0b0408 67
    0x164510350300c13521255504004194140014804141398048266030144643c10b1800300c0d004410001d559500191021640e0070120b42c0021031000a9000c0fa500610080d40144203900b041c0801811030010580040d01459440005c41c0d02d1400043c80c500d411100a00740408820070094020140d600601824000c81c0c24812035171001360062107404040c517042114046080c52982d1400d02400b03140d22541e6000010b04d125900015030a001010b409404420050343c480c500129100c00030070080c000000000140100401306586888035903003d0342c5460005100035010381552401d02a010104d03802c240c000c14080200107148c445003604282e007801c440003c160301d8034940c3c18100c140030316409031160311001c1031540d0300f19040003e1052500301c0115856072540360782164103400398041c883c81030007802440b803c01413502d48807000400d00c120078003003c2d031514042c0f00c00c1060b41041640300403a03550350314103240c07040c80c0c4076801d56406482548200d41d20700d101401e6802500036083e80307005d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240189163 1250 240187913 240187933
    0xa0f031e0f020c090403051c020d0b01090506030a090503040305030f030106031848050109050904050c01052107081b0a080604150e16091a0d0b0102010f0c0c0203 71
    0x150030031941101d180d0340180480008041130061134400a8011420304c4014850850082e10b0014440340c0c500020100503140d81c0d00c840341000303543d103d81900741845291402070095071241d000f12a0701000c08140031420030350700c1c9002861840382da44080d1080c0000301d900b140e02980d24009504071407966505000041d1214101481d141c0710700300003420380c0d07000b806413219140c5045d054004060758000c582ca00000b5001480105000b108448050340039040f418812903801074500c802502c0d0649111403180352030b541c0d070383d0380b4030035400c00030305005010034000150306020301c00c3c20340c180020180001508101714068100c41c0241e900002d403460100e0304420340455802030345c0584481e60b95070100380e00c480c03043c400200030703600c3c82c510451004c2402003080c921400c05d85008408411000b84a6000313035000420307203400c9402c44a50a008050292807100720581501c17070341000711030300190342012040144c1c01018650034002c007107401c2140e0543c0550300010801110b5000740c1c01c0d41d202c451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240190413 1250 240189163 240189167
    0x3120914060418151820090117130807050a0302060c09300303010b040807080712060b0d060c0c02030105060d020918030408061015030c050f09030a0f031e 68
    0x701d0052203200e4100540002c0c51543c40e40280c183d8103400d02001034241e499181400711150381032804881d990b01ca01100d0022603080f21210003000000d00c0c0141800101c0d00020001c1408510009410008002045071240141c410110480d03111194a80d02d0300c59141551300c594081c4016005801000005000224100201d50340288000c040b940800750517080f10008455079a140130401d040500700314400e041c00c100850103030500544c070a8441d8523000380185008a2030300902c0f03680c2c00840042094001440c041c0074210380c00900403810540100106400820082c0050b080318200300352901c1240e0840300400000380213a00901c01d6595034070500070003001c2d85200941112200b40051080d640861000280445c1441640c2c41c2580e281c04052902100ba220401c0540b400301080041039811408008034656030706051000415011010b000740c0524001d01c110880006580c4000703035130a00030441e10366400140792100024604005121880401925884040b000e03901c1000074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240191663 1250 240190413 240190417
    0x302091003151a040e070e09030a0c17090a03110a060e03213609150f06040801060b030f06030f19031b050d030f020f160206040312091406 61
    0x660880700850070b080c8081281d0707000b84164000521014021140030400359141e00030514031281d4103004280c0c00307041034800418808040d202c2d0700c0b55803040158060040c0c121074a4100e558101004020342e040300e80380086d4900c156100281d000152820100401a01038203120707800d2003c0e11a6040da42c1c5886081c0c459114019002c0d5160b403001d403000300c070040d2a10403140b1f102020456641000d180041e41c0315034686180f0f00314800c0c0d000501142a0100300340d82200d003510101c80446450400a800807001d85003907d0440c0988140e0f60900302989988003201d0042280c140204074440d03540500e0707030b91500705a030fa40000f03401400100d0058134000407803203200721410025020111098240448401c1c03442c0c021410f00c4a410011001810740104100d0124040c8019000706440c07443c3c0101180c0d11255032040c52403041c0b107260200c44d003a909980d0184807440e005c1c207540b8840c3c0001620f60089500041c207007107032171030005540d60b40823990b603089940040c58a0310070746924007000054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240192913 1250 240191663 240191669
    0x9040b03101b0e06180102070512010905060604090305030619080f0715020c0105120703111602090c0307020d0c0203030c12041703040312030b0d0c0902070c140604030b090705040f0603020910 84
    0x2000c42400448044001c025112417040e1050048450700c5648002040c1001403942100f00c8695444242d034092110500c5042d600a400312410418000300f40d80207001030001820060207010704440d5048002c13021041e0001900e05e02c0e04654104240f80c0034a641c3c1c807114001c080007046803d10f219281b900000c4c00d214081c20507120300e1304180301510300400f41c00004002c6000c240e01c80b801c81003044107500007802e10b81c400d040300300e8a060781801031104944000d0104911090100100010264081071604840a551410303000c60038480c00000e2450251a9000100d0300420113101d119041e6103000740111001114103000c0130094004c569240c1c011440080c2801c5c807030481d00e8022900c6039118900c032010041018040d1651512462003120080d081481c404d41c1c0041c1e01411f1001040d1003100400300c0c005035100302c034484004120350740110310006054402280100b100c0d82d00c24400c01d4060003000d00204441040c0480c180c000e800180300c1a4015080f0030003060031102c0340c20002d026 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240194163 1250 240192913 240192919
    0x1030305041509030602070605040b0f090d03020702010c050d030b150310140301200409060b04031a09150708101d01051005090402040b0c01110c0a0201030209040b03101b0e 76
    0xc0502d881d14003044028012281c40c1044800e00001c40090304500c00b500803240506800a25450300c3c2c548182c00e880051700300007020b01c2d800d017001000000000c803c0440095880d002d81c41d0006840181c2e64440f005000414501030100200360b030b194164029100c0b1003040390340c180740c0200400c070584a44000d403030390f40d0b000c03180050601c0040d4940d881055003180c003800001d4059044022031071100c82400c0c04844001000404201200c0e46014020292400b807a40600d80341c51684e40e410a803c0d4401e46801103003c0100040002405101c0b007090704d0540c2c1410a501d01c0c2612008040341400c441000c15009003134004941c03400328417070442d00001030705a1a2116400d0104001d030204800301218100700c010001c4a0480e1510b001034402014407100690301d6400c8054840e003034400a2540c00403200040c400031890b4940021140d07110754080c00c006945404120110300030703207081c1510a0b0944224401620407030480d40c0850510f220b4804450b8550050075400c8a88400d90303c24298 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240195413 1250 240194163 240194167
    0x3020706110a030c0f06020a1e02010b06041509030b071707080906070804210c140105060616051006030b090d02070b07081305030d05040f050a05150903010908161a01030305 76
    0xa011304403155155000d030745042c40b1410503680348401e90b445402e401002400c00c41d8018188603141510060b00c0200740002d222103e5000041505030056218070350005400422891559004640b00c0019540250020090380f8120b04050103031100010480704450b1294009488544540380d1180502401d03400f070a41912070023000c07141140042c1c816284000c64106030348502c100d503081c511081d4803c1c1c4070355035503903018204080340c9840040040c0c482c1c1d050104200c2c0540c1c03050111540010000100007550090f410941c3c9003411040701c54242d07034a0f04401005005c502c203103051040305a14221000c8804214040307841d00d1080c0705540c45880180444000106080040c01c1600c40380e00a02c144c031581d07900040d1800d007401f00c410300440d10014041c42401514020390000d03281c01d40d58006040d107007201180c0fa581c62595000360402d80807038000195903080d08905289504881010344480060b43c0010b1941002c220803500c8030000181e0b1021003040700c010a0490750943c841c54 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240196663 1250 240195413 240195433
    0x302151b0d09050f16050112200d0b030114040b0a0b1f12060b09030f030903031603020f1203060a05030a12030b0d05030304050d0f0e0f120709060b070302070611 71
    0x8080e100352a0200c441d8090561940280c0200708848004002401922170603a0301d0f0000140c1140450081e43d00f60a041889814921400000c003400e040c40040c4480d6542d40461201e0006080c82c402c11940355080400c10408000b02d21070f00ca00840c0030340355600194445010140c21110480c5181d0340042c09060a529a4a80400c1e038003000743e010305200030001c440038080d20446075903070800c0140c003178081040c4469040c100b00c0004417420f5880110b181051001c0000d6990184050300b07c03c0d440e180b0101d00400d403003849820310f2403180c0000c4860441001544024580048480d20301580d030746d0b1000102032400040701c0e01101e42040c47c00d4403140d0780c51000c0340940f0301c400d401d6810001c15100500012420002988210b00440140a080020001c002d0050340f5040d0030313004120725445962883d83c2c0307015000c420314004440d04810465001209810145280d0240703040c2d42c5482d00002d41d00c8009802010b00d28800c1e425034000f561181020b403048404da841200da1035001525032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240197913 1250 240196663 240196687
    0xc0406030b1207180905010207061a180103020f0a0b0a021c0c0c050402030c1603050d05060904020319050705041d0601050406060c0b22060207231015030501090302151b 74
    0x2d91304111200c400071820f13240d04d40b04c0500f60b9100050444d070782c039621320403205424541c003110710002108650143c03408114a5554900001c18000640302d040b603e01e0020380d5558019200e0000c0c1103402d01d150f1240e881c0e12000c2e4031001100e0101c4041008a20002511307445803140303110203540840b2101545080c43c050000079000280003150241003080032207034845205464030748440c8a941e07126038a00d11004000c1c142d40000d408940105004000d010040c0d40c00300d82402c0520094460580b000c4031401c2880c94031559a00c40c3c3d801c5441c149102000f51402c00c1c14414882100b022150380380d0381ea5091004441141c807411001a040c403d07494009110344500b50782140b44000c005078000301007000d10a60181c3c02c05d089900307950005600c000c0080500d0250015092190351040301e0010764500340c0c5810b83d203600852040d54801540c6003181960300e0620141d0b4008000300008499072030b02a540d5904000d5001c000ca0302240090b03650200d00403080341100c40d920085080540001c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240199163 1250 240197913 240197939
    0x311060106230c190611040b07150f0c0c020901081c140d020d02040302041d030a050a030e0f070305061302061207020307022211090d290c0406030b1207 67
    0x220507180c800c02202010700303800c00111884c00c0c800d00e00f08108460901c0c00c002103c60140c01c070704002009101c100b002921601c00d9852854220384000002c00c00d00320001c2c028064044503c1390b603468207141c044100e03441030354440f0031482503d07c1c4180e43d0b240c4044540c1c1ea80000c0700404000040c12800740502c0c89801c41e1080006040035840c2406842c41c04241070380c0000a840e950154041f44c104103506d814020140c410489801d242160743e01d10601a0b16807040c52185030a00070700107059403215229a00128500404c0015100100d280c51a000e44410203444107640d1840740c030000c07500c0e5290800713003e000c03968028a1145081455440324000d111300504a100303501040c0003880250701e601c0c42d00800c403482e6006140c01147c00b501514103d54144401e0b1a85810a0200401e035880c0d8606845120740c1007202202c8151502041c010120824000003200c1d5401000340311240c0d2100020b88141c2c1c50940b0207008003805c5000b0f0040e0800a0411451203a0040d04104000e00d40c00721 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240200413 1250 240199163 240199217
    0x32d01031106071502090a0914060114160605070305070f0923030a061b0306060912060612082d031f050303041d0f0408070627050a0311060106 63
    0x120490034200b80380c1310b440340d2405036009800d619800203401070306807811b1007540025040810080103c210080080501c031180104914180805e00d40c5905c101c8008600303030741c401a2600b132284201c0c400f034039150002c1c6c0001e03208580030904010100b100a80550741d07140b0440c00c0b5560701594145440441d900766480b65850504001d030310b5038603d0300e40c0c80900150840f24090b83c00421903081c40140445003821007008101007601e403a806000c400d034049804011201e00070902030001400d4200300b00102400d600041406e070000030189d0411200030f003d4603084045485140801030303203801c901b01901380c03068000e4240508000280e072000c100d6180540220382e21828a05064079600480c1c6154029085a5207145510688d012050360000c2d810380c0c810b558495031241e50406546071643e80c0200385004040d551103203800e400810000b100c680641402001e000c802200600f0030980f10400b040041e0000740d4038035403060007034900107a03403412201c5655070b1400c0e10340704a10341da03c0341c4403c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240201663 1250 240200413 240200419
    0x418020711040c02060403021501120303020f12071206080114040b040303060b0408010608070b040f051203090d0b2202011d0a03060603050706021006050603010902090414040305032d010311 83
    0x840c061905445520031040f5140301c5400820300d078100303400d000e072030039812007201e4080d401c0103001444400541807030f88101b66490709015840c1c000840c503a000351f0140d02407a14002121100308544980d00109201d100d4082c50420011640c552500c00d00342e440c200b450035889031912010500281200c020b07164058001e2800140a58039880019082e60040c2d100b100d8503034407244c0a0080c01c9007400000c000705400d401c511b10b007600e030104a170321a080d1403003250302c10340ca24001900780900500850b2600c000040440d800d03d842494001c102d820240d481f4001200064107500700801c04190004145805845800151707413034500540e0074011235210a50051280d190000004245005000c040e510031006410200c1c05d06d58001e141202030b400c2c9501d082c0c1850000c02c03990f260041140d055528440015943d07451080105015002d00340c110306451046004010a042d403000c083e41c0980116244454104004a00c801041c8515241040082070400041001400740440b182000c0809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240202913 1250 240201663 240201683
    0x1091709180a020d0c0e09040314040e0a0207030f0503040308040219030f26030c0a0e1c03020f10140f0703090506070201050f0c0307021009021302180f040204180207 73
    0x3459140c1c40407094500004458001c1076032210300c1e085002c2c801d1314041070701d0040b000d544240c000a000354000391000e4140950b6034004200c01d5410320481d4058800162a4401410020030100c02544844015800101074000d610086445841100d015507007540d9030a10716120364003000803510070007400401c030100c801c0b0000300013940749403003104072070060752581c14940c0490740b2080c48084403024105499410420000e0320320250090b036620407082e00d0b003281009200000724018a80c01035025480d215056110b40c00c1581c0001c44c0c003038241d0b940c4280c0c0d040300782c9805140b0640312140152546c2041c10000501111083d589403940429a4070300416502c0403520348034180392085c3c1d19040180d446004004184154015481e00711402440035807961401001c0251900b0b00540c0f030f85070003611a0001010f6503511285260360002014085560b1042d030840300e12400e44042d041805054101d0400302107183c00e10a5600300ca45c4400c4032900b00350740c001c0000084d405039400700c0c0c0742c07154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240204163 1250 240202913 240202939
    0x30b07030c050c030702042706050103120207030201021002030603160801020c07050a1503020c010b0918060705030609061e09090d0e03010b030a021012050a020711030c420307090801091709 83
    0x48c0049111006000b07082c005819419402e190195900c680503200a642c030800d410030040c0d030b0000700340c0240700f10340800588035150240024108050500208242c0b03a09000110b4038690660040540a090004890010755501d090002000482c4201c1d81c03600e00c0c20017000c0d810b60083c0c0003095030144900c00050710040c13800005501c03000685010f5020b01058080100507541007280c660011030a0404a00310306c0e01c070000420082008040e14040c00c80300090040c078030755040c40e242850344005d0842e055494844004c03030307a480701001c0d1840001c01c110340071011420306200c2c0010521012700980b416410340e40038402501e10720103004c03081200074041d5002e2401188038840c05415002d2000d41c2d40c22050400c000415145101c651103030700490a5180943d4618600020b50756801c807a1141c102d2000e000c11802d98031403250100b2181c5840441fa82d8818020015407040a4548884021030b032a1804507088900c290802000202c1094500307841d812480043c0112160003807400c601c03034407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240205413 1250 240204163 240204221
    0xa090503032d10080708030403110d02040b0d08030601170402030706030b1203130501090e101403161514070305040b090609030f100f020901020a1515030b07030c050c03070204 77
    0x102c01c803141862080364100a100ba10001d1005a006181c840000c504203070450b142d0313086a00d518001103101740c072102d65003411502c4941100e81d00702d100030a401035141c9a030501c0382c15948200c3c0c0c007a00252080316042c1003c50100c1441e800346070041d000302000c50808100343c006140c56410658040900b15030020000f100304006c0500c4500d000c460b00580e0b00e003600160280200350082e01e000c2e00036200b044101c0c102c04e0210303070459004e0712441081601400c00300e820010110014520103000d1000401c14501944c0710742d00d43c000a907100d02859000b01c10101c0107014482d0000d0001e0410441004045405800317406c8007030000381458905515400044e01d04a407a030703800e00454210300501003044055100b210b140d03151403102940303032410100c0000d440d2016250002c14024002c0010360005a05522079009204140d48e19200e06071207091042c03000b0002c17600307103000034100b455040c0c5540c442c1080d0342d80c28141c44011402d020140d401c000c09001400d2200800c240a00742e0004906 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240206663 1250 240205413 240205501
    0xa0215041a0f13030c08040b0708120c030402010915020705090a050702010c0315060c080412030207140d020a030f05010f0513060b0609150c0f240a09050303 69
    0x1e1080318400e4141110741d820703444074a40140085809401c1c90208a00a9401400b284000b6454a44000300e40e05074900786c0300b01e000d00d800c4144902d2000c2824410131040b100288003004042e102c03007800f5941c203440c0c0ea28a1004940007800506400c03810080440005400000510350380183c2e00030545842c00b1605071001142d00400c8142c4985c1130207501602882400c0300c6079013a140621008030405010710b8038001611036176042058090803d801d020b082000c0e200a8204164045900041030500030b41d220b038680a01405c08100400e10b0203e40f4140100300302055015185803002807464031454241010300704180c0d40d035500c0e9100c0000c107940b82d100b800d2240080e010904842c42c850304041089aa03070780c9100f40555005c2024000c80d07551206a05040e1b201280100d668007449100181059019101381d0300c41c0c802c1c500c00e80523500507040d692021450b00b28003141030307035200050303042070f62400c200c0a46541c00401c0407a0905047c5d080d00c54514214004c00c442010071800044506 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240207913 1250 240206663 240206671
    0x5030d0908030a0b010f200a0516050a1403060a020714100e121c05130602040f0626010612060f120218010803180f03011406030705030f030f0a0215 65
    0x2007680001006000803092044000700042840e0217040d0300c80c1c0440c050512078114407261101007101d0b19400d0401410401e250311030f075004081d103100302d070000d00844440a1900a151241c0602d400110701480d0740281c01c9038282c8000c008103207a0b190701c0700400096200c0102641d84080007000d10800b034008000003c80034010050014824010300052402c2c141c0c400040e401c0d010b41080704d4031006031000f0500c480018a00b5000910f0b4440981c0c034465402c504038001e0105001140010350b04440038124000c40302e0075260b051034112501030703121018060090701c82c20320000c54014001c0d076110701d003404c009000c0700c103000411a80720040d03115030041e00d83c00640c441d01d01d800c45404605000841c11120a80312104043d5075060000340b03500d034000c1c0800f0101015440050100310303621100a200710000241c020800f1140b110002070b0a4401201c0c624028820a03d002036141400107148030741c050980301450070075402040c1c60704e9940c42104010114030480007a032080b103006407403807805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240209163 1250 240207913 240207923
    0x2062704060803072001020c13060503070b0f0712200606121501060e0112060e070905030d050f1c0216030215040c0509040c0e100302030615061605030d09 68
    0x602588a01040141d60464100d01003640041c801440010045411031035607860a0364991802515040100d1800d182c100d609a807040a440c10103400c0366035035010350280c813019070660b84001e84130418408a48600c685820303c881003004100081101e0440b0405241c90700d26110b8851a00c0e52043c03c281c0820f02d250364559000716090203030380e240100702c41800030088405003a40c03040d8541221a101c0701440303003a090101c1c516402d4100d80c0710314845000011b4100d01001615103c0340c10b020f140500b11800c0022a000450124182c40c0009282200400c0c55a50314984100140c01c40702c5600028800c4807070785034003504080c0840f1640054410300e6908a0114000505820f00a2801411800e0213484148001c10310011a580d8030440058410965042e01c03191510320b0b0070400300215134041103050013080c06010f20400100402400c0b02d000301c0c121542a204d00c1d00840c00c01940140141e4031220030010003600c0381c2c00071020500680514196030808800301c003007000782e841200080310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240210413 1250 240209163 240209227
    0x1308010e0c0a0e011d0702010b09040f051e100b0301020403020604034209110a080303010602010f0e03090409030c4d060c0712080415051c02070206 65
    0x400750504002003001043c480259004075498111049415003c0124040d8104104030000d01350034000d4115031410140a4180c4106182c81d040284494130f01000440b481d028225080400140401001c1c1d4024a19809809045442d01515004003210350000e609035400780400800b581e035200c09400118003460460b0400500341001e1610168030185889140703802002c481c8085e001076400c0c2d080200d4a0000281062072401e041c5555040005601d50001802502003060000480510b04035074058000740440c0800340521030a4a200c10515402c40e4000d10030b0310520300e0241c001800c40c501030b0a1a503491049500c03411200c0f94002075491a00444c1081d08401000800356a446100120b50320b04c1150544a402040076441e4500a80302da04045041e046140090000740c0080066001c2041ba0f030b092440c080c034280e0028810048800c1040e221040d0040c0200100c03202080c0c40d0400c040e19040c0c04c507482d0b000790440c00701a60080c50034010722403100344089869102c2000104440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240211663 1250 240210413 240210433
    0xc0e0406030b01060206071806120902130c14070308060f040e0607020601150c05100e010e07091a0a0302060a03150f08010b090a0b06090607060f1103070f020703030903081308010e 79
    0x10349403100c0500880200018005003111600c8c3d680004415903a091405d01641c1c200d40b545c40c0c2c0680020388010358041c60034546100240b0701e591040d04031204984440301101030802e40082240030310034024012500300f000080712803410b041c0c10b40125500500010703020102160311481c0900803141c18001d40d1081c07005004075481e00e03803000515200c03840c18055100081d80d85940340e40c0a800c80c0e50003103403140f80f0804803840039041890311040c0c40080703905860b607030201c40d8054065052041c82c0051070541440c031a00700481401c0c00d5940150081e460301815100c210001c260802c05440c40913030749200402d00c0c42d2200c0c41e58000b000d0500000c075048489030b0070020302d2107001c1d1400c0303031a51410070410140c0d03c0e54020754081c15021161b01e5101d010904201020705001c0c0424883c00f442d04507030803d0541c903074001d14001c4000d03641d41e1880e4580c1d107101f60784d034899501000d00418071441c2c4c200006001d407401002000382e03a07526441c42c2c41d92a00b0060a442c50307100c04400c4c031b41003441c5034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240212913 1250 240211663 240211667
    0x2160807030c0c05090c120405120a0306050a080607050307110102160c05040f150902220905011a0703080a094101060f0b03040f0c12020f0405040c0501030c0e0406030b0106 76
    0x80084d0004481311615030900c260668184d1280741d44d00800104410005000d11200380070100400f90101e066541e00c00ba2080d00030010500c1d400340300e101d10840180481d0040700007a030240b181c10161a043c0c6075840340c6405403820043c10191030040d64080115030080e80540c146020201d20031034850007001e040c041040142c41545085480c110718000d040d098403005520001f00301e032412980140e81d56030703e081d1100b5110496520f5446c40109a00005103c03800f075021a04880241341621a0300c0703980090b154092150742c00180004d990b10020a01d20101036010100c5d180c464082d007050915140004103070031540c480182c02207000c0c000300b10501c24032140c51852000450b402004001d00309012191046d0840c0606000c82001200007010800f00c06044160580c00c8554403008039918041c120401080300720403070041035800c09466150926010356405582e015045082d801d0410004400420402504204114174260b1034006c90f00e0701e10441b4081d40c040d141c010010340c100500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240214163 1250 240212913 240212933
    0xa0210050604020a1d04060305060c03040302071505040b030c0909160207050109061202181c03090506090f12010225050c0102031201140a05120609060a0203090a020402160807030c 79
    0x21082c012030041001341c00007503100036100d00080d0b02e42c008410403c4d281002c20010910394000500500c190307000d10030b110700440091032003144664220364540e40c0b1001c0e00c2000100c01032400c13000c01c009100c148000000c1c100a503520440403583c0c40d00b0f00a200380050003039407003610301500912500c488407070783ca68184542d070003030300c03081c202103203d41e141c03000040c01c03607800b5001302031000c0e030220b408054403c4185d045c40381c0c0d120041c0441070107158040300c080401e60300130040703000c038500d241d00041a0504c0e406440c070005005085e0340466081e113003402418540e5416162242d5420850002140f03418581c4d0b860801402d44200481c411902e001c62400410305581815588140003126101d42d9601c044c50641314011203829084054a011501041844c3c000c81d900590003000e01210442c0050140e00c51803601086441e2500c885082c9400c0384419100c80100b6004401d444000d414036400510700c817010110144196442e644074082580c1008e02c040340010b564034460420f211a41d86 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240215413 1250 240214163 240214171
    0x30a1a091603030c0c0510090e0c07060509030a11010c090306150b0a03020d060504090b0403050a0c0506070c1b03110402070809040509060f0a1109010c03050702040908030105031002040503032505030a021005 91
    0x340200940c0310364200681800c40500c184c1c014227180c200090003072200242511407a6521000c148643d05003200b00f00c0d00c9420000b03540e4009900e981b440c44981c00c05003e503c01c216601c0c0c0368017440c1411602c0d004064401c40303020300008201514001040c1c5001c40c01400b00362030995005031102e15000054090300c1f1250300151255007090300701008110034407040c6400070343c1410b1056035415050015240b80e0407200c03010303000c0d002d6407080010b6581c008441c600520f2160340511740d1400e4582c9603004030038503404090440103170300304c60010a08060707000300401030051319a41d0500700e6842c00942a150119480882c0390402c10130b000b045404001c0c99034102014081c1403040c0e0001c81d80d507002500400412504100300100444280740c050001c41c2d0903c2d401500600c403020050420144550080c072416029229100066900c00c00791f10985080d113400601441c502050280060742c580f140d080d07560400e0280c401420005202000206800d08003a00a00000c4941c0c85d00d0318104c8800030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240216663 1250 240215413 240215419
    0x8210a0b0612150a15031508010e060103080a140d09120f0c08030c0403020402030f0f0603161a0405030f0a0b0105062b020d0204090b0f030a1a091603030c0c05 70
    0x4001c1d4402c142d4040510795020725407480090b10101c0c42d00000320344000540c40010340441408075518000d80c036402c4030700f840c04041141c0d1420790342c0d80409400c1303c4c4800b0078139009410100044c000910701c20000d0403603451914281e00302c55002c191558682d4842c620341c140a603580d603082010400f00380700700d10310b14460341001180304525480181c40d64003a844010415940040014080741c1080c040e60040d60b0094411074588c40c0c9610400744071a000d4814542c08035200f00001c03201d02d00090448901d1010300d103a100454500800e001e0b502822840040c0048418000800d25031420445050b60709121402081601c040c0c0c20481d07030104042c0c012a0040a04204150ad12411108007500100d491080d80c030f003080b84200c40100034094981519103c03070000900055808aa800030010a4022500d40c090741c1c00960801d680c4400040e4020034403250038101e043c1d00304883d14050f500c00c001c5415074800c0584d1110450a143c03443e042200030902c1402104140700249689601905040d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240217913 1250 240216663 240216667
    0x15062304080604030e04061805040c08060105010c08160203030703050d0b0406061707030f021801140901020c0d050f240a0c080c07030905040f020307110a1a0408210a0b06 75
    0x4824101d4030744000070f02c064240820a400310700740380c80d558020300091070010303040450300610700821006400c0940302030b1009407490002041c400300208001e4100c48050310f603902d008500366620841038101c10035595000f0b08444120001d61818401000443c2c4207079600c507918102d0003202e1040768130f01c0034810300a5151031010710000d03400042035003041498100201090303543c540c2c110050b08000f0352565165002103588002e00001c0c00c0400540750007621040e0003134400070b6034400d031070040e44080b0380141d1281445040d5404c14418000045020ba410b48280844c1803016900d44002c03c40c40c105280c3c3c0c88241c0e4414440e0601d201604490f03510820321040c01825001841c1080103424a111701100240400c1054000d15408008060140080c45120105841c403802504104d481c5004211035130580c02400d00c000c00c0070320031035505c81c0c4d07a4004d000c4800200600300000030320407148000104040300381503201782101c0060380c21030342c0700c080149071160710003080d1000070750150f00030041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240219163 1250 240217913 240217919
    0x3060f18070501050a05030a0b030d0905012a1101020f160e06011b03080a1806020d05130c06050a0309050f0c120a030917010207020a09140c0702012115062304 70
    0x440000c41d940501e81d840c1458403602c44030a0000144589d000c1d80b40e16100f02032113000c00d180c200c0052000c441090326096131040e80030745510b4455010f400003412040c51403090800240a01c001010214010310403208041680034140e8a07001c010000802038141814080095041408242d5031120080c40d206a096080069000b07260350703441c80c01070502030f50000007405a440c1758401502408032805c00b00440078a820008000c0d41b000d45103001e03042c18000090300340d114140c402c1420591040015070381606c0d201d800c84807608500d105900b010b46a0f00e2907004034108100c0c000c8148111005800ca40c0f0007001003280743c40e0520079506164000380f0015020a4102c40342c0411110400411400d031086d41400c0750082c490441c00a43c000714038540840d200075154065411440c880b032089640e0b840e66108115140552140240020f8050514946a840801003901e8071100c1c0d110100b100340d41105510040302c1903400140001c0c1c068025860342080c58030035140e002024440c0d0a1910742 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240220413 1250 240219163 240219167
    0x40801050a0e0d1d10110d030603080406030903020a020409080901020106090c052502090414070501050f0f070c1a120c0408070314070e0a09061a09060f04090203060f18070501 77
    0x20142203c1010b2040350344024860450084100b4507050f0024640d01111592400290440c040c540414500d4030450b000070903954000e20850041d01d030824600c40c241407070b040c1e08901604069800b10214001e100c6072000603181d0713003e544c130490f00c00d103000c94540900b000020300b107034884e0707010007e402d081c1080c02010b16000380413a460403024510201551086542a08440311a140000e401080c89000c000034040602c0202088010034070079102019510001160705002d25407984003220b500f00050072020ba46078006050700d5119081d410000342e99050030450348000c07014004189040000c8a031007100c512f808032075004043e50308079810276040104a0f0765648460000a04181c540b440c41c041400041181a0003003401c00841c08503850800c101501420300c00d5001c68100d405c0184d8280d205203008611078130140042d000720000ea4519040007030020408a12a130007956030913805026032010300c03940d4810684800c05d041107040c40b440c420391001d04500c040c40680c200010601083e0703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240221663 1250 240220413 240220423
    0x50c15090f0a0e0f010501021603050d080a1803050309010609110403260403060617061902030703020403020402070b10080f0d0c032a032c100302130902040801050a0e 73
    0x40040d500500030320500000b003560180c26800441200d980141000909210641440e05030307002070317007aa0701d501d04c94100785c2c61540c01c13030000415a07000b0b61200360382c151041030003d5106925050114601c03a1440c1110106190310300190f00003a400000c00c0f40c0c084090040c00010a0a00d85c100004031000041c40039034011408002c0100d14101641c00e01e80f0f05100c400180c111080c160307603940d00e42d60f10700b00c8000c055505c161112608440030010468002080b418800c003505d400000d644122900000005c0d0300007032110080c036509110100160b110740c4050503080388500140642030a26201001007211560310003001a07100c0b120f003240300d00c0c0100b031100c41102700b810700b080c40764010b181c15169003a07200b6041d4401c48605903a001c0ca4030100300202034040c0079032112441c26500c44030002501103006420300b110342c150b218403003203410218403403c4880c4107440c00501301030003001c029041d42410340c444c000c2e480e0045401e100000c000c0c421075800c5540c0c07800800c03c4110148650307840d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240222913 1250 240221663 240221677
    0x1303060902010302090901080109050c040b01050306040e12040602070503010f0207082b1e0b01110c06030a0207060507200a030c020111160602030703020f0c090402091806010303030207050c15 84
    0x1584a0314540d0442e40a82c0656115685c0240344004035a100c0315028002c19105400351224031602001800070705007407103802512441a586c091859030b555060102410480c41b0b03400a034494903200010324103000300540003611065001c0d00c65146800c041509680c481b95a22000c0762041000c0b000281000046420301020403040c024100c0c031040101c440500581841a43d050403c14105001c4d4004240300440380710141041101200a000444041388044074070a00c6500c8a00780d405c051908002466100440400c054501700042c3d58040030f40e4000c3e03804d0008144030300310316020515440401741e800030032a801404505002e48008003a820000790103810b104145c61501c00302d41c42441002c00c11400e000006000750b6407050007d56a501000065006001e406d907008001d580114184580600c024140780701a110390702003201001001d41112074032003990741d080c104507009008071802503000e900c0c0181c4030310950034080c0c00c0c0070010700c4542c4101d0200100d5001c0d121050203031000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240224163 1250 240222913 240222923
    0x402041e0e0c1e03071a040803040e04061505030714030f150403110307080906031305011a1206060907050c0f06070f09092d0e0102070804050a0b0304120807090e1602121303 76
    0x3081b00000030340d03141c803503a00402e03003e000000d408141c10105c800b0302c0c0c1c0914451501040320504040400c960441c0e0b038000d80d60701d908440010803c0c2c01d220920604120001400d03106a4032150108900d01071813074851808003107038001040185508810294840001070001d5490320f04241d6441129108584c0014403e020100100f0281ca80e07800c00008407550140013000003004c4904109265504214a0703449144208000750b408400401d003a03029507006003000e1140e44501c0310645061300241200314140c420b28075240e20303e4100700050341c0a05011340341d01d40001d8001c54001c00b411300b0b98000e00c0000341881030702d052580d2103d2001081d06030000e0708a000e1090688810050002c8003400c0c0c00a40c0049141401d005103500248104d803021642020b0540e513030300000c19680000c0740d010300410300504d07072400381c1c0d8000c692850748106a403504501440e103030302c0400d450740e000340c0b002800c2411405001000a40400c040c00407410401c074840d080200c0130860102d0b90035a4000104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240225413 1250 240224163 240224189
    0x601050411040b0a021506010c0309150c0f140d080f060d1407060e040c03111e09090405030702011206051507050f06190c030903080402041e0e0c1e0307 67
    0x51092050540d8050011500c01950743da0f110403000f90f9420200c200107551b02004004503610b50300503149140e22660503102c804041c0d103007402c400d214908200000e01409006420000021201c0800c100311504c20b103070000000800043e405d25000394540300740e0a1200ca2010300551450166829900c09400c48a5520f00a41880c10041001e003d042d103002e280301d101c4021a103280c000c41c59000c50503090750200400214090100d090360f03400e1400380c42e80c920800440d88400c148640100d40c0300680810075103021100f1002c40c000c00c3d012207003510960030214a210840da400000c0d601c080000c00c006000c5c0310306010000f40f07410041012140e1500c0000b0700c4104108080c0300b0140c5a149101c03d481c510701d410212500300400460040384038924005994050341e0080c45841102c41c0c01d0703070390910b03a965141d0a100c02800003001c5102070b82184200c008080d9070500540e405405040c01902800b079120040c4103010100c00c01024000503280c10700c1c034941d1000211070b01100d0720052920 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240226663 1250 240225413 240225431
    0x1030f020d1719020f070e06060703170408070b0f15040b12010c1e03180303091529010c0209130f08030109050421020a08130b13030203150906010504 66
    0x80e6444010704418a019070020608034160102c03100054100701e460340030b842025552800c21034981b10203011300000710380e658010483c0d03810007401030400a0701c04e007000007000b001c400101c039079580d0072541100d00480000d000000c1010070045540c120180c0e282403030050612441120410501040da503000c7e66580a108000360707111201c0391001c1008800801c00007040c0c00c0c00a020801c0f10110200e14030700c042d4004001c0d4824841c107020500d5100000c6c20011055604401034030340c6260079540800d01030300c80c0d0074501a51141340c861901500e840c00c03030003410f01007031404003100c14115818011601c0c02c000258640c03d0fa801d900802901815500019038501500d2a070b41218014005070303004400456012440c0c5e0206020300d0242c0c1081c0c002c11141c104100080040450500050300621100c074000b4800030060401c0581224021007419107640f0742c0906070b01702d141c03150360394048181b0400c15401c0a120803401c90a01c2140e685c4c403890300d00c050aa07500c9042c4202c6020f40e6582c0c21032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240227913 1250 240226663 240226673
    0x21b010302090a03112805061b010c09030c15020601180603050303040311010609050910050403140705100b0907141e0307020d020106050909071404112205010801030f020d 75
    0x40d004900b0003041c01181070b0301c0e03040c15015007817202d08141c000e50b0302d0300c0d4503000421400900030001c420805980725007410041800f1080c4c01402102e00780c2c03040b03079149240c8490280600c5140201c1a03640e00100d0b840c50a012024084c280d00c0500a140d00b02110000030b5804101281035801c0314506100e01c0310000301d200010845944050b1480c00040144010154480b8a0400100d0044c000b48611529010303d1402c0320000d44448060380d101100c50090b03003425400c0303176902a020b030070001031764541d407a10001544d000c2082202d00d07070822280f03801d8001c0306202d200761407001514500c0030f0f481d02d41c07805014001142d00114000102084841950740b9060820102c0d6001610803900c904107004080e58654803010600059406e00d00003007030606104c11820f219007810300080458518040000002d8403101e02880d4004d40c45904090350030090f00000c210b070a0303204c68020f031a42544100718108442c2d9421840c1080329180040011424205041802c40c0d01182c8254104003e0700d02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240229163 1250 240227913 240227917
    0x6090504052a0a1d0108070305040302070e0c040807090b150715060e010815070f0521040b091207080d02030a021605010f0c1e180f0b0405040c050a021b010302 70
    0x74406500445900260b14400c02c050691041651200e0080304044100c070158880649016030014204200180306244240c00050700309020740151100e650700c4000c06168020304940c21740070254000750030004d00c0c03410002d000080000700010000095000000b139210084a08403c0c07100c14003007802024032500400840342c45408400404c4070503903500854000102c01d100e03a81450140d04882c0d20107694140881c2c2c0310303020b1a030714002d92141501c001d85040c3c00c074094510b44409842e4030034451208c100991400340d4004c08240385285800507001d85008048800804024000c0c8000400180701c0400c4d0343e041c452041c00942ca0f55140c5220300000c1c0030341c040e01885040c05d98145420f11806600c00d040d540c0c0354402c140b11340142010f080c0e4068a04132031300030b50503105501c107280080c41070351800040c8924084040c01c403030ba40c1000d4001c06055800262180b000010100800d1a15215942c1010100e05000d42044c00004000c0e4842c1c404c078119280c0124140303012800c40e842541 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240230413 1250 240229163 240229201
    0x60a050c070f030c05030120030c16050a050607110607030207060b09071701290d091406070f0908030d0c020705030f10050a020405130b0303161103070f0609050405 72
    0xc4501e120b65801d81e141e40d010300ca200a036a10b1101a40c041910306060040c01103020b01801e85466480a2000f81401584001c246181c4138109200c42c1c0e025902c00c0741e110201c01e000d0001003080740b0f00350820750700f8030728080c102409202000c1d00740b40d8803941c00f0070100c0d0300c810302c4d080042c4c9420407820b202003d84948110784d0f42c03090752081042106034024132080b040952403002552980e0301c0b84080200b0034079200f180d004100654130392006d0184620010040a1710544c000700d0a44880e6407104c0d220150000c000701e03103411050030007820940c80b04040782d0030360080c07805041d642c1c540304025443e44200d12529101688405100805600801140c0c0c01850090101c45400070220452a11032491b9680c2d140424104030100b003843c00d0354000c0d0780a41e000146503a1120101443c01c1c0e0080640b1602d90350540000c1c0b0031000708804003c1003403909401000c0006181d0014420581405c01f241c22000403201c0614080c070070b66512040c0d06060324000c0c1d0f070000303150300c803981e0035046010002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240231663 1250 240230413 240230437
    0x19020c01060e01080a0b0a020a0522050d081209030304020f010309020d051204060305091b0d03260105090f0906011a090307060f09270f020702121b01030911060a05 72
    0xc0113000011040111030107105a15180e1300d8200c1a0000d80c41500e00800024000303001300c03000101c041e6080f5001007031a810070002c00c0d5860011840c0c0049505c400d492026000c0b070710b51401d091007201c5503401030011020310315518159001038850750110740c1060401da541d007034070011503c2d00165240c5064002040b24002011400010f98560103405220000707418440440e03044540007030070210078244c1d5629290300480010500080e0810340703c040e4204800c40d00b603400c2115503074402c003640703440003000d02100d0340c10b2005102d007405016111308040c218860801081c10030202c4d42c2410348401c100e018004806d440001c2d00c41d801800d4400d40c2c54050f803440000c40c190000c1c22180c0303900403a1500041ca50369034080c1040e000d24413150340705001e5141f00710303040c00b1070640c031a088400c41c1102c0181048101e4022a11002901e0340046042e0f11004156101c1d5405008030074080c80f0919061101d110141d03101140c007812864928060070b8082000102a405907003550042e007641 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240232913 1250 240231663 240231689
    0x20405040615060306081e03120103061d150103080c010e03030a0204051512041203020c0d0e0a09020702030304030206211e01090e15041b032919020c0106 68
    0x140c106080100b01060046900c2d007002c0000140c0e03140603001e07020880d55008060310003103070210015481041c01460000c07c0d400100039400407950ba02d0a510b002e103006074400200083c1d40c40c100070141d52004a58015640b110703150f000b4000ba030160140c1580d9000c10701783d440b030160710590b48c09454440b4510300da42c0800b20800040c116942c3c003a0080390350403510803101d40d00201c0480403c0c8188640c10312845030800004010903241040340ca6800101e290040c0b4151180030094205001080c10b50700150700010401d880e4608818203c010b0701c0e2142c0c08516004081d80002d41da44690b200090103004049000700c80028511440f00d01880c1c2d0b803980302000c3c503099040410100d00e2003141151550368000120302484c0038030420004403403240c0109440340800c003840c2d118030401081183c003049c0041d080b0503165100d82e0720030021845140100000c1ca000a4400360220001c400450142030780020003145000c07c4500103542c1903030360740040c5e58624a000103405421180c00c40c407101001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240234163 1250 240232913 240232921
    0x304050604090905100917090f09012c060102330408030709061b03080402150a020709050c070b1b0d111b070303080105300c011115010306020c0109020405 68
    0xc3d04103280c914814801d403442c80030440080011110750b110b0281000000c06612082030801000a0000c1800140541d02d0708500200081d5002e400746c00162200c549800782401080404400300c4070b101c0040a000d076245071850000303580e452400a24410000301800c8100e0340c0034803a00301030503002a5440d501182c80c203810a80c48641c42a1802000513040c1500001c2540c0708803403052610b12418018440e2030b40a4408441d00e600c098803d0782d02480c5443e51481c0d41e03110320b004124000c2a034000c3d00c14289000304c1842100c038010302800c40301c4410410f01c000201c0000000d54001100d01412088035100201d0b020b05c1e005a00c80030103180e142c00d803a03040d82800140030b4801508002111009980c00070441d5846a82c584801808034aa0303800600c1a840c0c61800d81005601300003c5050061f03800c0c2d000c0725103042600210819800c085400310395541c0c010311800916640300000c06000c0301408c03040e200301da014403026001c07940c04210501040000e4100000b0581c0080c014006420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240235413 1250 240234163 240234179
    0x9041a1507150510180b04140115020718020c0321061c020906060a050c030d090311060f0a1e0c0807081807120501090f051507031107140304050604 65
    0x400101e0640740c49a900201c9840c9a0741030040901c1181d000036168000d0b032401c00310100c0d186000e503100c0c0d211a280c400c0c0220701d454a105280681c000009699143d52502280e00e40d081c541c81d8402045410141e070900035042c0388003444804001260b80107994a0021110504600890040715040ea0060362481051502402c1090040030104d8113950003492100a40d0100040c80c00000e4002c041440082c404d803514a026115480050810502c3c040642617a20704680c0705a03003400c44290784543c508241a8021031010120300c3c0840104024101000701025500700107004221403611607140c1628200803d09034031088051450038042d14204800c00362103050300319045000100010000b85c480b02c01c4c550b056120321072240141400508140c10f03803800e22a249025981c642d00e40012034005546034040b2044070340220080d2030710044034801a00c1c0d071507011300303c441054240701403030315030071451030441c4e0700140c0c00080c460340004035048a600314003e43e44001d41c01500801c000800702 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240236663 1250 240235413 240235417
    0x1b0d020304030512072a05040609020301080105070f0c1b09020c0607021006061403060f1504030605060103091a282712050705010f020414010f0207030201020309041a15 74
    0x42c0c400e40503142c05020209034003411703011349a00648017540d806154a0403151040068044520040c2d0f560f482c1915080440e00740c8085030700500001da80040100300001c000e100c0d0700d411118910303241800240c002001841484011401b50814001c05803400101108035140001424520b01c10354a80950703945868071900201e0380080035018925044030602c050f489900191a600e40b16082d4580039441442140e0304010603160b002032107403090b0b03034450b590101031001041121841c1c95403142946440002d840020b801c25050604000844000811040015203a001d1420782110260b84207149062680401d80e41404030382110290915503211302d412015009288410f10121042c422018401c1c50300f000038080c1810000c0401d0584440c800c40080040314040c0b8008100025840449800c981c001e0340000703841850803140062958222404600b41011790019028062440d00044e44a11070203549078421603642c5d0000803600421440e5100011029280c0b221204400340c00303c60503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240237913 1250 240236663 240236669
    0x30102070b0f151f0e151806040807030b011a090307030b0402180a0c0f0503010b0406050f0408060c04030b0108151506131404060b031302010507020604120c0317120c1b0d020304 78
    0x610708011100345d4148400e910b11030f1800d10514600c2c0005a2119a0b60042c82c3e80314694018010000040e4202d4108080c1018500507a0b04c50090751400505001103042000da00c21101c905220b1400a69400b0a810b03040701e41003655130149681e01d00c00207240451940300041085c22038814080305030103075881101401c074580c543e591035200800d0103490fa030000b403007680c00c0700104020510540d88150040c03c0e01038807400e085418651a40b80380b5081c540c08840700701c10b030040420200b0030700c0350901d051070040c26001d000d4442d591002c800046d003006c008105c074000b6004081801d109032211400c60f420002442d0382910401c1c0c07100850060450440c428900c940c0c207100c400300f102600d0508483c000c2141218440803440c40e540151580e421400c02641e10246c240800516180a501014a20351144080c02415825440c04442901c030b04000f40c4c4200c40140040c0381c601e6203980c00030b908001010005500c440c014a003188600a01090f154520b004d078508080f160350300000a0010703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240239163 1250 240237913 240237917
    0x60f120a020406120f1e0209040302060a0f0b06090d080d0c0203180306011d0c0d021c0606021204050f0a0911120604090f031214071706030102070b0f151f 68
    0x290a030795050103142e013400c12070042d120002c598040c02c0050307601c2900c20500c0100d041e101c6074070700340c580004406600844095003da00004200100840d0034031540b60826040783e0200484105400030585a011750010140142012485c040038404204250b409a00f000740d403c0c0215110114004e45a4014401800010251000c011220703d408262141a101c160401d800c419000b085030300200c04010b03241905120f41008521040c6102d07000070a400c0c05100c02d2050210340c018040d00c11112154002d03c11900100f801c40050640c1d41d0854007203440840358140840c6001e0b00140b400d158603484030780d800c0c0c130303025000b1051000c04000e011480c80144800c5101d50ba10005d01c400d80b00020001000948840032110001e03000300c4921001c0200c019002a01300c9400e103a00c08031201c1982d1000c0403c0007000c0c00b8854540000c1c1c12030b03106074282e00950411a240e0750707050b00d0f17450181c600e41c0c00d0382c10781001500d0001c034400513591012008083d220071051140120342841e084040d4400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240240413 1250 240239163 240239171
    0xc01060902030c0f16023601060e0f040b04020301030c0519030803010513021204050309130612021c05010c0513090c0f051602060c0d08010e150108060f120a0204 71
    0x50303060014401e407845400707048052480c000880341124480c0e400ba03d428000090315011540258a45400d060074403000482d4103405a02120f18490320000c2902e036115400d07440b40b0051040d903a1021000c004e51005541c0d111a000e5a00700040c05460551607060b006807002c0000814001081081c0048510645103e89800506020408081d0841c0400342003d0701c00c00041100d8100f041e0700c500b40300c140030740c0103007010302e035410300e081c00e003c255010390300d550000c1104401880d0142c00c0d802411800c080421645141000040e189200190701a10442c0840500f0111000e0400d58200c455406802000003181201c4040c1842c0c00802c05c14055880b9404049940c82e080c1c803070421190f84a0f00c0c1d8a111440c0020304950640c003500203032041c101814041c8005803100d001820903004070402801d06c40150000003081554164402c4000d508410b0030b2050311000d54540300c0c008482071814900b02d94031107001c0b8140003c2c40110a80041400c8101441900b022514090349031007201c040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240241663 1250 240240413 240240419
    0x4061a0102070e060d0201110604030201061401090e011203181701110702031b060f040b0309010e060712090819030b0901080601231f0c05150705040303030e01110408030c0106 77
    0x207941d00c031140180040780964001081c01485c0400340162040e20503d0718050072150718060038209901650210007503910380c00240310441204c001550780030740c20f00e0000c10182c500848410300c0c20040c843c1c0b1041a584401d5541414420524600c3d000103501c5005c0c1a180c0d00d013010912200da5400081c5103520708420800f54102c600c00b1900c0194008008110007080c5c040010ba1070069003c0040d44040100000130701c0415000142004050502002d5103e20b02040400e080d1180b8200c9809070350008800c21071115008902c0812003c2c88042c0010304400c18902200709100f280c00090680115a44a00c020303036041c0c00030000524203a0b08904d0590307850484580c1d807142805020034428202d14814450012000e03d050047c5005100e0010400c011103012440401e04035032800003036207803014000b4048208070490800303004c01400342c01e0b40f0741200010018040ca00006082607100d89005035603402c02d41003d509110702080107690f480c0d451078290350366072200d00cc0c41844e5081076000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240242913 1250 240241663 240241667
    0x801050114060c010b04050c120a1404150204050a0b19030509120c070306051807170a06020a0309050f01061e03020a06030c05040f090203041703061f0210020304061a01 74
    0x890407211121001c100030424041008070981040a15000966036a04a80310907501c5002c1d0038003603042c84020380c3d0346407400e6011150759003000b0302c585510340c2804100b480000103006c1c100e078000c0c4c1199070f0042d0440940e0b1417602901c1307154400d6134003035881c48000c500c1e80510740040040107403070011500e100800300c00c160280e82003126103000a400c030410702406514030400825040d0703110ba05a81005031681d41d081c0072031310103071451440700c1341d4050030070310030710041100e04050802d8282124501307020800507503803004800c0d00101403e03000306d841c540c154040e400080c00c0e1076000c401d403080b80780700c000414000e0080d4070444044081083d08074010030060800070060700d030090196400e10742095410740c040c021141a040400404120000c0d1b00307010914114041c0908201c05a540d003070030f050010207841d40103030211080d079041061240d01d1b503920007101080c0e608040b5000040c120004160f0918410300d80d0381801074000404c01042140503030105c1f00c12103810f410f03a0800300d022001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240244163 1250 240242913 240242921
    0x1031d0708030301170a121407051005060301150b2b0c02010b0102060a1503140715020304180606120b0a080307050109051b0904060b0303130e0a0507080c0403020d0501020708030403020706090801 86
    0x15014287c078460413245603100d00150341803044800485841c2080310f030340ba0f81c580203517240000c5020781d6440a0000a2500f03002e05941c040400c1455070a4504100c2c0e201c9140c8503103154800c20010000074001d44604800c0c00d204420900c01c010440d81d5031200029000e072400780c0360b1a00500a00c40000c5125642d4451248002102184102c072241503a485202440010710410554864010300160980d401401c1b0401140c443d4003464441d464034000e1690280c00044030403020f0b080120038032090740d000304d9100e01a011303083d0101d603200d0440042101040d0f660410000c44c0400075428045c0841500700d03141b254400c0c41142c03424030150b8505043c14a00c4650507a11a0900d0701240120300c0c076801c40d808031000103060381d15180b0340c21440341c50340c411584402400308600d810440345c440c5c00d2140b1940b0100c1800c00c01c0b0a45440d00340c0c01640d00c1607010088c41a1008500c0344103104c3d0941c15624500e502000c034039500d0030039060203540e400c00c3d441000005406107201280300b20301801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240245413 1250 240244163 240244183
    0x5010b030c120a02070605040c18061a0d0e071e09020a0f0c050115030b01080c0121020c03040306090c0806011226130311011b0c030201031d070803030117 68
    0x218190a01c558489007180c42d110140010507601e03002c2c0700f15004180c25109590246101d5021000b241c0d1a2480981d44c4202144035101c41034038040c0c0811800da0003002c42e4541c444240111039950000303c00ba0001010314800c000c00c0d0b403040580c0801c044a00591244042d00302c9002409084c1d0395100200581c411150fa21001940c0520f8004605000d600c035246000d10400c0082881204c840401c1c4400046034002d4500032201c0380100b013194003d010344d110701c5400303281c602503860584c41031881d8410380240307520b00181d00141110600106000740c8001d540d1001040c032005240c1e007032031588610785008031344003401408000144003d002c030f0312600e1a41c0c400001140c1a00020000c001c84800707201c202c0c4034807010880c14284258811454000e50310440700458803002040005248210410080040c2201e008001c404a1181d1455608590382440d010418100c0c041c01c080480ba400601c10301c10f881480804941c0501c04001345050701c1c840d401d40f108010b525200390303541300c070400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240246663 1250 240245413 240245431
    0x230c0906030d05070503271f0801030b0a0b040501080a0c06020304030f0605060d020319110f010212130302220b010503010506180111030408010b0a05060307050d020705070504110d05010b03 83
    0x94003580ca0060000c3c0030070600031803e4a042ca041d000c9005403000880034000000d21090200381c2036454400300300400d03524451003e08200232020350141c0000f4040c0000781210310988009441c1e149950040c0000d9207015200344440c0d692229184c0e03032129422400c50f03440b1001c1b400403661510000035282225000724480602c00c9164a07440000d0030301405994203c081585071b500541c40401c501203603003104012000307541c0214140403c1c1c0b240b10441b0f4521980480300000500d80e0700007001c500400d50700f045079a407284c40910a4080e1142e65100940080c8402507000c0022802c0e0021515101207240601c00c5440c5d0340e0044a203488240620703540468188210045601c2c20791903225a5601030400504d5482500c944915680050b48602d860340c1d100c2c1c03d2a0f03c1c904082c810b00000703110a89a603800c504082d400a81203004d4248100340306a8081194014002c0c00c001c54070013040003400c2000500c1c602c01c80003038517901c07105028220f1420800009100c00007003040ba0310550440e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240247913 1250 240246663 240246673
    0x40b0301270c0605091003020c0307060c0503060f060a17060a050315040b0a02030106050406031802120109060e0c09010302010809031908010512070302061e1308030301030201020d020a0b13050a230c090603 90
    0x6c40c0064000b07400045051010344030600c0b070100007038802d10502c070340c01010392541511313481e02c036040000c1e440030254005d0190784103001e010006500f014450075109152114040d50341c1d503160100d590090360741e1100d9030500c928800541240800d00300c2501407801804084455558022400d0030380c442032103a00000341d01003104002d024842e40c049181140d051030002c000169640000e400c00382244000300207655104054010803605204079040e150009024090494103c00010000c65051001034180104103000415200c41482114205d01102c250f02100300c0070180010054131003401468020101d0403a440e420b883e00080210440380d0040c0403a242c0148081c0802c0040000c4281c04094081449012400b049480d15080a001284004c0d03403290b156000092904442400e01d00030b5402080c000c0012400011035542d00407001100c42c3d1880c4444c0c603100d40781c00d100d000090010b003980c400d1401d50a0904c001844000d40507405c41d080710440e0010864403403c2510410303899806 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240249163 1250 240247913 240247939
    0x5010501020c0d060b12030a1803020a12050f10020406031d0607030e0703020a0305012003102912010311060f031b040305030a050d061203020c040b0301270c060509 72
    0x100c00344102c18403a20307001c58485c0c40140410b050a4050f84909032075000866000e1032141d01107500c42c20a00300507002d400d050700e1070b00412201602c0e8015100b560030072400c14414014100040c40c0c51300722410890308044440840800250014054880001e08002801c01c1e0b4440503400c4001c5050880060001601c03888003d40050070124080070050243e1300001001d82e440784a03041c01140a80004581d40034145404020b005600745080d030b1189081c401d000c010181541d0200981c0c5066403001c9855000c0f007450210b113003891585440301440015400810b5140c411310320b040781d200e009210380040100c81000744500440c00e004008003020b200207000d400042c0d50000140103d90302d0145896100c0c0c4800c1c1c110b52103120f4010102c0c100040d151a00c4100780b150400134000c8451444041d00c3c26130b40291603420312402c080c82070b0380305c24114100340e800b0751012030b480814a81410700b200f00c2c002c12a88060440c3c1c401c1d5800070350000c2c00100140030b03500712942e61038000c100007000d0380 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240250413 1250 240249163 240249169
    0x17010906060806120708030a090e010603061a090d061a01110c031b0a0902030115020d1404030f060608030c010b150301211401140105040c030b0303031305120f0901110105010501020c 80
    0x6030705074001607101d0500d0004204009200a01003103c407540c0d025201c80c00c0120038410550103074003541c01c0dd0320b0003008011000c00a03e1510b00740c0c3c83c3d005681e5446500d5030010310f000312107504c054585481e1018030090110401d1110a0b6030741d007a200e06020f20384100100740c80301414402e0035095048088030840344540e810308040840d000408440d04070740c03507200b50812030700241c01051101c1c0c01000351014864040020403044121860581d00705c60b658490304500f4025407100030480d103540100501007000c25003021000e0a141c50403039442c0d64403c800300780070700550080c2c03038050000f00c0304d43c0743d124000c4403c9a0603547c1811810f4a84480b03ea10203504040e41d0009980e0340c1800c0d0b481903103046080c01a12448600300a84250f65410001040b04840b03040c000b076401d061034000f24004903240841601e6105510780301004000f581c86c140385052910960503003a14900020b9241c8404000901030f040342d1400380e03900740703100940c076100c3e0303003201c8003030107800c0c05030f88130000c100d41c585 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240251663 1250 240250413 240250429
    0xa08092803030216050c0a0e0615030c070f11040612110f12010906060e0a09170f1612030e07030c050d1515030b07030b0f060a050f03010617010906060806 68
    0x20303100b0700e8018941034107040414012250041c080310940c01c0b1005030581e62400701d0b01003010700b480001303241090514200207100300700d0001d4000035a46010000071440f018180a83e48802d4001100303800c4424540303802da0324840c00b504250b214518281d0080380103941c1c808003e441a40c004880300e40c1e0109a0100300300e0b100944261a8403503041c50103040002800e000e0000c04601c035232004a0f0072400c022606409002c0203080459491815810340046041c1d600200c003059034040318079644580e001500702051140030310014074905607440e5581085540c032084120428666810007100700001c8a09458601c1484003418070144403206009134034128000d0880a4425843e904044500048000644c0d000c0403554001510b030b16020001e105183c07006a07403020140c90b041210541080006440889252070f9a00445002c44c0c5192061b000700210b43e0100452800305481e980d60300d00042202402d11074506c00621b84100004955905001c0c40301582c0054560404983c4c2d450244550340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240252913 1250 240251663 240251743
    0x110a0206251b050a0f0c030b060108040b16090527061807030b0a05041a03010f1b080406390216060c05070e16020606100f050708040e0c0a0809 63
    0x58020000548001011110b0a4491701c1c0300e2a4201e56451860900c03505e20480107003d03c0c18070585004004c00248131038a16a03001c80e8000c01c440300b140340400101d8407002c043d00300d181c00c8080a0b461004884003a481c1b048001c0303003424150243e643e400f080c03100d0701000418005508030184081a081030007900440d07240b42014040d0401c2c19aa40c00041c00d55802c11303452030350705222041100403803c082c0500180c1c0d182d1210309004440c1d500c1d042c0707020301c1d2030300f48580c00300081c0901003010004140c03c4a0100c11303907900c85c4036607403000d50070303944460312017001140b0f1214036039410300402800400c0c00d451815888a040c44900c3c82c1c0b0b542500c0e6610413140c22909800b40980100702803070142d80403030080241500b0844649002c2c480603180c944041d10440c4580300c0c00b15108109079214401844142562514507103c2205180041c0640501d412002c0140050f40c200f15046400c41e000d0058000ca550724580c1c01d031104501c180d01c0d5080b00118000459201c420004010060a0291a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240254163 1250 240252913 240252923
    0x708030c070515010e060a150e0102010b1215010e010f06030c02100c020705011107050906060a0909050c0304172701050c01050408090301060602030c031c110a0206251b 74
    0xe41901566064288090075244611807440c03c801408850f08845a09904c803a054404845c8242049880c500509800041e441002450b205d030031540d074400c0d0840e482c1800041e024410304030311007440c0c1ea00c42e40a500c109111028600000450006940c056412218165010034505080140c01c4000e8800081050103601c112482000050658840c5405940c003a601405031541090001040c1030f8003200400015485804203000c0c9986a184d8a604040700311003440e520000e40d40145d0701080c0303c0c0d0000703030308501d030504110342d00340d2100066214a128a506000001004080380000d02401200c0c901d40d5440704034041d00550051416814a6014105942444485034502c0d09445040700e044a09000c08202c85019003406d00400c4094000b5001650800d00110045540e0b400f4400804020070114000c4501d0713a50144d00540208440600007070f40c0d040200c1c1c019603918415a070000c1d0131614001a640d00d50700b043d00c501014070342a5281013000016008140050050b02c1c42529 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240255413 1250 240254163 240254167
    0xe011d090c0c060709090509010e03181503040302030307031407021e160801020705070902030f040809060d0204060c0b0919032105070207090c030911060d140a020c060c040302060708030c 82
    0xc00c00c42c08002a510642c4165030340d409641c240306498054441c06800010941e040c0000054180004001d8500350807003d10a00c0000c1228400140900d98a020348240101d0001c01c2c00281540030004522039030a6071800c1c090200303002068a0b40c010f003120040d0061b00045001980c84400480081d90764400740b084940c1c079031a8960315481408503078810b0005a5001904504000003840b81c20010490000210300310310b030000d1100b0541c1c1d80148001d280c080c000a800300c0c4ca40c0e030b96040d03407400018050110340b110340703032000900321000444042e1050050036000406103000022101118150305c0021803803c01c3c40e175001c1c3c1d4900c0d44410721502d20a0301c2c0891100d6a03031700744255445201103a005040303180c0b034502841c0c00c540010301c0c0d12040505000c2050049050107801148042c0300340e6009079101d0401540d04004c1c541103801c1119410900c040c400e02d604250058144a1990026240a0b1721503d111a41e40d22a0384002500514184502c034003080000c0080d5501c8042d24000034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240256663 1250 240255413 240255427
    0x1a03090f07060f080109020a0f050c100f0c1e050f09010c121e0206010506030114040906050c03060301060f1505130e0103080706050906060117060d0b0a05010302010e011d090c 77
    0x182002119040b540c00114a142080c0c0d00c5548140360a0040040366000c625188031600300611070954100e03140184000040c600c8104041004444142d804064040007040040301980d0050202410008002183c24910780baa690050201a031110391300d441d414039184030301024030243d070048080b05060000148110b40894520a810898001203540b1141c00e080c0352001c1c10301580c107001c3c01b4021584080c0051040d626240300701da054400c1c0482101706800380d80b0000d80030b4008024000c0c00103003040c0c01c0c802d80c40c40c1d010140d406250224024402c89444d00c00100700c882561042d040c81e01c00c01c0880c0c40c07046008500900c9255000100000d000d500e501d60705c0101c14080c1e10441d1a44070002e004400d00c08680701d00740d00f11001c400076011505041000800794103da5440151307074600c41d404591145e0b600700c0311104031940821b591403a4a001800000140024403003030740892605407295186600c1010000b0a051500e03010b5040d004010040c81469a4010190381241c40d01b00406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240257913 1250 240256663 240256693
    0x20a11180c0703021c02060103080d020c030c070512010c0c0b0a0905030a08100f03030e04050711011d010c05040308040b030403031d0610051210051012030804060c08011a0309 77
    0x4a445030041049031075482c20940340003858291701e046900c1c044500e45034031072442030b80400e6041c1101e801c01c540750b8450200414600080c0300d800c007400c449101c0028035107090a000b05000d02250401c450803a080c2c0000b01902e426100c5407469880050704803030200000031205102d844d00b0070714110001401c24035aa503000d16681c001105140401d2032442042415505007040c5005010b6058407a1300c50b40c915580a040c030a00030f243e10744166102c100003803100d44142c038a080a041a4002404074200e13818820300f0081d42690820403035424082414002409070f412038044981c40080070345803e207000612405a00080c2049040545491510705401c40040315070341906400c070058501070519840604041181d1b0b4401801211014469804c145010035105581c400700100413506941d00705207160401e1f640d0304410740700202c0000300828550b1084000340700314400c070360400c0801c4160900b55040c0b0b50034401ca298440282e20701c001a062050065034100342034400712222000b07012a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240259163 1250 240257913 240257959
    0x4061107051524010c0501140c0a020717070317040e0a0e010c080114240a08010e010b0310050607020f13020d060e09030403140712050c150901020a11 66
    0x1d60302036002c0e04180e85034184000415030401c164103503411080500c0008245240d00c860049414070140c04408410301500f074101c3e203c0e040880c58160320520f85061494659001403401300018410840081180000f1611a840904441c3d00900c3d40d2840c680d901081c0c1502030100040d50b00c4240000591000703640c0f1340d03038001c0250002c0401c40b80515281182118a4000c0100803c00c40c400104007003103414450a00c2d480058444001c160640788088050900c4c40d1a040880c02c0e000402360003140d445074016040e241c2202e00158140d07a01c600302c070900c0c00155241e003140d100326081040a858031400a20311144094000200c039020300c1d001881200744114000181a00010500b609403281d00c6a40090300100001e8102c40c209840c1081e564062800b0050204070030410135000c40504002150003088200c4007114400304904c0c000d503c400e03201c2d15142c0103811000d41d40e903680c94101c041e2022044180e0042c602c0010b00d031203405012001800f41b60300100040d540d04c490149800d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240260413 1250 240259163 240259177
    0x203010806011505090f0103050c07020604140909060f070305180f0c0a05030102070b0610020102040e07020a051b10031a03190c0905160c02030102120106020a03080106030608070e040611 82
    0x102514056240140c0350301c42c00140001d107810002e081198042503030ba001b0022514a10a117800600d550702c07c442e0b501c0c2c0c0e2244c254045d60085000c0790006405c1404040814148005d861500d03076921a102d4050b86d030311054441c90002c610100001d030034644241c3c080da621180d49160b05d01d441c030fe4000603d08220300c0f0f1141c1d00e400d4014500910960038040004402000c040e4000c6103400c03425220608d56510203004580b0501140e82000b1480707200350184e8029106140b2496201d0411a001a6950341440340440302d600030650303214040c507904505604104000b50040d0420221648100e00074140820000c460484940500c05646c40c204400040008614018600c22642e4180220003203546d5101c1e080302801d000410540100b02c130710a8545981900340441a10540c1c0b0000c0d029010b002010a140c018807000010800c1c2c1c005401c60301e0f0360007922642e0813640c95003800c0301541d801d40a55070699004038000c128145000ca0f01d20740c000e00a510000d034516240da481005039002030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240261663 1250 240260413 240260429
    0xd0c0e090f06060312090d02091306150b0a0e04060b1605060906041a09010f0908090414091e160905060907030c080f042306070311250312020301 64
    0x10801152610800003031104600401c010681498640000307a1755528103581c40c0546040403581d550280c648100c2c0c0b800083e40213007010307c0d13840d05100c1e101d20300030380c1e92007543e003241000c210001610703241c5c2c0703d40151408400b900d45003c403118020349010070350050b0b03150020395a80e0f00050b000b640102902d032000c2200382800e0403c4c2c1500388189818805800d490b02c40e00319a083c000081c4040904c1040e0040c00a0300400305e650340031340140140750500707290000508100c0700768100202640244400c031000c550800c02c4940382540408501001c13155070059a2052404034250200d1803a0001c0101024007190707281551010000e80014241d80400b07038039510342c4140b0000380b51658840790f12494525040142c4101c218004102d01009400400007221075400b0405002c099115408400140d240038030342c0c0f454034110701d56600c00031158800082c2c90030b0885062501c4080c212000c0170135007503010002c0c80c0c014000c08800744828008074140000b007601025065082e00185000780510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240262913 1250 240261663 240261689
    0x1a010305010e0c150307030c11190308070201180204111c0614060712050f09030115080106061b0b090114010e090c04270302070f0305030304060b030a0302070e060d0c 73
    0x201c1c403880c0202d4440182c1c82032010070305140404e0141c0c010f9075403000491402040c2ca8400120560300c100828200603618003504d0400d402510100f10042c20091233966888038590392060220308a86440c2c4a0355810325566095501514040c0c00252401a100b0a80d601c1c10385050f0b90074101c0714402e0740351841d0325281e107002c0082c2c1c403503460101e40200041c0c4106240684640c0da40c80c0701d002e1705500c08284540818401d040c1600c010a0380e05000c40074008204030f000306c400b0020080501c0c03041240ca582048400700b281c500c03451003403c120b80c5600700d4200f40b10b103139a200420244020110703000e541da20034941c1c1c000042040e4040c02801059600030481c20121007880c01c03d0783d450784090040d4140f48104020340384842c041090300082405c0d56442103440d260890829000d0b60008034003100d040f102000740700d40407000f1030080d03110306010840e41391040c1c00d26860b0b021148010300580c12510007001102d90540d41304d54414001446405224115500c4640d81d200e9034000b0f107104100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240264163 1250 240262913 240262931
    0x6030307111903030c0c090b150d112a01060f090f151e06020303071b0201020a08030c04180c0c24050703091203151203022103040218040b0c071a01030501 68
    0x16000e40c06e405008401001e1255055084c042074000090799400c50202d900084c0088042e0040d030b100d1014414081130503035607184c3c00c910103c3c0c41089542c16051810894010703440c100c20521583d402c40b42c3c2d10340040d4081c4c0c5130400ea0350013460042c114194081c0c8403004100301400301602036000e803003a03450090080701241c556201c030b0055500034a065500c00c005104429030440c0c65110462101110300c00c3c019010310040341040c0d002540284aa08c01201348100c81c4c4803030003e04180c4443d09604205105030840200c02d481400e061140810898511603001c00c46820580181c40c02507101c4290080c1c8001482c030071100308031809000244cac0c0d040000e00b0450080c25550010040345001e1003003140c40c40b107200d41000144a60700300010703102c850a040500a1281d290400e0b4060400324011312001c1d40c016040d4811241248600002c21640501c1c0c0c5181784500d02458201030031111035a1107910081c46c56100e25016a16214000c0000010421440341c403806184501d00109400d64 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240265413 1250 240264163 240264173
    0x40c03060b0f070309150503040807080c0f0f150f0c03060307030c0e0a060506090a050108071713110109081c12230c0a021009140a120210020306030307111903030c 72
    0x45d03030b0300003c90b000305050b000705140ba4442e00340ca4116400c041266910030300c51402d211148103c084480e480c0c0600010307017070407030004122540300000036400d444040414503002c100380344040b5200000d0381d180f0804505081000809158480d00203000c650740305840fa164046030301000c0d40000f0310440f4030420060058a9030103041d00900c0250ba0348d50610020380f0008242100e107014443c100321003140001d10b17603803251410710050180c0e224541041d0a0581c040d0a90100304030f8280d9140784100c00480172544201c502c1380c11103205134003030040e2400f04080c03e041b0b428a200e031081000340c00403a00c041400d0f203101c0c961401400102000d91140c483c1d0703081c41c0d0802c0c0181643e55101041c826190303080d8001c10115096590b5420018070f104042c0750204948074000203401c99841441d01003020480ca00d2070381c0c00b82c0f000b683c084440d03101c10140150140d00c41200d02940580041c40a200001c549040082c41005e0003050845070a0030390b452304560104940c400e400040c03142c80c00f441400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240266663 1250 240265413 240265427
    0x5030f07030c051e010804020604090207300f0806010e06030702010509010c0f020d03020913180605090a030c020d0515090d1e080c0309010e1903030e010b010806040c03060b0f0703 79
    0x490f0035107281001141c02540403503648002046035051007010400202150350b0901218040c2035090300840d02d800060500d09606800450a001500011803017508007403a55400010030302801c0d0750740d480b956041c0d01c04462044001d04401e0610001d00b64101d11550b40c00040c511602041e40005070529088202c1800d445415041d81c0622031801d811060640d070115075480c264400b4100540c4d15101400412042c1c0c5401c01d24114503403625500d00c6c0d902c0d600f0130018013543e00680302800790340c881c48092a00c88803d000002c010403c0104050011700300f0b5400342c0c4041c0c0c0140b00341c1c0c6113844180d00e0204091004ca0b4000c4e07242d0801c0c4c1030700c0380480d00124040710101907021144a1002d12480140c5480307005070800700000c81c00300000700414425040010012241c50039251501c3d18541d4202404d01c00d4002140401e041201000034860141304200080744141d55401d025201d0b881440000d00140200b0402c060303c0c1e00c404200200c00740f00501070001503028450b6645200d0038020000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240267913 1250 240266663 240266669
    0x150d0309120602270a0b28050c15010e31030206010609170618030705030703020d0801050904020906040507030f0509060f180a290709030b060a180504030905030f07030c 74
    0x10840000b524519882d12818603054030042e601c0156652110219007040c03944410110104500d4003408020302917102012741a40200c940c1212551a81d003000031f01c000000b4010300c0350050003c07002400c681d03054481c10703281c80007007160803207803290207010510b04002d0201c042d4003607404200100292584402c0b4803004021610f80d00307042c00001911700b5120a0098266041d00b40740580c2c800044505008407a98158004102c941d10b4810b840c02a4850349241e0140380801e82c84000002c030742c1080600580316641c000e03e01074403a914101080b0003054040e10000c101a590282c001005031548119406000c002009240c03901d0401c407a0035441c0c1000317140d900f1904003140c1c144001c840c0019048059075003c441140140303010903110006000c40340c40181c0044c400b10034860610341100c0c3c14030a503406403540b940540d81720b000b405403402203803052000288141c0540842c421490b4400c0360032520900c1d1600a1a82d03d00000e86061400e0089840540000c403041040018601a482c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240269163 1250 240267913 240267967
    0x30f080a1b0f15090b270724030207030206040b0709080a060209090603010e062a0301140f030c010c060b030708120c07080d08040803040c090510030b010b03150d0309120602 76
    0x184103045d0342c2da01e00c078000c060460300962607229001d40300d040d14011600807401000084841c01a600d60f19202400010b80495440c0d100107000c5601140c0720303000f03c48480d50150018015611071340c0c2e5041c01003200038460801c102c00d0070404580082c0a200000c034040c020100943c984881d241006104c100c00340085109138900f080d17108520a0208840780c2c002001440c4074280f10125a03e4a06028260001086803000100204010203509030b18021900240d48200d504090101819602e48100160601117003890b0b0320400001d215800200020601900380e03412640d031020074514003880c00d6040c0c0031a0707102007132482805008008403002081d102d1700410f01050080406003c10501400c007810b031140c000b001409200801c00060001c00d5048020001c2d4508000c4100e40303214107000480e1115960000040c81d091508180d0f401125120303e0030b400840c1c5a02044046840351504400b801103440002940c50f059041940443c1d028000240c0e88010941d01850b940e00c0071042203c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240270413 1250 240269163 240269171
    0x12010b070b01030314071a194a07032010030b010519020d090b090a090b030a0f0807020f01030c0c06050a1e060e0f01030f080a1b0f15 59
    0x100312034036085030460f5010309100f103069030317854003c0d904c0344a41741014280b101d00300601031020440a4035903200d11241d020b211400f030382140307032002a05c0c494040050351040d040c2c40f070341c1482412500e5001c43d030444502c80c55150070600341c0a42c1410742c659112441e030000b2008000348004d07240500040e0190381c007103100030151400041c24218000650b68101a500c0030900ca003070340503600311030140c800855840d42d0800b0504009590381e8805046030001228190001602d05800043e90201007008201401d21801c02c07500000400c0c0441131180e2600c24088040081800485640c80b40340c000d124450b0785001d10300500403009040c03105a410180b400c002c505c0c1250f444080c3c0c022483e404000443e06071103501d884e0f030142616003651030010303180050b09166242c85038000021650784800c1c01089981d0910400410302003448040c0001449100f004002203290300185102015410500e48002c0003138000d02e4400003044089407258001030300c8100f8800701010b12485c81c154454180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240271663 1250 240270413 240270427
    0x80c031c080f0a0f15050319020306040209040f140309040b0906031b04270c06081b0703050f0307020a0b0a0623040207050316060501120f110f1512010b 67
    0x3850709070001d00344682c41c104a000300d50441c0d202d4004110070761007214203002100459601d200020880d1051610a02c40c40080030001066103034404c105036001405880c280e5141c0d028440c00001c0104112025054204920000340c242c40303040b041c02d4484402103448100c0d1030b05100031500304481703091147c0c408004101030fa81c0c00103500034000c140000c0f142da5502640001c50080d040c400c00c1c000c500001c07020000031a611000200000314004d1000841040c0c1d600300c1502c0080054581595038001e46030000031818031030b401004610721030703c4c000b0300d03081c9507068011a503081a0341d400010703001498544103010746203800640001880c3c904002c41447c05116442c07000802040c010595000445207440e03a0742d036070540308929005815640c3e29840c031240c40f03008003102941150b81915040000c6a03030100c0c035160207445a8400302c0740708000c60f6521660403030400c042086600c10444081045c039900c96038050a500c031240c1c00340640340c8101c52401d00b01d407801600710704040d4074244100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240272913 1250 240271663 240271667
    0x703120e06042102011403070e0405060405060d0b10081603051005090607211d0d0507020603220f0503040f08011803030b01120908030709150909110903010501080c031c 74
    0x4000b444a40d80706003e0032228401a07420000202820555040c04401c2050003070b0031800b0f0702c5100104a9007000150b0380e94040100311941610529004030081c8100f00000b40b02444454100c0e60500801c0d81d2143e944c1e0100e41b8000c480140b50041421900b410001c0181c10050102d00e441207600500c1145400326103165a41c500414070f10400034824080080060089000045010a05018001c4481c000390703c455035260356858801350300c940180840003c1c030800c151354506078003e005500e181c0300c0c10149800c41051415400c00d0811136811034002030440c10071f86640310300c100e01464440c0d1030466000501d1440e40d0125040303905007442880c10018402d80b11800980c18200004c90f10b41c4100102c8400c5220003104d244030385061904000d000545015510411560352111041c42d1903660b10413441c0000880b00c404201d40e00000d200800c2907400c4070760480012541d0508222500c80000c0c01d5030000e80c000e101c50381044240a0080c01c0601c4940e0516003200303c5100080002c143c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240274163 1250 240272913 240272939
    0xf18050708070f0e0402070605010f060f1b060f0b0d06050f07020c060912010e030d090c050616060902220603020315060907050903100603151409030702120f0703120e0604 75
    0x4804100400400d4004c1260b6955042c0c80a05803c200e0070426580c581d10780701c0c00e0b5902c600454021600346036204088912602c0e2500b030300350f0f1028180c40940d540c0c0d0741d81b00103815429541032041d9110290840e0136112a64588a024003420b00401c0509014026540703801d03010700008119084000d40c01841d490320300460310364000076076080c0d860300e003266100b600415690514041a02000940e0201c0007026088000c10300d0103003e591850660301c40070401c25110342c01c1915404407813640c0981c0802c0e038540c002c002540c00a02401e00301c1805d404440c074040d9041d01000c00c40c5580380d4060040d4101003020b80c0002150f100d2031107241c1440c5000a10f110030040c610010040d0005003525140c42c02e2200d15500c0e25418014440b96450b440c0c0b194000c09541141880c0600c0d04014890302d15651a190b806404600091740c41d1142a809100401d026811a1841807080003002e4aa01000b080500700841c000c0258240c90071040c54003e001c103100c01c807014402d034402e1009100c00050f0740c603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240275413 1250 240274163 240274187
    0x1508120a0c05010209120709050c040e130f02030d170901140f07030b0a06081503160b090a0f081612120305040f060c1101060504060305190206040f1805070807 70
    0x5101410107420315007980640306040100d50848406070000c00240b000245071f1081d2085190207004a5a0300c0c2c4001445010350b100d0019020480c5011801c914004446421075601a5103502000c20a40d00442e03e01b41401c441e00b4002001c09040c0c180c594101e008403500801503500a0000d1002084980420140500784040010404003c0b9030b51a000360712018115101a00e0b5540580c0e0f6054042c0c09000100d5500d007425940d8410078070140740c0801c080d4071204c0d07480800c0c20b1030350814500d8101ca401c2403442d82c0d008103102502162820505001000034456480181200c00c0400d1441910244a82c002c007441d00b461280c2d080029044d400300030f100b030342d1482c0c0092a81d0301c0c1d050401003082c44080c0a40098038000340001c0195026070405484003240c0b000384a040d54404c28841201c44611003d0410b40041300a007850500307901009a07141e000505140c20140c580d1001d900f0062035074007040d40444404105d00c4800c10030702640d98000880d0074141014a0400c10281038082d40741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240276663 1250 240275413 240275417
    0x13060e1902070c0e1e07020a0204140405060412110a060f06150e0603070c060c090e09070602060a0209010c021801060f110606010309210e03120a171902030702011508120a 75
    0x1c001607604180400c8048101d400d8126400c5d45d801c0528000e074541c1d00080d400d9004601b0803010320344400f528400340c0e0003554400002c00841d44c594460a90a50703c08c0340d150200000186103580f40311080000d110018085c01d00010840d1010034080f003212041d40c00780764190180380d070000ca45a04541002009002511916965601e040040300d05640f410002802c0c42d10300140350504542c032130015000e40d006001c001031140c131000c2000f56200140e205130300069001000081e0030446036006029282c206040c485690812540003c005c0d40b00f10078440c1040c0011801082030070341c804000c0503d0106418403529a21051200300d80f98040144124180f540b01c407003100c10822039000c040b00b240107150310501100500b8100400c4506040407a51182c4140860549031800e6202202c1001d14261030b1422002103000c80208210002050615403011490424075210842e0000718440c810303a500005078043d0500500c1d00c1c00e00c5917001001c0c154800306000001d68405800c80e140c11680b8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240277913 1250 240276663 240276689
    0x70609230904080f160803041b12150b09010b0c010b100516030c02120c01020c060c06060108130c1404050912031302062710020a0506010303080613060e1902070c 71
    0x100742d0710784c2d01d100303500c07080804401e054074500a125810f0301440c06503104108111800c0c4012140c081440180e000d050b690780d4103240320800050070302c2c140d60050181c2113400f00c1c035402580300040e8900c07403d074840107040070000342c00c1c0340c0002d0a00c80c0f10000e810440741080ca4030280c100040850140800031a0f1180c6a8180b040c10b00d40192441010658000c0c52444201d107090003007601c0e9550310000310b01620034000005164500801038400b41c898050091240380e890340011107021402804040c91100c401004e60045000521000003400001c0000e1b140404c10302c0510007281c0e4000e03c00303805900140d41365043e04180800b2290020b22901090624010070300010b07040c0e2103a4491560030700c1d1503110b00e01070388912140c154420407084400503000400890166103c00d0605001403441d08030000500c0000c0c081e1001030b4002030042c1100520801106024080301c4d0250068243c40c605201044100c0440c10b03500c10340c10314002da0035402e05159a0368004088007500038603d181c161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240279163 1250 240277913 240277927
    0x30e1f0e0109081c060e0c030408070812101205060a050601020c0303040e01060201060e0c0f0a030b100e0f01110309060d020f040b040504110a02030d050c040807060923090408 77
    0x1180c0101000c485100300030000110b40f46000d0f600c65208204030410000014141e0b00e0700c50542c0300e00011030b030146484a000d46e0315940800a5540002c00484a1031030501c000c8000c140c00c03401514180d00146030301100f40c1884d1014180301c4450741e000c040e80d40301606240000400c0407400700d801c03020021003c907d5454080041c0e00340aa5000259003612000c60001500303001d80c541d0074101d0341560000c225150301c881002d00042070880710210b05d544200080c040d51240740004143e104103c1ca00003540f00110030000700300d610305003215030000700f50348103101c0e044ca01160103801103070090030200c02142c28000d20913268005d01039103510908003c1402d6480b0095a0100c500c440c1111815668443d00c55038055035541090140c2c1d801a1b25164074248510855011249035501903001141403c85180c8c07503401411000309586c0d0a000d0074000000c15040421828014207840d07202c031103d4905281c15500c000c80b01001142561441c905265415155804001d030040e810562066075510 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240280413 1250 240279163 240279223
    0x20150a0507060903031b180b091c080909010e0618220f0203010603050601060815090c03060f03100f1503030f0c0c080610030201020d030c0806130605042406030e 71
    0xd51140030111461b02c90b181d100881d5120788080d0320009854400310049440b00804c0d030907406036205080e0802400e0345c0b900c556041c41011100030b54881c6c0352651a2288140c04a00400c90a911544603c46007005010140c0340443c0c0d01d482c41d00401003100c007189001115070220031202c0400310284190501c811083c051380843c82c84883e60050020f21009580346400c0f640d4100074803400c400119894040358500c44011f041d45a00c01e002009028940c5810a482c456a4000743c085da50080300103200c0121614240700c101180301584800203940026188010140d8110054031003202c04081c2003840083c1d0080000005607004c0e1034a01600a01c3d403808501380c680036040480305110381400c104041c01d01542d50420749200381d01303030707040706501c09001d03416181c000b98104042003904001484034202018554a003409035136000c640980d0b40c0011400301d0b94100a0b29107032a89140705001e842c84000e580f00002c200a1404000c80034010309601e45540d0441c006042000d02c181288100203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 240281663 1250 240280413 240280421
    0x9120303020f070308061e09070e031e01020310050105040509010b0703020a061503140a0506150103020405122811010f030e19030f0207050a030807020a0320150a050706090303 77
    0x5401c042d000d43c0c42480d400c001d84001c40441d8058410a02121011083ca811150b05a0440005046440c0e151210a010b4510391010348645415220307002142407034407400c0600d1701185801000060752410004003d02096225800260502008110401143e01c83c03807505030440e0f4106800326125005440e040b400e10340720303136005081e490425200310520401c00d0411002c0701e104150040c041d0209a1340039032101100355010b0407541288002428901030340755110006081490018a000d03101c9001810945032440a500158041c807014514440e409280d08420340d44c104080107c07800d41c1e95002c2e02130425808860401c690449000c0c600350094011070341401c404000c0e01c07080c0d60f00100c1c00c0140300364010113a002a5907140c60011050001c42c01c44284e58003d03001a0420742107896200c000d6102c5001245c0121142800001050024411009104101002c004081154030400c4811070a840040304800000c00c00441c2c1150000b044403105d030b510080118140301d0500307040d0010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 240282913 1250 240281663 240281677
    0x308030903040f1d1b1803030f21090118030507030c0b010314011d0a110d061e0e010605061804090204020a110f01060e1b0d110c010b01020604030912030302 69
    0x41c07941c0c1804110040c82c0c1148a031104400c41c810780795942c4014440d4035600703d01c804882c41715820461118021a5070001001058000d401c50385807414200e4002d07a60b5000f0342c403500d501206590349100c108080c05245401201003802402441d5000d24050606980300000070305010000900a0405001741204c1e54880c0d0050310010456070b4a061400c44c103c410202000e09502c1c00c0400030a078188081043c035806802002011040704681d80c80e00404100c019aa034011f404515220018116015601c00343c01c40003440c405842600d1002410b0b1041c1304007841290341001c0c0c06015903101c80d81507900b52082c60400701c2e00480e800020500608000074040e401c240001001044d40f0f1304050100c2c3c0340200c0408807406423404a54160803549030707000e82c00450034a00c1c04603040085807992105818a0445420724110f26101e11400311031080400104c82540070814021b0380f8401c0c03059003c1403c003030000d45814501550002c20035800380c010326400d080154226800e040c86681541d0310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 240284163 1250 240282913 240282929
    0x60f070f0306030c090b0102060a050f060d0f05160312050c030a030b0612090105180606100804080c01060e070801090c0c1401060519030204050606040b0a0318052406031204030803090304 82
    0x1803031740c0314a240e002601d143c03080f090262041c00701040781001e4a2003450701c0f030150b4030b00c00452a1144010450086104602910900c004007070400210b48144001074a9950510111403541c1c51440d080c03201d40000d0b4000014000c090004821105000c400c582c4a110b0300d18000814040000000b4024018a0000b03071903d00c1000410440c514154462070043e407202114500c000c0e0442c0034070b035540908a81054000000c15480d4020354001c4030281d404c5442009a01e0800c0c1e1441100742c2114170b603510100011030b8500a00007400c2d001041c0c039025002c80389050010000850307029151400c0c0160042c0400001d85001003408804e5100001520000306103481d1000d071b0718183c61035801240000da100d02d143c10040b8442c0d14010b01214101c5041940407400c09900d9181503004040c1d074040340c1d4030720f200721f01e2100000e4410b0101415003007811003c0100c1e616442181c0c1f80300f14000300b80a020b03600c40b1800300c18104190b8142e6003140d0b0f1000c121980c83d95007091041c2540a0b0340e019040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 240285413 1250 240284163 240284183
    0x50f0d080307020115090b01050d09031115011a040501081f080102120a06051207090b0303120f04030207050a06121e02030408071a0408030412091a090a08060f070f030603 75
    0x3682c90f5041d08950310a070b40c500d0442030b1441e00c9407644401c803410588040d0200d00f00308130004002c54550408180c00d406410090821000d240d1a281084100160307410900c14880c0140140c1c031030002c0340349003000180c441a09107814000060481e202c0500104185050b0901088031140c0c464031000107050024000e546988403544004020071095446c5680103003441c80100c2c160034003000b07485d071000b0f0f41c074001c05000d840c0a0f80c1000400109541d039406020401c002d80d0900403045c038003070080080810710101441c103800c0c002d0401c052034114511562002c4020080035502004a456900621400180c40c211580d05031151000004e500c3c204140080100414040c900380948000703401100300854900f5000754030103030700c03200b214018201001030021070007080c0c826503400103007015402e00c0c4800c203403103140da22b4407440c1185140e041c00d034000482c51003500780160701c0740090108a00030401401c0808181002c000700401072002c02000e0a5840c0056100340c001500440e04106004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 240286663 1250 240285413 240285421
    0xf0109050f0f151c1401270f0c0e01030201030e160b0a020312040305040e0a1104090b0102030904051005030c040608061602070f09050a1a010927020f0310080610050f0d0803 76
    0x4103075a030000b50140c07a40c5290640c0710345c000c04103008018800010406502061446202c1c41001c244038030303020384a00e54001000d000040010000201800c4000c240c00050741c0345100060645e500d083ca000ba00d0f42190801c04000c03031080942400b5500641c090329107a080c4050224603601548864a080a000c3c200b172205043c0c00c58000c0069030380c250706815881d40c0740d241c04400d40700005059845514100010003032070300180d00241c1c924005106985ca000a50800901611010f881403102004500d10801c082e140400c900b41004809903424442140341203151515150018950303910014403480b800a03951080c0f20303103c0500005d42c90f18001d030392900c0e800002004121400045c052800700045000c0c1d20703031100d401001e01d05940d00d2101d14107200ca80c503801811400e8020345008698500700040031a40040c0506d140300c904415268031300f90300e100d0350041142c4c0c403207140394108400b40a001780192044005031075098801780a0344140401140c3c900031ba440000d8a180d002000740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 240287769 1106 240286663 240286699
    0xb180c0a050417010c09090908040b030a06030209041208010e04022d0402040303031a0108010608010e0402010e1314011a0d11040b0a080f0109050f0f15 67
    0x11a0600f41d03101c1d00b08041c03078140a030000d5113945691000b060070303601040d518000e150201003400b5040b460340307400302e0700d1203079014407541e1110000000342c03480041d4100200940e80503168684620701b1341810360407141c044250100180c0d502000040300b5609a40705030003a40c0040c0301403902d4481150110f44140011402d070720b89040704d01c2640d11b0340d940f4405400118042d0f100400d0801c070500143e100103a403040d881d4140300f80d0800500490f64030581e02c030306480760500c01103100d03101d074001078803208203410b00340b07500066007041c406544010f078024003415540c07890141c0c00e507629407400714080b0044548142035100c2c1840000d2074081942c221015000700d18402c01d10b882d40f908a01b8105a200a08403000b05201105000c034140c034070120140103104510041016003409141030b441c0c003201803d20100c1c5241c9001040e201414240c4e588614400203000e004841c0382c00f501c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 240107913 240287769 := by
  have h0 := BRFrame.cov_init 240107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 240107913 ≤ n) (h2 : n < 240287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
