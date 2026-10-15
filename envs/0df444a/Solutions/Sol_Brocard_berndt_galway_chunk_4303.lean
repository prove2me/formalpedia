-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:35.477628+00:00
-- url     : https://prove2.me/submissions/49e540d2-0fa5-460c-8c0f-d08cfbc3c6cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773741007 ≤ n < 773920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773742257 1250 773741007 773741021
    0x7050c10031d160e04020f030610030b0a0504030c08280e03060a0b061e040932010e060d050c06030a0203100b0f1603050d090606080106060201020f300a060504 70
    0x310041c000d4884510364220310f003a2900c00d8003503481034003001800f951100e00d211400402c00605a96103450034140031055409140420f4a041254000185100d01c06110fa103000c0c43d01074646030b401c0c0c5070691b1020641c0e0311141845610000f40712540c04501d0001086500401903070b1100ba8103c05003500341450404020306c50020f21303052840c40c09075520380c00111913407982104a00d6407443d0200f1440400c2d84281d0b0300c4460214500301403251059140314115502c1c075280f1050000380705100240100c0b0725028000d9010920040010400526040c10185070041c812415200c820008000242c0c0ca500215400e655040d000003c000e01c101940c12904054003d941480742000c582103070a1003075000701483c0e160110202104142454010001c1d10b01407000204103001106943c6001406801584155402c0c0c0d801c100c0045003950041c000d83c3d8603071401c0d4680d01c0c10160342004d0340c0d10300e4000f482c0085404100c00c119090b0700070303d80b0079a4420b80f8105008a00103180c0414002150b440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773743507 1250 773742257 773742311
    0x305030c100917071a010e061f0e1c050a050c1f050d0225060f06060207030809041a03060f0907150f11030d150e06010507050303070507050c1003 64
    0x5040c000c0b01c00a20310121080310307680e070050307100e841d042c00e480c2684940380c0c0c094800c1400c0072040b000165500c4141130051280c04141c503200201403108a826aa0402050514011804505071041035050101c2c0448090030780e180c0317500c88601e441c1c9890b420081219801d459a402005801d00141080061040e9041c2d03800c402070943c483c9010700801500406004418203500000c620002d52026103101070394082d41074002210503880e24040b40200511203440075280d00b8000300203a90b80c0081440002c0f83d4108d0032072407400b0502c1d820480204400c0340104140d40c05040c083c9100e0320108134043c03089910004802840c2003040d101da180c4629540b041e42d0900b0000781c80c08160ba403003417610110b41001d044c022201500b6400382415801480c1c080c01e00c1500d040c5441c2c07807031140720036846c00315036070282140c82c1916450300444442c420020050881d030b10410116000500c190000c22400340244180c0d81c91084490000e1460b441d2031031a8030010762908801075062113030b2940007840241c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773744757 1250 773743507 773743511
    0x4031a010f0315090203070f0b03043309060f05040f0b01090209011202030703110c0a1103060103020f060f090d060506100f08060d0c090207080a0f09121e020a0305030c10 75
    0x40740da91420b85200c800b078105915a9194031341c20301191401c001340806400140c41071100d6a85512800256400450b400e542e00d1036150051031642c001442e2a20786400c80215000052003d009820080d281d080c0702200e2265a600c0c0540d820401445aa40250b01ca8216204c80710410304054205460681107600c08074070421880020340e80110006c88071100982c805604c95480100550045c8803800762142660300000702c4804402c0c000c1004042c0074480c0c190303072100702d64420a266131040c2c01d000082d08001031041d800c100d850708201500301c0c0d02c40d00c0b984904e060100d0340414031810901c00c04a40716a05c49003841400d00d422001606141182c0c580030ba40403039500030051658402a01460199140c034500005025071010010301800801d04203659580607407928a205502101e0080001074003200460359680c403c50f403c200701c556207010500e0400c165119801c4110010101034036150400410100584070488176200640c041c1005d15100c50318204210f0500201c4a06008654 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773746007 1250 773744757 773744759
    0x5010908031c09050a0b0a0c02010e0c0a0303082e03020a090b0108061309081903060e0103120e1f0809070b0915030901090b090c130c1e1404031a010f 66
    0x4050b11124900701d105034000304020895040c0103080500d180006082d9200345c4041042410309071b0040f0f0300c0c03401c1c643e00802204c1d20149440f42c40c0c40300c400360f00360700144081040022070300c156800c42c2c0006100ca88a0b440740380030541d5903012500c5c11100071210401003000c0003549801c125010042c40051001e0010015002c0002d01d40c2c070000304007510036240810020b421071080e50106622551150003155500c60000c2940d40410050360b20a00080c101600801c51910f0884e400307040b40d80c42010f0204401005500f611003030b11201355242c1001100200c117558039098403d8460b095059290048542800300001d0700701052504441c0948008003c0d58007a6103c00d800c2c1072110011100c0580c40b0380760042441e02500040c00060054001c0506100c64503001080782080c030101194804900c8002d80c1c420404d80d940301c0d14410201c1e600401d11040d03100c18019041828125107407120749d20303000380b1210110350800c0d08295025164000310340b00e80a841c01030503024106208140402c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773747257 1250 773746007 773746027
    0x318041d06071e050a0c03090b0d05090f03041215090b040f0c05060a050409020d0f0617010b0d23120d021309060f120c080d050a020d080103051902130c0201060501090803 75
    0xe407140c050741700200030780c00311108185807103000c051003d85000240d60b80e9841e0303c0d0340d04501519042da40105140101da20109032090000112400c44c0e0a481088507508040d1300c507500c1114928a00c241c0c015120046040003c24450740c0900c45c911550300701c86001c4090030401e5132504181c1200d4000c0d0300400c181a440740e0413406440464140c8040903944100b642005006001c0d541e8040c9200c60801c0c2d008541144110030054a40610307400811001c2490000c0285503100a036014002d11021a034607500d40c0c0c0c0842070300c036182a81504651a50310000945011035100707035403a0391030030341c00300381d0750545c562007084c0c0001000184004d00c0954240000e0360b415003074034842c0005654021500c5030803c0380700342251008101d01070998400c1c0c1c0c52404058001d44c882c0c200d10006004216410780c1d82c9016080440c1070f280c04c8801455005d95a0804d100502d40d0407401741ea0006000d02d00c3c58010000e070044a040c682c05a0022561510300000506600c0194008058070341040c40480b80d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773748507 1250 773747257 773747267
    0x4140d05030136020901021507090b0306030f0f0d0e0f09151903030207060e120a06020c03070c0f080d1707030b0609130510090902030318041d06071e 66
    0x1500d8200100000303900400204900c1103880a0440c41c1a03580c3c0c8041a103151a10b0b806800102d80a030240c420245c21404104c1c82c511040707a14801041400c501489000c0c4107002941c1c3c089406011078504400f56010309182124120b000d0040782c0c0b050580d0880140c0c482c59001c80700380290f0340040700e40c0c070460010326038400003044049000074010310591a65180000714852226844051180f075459080080d06d40001d80135610210b40c205803648440e042104d40e12140704105030260070301000541d07440d406980202e0b00a01144814011200420b48034440900103000c2c000804021916084225040008050700e042c240071f10000e641000201c075142c065400030701d03444c0010b0300510b480005807160040209894000207001005102100346038811401041e0b103100000d0301e9961940f00c1c50644801d040005e405400c248030390660660300d940c0703003c102040140080b0b01681104079038030b02910110403145080d8440030500009540215501228100c0240702c101d40700c50056025003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773749757 1250 773748507 773748509
    0x706030204030b0a050601020111130801060608090d080c1b031818040b09070f2312150604090f0c0311010c030905060a030608010612050111120403050304060912030504140d050301 79
    0x11113540700e00000d08268803e600c0030240b2610001b2981d229103c000342d80008003014055881a5881c3c00310201c1c40a01402409106142000090440d04c40000085584900103404258041d0042c00940d81d0300c201d0891241c0b1410402000756207522001030b2118680d08140032103809460440300700052440020b645a5000307070051200640b540715444064600031041e84a5907502000400c04a00c1d1003030b040186014401c10b072407603200c8855103000c000d0360880403c0248200d80c85101514082d1090980300c03a40080000c000003500f00803500e0b5004010301c458000c0301c1c103001d1440140100210154101c013884001c0c6016002e401c1e6039a800b4180940a0045c1c2d841044e021540d01d0300c051017a001031010301040c0000380a442da0307519926000001d20300d4100d5003542851101100b0002400540d440310070b41d44144105078403141c90075030396588040e005640080d100d031003040103c1c40488070070040303442654002a840c501404c01c02a403120320070380d6903610303000b0401310072429074040c05680c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773751007 1250 773749757 773749771
    0xa0b010806061309020706050105090907080601060f0e030d0e032104050618030109120e0102061b0c030c1b011d09040303050601180305030a090602150103030309171b0706030204030b 80
    0x15030300c98030080e503a16950f082e0383c0250603040c00003540004004240d005181221410b81e104034542e21507244542d20b6410324080c400d2146e100b20010400d0900c10801c8403400d06160908018a46580d030100f4244004070b803c0d00b010034a2100c104000c4c0c107080000303000040400003c401003018502d9140014880c5104152065902280319422079010702041c042401c802402042034042a00d410010031400741651001704102440c840c003d03500200d25948130740045543e000d8540840081c9443d56045020540401c2c0302c1030003540c08550707041040b10004502940003c400090394000100100545006440c0e040c1c2c0c1b100030003900d40c88000c0044d80160385810080b90356594400100e81c1c0302c1c5416034400690410200000900401200030040c101c108d0751420314194030b0f0305043c0c4c0e0300e940c00b030007940400b07513508010400301b440781e4041140640b2449a43d841e164036680c04031740741e4100c51150031107a20622010304041d00c00304041c4004081500302075080a02d9600c8048a8031001082d007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773752257 1250 773751007 773751019
    0x4061b0f08071a090708011a0d0f140307031211041202041a04090819020706200a0b01060e01090906050f040209150316021902090105060a09050402030c0d050a0b010806 74
    0xc0b900300403a020341481100000a00c0c0070041c540943e4031a542c02542c41510519481e01840300d1038200581903461911101800100c0c58085ca9959007419006003a003e80b01c0461184252900900c28001000030340d00039694240c0340514035100e03070b046070030342034108102a0013000f04011843d490400c2d20010f41c0c0444000a0301d400450440e03942d820403001032540249468100010040d07404064207040c2107040d4005044c08a4540982c2d440641d4060100401d1041d1654840e80120352446204003641c1c20545404180681ea00511000203070081400718a58040384e0802c0e50b40284070600a00082a060100c1d80c0307020301164813404a41c28040c00386800292540940d111003003070300302035240062100c0e9030b40340030740d00300c020307800100c12120050042181380e41030745000fa4445102c4a03001004a103040e4604002c100c0700d9840729044400f07210310b1000008681d519071000e18820480c000080b0364890f00c1034812800c0301c0c1c0040c0f42e141154a84040680d699071b00480071a4810b10079600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773753507 1250 773752257 773752267
    0xe03121006020c1f0909020a02070608060402030c070b040312020a030b090f1504111201060f1808030406050a030b0a26030f3408090a0504020307020c100908060c04061b0f08 76
    0x2041305e056030b494000d0340034280002402e42d45140e00181010484020b955500020380354002004181e120540382584c88003028440380b00821644e0140780d420a100c0d0400c00b40c00c41961355207000781d0304001c1500d004240e8488280000e4141482110b6015002c54028415071a0200140d503904c000b4450140c06160307a800c00e03184412a1401720f0b210b222031304e127504000d50317035840307000308800780340c0b01040e000481c090b81c440c1c101801d407800c44080e100f42c100510700b0981002400c0750690400780190041680318070001c416610740803540f03030161a601d800301c0700714500f403a11002c43c510040380d5000240d108010b00001040c80805455038804810511140146003640d8141c8260500d69034175660709c0b80c1444c480c1081690801002d660001380c8140705082d07540c008000490100303c41e440090303044191800d4051806441e081900030a900f0301d1a40d85454008207803600784111280f140c41c00000a040c00600d801c40c00100303511200000224901503170b030355240050011600024542071001c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773754757 1250 773753507 773753569
    0xd1208060d0b0a050a0b01090324110c072103270e0106020102070c060305010503060a0506061c051504060f061103090d03020c121b060d0e03121006020c 67
    0x1c901044550040c1c00e003485070401c95210b01c010001071359008a03441c601944600b80e0350117481882c0c1280e4010424a0300318201d19010251004070f1007100c00c2881d559155105c02450b000e01500541009100400c00142050405110603180a0b6100c001c0c1c03c038400c41d000025840301030300c0350100240100541e4403604512a85400445400203001ca0107400000f190307180d8154003400d115409184020a902d9440300c0a400b198401e0040540540004001650305c06aa03000b090b0007550180c002440d01c81c0204503005041a4021050106902c49080c07042440c50131142c40f0004c541101c040011516064401400e2501c41c4030f4a0144126045d0381c01041c0401d0040d070704851000380c04404040c2d140e1070000d48404407d00c00314441c0070000c240d03403074540f0300107500c2d5890074140c407501481917100020452b160308890800f89600d502d55200601910007030000d0150f10b480440d0102ca1410950304003504502d4542000b000c540c0851034000e0241d580b0300401506202c80b0200e031b0b900e124100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773756007 1250 773754757 773754769
    0x2301080c1605011803170c03041718060d091a060d0f1e0b0603010e0106140f0307050a06170705070f030c1112160605070819020a060e0303010e060d120806 68
    0x40c041d1800020501c201800340364100000d00300b040b0040102c91b02136622040407111034001903801070042e181d941c50004038802d40350b000704090943c00701924080020ba40004a181d400142800740040d1907940c40010010000021103200410080301c0e2050315040d808544480d50201014010000f4890700c01c050258002d00062001c180660380c4020b850300f0304041d014020243c0c7c0e114005c0d03213030051401c50054184904400e503800348608100f0048000304010041d0400320481e507050181c9000000e142d0750300b901050003000161584041e461411611645103d8010240d400f031003030401c4800000f40700080c840c02d00384d5050808210265950512200c042d40003445503400007200e000f8940164800903080f242a01e07004c030041e02403a00c0e0030f411100390003104001406034100b03001942005414010035000c03007049104030f94070342150703849030800e8401e03900380503401e80c000200610075801d02c501900c0e40140b050f604071035501c4255844c203070600c43d0080000100310000340400e80c603503218 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773757257 1250 773756007 773756021
    0xa1505030c040b04032607030c020f06040f081e060403021009150203040b091608031209150c0a020706050307270803130504061221030908042301080c160501 69
    0x70500c40c646a54a170b1800c0c4070600190128110720342154142021b844203140c003120005640341ea07410b03c11000550910007904050000716a000b9401c0c0004a001306400000d4001001c2e07074030003001d01c008101c488850000081144046540004041001080d000034441d85144081040024048003500b4840820b0010b07a02d00710380140000240420b10075445105402559200d060700c0c03559000040b0b0000c030403041d110703641160700248040d030307030510051100c0c2d6409040c3c58140c502070300e51046100d43d403140440b0071409100001c02c00034040342e410008640034100c2410070900c1d50400e10000b03841c605a0302241d280c045071505030f81345460311289004004110010482340c40d1032941e800200d0041a600a0900883c0380200c0010300500e40d1910388140c64000785012600c09080c1003010141128404003000e158a4001e9071000515410040c0002e0640040301603400709813200e0151078040120f810b0b410012101c081c084000c1c9031600301e1781d2134111185d01800000c058502203025000c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773758507 1250 773757257 773757269
    0xa1a1e070c030b150415050f040f050c0409050c030105060711011106070909050a050c1207020106030b0f07080702010e0c041517010501050a12030e091e090d030b0a1505030c04 77
    0x8148000070400c03c01c06005030003801350f4800703a50006120020b00c0110391a0802814104100d00010040c0303007444154000070900140000c1008007081c0c1e0740000fa10001e9482c421441c0000408110110070780c17040b01e420042c02d000c1640b0b50351514002035900d0180407000740c181e040840e40036410741c0c007070b00401c40000311840c1510620b14082c070780645084001e102d004a07050501e00004d15155841c800c480c801c030015070410b0b00701410325000140d0312000a014000395941c9500120102c0d238440d50981c894032040411124918210310000c2c91070320050554001e5a040044d103c05100707000c107080303d40102c2034400244008200545541000455100010381c401d030b00b06c8002d22032419048581655070039030340c0d40ca0305596404440c0802c803401c0d202070001303084032840c3c00045c9800c101894100400d0000240700c41c0c1c3d510190310b0031540994104101364444500000101d405014044a02a088a8008074140f9103040000b0b940400070204d0200040000040c07403d01e21101a540a045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773759757 1250 773758507 773758523
    0x308030a140705040503010e0304031505100b0301090b010915020606060f09120109030201060515040302091008010f0e0f0d05072d081c060311010809100e0105060a1a1e07 75
    0x140030b00050420b50040c01482d0280d4245212061500f500104440031280e0010255034840c01c40d060311001030001a200039034000140e07100242141e07511000e1800782124500000301c91503001c0c005049411903a00a0854101c11600e0280b955000300d800e80e40150305403181303035035240342030180301c42440381d1452184e100496a100c100074400562045d550070f84a50002c00c0f07070b140c50300304001d216110036800c0c50000000308810710060a041d80307525002040c0000500b0780b40c3e01d80d034565003910074411820944540d03840001d04560030402840c040070200c000038080382180030380010020b20039004c02401c84a074069404011030210403a90740d0002101410003a100074034a0090b17880c2d40444e00c51300b42d1000400d0102d8001034913100d1207041301d500000340e405124111006483c12000100105564001d180b219060b01d42c5c0f50182c03550100b264000018070b481c1c418200300c5805001e4000c0c04450b210415154550640503040390603200011040c904118607000644500d4420310100030401c071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773761007 1250 773759757 773759761
    0x50d02181906060207090c0302041809060b09010b031f06020a29070c1b06090302090a0609150608010b0309072105030406050d200313080702180711030307090308030a14 74
    0x240d030128241741a185600024480382c20072140880a9025602840e0720701c3e4440034003080900c03a40d500c00380300c0b0f07071040301c01050b24072650001805501c002d901c460b650400001c00c0080e80e20450410900c1e0802505c80c2c0b201c81420014000d580d800140401080c0020300c0c4030a13941c0403480720303540b512000140408000c07031800410081010200c800100c47d82134940746440d0803282c003031840c0000d0f6544c60340e41018091458080040c00036015211400300c994460f0040b03031071001c1d40aa0300d010382000c91907000d1149010401482c1c800140e020851410041c0f0078040d40c07007000f003110012100141c010070428015440400102404048024620310001900080064010000d408400303d1303054200240420700c140c40d19420305510341c10b0090070301000081c2910150300c00320001103004407840f50508000e60301082c02c202520b0445110995203d0810400562000000051040710303009036041d418030341e0000e40040002d020060010340080000b1341384031a103910500d604481e07a91400914 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773762257 1250 773761007 773761019
    0x509040305190f0c121107080d09080c06030408031b030901050a110c07030311010b03010e15180319032304020f041a1009030c08010203060406050d02181906 69
    0x81d5100b9450a82900d681c041c1d14505180203900b1981d03125107648410b4500041e41e079500c0b041d0542078801006100c075000c030350540c2d02002c200e042c010700b10903c0201142103040c0400303404858242d2020312940c7c030a040440c4141c855000380d90700158441c0b1515200c0c0c0f9050038405164001004000c445000070042114400b41500201d0090044610400c01d861683c6422100d030b00c2070008140f4241d108410801c000f138410b050160000000c0c500015100c0c00d4000042d0075035103908141c80180c0c0c4030006036503070b1448e644007098104405c246903011b0320082c004250788038050040170380e001e982d000c0101fa90b06800781d00035200b424001030328050401541d0f403140036100300a8800b0383c040c03140c000013020141003038811140c80a00b21003008112001e0349003040b200035525130b4114100880c600c0000001130b150054500507002440c0056140e08d4020140011168580d00052044007140c01c4000503803074805804683c92400702440009646604d159120b03881280c45060038240b40c03410000750 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773763507 1250 773762257 773762267
    0x30a08070f050d17060405041e05120f03040c06050a1b0206040b0c030a02010e0309012c06030f010e060f09070807090510030e010f060e07050c071e1d01080303070e030705090403 78
    0x5400e10040040130284c03151010b000071a001142c0007085842d80c1c0110081144508800d00603881c869030441c6c5202a0103410b442c2035401034214100b0015022051100b04810210010050302ca185003190410342c1d00c1c107005090040c01440d1000d400138050000083d901c400c07003214003501001009039902c40071101015581d51020017000019485c1c510176403089a8040115055200140d4402c1881029540c82c15400c204003501134080701912480c2c8086601c2c0d0308080e40c460800440d41c240d20790714000b0943d40403c001000300d485401007029600256a0b00301d403454001740c09107403a119a540c1c00d2015908445240c00655010f00201c0341c465610380c0c50b800024891041a000340090301a000c810402e845150040100c0c43c0b6550000540c030a12540c06440008000406c480c900b59030b0307004100100c182030040c0c061500a61405010600f4070302640b80002c1d0440300800b070300350f161601650312400050241010011500c44076656580d04001c1c4601804005040ca615801c1916001d80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773764757 1250 773763507 773763527
    0x903060103200904170f1207051e0412082505030924030604180606080604030e03030c07090b0f060d0c030506121009140a2f030a08070f050d 62
    0x45441c0490402c941d080150b08540501e0307202003c0720240010302c0121459820280700102c00403014480d0240425030643c003240107550a44400c1d6803000f607107880c1d0005009240703035151030b00c01c104020820207078092640200303281c214844030b49846a041090500118008002512107900403001c001e0007804801841424070803544484000c00d0b0005007116612a00080c1d021150180001201420280c00c042c103982030703858034002520010f940707140c1194410f81084289030b02940c01c0108054104e0200080400c4c01c400460500c2e10564069645004a00405803130302c0c0c0741d81d65941103031101c000a05040c1c0c401000f00c0d481e041750310790b940c0090a800010320006400d00700071510f9414041c035480c8440340c00d1000340282100240d094809000321060444070030070200501e1418220502441c19410b1140e0702001a00d6041102480110083e0007140d8400404000c0350320f130760350b00140308440305501007011030300e54856091800010320b030300070b0183c80c40c0580080e21161643c0008152 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773766007 1250 773764757 773764793
    0x21030b010e0102030f161401060303020706110a060b010504180b0f0f01020312060a0302040e0c03010f05010f03150f02040b0c25290412141b1003020903060103 70
    0x4009614801120740c20350701d0007040c0c05030304100003440790900b82600070103400d11061001d9102170142d42c0c071102065940d21001189035074600003441010707410300214004111926100001e0554100c025072514010040204040d50300c500300b82144e40103605441c0101303030030804058000594851070024005490500b4451500e0071200005031500c10030015201310b0690080d800d2a10308880c07015480d0300640401e902ca21081c400100603030b12401824a01912000581007e0081c05d0a041c2520681840300d48020b0074000180104c1c500aa4000304690300402d00340706626240350b1100003000340c0d02a09032098000070b000705082d036903d001016040c0400c01242d0044200402c806c00d10b07a60b00318909400076085500700302080b040b404000e0200c03125000c21210207104c207104600c1d81e00680c441500849421020010300041552860507880500060b10f0b00000a41c106000c0c8441c103e0a24805e400c0032201203202c4d442a410307182191b9014044030309958403403c002120700d000d45406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773767257 1250 773766007 773766011
    0xc03030e030c0303071202040b04121a2206020f030f010302090903190f030e0a050c0406050906090105040e150c31050f1201061205010b0324060d2103 66
    0x8411041000411102d0000300140a9421520b0741c00d03048031a0030740412200302654003800b012a10300c01c204000c10051401d505203020b0048a071414014101c001c01840c4810000707171042000d44844c000342e1101d11400c00705051031115252030100000d010751703040180881404020000348102c00300e07005040c0c0740203c3d103201e550b980300d084443d521310460580350038503081c0207030f49000070303000380c091203000321080c00c010501030f4008031002e01d8844802e506940580c0802c042140d9402c01e840f0394000342a054035094198600040414020501032261074084c0303a03101c0e0344040300c02d03080c07100488501000d03410018904000e44154126000040944401000604643c03501c45080d122075181d40c000724041301c0740a252604020665a0801e00c6c6601702c40c0c04081e81d92010028400c032000760110303003044810504c0508201e070071100e03040e90181c0607a102c0d100c020308103000c00325081230103107200318000c8080c0c2c0e408010841312109800010402840340a00c009017545041c2c6d01d4105d00c4142c3d8003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773768507 1250 773767257 773767271
    0x12060e070506160b0601170406200c150c04030c12020114032403030409021218190609110619080609070906181a0c010609050402090610090905070c0303 67
    0x3080b92038440c443d0f0410064071188907020001c0d00d61107a8a510040504180c010883d4800200e5070303140301241c0440325a81c0e640550b14062101903441c100072100d10380344c10300f008200503686031b031420b811002c044141c0c015000150003000c540304450203594460840d03814940d03106500b04403a25410b40482c045183c0f20400b00c0c1c040051429607100360900103071500840501040c00c1000407507541000d806000400001c19400d81e1400104201c2c2140f585040803494900064010103102d102c0d222000d42019488540d42c00a108500369455045200051203020311b14004005083c03502c0b4054000e040400c9a40f04542c2264007540384506a817102d03201540d503402040b207030040445038880443d131603407001d00c18140f007020440340c03176480c000240a14a8407410350000c148540c20040d0022640055010130900d001e0041200510440b04141b1003410150300190107c400107140c10300907085100000341c901d1155549034001d00801e201000036040c00301e0020044400ca000a50101c1e0500c21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773769757 1250 773768507 773768509
    0x30c0e0c1603110a1e050609071a03100302150a0e043b0a050a02100f12020d0b18150f060a1b08280804020d0b06010912060e0705 57
    0x444020886141c204500d107000c035581610040c0000109200d41c3c4160503018000424094440e1000f954500c0800c501805601d82540f0305140100a20516005a082005461408980030880509104c405034482d60f40514801220b8615440650b001d004d0301d02c241280b20640c8000e101e9510f45998080d038612159003840142c4040b00e040d004009120120120401881c0200413074104003d1050704c1e135503580d05031192074500031081c140c4440d00060700120441c68065090000c0100a080146100d002c1c4a006424100c000c081c5031103164000403922a0b00c03507240c4c04100403400040c400c00309000c12001c2602c2c20b207000c94010345644006c1c1da8084052400022440780307031f0341c020444c62604d02c20b050120703404e940c509140c0a00b03048113030030000040e10b05409401c2190b5100c03607920355820400741751802c1032403419035401440200c0303040c040982ca500340a2081c058002000604507103c90740102d40c10708465114400c444203032007506040201c5074211520b444607060881c1c0303805031920 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773771007 1250 773769757 773769781
    0x6150602160b0f070b190518061324050712020909130501020c070303030506090709051c0809030a1103060708010f0e0c0d0c0302030f0906011d180304030c0e 69
    0x6200203845030202010001c042d0040010050429140c0c2c9040c2041e000b90f541242a00c01958001511508250055600415407003160791100095240607120781c107402c603940d200c44001c4c010800b4020300342000c01c2400007002c3c20760b9180c0312541e00b0541101710245048000e0809841d000c00047d040740281c3c0c1035421034001d90b20b9111004003500241d8444c0f1520305420704041004032042d5400340032910681105000d403400850080d04d002c662803412004101000d000200f011051140007803090000743c803601a00d50303090a0041817014100c01c24100300c506801424015907051048140100c10018540340410b80385c5d000f80e0840c2c00c0d584440e00107990b00002402000310710041c0034002c11002000c0c0c0007441c0c109a019513201d20300b40d1350396081030541d14007503480780219400006101c001503401c1c5c1c1140e401441d42e00504465414040c1007020788245910444020304400003040113003040f4140c0070b403803128410440f6a10307070380c900c4c000110400c3d40c4201b01111070f90200141034140d00b9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773772257 1250 773771007 773771023
    0x1e070501051f061b0606030b07050d06080a0b010302090a1b050a02070e01061b03090807030c030203100902031b1804240e0309040c03020d0f38012a06150602 69
    0x50300e1306403c9510405403985006584201902e00301d0303c4282c00030104040032070080c0220b0503980c4440d40d030312801c4032500680701ca84e07212a60950000c2e5818011594000046054903811260b408864032556101c9024004c01d4220945c1e1550b074002104460341c200d0001e00030f02880e90203403454555070345110714210342c00b44038903404507006103500800454140a002c2e00b05200c2c1c10200080b03912139066600c1d1801d1500103c0b03030070000a50910a40c5010400c02d082d102d07601c030003442101519130210351540620801043d40714400c0544150036502d03440e0b02c0b4901d1500c00c800484a28040c10020340324012483c180c000040c16030201450815940180c10149481e18000c40c9032500c0706062000520700c6034581c40c00c141e03003844184c001b81014003510009134020f00300418400309010070b420107800c01d6110031500600082200e9003070307510008081034485003420140c07240b141086901c4181c0002d0b408442007211503e8040007000b80c10744c02040c02580d0a607030515519282c1100381d94a00f45 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773773507 1250 773772257 773772269
    0x1020f0a120c020a18050105120a050d0e030c031002091c11012303090d1209030c12110f0a050606010f0c060b03030c011104050f0411040b1e070501051f 67
    0x100340320050440d0700404140440601c050081054645d5030000d0340c845906948200d084142c80d90b00400030f625000009610014040000e400300110b25a5855600c40b569002e240600041e02c0410901d0b40d400e003c0c111840001400f0744840d0b41110345040c00030343c40b01c41c450348507a040c1149010b5610550181209c440e034001d010807091900d041c0155400c080240c00f41400d4507030b10b54081c2d1a000304c40c4c0a14014801040141021000c441d406088624511000084645000d4000700420351140703101d01d401e80c2001c42141d80c0c07029600216420114030486a0040c071684840d8550800d0014000c2c0d807040c040c1d801c3c1c80727491b29008011506120030320042c800160388a146840451196030098444402c010112450300f00c034802c902c0d00351429100382c01181e0001180070402401d2a000d42d04c1a140d003110104403403940c00030407544034080da006004803650301040c01c26a130003240c42515007442494a85944800390351038500c8c080c00e412076100b04000c0d100e0b45400b6100c41040041025190 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773774757 1250 773773507 773773523
    0xe1f09032109060e06060a0605031b21180706020106150e0d14150a0b06190e130606120504120c1b09020a090605130302010c081e040501020f0a 63
    0x156000e03540c404140030500482250764909000c0014a240308000b0404d201202401d05d41c5020000c105111040340d00050500c2001c00c20002d0401d818609061000100550b154850f4171024251a081d00c2004039101000ca084050008080f0102042d04403860581c084803680798882208a0030380d801c40c404c4000c3c60b00d25030b443c4050940107110102c06407001030402d101074209a140e265001c0e4010b50b61183c1038124081020044190902e600d9029250355004e001301903403400813609a02c074180381600507005e43d98101d000d45208001c6900760a4009088800881100741c80e000101000d00c1103101080c0c8896045070704880c503010b03417031040740c0241401490031010902034409400c0b40310b040f1010b01f40c2500380c0c1456501da810b8507014080d820740c016122403403540054101d40081d00080c1c00d211003400001000e60150410300309595080c608035080c0c801c18a01151075015404040c2c1c0244840000d00c254008004060422504241c1c203d0f06c406290100594481c0110700e070282c8040303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773776007 1250 773774757 773774777
    0xc030103051903091a09030726010b03060105010503180307120305060301090b150a0b070c140303030910020a031b08070f1b020f010e0a08060601120c021009020102100e1f0903 77
    0x100c4e500340b09203e02d40280c00401e141c11b401030006418801c690300069256060030160701142c4145207104000c3c0c8e95104d008011503541100003030741d210350511815042240010000b504080f0405140c1280105c88080301e854120900d80506907121118480f40001d19005c0042c10502d81400345402c40c41c3c0011025080b51500d0718001401c1c103400d1300a54118882c15400151a1021401448254000c881040115003410a0041168442000988258030500501451100100b040d142c0c840038028010f82d140607500e401d40c09003002602107126911801c10345c00c90590004e018620542031969100500300d144030301a00d5400c400c0d402d030280d281181c0e40e0b1400505101007408110081410002e01219040d40002c614003403035000030b01c054100b01c0c244031040d40c104940e03540420480509224104248800940e074500201110009a8071038242e842564004d101880c1000640c2c0028031003d422102d0341941e03030701e103a40c42034035181460100040707000301845016009030381580d40000803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773777257 1250 773776007 773776019
    0x30c0204050f0f16030e0a03181a0a050c01380105040605160f0f08040608092802240c0f0c0630160e0d05120a09030b0c03010305190309 60
    0x180d148169000c1c19500e0202140d5040c040010401d1144230740d480f2861042202c5450382211119405241c00035030328601d050b20380c4074840035204402181d00d000d42d00e40301640c0c20750f4003501086900c036a02d400c8290594802c1503075103080c00c14200905160003000b225540c011100c40c4914401d40e000108280030b0541d00c0328002c0710162030f0074000e82240502c0101501e40d0b40304404c0412044a22000003d01000855001403210f503000b00a00060280c0004003492411031030f6034064844010085d6405003004c56492061080009103c0700003244002214190007083d03500058800310300d4814608012990040050481617404014020038180b548408400c0c05d1941408400707442031a100e00f1600709944888030b2584a0004000c469603401c1c07444070050424180080c14500802c40400c2c0f510104000182405c55030790340011a42e994030b80140d0850f4040c0503078100134605a6840c06004841d420880514180ca001d042640c2c070312000d0403c03400d65845c00040040120741c214900300302c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773778507 1250 773777257 773777281
    0x601080c031609050a0906030b0c04030b180312091018020a030b0c07050f0307060605191a16060e06010501081e07030f05071706040603050c060a0e0d030c0204050f0f 73
    0x8a042c4509003071103602d440b60000307848890540c000d1400d441c1c0c0c90800300244082c1e065510f4110944c2424079151034110307180c0c1c01000b04001d00b182e03800c1a0001144941303100401c100c40c1000c0424200012030b09040c00210740b50702c01024008802c5003080290b000d2142b50201e000c0040b917004102004080c0740d40e40340c507035805005000c01c19070b5209106c5803000c542c06104002a1801c41c074051076582981d4501101100e40b40d401650084503485168040303183c8568450040c1c1d985e00c41d1440c84c2610001100f80148500e61455142c2e054a402d40410810542c010702031040c4044181c8103d42c1c0c0301c00046130504270032603900910205003407100a501c1101022560810f02c14034000c2384244007600c0060079180251860000070340d100d001d0b904690f109007041a042881180c052214a1454403415a80d00800b28814400e0b03200145d83c108050107000e421710400300c06801e080740c48000d42000741c08000480d10aa0189040000140d0820400c03d949071003041a1002c1f4062621140d900d11a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773779757 1250 773778507 773778541
    0xb030a0b0604090f0309030605100302060a1805151215011d030705121c18140f100507170a2120070303060914070809030d1109090601080c03 62
    0x50016950f08412000c2149010310701180340c043d40300c040b500c40c0386281441c215074000f8040c00703400003403620500050b6075040459004602c149000a030344026030031450300f901d2580e40400d52000900e004803141d513621102030151540300b88400341c2c681e42c07407070640003560051341c151030300045420070806200c3e4414881c0d540307112005000c07a403176651104046402c0c085108100c400d03951241840b20395240b0b0340314101c0702c45685850503a40b0601c24000028601d4050b000720341c442100740303540451030349a44d01c50041080c40200b141d4044140301402030240d9008d880c1c2a84c407400406e030815003614054007207135228007030b507650b40c43d03a80030002d07201d002e07030881c00c0c141c5801035140c80d581805c56010300c2d2006400d001c08a005581c4201d03d00e4080c0c11140c02c0d5000b000f50b1070030190900310780004040d01c1c950003e43c1d818046419074520b007181e400d61080940c000103191501c0d5451419140400250005040a440000342c43c0c6a04005441c0395404071100d421081c002c0000494030204084058 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773781007 1250 773779757 773779759
    0x40804170f033f180a02030102130e011d0402010507030507050f1b03070b18120d03231006110106031403032d06061c0c03140603010b030a0b06 63
    0x1c1c00c0011020480d0705650152403400c40003102c1402202480032015100e0b44680748a800140603c52150304480764000300130013210741c5002e00e000b00480d943e42400100e03401e0354000c000311b40e1107240e0f80d082040754200c0d0060b042d00c84070883c0007281da10303018406110000c2904c130a021543c0d903142d0044490f98002c030b1044042103000d110300710010390108901e03c1e100d04024082c01415241540c042e0414030300000d418400e82c8240010811454a082200d03040c0f00c0c0606001d0038505070901194440b4510303283d60719a849950705c550f05069051b404001507041c1c0340c12281800380d4001200040000c00d4810301d0000c03082302c404109107802051030315029904900081242c641da615021407546001d01c0e0f80542d500004201305d000da54102100300d81941d1507650101c1c40e50039504e140c10300b0500402c1a40100030000e402084140314107404a02c0001c0c8400034081001900300c018040d04042c0f201e940c094503440041000e5203018019880400070150003400341c000d9646400300d1040c4050304007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773782257 1250 773781007 773781013
    0x6020904020c0c10030c08061005070c0609060813051009170a0302070203240c03070c120f020c1203070f02061204030c0b07020115030b091c0c0c090504080417 70
    0x11a415100ca001404207910b48401601451030801e09020140510140d41030415103007074400400c50380c00240254020070300369410100f458186400391098410404050201413100e8000650190700c8141d010a03101556252844c90310bd210483c44444590f050003026601f00810800c2550901d0f0300000c00a4022400034441c031000c2c3c8503550166010340303d044002900001c501c1d055040030401c940c140308055104076590013141a42841d2031101402a42c050300d000070120701502d208a0301d041d801070704a03848002444414001400d6800d0382d104074005030003900d40164080c680202d0150303081050002640c40c1014550f00c00196031740c000b4080368070090034403849107000702c50048036200310321a2311180c00101c2981000241164010880c8046a051103060348000301d03180c5020f01201e600c001802c94070380f501c40d0700d18140a0113400c200c0e00030100c115150141540508505d040328014140120244c1d25504001c0a40e401210f003d0701d10041048104401035040610f03420844c3d090050b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773783507 1250 773782257 773782267
    0xa030b1b0a0201060e0f13031419082d01050409060f02040b040509011202011b050c0d0b06130b24070b01140a05010518090703061a0408161a070602 65
    0x340c000303070420300240c40183c3d9902d506220110310383c00001e03008060310009442d03a140c007840500015408602c01810000403110241c0500385020a0354410088090380848800b00c9140c001e00001048400d0311006415028441d81000302108046201c030b96020070348856800c010034407003d0700e4048000c07244a50396518003d80c5012a10141000d8050a19140e56851910007000380e81c5806030401490003203a030079a800141c2e00b210810b688412100b00c07131641c2c0c0303e05051180c20401c03880c0e50703550080404d0480004101d00510902c0c0309103012181410300000c00c1007260115105070501e140c00c01d180020038204003000c0040c00d68040c8a1541c02d07803401041d0782c3c480c40002d0003a0700810855414030703d540554a45103c522000d464213103000c0e41024208503044000301c100b09003040c00340040c42c0120740c0c090b10a810a0000e00400184203107030b50301200404000e03920500c9039035140d0203886811000441898000d0040f01c500070420041c4070424a0f902d2080c2e80900000c85a1b1755007004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773784757 1250 773783507 773783551
    0x311010c05011409010b0303040f05370303020f0f0a140a050d090612020f0a03050a0f1a0f0301060e01090e1c020f120a090314010908160c140a030b 65
    0x80070f80e44021884011600d00f040d40b01c0600303541184034001d210303800901080c00340f0520303848400c040300c0b412940003004000b00c203100100e0704c541c2c40c208814031a8100385203031118034058072941200e1181e070031101096030a100050311000c1108105190340c10021440c0c01042e5a130300010344a040610a03140904680c1c1d451b685001142c0405c403010400e90a020030240b5008800100791154881081d0719000d045030740a040c40c4100c2d515078041c5695000401d0000b43c25612440030406a24000c111541c80c082600481a03c80a0384600c6003803810461340c0e041c1010701448007242c00c844000c14041c0d00b40301031140074000071141001d262188840a1100030314100c1e15002403032240d00642031041d11902180c0c203141d101901c10400781e600f001940c0703455511002c000c00300ca0b0009140c40c80030360400781903409000d0112000d0411840800c0c51078000141c18440003c0134803400d03940ca88135558a4202d000488400780366076000c15444020000704440001155000800418118075419952 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773786007 1250 773784757 773784761
    0x702010f090b0405370303090801090b0604091722080a080307051b0105010b0a03150e19020d0507030617060f0c1813020c0d0305060307060e010c08180103050c0901090311010c0501 79
    0x345c184000410703461400c000f459040004100030b05075a500034044c80450341c444081140c0083c043d41d0040b40d13544001428050102d441c020300030207251100f0750301c5a15100760703c400622076010002507611440001040031002a10882e403941c401407681c115514558103549a80041c2e54000c05900500e6907038000710028400c0c01e001e0590781c850203854204011004085944400c0e50426101c03e05400f480081c00010303405030700054240d001c3d025051903c05107806409a0458110040e040c1400d1180180d0075806c00d10944401401d0741004c00030b1850000d558150688610010b0341046000c21011300c0c206005110300f111010008034004505400b00b21f0031030101502c2c181030341c1c0c0414028a10035060042d0029001549400d004500304180042e44550a0b40320744014040e0403200900b05034090001f980e4080e070400319482d2140c42e030007002c681044940034000d00203072509002070002010241925a1600c060791030814141c00c65640900140346d000c08070703060003500031110001032424 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773787257 1250 773786007 773786089
    0xa0f030201031e1811010e0109180608120406110a1104051003050303130605010f0e06060703021c051201091a09090c04020705030903070506040e0424060306020702010f090b0405 78
    0x5000313000d000e20501d082c03811040740c42c00000390400046001101030b582c0d0040041060318607002d11030b445001c107443c1200041c00c007548030710802d01070190300a4284403081c0181048802d2516806003054041001a4881c05203110081202165082ca0001802d0075030129034000f1380070005000481d01c0341ca40900e0b64104807000d0f02400300e0700310305d40100103840c01110300604141e0b002d20f03d00c908102450f0b4188034028011406184003060709030a0520801c143c4804d490040740019035075011003002016680b0400d600c1101c0c090700400012500901d2050b02c0300b400541c55080ba40320801810480042000f0740400003c1c400e030541040c0c40d40c1e0b603100401c145440795005660f921030103c1454180660759101e18443d82040c0001c02081c0d9030b03096841d40c01503010300010b100340100310340313101d070200c81005182007145049030200812190f0750041002c01d0003620354413600b9070b02100460b00014607001d41c280300c1c201403104100030308201c2408442c0031704204ca03d4001c4e45203804007c42c6c002c21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773788507 1250 773787257 773787281
    0x7030207080415270504090c1d040b010e06060405010c03021c0509150a081816270504020109060e01030603060f06260316020f03010501060f020c0a0f030201031e 71
    0x1000042501d16500241c68410010800f4480e405101140d07840e4540030314644502d0b400307162a03050250400102c5148c1d08007900001e01c0036450030017507184007424018111002c86070440200000f162110511601c0c92152600030310640c03410b810700c801100c3d20740c52000101d0540c49449580c8000b4001d480031002007484641c1d5a0380c49140c9a070030003845002114108c3d4a480e0308110084100d9400500e10f5800a01d02d11100400100040040c4c40c0100100348511440340f101404602035101445420240104085910200c0c40d20110072040360300550b0000e000c0366110300c041207000d0140038904fd1800050500041603690f90b1510380641e58280408484a540c5440900110540352020200502c04428080303980300000400b55480c428031040c560120860f40d042c4003159588407400c0050788024000b4407003075a58290103004c00d0a0034280802602400403944514108280d520301200d113810104420300e45580c005400500c1280003055420006100010b00200d05021b1984c011300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773789757 1250 773788507 773788529
    0x70e041e2001021005040b0105091008120d050a0b010f031a0d050d032702150c150907170a061107200906010507020f09251e020607050a0503070302070804 68
    0x4601d00009041902d0041d18000c1c6902e04814007002c10821142c0c581500d5040d0741002c0c040e140d60352880c109040a034019803151207844442d081c0b02c1c2500e40540140305841c1c0c8140400c0c1c0b903c0c60349609645d100c401d801c0c00511081c1c44103e081e84a40c22001a844000890075074210f1104046400c402582a0941c1c165101c00c1c0c1900f58254180b14061100010b800ba400008007948960080903880d084080c2c03048440b10004480d00000204031040081c4002c2160354490b01030941180c0400300700d0b60001507010726030000448000380c103114040d450400c00645a1402f4641e1850010200ca4402408008041c41480e0008420300201140c0c050125030840c0c04988050070805000e90081003030303042050600c501e00050b1208088020355240803180b00f5429600d031310304040500e402010101c03d640c10103008038081908540e4100d200d11030400c02c80c12860510308107a0380d030076059a81d500010710410491991340d02c10005144c02a245140151905030360740c6420140d07400a800c4251072070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773791007 1250 773789757 773789813
    0xd020f0a12150203060a031104230910110a0503270303150d1a071202040906081203040f0b1008030a030c0f03090302030a0f121a12070e041e 62
    0x1c801494040851a01c076601540f03146005c001150915084e4440101400e0380d0002412507551550042c8442c0d070b241e5032400107a41d000c803404880f000c0c41900d12000c18010590503100030089802610510b0102c2c40680780b0702082c1c1102259030381e0004141d100034900007200d001d801ca440c00c0442c080003400304010342c0c503810201214450b420044018a1280c0c1c03a02400b400000c080200e1903106004543c101c1140350384010080d01c08028100303040100e0362000502180103a525440b000c29500400c04071003001141220204540c8401c1d2405802c1c1024420500002284510003540c8038001403500b00255035915030103451a00013820b02404291101071130300540741d2104c0c4145032641d003803400f40450032061310082e40301d101700c0d00c0e10000c0000c00c15603c103103107014a003000f101c502c500e00200450803141d0309140d01881015010348c805c01111071011080c0f08000352040c1900c001022100c8030740c40d1569030828181d8841800d00007c241ca0350810045000002401d1a040d4005a07558200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773792257 1250 773791007 773791013
    0x8060a090507090c02060a020c0f0a1b12020f060306030a0f0303050105010f0806010f1d210d080f07030203150607030201060317040f051302040b0412060b0405090307020d020f0a12 79
    0x12402e0b0f500f000420a00c0c00e00e510000c5580001c007179402c0100b0500041c0d440c004010740e10300703010a1004100030b5100d0024041d08200f02d1f101c400c42c44250848550070115150101003013040a061130295000400461300350403032070110000c5411100050441c2e100020700e98071400c031900c14400c1640400d50f5880100102e503040114004200101e1412104600d03000001038010380340042200c04009101030b000d1103181d640101c1c4412110020321001e4801088800c1c51011500764000c0c00e00340c065210500b4146004041c00d500424001503604402c6d03960007003c1b0002d41005090320907043c4078000000140e21800000e052440c020360010484506509041e220300311280440c0040b14810081040040d4450400e0300540d0b80031900d41903110701081401010b8040c0c0d810200c1174140000f0300041d42d40f0111100220340d84940b81c2030012101d11020003044a40031a0740340c911f6042000803e0052901110301007032180f005001c412200d85c103038081800701c0310b83c0e04595a080241c5c0c0b00b00b414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773793507 1250 773792257 773792263
    0xa14030106050d031b020a17071a190c030e041d0c03030901050706050c070b010e161403071206080d050705060c03010807050d0501091a061306050a05011808060a0905 73
    0xe4001501c14501c10700c0d06a030014031180c06803d005c002c5055500e0b580045507510603110000f01100780d4203261751000d001c0c5071307a11451184555542c0d80301c103641c200c4801141c1800d403a500c2e9400c00c05140342071311607082904d1156411004504012403504440c0d025662441054000c0d502003502d80c8100c880180020702d8000800c6049100e54000d00c110343d0182c0e1b20404559003258010404902a1540c00b81d0303600754000e00c0300044c807120319200007140c40c00e0315680c103e100388184d9444008172507007a00d058407680c030848892070381000b0400000341300e14001c45c0010511800c540c0c0c00039034142d50314041e40c100030480645200281000840c00b05225080002542100003490b400b8130710751404049a40d00c10003481481e010320054407060062003800c2d4842d0300007980002200041e070a4100020105203011100280319410416000c2c1101c0c8240c03050900395407024010243c400c3c180030055036003030a100c0b40b0312414a40e42c100401c42d48014401c15000d04813072000070600d202c2d14070b40941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773794757 1250 773793507 773793509
    0x703060e0c0a0b0f07050309090a14071e0809031306020c0f12060f09120309071809030206010e0a09020409051b0d0305120c0c0a03090602010c170114030c0a14030106 73
    0x101c200ca074000c050103403c0032034085410140c42c081e202c0d50340d20320f0b620744182540520340045911544400400c05801500c1d000100c030201170042019241d50390710026102000201c1c03019810001c0b0b000b000440502942c3d03102d402400c0001124108041480c1002e4610450380003180140c000703003011070060515030403842000c10102c4d51036a007600c0310850165540300040840000900d03000200f02e079150203001072008a071420030b51545e281707020a1095a95046480796820890002c180400da00d4480d10403107418541c1540909040d9290200c0d041d04000060841c00105517035000b4000141d81d00e100b09a4294420800b0f407406504e109980442c040c211421a4002e0300c40000600010340c1c000112401d104148000454131340b5100741403842c50280c091000c40601c2609255070900d500030f1441340c01c40702d02e54024845404152030860382c00d00c071031004660084242c8014003e030403110030f00040c10311015040f1002c59090b840090204e0341190700071001ca07030309454082900e003401c0c01514 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773796007 1250 773794757 773794759
    0x6060109050607020603070516060608060109051e07110d030e071508070c08040e18121303260a0503041a040b010504051e07051c0b0d0b0403050c0703060e0c 69
    0x2000c031407070074011862611840c2c00003407056200000260314540103030203880700c81c015000c508082003814641100202624041c482c1640300b070100014014107107000340ca12405a40c084000086a4040b0003603103d64003904000c10b024404d2482144050100142e0352483e42950b8003144031801e41640c541480d03050740003c5d10200c8403200440701e103508050071540084c1d0518146814600c1c605042c5698003c94100e118906808403d0000703404503110359001040c10b440503900d041660411110702407150580044c0100d1810000b080400c0c01d00000903e103070b1107446025055459080c015046a1114421501144010090100f8030007000c100d6640002c0e20b514581c1c2da82042d44a0021240c0305200b00d911564803500055082000d41112130140003002c0108400b034108000013274150303005622084000c0c03e50b4124200401214018140388960281211503503000c0c52f103c0e501c007280003c001342c0600c0b20820410710b0b580d0301004080010760080400080b100f238400042030070300c03011041103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773797257 1250 773796007 773796017
    0x901030e0d0f08070c060903050c010b0d020a051302070203010c0906110a05030d020313050607022515081f0807051003053615250c03180e0414060601 66
    0x205400700d42028902061554500f01062207650b0320008030342400303c0c440300034a10750800e51b85c1820550000081d00103c2c128100030310807152201e083c0034080302e07841c0340a5440320604034100b010341800304c404284c043d4011009403401e40950007103400e403007120034504002940810b0801c10103a000504039240001c40000d4000d98405403101d070323604d00605d80c44030455a40000810041c6500c0000c0e003030041e42c4082520755510380b0180c042e44490080281d06052a4500301c0342d00c0068120503c2c1050710395103040c040c43ca00a20104407410704000b80803210380e070000c402080346941f01c00c80e240000e05c2c0c8000200445070504040c0042c004007820448181400c0505000310781031160007001c0d820007101c0d282c030041302c01c03200c054061800c0741d500101316004180500e1203001d640e2126520072112801c0c00b1601c1c40580e0005400c92614105480000303103c603000100080c0f044d1400c00900d896080445091629400174a216210907182180c0c0308041031a011800071080c405240c0c806000d00780 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773798507 1250 773797257 773797273
    0x9140a17070807021005040513060f0807290c0601030606060e0f0f151b07090c090f0306020c07031202010b032a040f02130f0321050711030c0909030901030e 69
    0x40c0c0c54640c0107542000b0305c2420702e00d00c80010f1074403036401d6130000c120041c21b91603564076042e140c100a0045000390344121040e00800300b584100007455100302e07000d0054900541941540318010401e404441c9600c01800b0484c03a40d00d0070080001700d011b076001c1c01d00000e015140000260080042c2c517181801610006910152691480c2c00340e010340c2c1003980d4854401003c040504100e1054a80205070111006c0e980c501c0c04034001844000d80d988a00100000c0640300700a4902070143e00c1007002c00348101605100154294016083d0303201100b081710106038484da2408000c0f01035904220050b0b45d2105421400c0c03808110455000140074000c01000d4420400c00306c4100444c0b81080c091511040101081180d543c1112440380c1d070340076004034641c1c490a00203200000c0f440700361140d0040ba11161404d038005400c0d00e2290080d03407200c900d0701015540e0b60147e1128140b201ea0705000d00c3c2c858002d44e4541d071000911500d00e000146660700c56407400941120078443e40001e0a50001030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773799757 1250 773798507 773798513
    0xa0f03052202010c020f0405070c02031522080d18030e040606080c0a091e08070801050705041412010c091802031302190f1508092e09140a1707 63
    0x71094100798081c40c06201e03d503078500214896800ca07580107a0001d01e014100080b0561004014407141e1084007900d190346181c44448143c041c040d40d0800305125240108100003c0c0ad44465203002d1041b4403082c28428405504022240a02e4665104600c49881c11041552000c0c0c408070404080700c04100f11401d14400030110301004182c104055030015124002602078035a500007041c65103418100c000074029540e40400440c40f410f000340c89445004038480d44180034482c81038641d80d940b030b410249485809034107800c9108049812013900510340032403813804e0040c3c0d031101010351150318100d4a0b00b0070301000b1800c04034002000078414403e001038215600382c1c491900703804075041816170131340c5c542d4413807904650381c0680b0b6410001c050006010140030720010300c0b13400980700e201541e0340b650300301521684031190300900314910b40000480c111580702d01030301c0801700007000a015240b80d44c40300720841040b0860040c5034011991101041a0344804981007208080c0aa08018643e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773801007 1250 773799757 773799811
    0x103020a090504050a111b060903040614030a110d05160504060914040b060d0905070f060e010309030e03160f06030603080f0f2106011d130f09080a0f0305 68
    0x80142e80c81540c8034800b003481142950081c180e800030100010b65178500d44000740114149100184900c0c2c066200011034024020081d907085030666100d90210400d0204005c2044d8001040d481c101076807440390715a8995020003511210594040004440c1001445101040c46174112442081070400c0240541e660103d0b000003203900d02d81c200c0c25030074008400078010f4009040c015170010f50218000307144045540107200c810703004406070b030055070303c07401520300c5c5012074001c01010826602110300c0c01d51003a031001c40f0140c06498290704400e00c6400080c2410268559000210f84001c401e0280060b841030074402407032581400c11070180781d1f80c0d070700b000b5011701c4c6418800541c0c04501007001da12050200d07803c541613004802001100754520707004080054649500082522040010319102f200c016040072000411290307080d4560315a04010303241c201072001c3d6840d01d800a410002d030b801c9014040c11419a15880e1044840d80001022600001c0540d07840181004280710040001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773802257 1250 773801007 773801009
    0x30216080c0105162103050604021305010f1e0216590406051003022220030702060901110906090d1a0121080a1b05010c0806040b0103020a09 62
    0x20309007141c441d4140c0b0700482101e40308207005084400d900c3d01e403840000c1076170800d2001800d02c0c2c400b0402500c41c90b0522080b8081d9444064815289107401e1119601516040c000c0283c21301c1d06141030005800c3c0948030b640c8181501c00560710640044880c03504588000307001d80032003840001804100c410782c0301d10144032182e9102c000e180f040c4c9a4042c0140100001c011104039030b0344902e945c8a18500b030f6041100b124252003c0e85004040b411002101300c0702e800310303900113203050000340790900d40301048810201d00402c4035079260813030580010300108103000341442d0703c00c4a4417403500010190910703078010058426030345002c03a5019801014002d07910665802c7d540700340c0700e5400c400818118802c044014011180a46000032020500303e00741c2d06951030f12203003074000c01c00031568488030700c2040002071152205000c015000e0b4071484078130748204814160f4240048861f00c8050845030340c1d05601000070a6176080208600300303805085d580081c20b103007c5141c1519940020000002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773803507 1250 773802257 773802259
    0x60121080d090c0b30220614040606080307032f1207030801240c03030204050d05010c0906260703060302061305012615060913022203020607060221040f030216080c 72
    0x30364440743c03c0b80e04020303440c04c6c038290701078810441c400405c00701c1507100e502100e0841e000c0b41810408210500301105030750045500d074a944900c00e201c8194400ca0b890703000c1030b59006c50655541c00c10004c10030081c9500100c1c80c0c110850752420316040090445005821079000e0807542001d011054040d6020800d281080d440e080b100b8030b4652800b00c0c0a840703164402c5601049289541d405c1c80019030011820f088591250f1012507078400f016a24800020444004038800d06245e1703031490981910340f603110429140c009602500d80d800203210f0b4000341c05480c030b02c4880e40030a00c45541c1180c009000d522844a840642203841c12080034507500081c1100f45070350044101d02c4040e1200800e4800c1c2c1503000744090412956500c00c03900030740050042e800d01200d0315078000700d540040c1290708240c9401900903481c146494850b10080e42c0000703c111000300c68840e000192442c01604035000324407860b12103001c0035039428001e250130902d00c000790f213102000e03004200d1514009840421914 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773804757 1250 773803507 773803531
    0x5070b0601090302043912020705070306060e0a060806061c0320031c0218241209010c08060109150c0501021209060121080d090c0b30 59
    0x61000c00480302d080d400c0e84025002410202c911502c0580b0344207041c0c6c2418105182d01020000065003950302036020050300108100144580300913015400600b50140035204403400e09680b076603200c0817208507501041c90740300d4420510218030480e018800003000804010b14040c148480007a00c201d800c00c4040d030700d040b01011042c081500912052030803070f65003c50402402c1014044a0301c90b440907680700510307400003522180c220980d100746c0d4440e180c44d9120800c1c62000906110680303040b90b1000ca5010500c130320180c910030644000f8960030f41d01d401e0314181410100340c15420b6600d03031080603050104200420a969a0040d090b03000c45d04003034980040030fa1a64010b90f40748688540182a650001405004403103001c60318902803d61001122001ea03130f14483c0d024032a80c60541d085a0040610303171000898458000b504203681d00490014039140f81d5982c038074a4405940c4407070301550b808900340103041c074080008010703901c029160400b854081c00c0c0c0701c45003400c000d1140c00085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773806007 1250 773804757 773804761
    0x121415120c100c210810170c040903140a020706110318061c2405011e0302091c0b04030f031103010348060309033212060f030109020105070b 62
    0x80344c110005882c3d1072000301502e00340040244002c00d0504211008042e03031600d420002544868069000e2107072103040050210100320360202310103000002c1c2c0035400c1144241014440d4070f000402440d115010360000e08801b81782c2003000d0b04401b0b15262165060700103000d150801e01c4000c10300743c0c81a4045030082d84d00c901c150031181c02c103901d110113210824507220010500c40900301a00e00300612000601007410344d41c1c0e004541c1000e440407041e01150710140c10451050282d0080c2c8204140104000c18040c40000c0e0904c60107585003082d203009014000340f01c240340e00a408117a11041600c0e01780002c00c2070040004e50b511041c40003e11800d035402034120303400c12001e021402200702002100d150074400812071440c5003c482c1d2021703411503600000481900038410010300c40e80c580c5070061040084440c0040d0ba03054000c990000072282c0b00e02c0700720301003204001c003034400115002c4506800c0400500022030440014580139030f144c424460050707030b00030302aa800c4503804442e004441e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773807257 1250 773806007 773806013
    0x60102060402191a030a050f0403020a12090b0a12050108190f0c051c03030c0309020f040e07030b07021015120f0c03020915090f16121415120c100c 65
    0x600344d8030601c0340442d000ca01440845213000158001c02142c0c0c020302c510f4440707040c41c2041072420b480080160748821688030014a2a2045220f1b540741400e00303101e210b6075240340310110f5111252003400030302110903281d1214542c0c1300301d50160100078010304940d8812148803c0743e564444016201a103803048003010401030f8418507002e00005000800b888404445900001c5641c2c1000c801081c1010000c40c5018401e12a00031482c2c5c0050002102e072007203000b0b00c4014000100d010035503000d07600c004004620420103441c040c20155006101c1c0d441d01681c81c00840b400789890380d0035110a07c0e810020380114903480c101b0f141d0041507551940c40c40b07152030903e600d050b91000350001c1042c0c080180301110403446030000942552003403201c1d680c80c00c48000c0000e0440d0b403100d01d55007000c4950101403191405600400148800148080c1190380000782c9042c2103442c0c3c25115031403031100807641819400124050a644004c0c00c1e07105080c4d001401c81010f40c400c0d10104620200c84c4814 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773808507 1250 773807257 773807299
    0x3050c16030525120c03030f02010b1e030c030129090402030d270308040603050c0310030b09010902031c0207050102030c06010e060103060306050a0506040b0a0501080f130b01080a051203060102060402 88
    0x1842c0c01e030501d103103130805440c00c1e0700503000030300c825000f00d0400c2103200c20a40c01801440d20890340200444680103034012090300d00d410040a0981600c42d000d07220708103440900c03e54144031681c49150030b00d440c541d00ca50a01700c0c0103207060b9010b40841d000344030050700c0006849461031114142008824800c842061004074020800c074484107484c1d4002050194400040041e00c2080d0703803d102ca903882004650300c600c02a200700740882241e81080000c11070510300c45410458010002c15044000d8000a02e41200b00d810407203d00c107400040802617804110550080c03c080c00a1824240c2d004860f5484070b6051050303010f00780c498030010703400b44c2c425032101e00910f600c0361003040300d400e00302c0c4540001c040460b04140501d1070481012105c3c606501d07800200c0c0c9050751070501d07594030107081c1d00c02d02c04c0c040d02d80c601c100102605240014030308083c10f03000c0d000352002045241002c0c2002c3d490001c05911351402071008001b441042e03680803c0c0c0e654080c0e010b0343d5001a00c0c05031014211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773809757 1250 773808507 773808509
    0xb130f1205030411120c0f010207091406040b0d020d060b15040b0903060a02040f050f0604030c1d060a1a031306060f05030f032b0b0a0303050c16030525 67
    0x1030004000c409161968010026502aa02460800c410300007200309020116443d4000c00d0720582c000212450070b0710300362152040f50041841a100d81c55a1583d03078070261904418400c2c00c6941090400101b03007004d11542d180e0741c3c2c1c100c0c4d15606a40c201d4021900c1d01c00043c101402c02d03501c903410038109444038210711240420751036000350782d50b9440440c103919800040d40a80301e4001c0d2004603110f2420342c02a2010382d410382c5a000c0220f450001005681d9241d030645a4102100384000008140105941c100424840405501841342012103030b400e9080200003a100d036400c04c01c00d201d5024035403000c0c00b0b4082e07142511070392902d400340a203114136880701d802011f00d400c0500c04195984940c14a0303044400540031a8844842c05941d19201d00802c0301c0000d041d1114079417115a01140001c0c900385410403600020180c101c100440d9a1a035650010382c0410400034030740880c9002001241101242822620012030035980c0c2c5daa10b46005a4054400300e240150a0030106a1161110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773811007 1250 773809757 773809763
    0x11413150c020301390201060b0d050610050f0d020901033b01020708031303051b0106050a0e1009020c010e2517030304230d0305220b130f 61
    0x4469400504401000390001d01d00403030080d4213041c2d10001c4070000820780f6030035a4942c0c9a0040c0018849a4081ca5840340c1510130f045640b5000e0001e8440c450800818501600c4540840e0702d19205041c00442c240f88140a010403408204204540301120143c8021140080d00540d940413841c0048000c0c1a8030072411109226080589980144003182d15082038465142190f05c8400b20402030300703e015004018100900810029080d41284420300803031501ca030a049080229102855980d4000b0040b0381820740c0d980c00042c0030511b421407440000700461403006210f4582003555a0903108036200e080002c7d600814481c0000c1403c0d0450b8000c0400e0b6001c031021040780181c0c1d03010200d031aa840e44105206100041039400300040c455507000b050500552031031b1125645e504015403403000c203040c6081c203403411145100f0240040c40c400712040e82c000c2030b1800c2910202000045009016103c45107211381c040020304c1408446500110b5544d8290b02d0b01c0703040c107140c410b03206801c10007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773812257 1250 773811007 773811029
    0x7060504020406030b0f0a05070e010e150c15060307050f030307021003060503030a12050601080f0c0d0f05280506032802060309060a0b030d0915030e01052d0402011413 74
    0x2007481c456106c100c91140d80451420b100036200c100301070300d07118041d19040380000c5a103128006503040840280c0b000f0102070440d0361030700c01d40d10803607030404e8540e50b100f140e400285030034050285401c026040c00f8102c11290700d6141d14070040007070b944c3d224a14009004410072059000c0407806035111100801003c0c042d283c2d036030940d21005015003520911518068640b0300414080d500c608441c40c03040b581900a402c00e070701c41d00e03c0d1380d883d134101d440035884907512450b440c50148240d008444c02550201d00410f000304102c0700744090181c0c504403809a061801c420490741e560f0004180340751540707513410607541c500d40f007074800200701032214065002100001032003003140d00000e03020f00c03e02030f4010400c9003644e041c0400d501e07103a10a51110020780041c2080c042920b0324205542c101c0301d2824001594074808040300c1c20756a00701c17503801c1c02e90700c0c1070350403605078058a2040304d00e82c803088a008040c2c034090340043c01220008100407600f58000c51241503107000041181c010b04940001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773813507 1250 773812257 773812261
    0xf070501300b03030d1e180f080d1a010e01030e0c2202040b0702181306111308070612060b07060e0f07030f060605031b040510051804030e09070507060504020406030b 73
    0xb4003000f4022601004c0d07401a2850300b95640c00e0098401c072440060030f100300750801d01032900c904ca0210081101612700c1c00c0704120031400051148102d6204640e0501e800301c1400800780050b24a503000d60300681454145510000c400c040802d00040c940c0048600914054020b0b0600101d480200e4005002c00d00c001004074400d50024017800e40710748220703014502c3c03c1c03070010100003000d8150762080402c042503034000001000f980040e000c005a00c000c890a00151081202094842d944604195000f00c401404050f60080703441507140003901050124600d0f060035403080f48240700c4060b04680d82c1e06a000681c803c02d000142004140c50701b1100d486440f4104240101d840083c00c981b40e0786072a00c002258103002c244003030000340d400c05242e6040041c0c400d00019180041c4421261000c140000c20181c2d55801d100c003190142205401d03079403030301e0b14002d8a800c2d209200103100d400110104a0078a503c58111807607903500200114186d25284049400342917180c00003482c04c61070030300b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773814757 1250 773813507 773813527
    0xd0e03090a1e05060d0f1d010b0621040215040e061905061803030415030905060604140703090503091c060f1820030f0f070501300b0303 60
    0x409003145440c201c404144155581c15110000d081104040c04051142e01007004030340303000b10141460081082c4041101c2098114650844081c2034020003240b50002c0c080c407282c4400d210300c109050042d00e1007454451450059124903000307802040001c40d1140014045440d452100b484900030f00c403c160721030341c0b00d088a01c80c02c017086503284c1c05038501801c0035041c0d080320369200c4c0483d0800380c031042c50600801001007131001b482842c2034041c407040000103928034410415040b0a12a5600003d401c075151509504220703001d807445126038203000071a64130740da03d01203ca404c08400d00700041e204d0542e1805500718000d4002c00e0fa445a040003a0401c03224869060f580c51910450081010000841243c411a080910031003084101c80c04c40c100080c95410500c8551b82c4e00025100410510000291600300448003c0c9015004441c6071307200e002c1c00b000418041c00c1c003428182c929140045040a801c040c4101c1e03c42e06007030110f25002640d010340d1040c03030181006420b580d070390300c5000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773816007 1250 773814757 773814763
    0x5041e05090615010215060d050a0c080102091f1e02070306150512010c0801170a0215091309051902010e090c0c0706030207120f14041503050a0209011e050d0e 70
    0x25414000f05040c140c034041c640d0b20114248280c0c1042d00c03401c162a496032020700010a1610004603131900c1080c4154000c14a8034041074000c006500c0090b03035444812090014802c40303aa03040d41d9540c41c00e8600b0b1030041e041801c0003088100311030101c003094000c42382240740c05815400a46072520303200c0109080d4000e2107901007a140e0640b44404a44d00341210f5500701c400c210002000075171000c006007d400c48400700160461500070403100181080d030001412920f81000380035507040f0005400c0011b04146464080c0304044400800140f0010303112251540300504a44202c4203824098504687c043ca6918000040250503580645040e4040c3e1106607c5100c2d0a40180305408001440e036200e070086032140c6510011180c0310b440035410642e0300488510180d806e0152122181e2038000d80640640005d05c140300b8040e0a404050101030122440a8940444107004118001441e6041512555071340301c1821003591141c001c201c00c031441e02811442286a40c1444c1c24011046400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773817257 1250 773816007 773816011
    0x110a050a090902271002060c03070c0804140a06050c151b0a0f230f031b0705070e010605030103020d020f03030904181b0e010306052a0706050f090705041e050906 71
    0xc481060180484c5504000c0b1141d02601c00c400140d01a0380020440a040c00241d40c118207181044803040c00d0507552001160455003100b882c1000103260440e0f00e160160a00703004000c682080361509412801c0951100c850518100144001001048040ca10600400d0561044c00c4c03a0b00c0d1105610f0100400c455110450000000e1000e00c100c0400b43c100b182c0e403425102703c007841c5860200c40d0000c4402c60340000b81003204d0b01d0350810f14000924403400080544512400203040b100e030500003002035aa8044c1c112108028042c8010320050300d4802070764041680450b00044868100300000e07255100c0e2141c4c0300d030807a0400c00b2024020036440846000d00b0b10482700792540004518049450100c02d1040d0001050050300400124005900c8680c220000002d01d004580c151001c80042d150716500078031080c40002208401e0001d184600798000b00c0d070010b26030075828000c01c40341d07070b0b402113010f0184525a140e00b005010180c0422402a0310b090110034082c038a45401059107540007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773818507 1250 773817257 773817307
    0x30504030311090109030f110a0b031e07080604020c01060b0f040305100b090610030905072c04120f03141f120506160507021f02010e01110a050a090902 67
    0x10311440036220300141c420f58180f00d4040e590101010301d1901c6051410a15000541c0c00b904049045402a2181e000780c82c050314001c840540d80303007400d0000041e1030310504a1200582c03005010f00c44025481704809030422400c84d009078030713410801c1c01d960061030103602196004100290b8284224400301c003038411a40607000b9541c1c0c0f1554540448203580890050b240e2082c002400204180380180b4022580b40c82e500d4006181d0045603900c07482d2440c0381d040500f4205442203456201d003a03c000c215840b4074411100002418166101c3c8501e90f10514040d080c040c02003491000c2511907440312200080b603e112084a082020032840345c900140201c0200c0c024180e00072518014280600081a81c080000c00c040e035142101403110035603a42104041100400000016958105281360740e400c00d504260030321842c0105c044d085900c00e031181160359052030080000c0c00118029221800c0007420016a1410300e03d00803281c1c41d0aa8200301820b6102149502140c4540c0100e4651403103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773819757 1250 773818507 773818511
    0x6010e010309050c060309030c0607120b0d050a2603041104050c0406050f0a120207052a01081504091203090203100603020d020d060e010608060613060305060106051305100305040303 80
    0x1008400450540d45980009040c590044000d035a035810700100465114020205890915030116681030500b01d003510b000b000514543d4090300c520065200e1501c094108803464500c0c6001641d510f0303100d0032803000140034038000400d01d0b034811007403a5405824040b2206800d40d203141500e0800714100d0400130321402203181800141c9101c1546040b1010303601075845035801c0010422100c5010350164048404001550305100003a04250001c0c281d03c0744180d01510070400b0603179441e2468507040c0041040c2e00d0460034642000d0360801c0c0003e40144000a0250407603d014022801400c00c100b0010040c0d4180c80c1e0341100903034503510040c200f91084098851a00c4444084d100761000c40c0000b07907000240400600044c60081140c120091048001240950680005500f180c4450388242c04a802440070403400745814845c9410442405070104212811030701c82c00e0f500c1405000c0c0800348480024034901940c10444a103008001c000c04001b56074000d014028040c0c2010395040b40803034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 773821007 1250 773819757 773819777
    0x403031b122f090117252a0c050d0c08010b03061b0706090618050f12070b0411093310050d02070c121505071709031902060601 56
    0x10b800c07407a090340000e01088241050100c540034845041d0f000401c01414030100d40713130120b848100d440302e040c8964030400340c4030f6440340d00c14105aa0301048000100c200881900503c08203e00d5000156030728200392170070207070400140740030b1440c010340790042a44600c1920113501002131218100301a104d1a038000e00c0a500110107242d44e0349000c0e2500409222071910f0743da50b6940c114041c004460280f007020512440c179455440031100e56080c1501e9601104240c0c1040c44010414600600039110061604200c05000c41c501c034012035000501082c03103000420144120385c4000840b0110040243c410782c10800107034004c90a0401c428410007800030b106240320140c0421044903624040c0c94401c01184040084610307610008100c02c03556800d1200b0004114100c1c03100020f018240307160031400300c15081c00702c10b40409001d088121070815040001107a4070012424410105c03064560054481043c0305041d80907107801901c244100c041d00d20001c40d40041d080b40034200a80355202d40c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 773822257 1250 773821007 773821031
    0x20d020705010801032d12030c080135060a02071103030307020d050f0c072d140609010c02030f0c0f10081302010c0b0c0a03060f14090403031b12 64
    0x510581c0304160116032624010404140d1001072040c044584005002d000200040004600c0314401c2c016201c0313407000f00c41580c280e9014880c040e10f6541c030f070416602e190301d07141401c2e500b214040a04042e01c00c0c0b1000710381540c00064902070145c0010b10039038845203000d204020003500311020669120402100100c0a414044102c034003076807455000c4d021280c01000142c139960f20000c0c089280c40010000c03421424420711407040039004800c840031480b40f0340011407003ca4800c0041c4c40b42c5513075075081004038403440028840c4500003552520303100c3e52200010390340c81c0900c01010750540520242280481c1c008502070f00001e000b00c5031550350032070040500c0116240b070381003e0040341c801b0000ca412014084402c2d00e0451051504035071070101da0350380000000099903c4800d00c4000b041f02c0e103a440e05805260b020300110003007404603074034006e50380d11a14070010581c1d01071811100803d09040c03281d0043c040c0c81103400101e90148146039001042d80c400340c6401064603180c40100691 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 773823507 1250 773822257 773822263
    0x40f050114070804030305071103070605040b01170a030e360a0b011220071a010b0703050f0d0603060509281109181504051005060603190204050a0305030307020d02 72
    0x400070b81d0381d14206581e860f40e0a800400c0f0103000641408484055171044404c1040200000c83c0b0a5101260b9800c0900d800c2c4600c1006800c80701c502810760101d01842140050b02031501c0782c2520b089041a984000400c10500c07540d50484441711008140005869200081103840440d500c06240d4035550402e404045500380040540041c0160301104000c1e03401c2c0c0c1052a50b154a0084501c8021241c42c07804440d5204d200c00316102e26080201135011280042d10b00e004105580c20680340804039a0014264403400c402440184008034104400c00415407201d0007459005c0030812241c01c000103500d944400d00c800320007101c20480100a00c880c10024038171b04641d8451104109010940200b11400400502d5112201003003050b00a8810080140000011030100500900d060900f810b6060a818103190031005044c1000d1040c640c5480040302c0d03200d2140b602d4942307004101c03d40d020192060340d0000da071000c4041008000d003c000f00045010340b406030200c50700c02c40200401e9803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 773824757 1250 773823507 773823511
    0x1603020c031f1512060615080103051515030106080106050a050a0810020a140307030c08070309030e01030b040e0a0b070e090106141b1605100918020a0e0603040f050114 74
    0x2c0040740307110006540c1220b4100d504155884030101c84003a84400203618414500201940c88981320300040151182c3c4914009544d802481c1018482d070441e21031071ba640c4142040d44040090310000582c0740e13041d004c640041924024000e2100b90343d9418198082c002034000c013445141856800540c40c80c1003813494040700c0340800a001d080c0e02c929000c400135008240e0720814410100e010070040c140c00c200030340c41107446450004040c003440900a200b140300a00c1070040c9440c0080c1080071030781000b00c410443e4424a808512509030501050142c130700f03460fa1005a200310030f01001000401d400c224816001562481e500550348000c0154690081c411940030070035540001001c0090705000341040c800150700200003e080840365490a0100c449203049540304480c00c0c045032404201c4060b180955250180d5517500742100046010a42c40082d1020799000404809107402150142c4001034010281a03da00d02801c0410a550305c03041d08891951810700050340c107441c0200014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 773826007 1250 773824757 773824783
    0x5210c1002100504020102010b090a1b140304020d051204091e060e0c0a05040509160f09050f091b04080f0c03070b0a0c14010f0b0934030f021603020c03 67
    0x440b001d4410341514006150103041a81155280c9020415640300d6045840c000c070b40155001903c94a020449030f40b00f140040030f00d0420404036101088905c0070f40549400c0750301241c00f00e2500c00b4628155140c058440c416034105100410000759000381d660106400740c9164040c1009441e01c0d84400c022690180228001981d040c4007003603040340b000010b03000300071b0700d0f051142c43c0c00d031180006688101c0440c0c00e48072614202d07042d00c28203030303200d03400c0c1740302040505201d22051708000000b244055011080341c003034502040012070001c01c0c0c805032403035500041200d6a07143e031100e070500d86482043c2d1340c0040e0340c418455010200d0900191282c104d601c2d00c40043d0804400d2141141c0c0440107800c00d40b007600800d40c04500c06502031048850060b0b18450015280c00e8a1040c07040d000700062a000d48409400b200d5034042c040f6101c034101e1401c07080e200500114004000f0780050500003400d03803415201041d009011848095644401c5002c6d800310750b80d4100041c10540e0b1034a0040c5d0308 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 773827257 1250 773826007 773826013
    0x402090403050d1503152a0311130e0f01060914040e2401061209080d02070804090603050a060e0c0d3504030209010f030b040201051305210c1002 64
    0x10302003407003803001d03022054141e00007040440c0000441490001141c1003501d2101c00e074040e40514102d58402c0c40fa002c24019005d9941480c1c02091500907800c9580c00740c141500c614640604110910407595601d010200f5101036070384403141400c0e10306c03080310794080c003c0d00e0f8000400d0720350203504054200c0d0181010310b20329406402c00d02c0301609200e80c0502291042c2c8148114042030000d0548022880a03d1443c01d0340c5002030082c40802c100021448807841c201c2c461010400f5681180c108000228000da079449280c500010540715039440900014076000000c4200b09000c00d29406280c00380c1c100b40305418040100070b0f00c07944409581580304426015400004003000ca81100020b01441000c2424031280b42c08882d40580092401410310300107401e00441ca4500748441c054007503520341c0c00e11103003180e0300c8092110003d0f01c0a8180200450341880d01d04c003031540e52000d42005040d000300380c4900a0055281c10300450000c0c03240c001c980403413155007005015503048600f20760003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 773828507 1250 773827257 773827261
    0x3030133030c050708221a040306090218040309090b09090a0b0601050d2406051e090f0604080c0103060e220602090319030201060806060a03080912011d15040209 71
    0x2003a8018598800c0b00c0003806000d211540c04103440b100a01020035062401e5140303200e480b083c80340c506a89030801d4a4030f0703030b03c50000000c244250040d2000e5a03030100000030320305d1290000441c1c603400016030b03084056945080200301030b80600d0403411621220400c2c05090500410000040803ca6071210f040d4011000b0602007003e180160390040b1041c1800d5250010344914203003650120040520f411713154240c0e07001606c600203480350040c109032800c0750402d601c0038101c0c0c0103021860701c00c4001680114a1004540e9080040e0205035001441d20340d4a5940b0030b141621000100880d5000c00e103001800681e100000003014802d03009407141c091000f003401050b02c01501c0030f130f9095074070035420b0000c1c0c2d0b0707161000c016583d504083c600e1102e0344034a9510700242541d5440e000094142c0021082c4030013504e9482404041e41d501c800702603115a210404035a5111180356081340729070910780d01c01150402041d40c0816248403106a4144e0050034039a0384035042c00781da000f5004030401c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 773829757 1250 773828507 773828609
    0xf07030c11040b10051e032806080309010f020708030d05220512071109010e040c0803120112020d0c03031806020307021008070c2405070e010f080702150108030301 72
    0x307100380e02c6c8196003a070401844510208058000b21281da81c4031000a0350a8221000c14102c44440040840144a030509101c0f415032a8000c182009042c48400054108418024815040a40f04060460340c0b1045444070802c081d2005803692103107480707416400c1c1c00412905500103d02038100c402010480030508103031445034041c82051703942c0d10307044103110442c2e5660241d087c020b0901c0301441240b8101401c041d44040b440341e006150940c42000242e075103080040c1e80b58119650019aa842d060017800803404d1000720b10300041c2000c043c2c0c1008420180c0050348541000201507040c640701e91205400e036541e11528601070b503c0000c01810302c14040c89a280030360300036428a42102c1c6442182c2d1810b403003039054820740685d00c0c2007104240350000036220389640040c41d407a0002c0c40107004000a001d00c1d4510124404000480001500050007000004042d00d50045565210b60303554001640300d07082070044c00b00c41203500ba084400820f0b81c2090120107040c0003001144101010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 773831007 1250 773829757 773829767
    0x5190305280c030818030304120315030308060112020c03270f0603060904050a0c1701150608060d030203130603060e09010213120c170c031615140f07030c11040b10 72
    0xd040742e031581d1901703403940c0c6107038001d00155003d6440340c1d5a54007007131018400035081d10318846481350b610f0480e490400c0442d83c002c2100d0f40200003800c102c0d082c000384010760b001030702c580c00388000c0034403001034500720048044450394004a002212540003480d000c0c1080344942b6aa2180340c3d000100344089011342c0b03042c3d071941341c000381301d101150039683c2c896480152100e2203038010302d0382c2c040340c5840d8012120280a42042c041c00410800c0400d030a00f54007038583e02000c0d01c014050303001d032843c0108140c003c004a80140044200c0102025503c20307008000e81028000c0240240c5440c011541c1d1200500984042e085080d100d001c0082c10202243e0031440f10901c00d44440e224681c000910011040303101700d414100e0000703851406c40c41000d04d850b000c0c2c1e51040d00c0109000c0c0108015a203a40311903035004100516128410391403d600b4200c55000314006810107401c006080010140c000780f88039801440345074510440e00d44502004221840881010b8114002100c1e41d11428414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 773832257 1250 773831007 773831011
    0xe06150a14120a020301050f04031d0d06020d06172b0503011e120308150a081002070f120306060f020102040b0f09031e06100e0c09040905190305280c0308 68
    0x2d40c11a059191290002801d690080c2d898003443d0324a541440241580a4481c000341c540c01c01c4010030803208a80860010900341e200902255030204052110701940e42003200248895281104240048400d01c0d850340c040030340e01d0031003903040c0d500c9c2079900c40c100f03200d80c0400005440d81030850780707403200f0b01a40c866510214000c280700d91801060102e002c400118403980690748055044c42c011200500425609038524428142c82504000380700001503500b8016002c1c0c0700140c0c4421461a0000d4103403450003000f008030302410005298103602d98090130880d06107950711942050a041c081e1b00701c1c07145016282080c94200071002000003407000603c41c44201600301c07001003140c400503e030322a01e010041000c81d00884103112a0440d20b20050018103581c0e81140780da41040c45913a41d0a03c00d414a841c05240c0b80e5240b4000c0c00740a00c900000e07517085040041501005160003003166200340a40b0f00e075491030b41e202081e5550000d0b401e030071030782c0c0a488580303030a00c4540301a0303121840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 773833507 1250 773832257 773832289
    0xf01020f07210606060503180105151314010b070501050f010b0a08180a03021509070506040e061f020c040c0f08040b06040605060703031a06071a04060b040e06150a14 73
    0x30802d4100010b400340c482c00f0018440d82e52210386034100b4412241545007840e843e400142c0c105030502000d0084505007200060b0212030120340c000c80d01100701c001c0c041c802c0c1c08450340c85e100000000d40c507001c400100f89081c0320360005c100542d80c1c00e001c002940340c01e0141d1488000203210554509014511658000c80d940290f00010880d010b44c0a00d49420300d1000c80060b00300c4c0103003090220000722034035004010300002e4580070b0704000109805002d60310a00740e10546401c007054039034803140c8504900252010030291040324064011351b481c29821007841c091480c118006040a210f0b001080b0341782190341d035038441601e65072513404141e20050b15407079100d540c4180c0020b140d51076000824526100c0d45000c40c400040c0780b5240f012940042407140114420070141000504110780c1001ca1020510400c90a40f80c500b8207000900301e070104c0342c0d002458042c049104800000c0c0b03144c81013458401d0109021080824001c600074544100c1c5d28030b1000710b031032004610740390a2030b191f0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 773834757 1250 773833507 773833559
    0x4306180804180212150405180d030902042007050705030705090c0901020c12150603060c0a0c060204050a09020c01230106110f010f0c140a0206010302040f090b0705090f01020f07 78
    0x3001038404c8000d200161152003c0d120001c00784111400c041c011150302c013201040402c41403043c2c0d14080c7d106c0703180e01c4a58040660b219210404c40d40c03942e206204000c91901204c00300440307403c07110380950064806880500c6401c0740000c440c507001440c201039440183c80c44616854440c00702001741c008002c050b055003e0060701c45000c0e101e01d04c2c0090020054001441801e00ba4a0803041c20076002c1c0696001e504800304104039811801c04030703000f034000b528086060401c2c0d42850402030085800556100c00084400104420380e900034004000c1c242000304518185200c150313600d01076007200316030783c1c04c1014010000240a0759164421400d99800e4460040207500d182d82102d113400a500e010b2541e4480141a040d4803046407001c9140d9803040314500400503001941e03404052200038425070301d411b445c58203414103420181e07031361760b002621180c1070801d0000074105400014840f40038498841c800c85003988005460071003a00c080025244550520f0f03d812103410246030380d40c80c254 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 773836007 1250 773834757 773834767
    0x90b0304020117191103070306090501082e06151214010b0a1403160f020a03021005061f09030512070803240904211443061808041802 59
    0x350180c0600c5c906441c894075a00e07624904080050101c40d11604180c042501e0720300140300c08600010b1481200300700f80d1200c400c13003610800440d201c04588140c50381040c00d01200080c110503c0c4200341d030368400c6403075048141c400318014804564407000c1e20f03404030702c0c0d030700c0100084000c0a005202c8010076280030030b0006046405170f8030603070040c2c42405c440501e04c4101044a544130030a85016240b900c0a885071003417545000b5a03540701c144071442c0d1140c2d10404a0032aa84d0305a948000e00e2004460200c3e9104050707000e40300035003d200c00c0e24a4020420711110645030201142d85199100b0502030031074480c0719103800100107421301c00c00301880864090203240d9030314031082d101c0c610036490542102c1035130303110011408680c0070716402d21801c0c45000741c1000d8800207075032159004000108144190b42e090074440c9200e03940440540d0f0414001d018040100c40051010500a12051083c0403244002103140d141e10207020704106002e010a100d402005036840c05105000c0c0800b500344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 773837257 1250 773836007 773836051
    0x7051b010b060a120b010f0f0e0d0b01061e020d0c0803060d0f05070312180302010c1a010617180c010f030b0a06030b0f03010509070b070f060e0c01090b0304020117 72
    0x907400110058040b0300201310419214401c1d000780c8510810038a0b041c4804c01004102a025a086000c030070244440c1c0c04054105071a040c1812003181d40000500c4c0007541d585501030680344100741035000049a00004006141c00024400070718145d23a514000030b1943d5880c3e207020f5420282c14035600090518080c1d02140d13139481a034501c14002c030040c01c51649185400904400c652280c1014080b40010096040d030003c0403400440780c0a00304907c0b595428038211344100300701000070700e500944000204909602c80c604401c1c422901141001d2901e41210f14101c1a120140d524a564089041c1171050b5100e06035611a0014038100071406180c650700050a40c803481d0090350000e582c9483d0580070b0320708400358142c40d01c030540082026041c01c0c1c507003a489442d18001c010350910f002407520700f0040c28482c0390180300d41000c810072481000e00022a150003003080042e002506400d004196100380d0ba04487c003859050b11080e900041e2041504c0900100070070700081311403030072000481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 773838507 1250 773837257 773837269
    0xe030a0c05070512150a110d0507030f15140916180b070602071e0203060708060112060806060a05190519030206070f06051b0405060906130b03041a07051b010b 70
    0x240c1404d500500810462010a4420010010801c502950070b2401104038903020a080b90a100026200810b1a5403081d50a9000d401d01c2802d0a042500e0991034603404c05040025609071001d222000038444507440c10001207000c1500c01010800614112009981c0901c0c02e0b40d0190f2408010448815078401280c6400d03000400d040c2e0703c0300d8000804008006c000c03042000d0b1250ba0007411b00c50031060b9004a41e1311400100300b4401c1c0004e41010655503802403a02120044600b0310038000c10b82c85192242e2550016642e05000b10a509070100e1113142003503040500f04001102d140c1e02c28038000400c80a0003080c0315003c90240151408005a100d000c018601035010f0b128562071b445880c40c0070402c07611f004025a411465001c0d0300070b142902041145c0440700122092515540e0050000d42607100d0080400101104c140d80026611000801786108502803444580b985203400c2080c03880c2d101c02c580140000e42e040104c4c9074146000e0804104070240b11000249643d40d000118038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 773839757 1250 773838507 773838529
    0x10606020c0915120115150f181e080705010c02060315060912010c23160204020d020c1e0c010806130e011104090e030c07180f1e0e010e030a0c050705 66
    0x4150f51106014402000d450704039800030004015a0852446151030003041074102620300b8041040030002c427060070700ca4244090251031b400700005c2c1103c01c0060300102100c103602c141004e9000f55040002c01c1d600030081a8901a0050038840c619692140440305c3c01900a0034a81e22010034021000240c0368a14100e02d58030b10100002400d64031400060101c1c00d0700d205861803100a1030070300700c240d01d0043c1a6903030700f9070001410081038058800200a800f80244068015200dc942d0000e002000038110001d040401c4a500603100c84812807616940c3c0e008200313021030a00030200728a81412403d103010102440b078001a0702d00310100003402d461200703002e0794100ca0302150900008210b1321504005102010007140307051007914125444000b00d1050080360319242030f18203a200482d401c101c5e03000104540420034018900111080315000c0781d00c0710303102460044009500b400510403855901c0c0c825005504200c8a400c3c00c42e544140c8920841d06400740c1100081c41da119800030740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 773841007 1250 773839757 773839789
    0xc0b0c07170d0516020304061d270a060509011a070f0b07020c24030403020f010204060c11060a02060604020903190506061906080103030e0406030b070e0909010606020c0915 76
    0x41d990710b800348801400d0724005810008003075402c100d03100c1e00c9038000084030129191801c0000007031900c8900300a011158050080d0409000d0800115000000030550b10412102c4d200b0001605c4040d00c040403985203008047d0080303040c600500035036501c0c411032010010103060366446c2c00400d03030b0755480c07030803410074101c4a00280301c00384400c09170140000c01040801792250162115061b801404000c001461a90501000400718050610034401c031000d4400c82002556556600c410050811500c1c0c182510700c00b05001034800c0034039010003120301c40d0885500400840c1c0724502000000d51001c0202c1740d1512410072450307040201e0310400b010582c01103014100b145000c00610140b44640380c511045602908403e00481e078001c00340c54190384d01403803d01c0303032480e6680101d8020b122941000d03286204000170841050b6003c4510350101005507240d00035512180c410074260707201806000096000080607c03001d0901002140d404004030b040d03020031104020105200704c110303100301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 773842257 1250 773841007 773841053
    0xc03060908221404020901200705030609070603060510020606040b1c032c01020a03081e0a1506020c030d0302160804150201140f0a050a060b040f140a060c0b0c07 71
    0x400c1008400310718615401404e40d01540386c00d101c00002000c000079640903641d40001c84c044a811203900b00807800140c00d010702265154109050082d0703a03036072203100d0031000034181813020605040500c0b0b0042c1c8581540c00402c5075442d00001c01c030103400d1003030860360420f945581c1940ca022030880e0740b006503402510b03056007850702c01030300c4071002c0d01d0720702080c002012003051800c590340d000464510303140d0503107001041501c41010b4003041100c40c81e25541010362400c10b0200800071039000c04000308104a1914800395541020303070b294500d03001280e915801100b8020781e198085d8005045240c07041c22419150143c50340c1e03050568000c1e4104420f134810540c42081e18540920855800700d085c0507089900385003640e00000300c0701c402000f600740c5e6900c6038040390102505070005400780c15500d0b1a507443d00c0c0c45d1410001c80b405a486040b0b0030b076084000043e180e082c0100d041003074408541d5101c0582045840341004c4132405843c0b602c020714104640408925803044122502968000c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 773843507 1250 773842257 773842259
    0x702031e0d0e1e0c09010815130503040906080c040615030c030605060f0307121e0f090507030506161107030305091201140a0f0209092d090303100608040c0306090822 73
    0xe203000305000321319019070306450040c088800c2c0090303801d0b20040351102c0c1c501255210102d10501c500244e8005104c1e01c07000c100403540d004503402400a4600c5c11044480c100d4083e000c00060343d40c58802c1c1c8100b801120005824175209030000282c03c03c5030308000c121190fa440c00b0844a61204044042c405004018091010b82c03000d182803040c0700410003480a0242100200904002c020001c06220364510000003042d16682200b0309580d04901618021039580c12b015403104000c45880e0264501a1001c2d0750703060249803078600e540d01d041e00910145003980c0c1e055815a001810080e0b001c1039012610704030750002d005d28890b42c29001c5480055082000d052410350b0013031003141205ca4010310120a094441d400700380ea02104000700d0709c0d2009450b400901000c01040c104d80640f540c10070401581200010055005515410b41c03070040580c1d40d030040f501030106031801440c40c40114401c10200b9042d4002501c0b55000d54403151070081c4140114444104500c0030300700500c00e00c48 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 773844757 1250 773843507 773843563
    0x2b1209050a030b27030f07030c14010f050c04030c0e04081201060504090b0a0608190e03120f07031416021c170106180b03040f061d060702031e0d0e 65
    0xd4480c18a070442d04011306a11070586450b8490043d00e000c00d8105001040e00000c0c14400d9812161458000c06030b000403a204844440c060407141c01001c401130b007810007041b1441d035440c00302d5080f650003603039010307070141480500b00ca80c840c050700039a428401070100011400c001d8110030300a00c41e130307194580e446107031150341400e4903080f061103442040b10074010801c0a030880421940038403280c810050003c00e54030060014001d0303070340503e10751002103070708a06a460702103244c0c01b034550789004808964a10400701c2c103484407404005200e41c07688010510741100601c104074030000314015516100c1802c1d000c2c00d403c100340d01c00d400000382106009a106800a43c41c40d016110030700e0607004c0001316503080ca20341500344c46940d11a210010008080c0441114800c89142e80700b5010710003200a50480300c5420400c1021003021b014031004105824000400c844141000032002c81200f860001e40c5291900260003403603145488018115080100f80b1100c81012030760348100d400e8001d0b10f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 773846007 1250 773844757 773844781
    0x1005090d14030408040621020d020d0b101b0302011404030c060c0305060906010c0f08030f1008010507120203060f0d0506090708060114060703021207112b1209050a030b 74
    0x801d15080c03040030002e010100b0166412101a1803142c1020800640c1100303440410100c02c02001e618a4030128150480410f91380040030001c4682030300740442100a410007202c40c0511220001055911480f44013a40120090f45480c5009000010b1081c0319450101e10068003100d0860000358140e9130201002524440e0781d1b4100d50a1400b007050340360540c08200300740e0001e0000e07418401440103240411010344184540d00d079011011503224103024250119450703098505081989010f40081002d04051003400e100300040d03170303640c4014800c9850080082d40013500150300400c00800b02d205985411001c2c4a250b40f01c1d500a1015150001c08582000401d40108029070031880c0108034014404410000002c41103d586684d02c00c00d02d0203928002850010810124006c1408410b005651217904030003801500e0751a079255020300858130f4907480c00d2600f81c60342080010480403454805240201c03040608011191903103442c001499039440e5403084400c40401c004101e102e0b0446 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 773847257 1250 773846007 773846027
    0xb0307090e130b0601180810050907080a150b120631020609102a0204051617060439050a05030a02090301110f07121103070b0402031005090d 62
    0x42071226124581a0390f8143c4101024040c0d504114050380b8201c0e1403244280c07048010f101c100112568018890314040207854100c40240c6103006900b4005001140822407240541c3d00203c1201c42c894a40c0b1f100c0c008124940c40c20782c2041d07602e48100101c00d010001c45020700c0c00464a010b6040d40c8000361404078440c1c40d00304602003900100b100040e120701054440b9140f04880810151100d110207d03498800c0d0f001e02c0814000b804542c6c1c151281d50f909403681c0314003d4905108a54034a1b01440d2403e01a0003a1000115400032900b5665003c00600b13400410042011803150b03c01c9410300c0066a0a48088030400031a0126218041ea00d00c140c918100b140d0815600308410502c02a1190000070105185642c00003038a40c5113540c2075000b000303020000180203441d5001440c6a921a400c10340c01101d0804003184001d1110b40a44000311039021003200941c6845020303aa030b2031003414080d01c22030f0180b08401d82604100c1180c06994410800c4a0080486086d800030040010100e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 773848507 1250 773847257 773847271
    0xa0303021e19030c05030c1504052b0509010c1b08281b0f0f0806070903051e03040b0705010203060117130209040305160c090b15071b0b0307090e 64
    0xc1001240c000703180c240b101c0304031501400c00131503020460a0442c00d5111b04980715020780540701c0040b0042d020102e1240c01180a2000c40f100c0c031540845404c400c550030020100310301c4840760740d0b500842c8101d0041c40303240300624080c1914021640d540b400d141c0c8401402000b08241d101c24094510108001c1c2c07280c106501280344524450640820090101300c0080e010440d014140d881c24100c80d8000b10007445210804500c0903503c000c4141189594050305019002e0100070601c014400d4402c41d0035a83c0060142c00c544251109102424101940c50031041c04184000100020884013400d030b56802280050307540d1500500040083c5000c8142030045c82d200703428092550040440c03034814617070659499485841c0c50409403814000c192225401a40078603010381000300021118003190307042003090000d15450740800007021030320070000300b02250034014400031800ca0a0340c03d50b020040c031070700d0240307030307103030540d13001c1c00d1303208841a4000c54540700d000c001501100030000d503c520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 773849757 1250 773848507 773848513
    0x20d023d050117010515041805030a0807170f07081906092a050d02030402041404030306170a20010311040f0f0b0306130b040f060909020906090702120313020a0303021e 74
    0x6d01400c6626070120104580c6011b641c0d9039821041501c0f0301c86115880c25040012680c65000c0610000c03d584821241003001620f002c811403d880c046030a240c0c0510180380d00700c2c1c0c099880c403404507000040101810000e088121030408048550711a660291080340c0010481e401100d4524514001d003c1144441c01600410b03c046117600c40141d820032240542e0143c3ea90300d407400060080c11031000255181ca02ca50140020150154010300c2140c0d03400d1890010011407680080d01c600010002600601c44070800c0c2c080405018101500c584050500242b0f82040208160413a007003034000e540300004c42d05050045036507815100c130003003c10f591a10310b5450701e407000c240305003855050002e6140d202d14402c50b06681e00c1c3c0003280300c0c91030704108100e00c0e960f43c2101c42c058000690241e002e01d42c0c29001c10900d00b0611705d582c1c410010394009104400c0c0c54032010701545e0000b0041e44403a5088a10307080181ea40d120901c0086009600070940c00e00560300c01c0c0d208214150044145074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 773851007 1250 773849757 773849761
    0x409050327060412170a0e2103070305070f1e0303050c07380c13050f0625060603141c140d0608010905011b020d023d0501170105 57
    0x26442c00c0894054038804d80c030807001401d0514010b1110b07219000c40e11000c0c100861003003141640102c0010720708a048801003004240324040656005c114220310005810800c80a00400d000700010304005100c2c1010068456840d00c0324011070340d4410001d600749200745040c005040e8503001c0c190b040301070846218608000c80d5110080640c219800803017689403007031307008010380380504984c82a140b4800010301d5894100e1030b606041e0b001914120b145c00000c46e000c035460500720b150b452140f102802c0e0700c1c170b40144141460f1315900000045400701c0900c240d94000a1064000c02004500c19454070001d0428100070904010080414031701c0324005e0241d0741c0105030f00001c20b6419080c100780b0a0341c0c8602d40c0900740090542030f04640c0b060b60820340d4982c1084015401108540d50903514160201840902240c4901100450b0401640b0802030102d01c5101100c040c170705080e03451210380310078034800040a0f40000200035401e01569890040040d0320017250881c25008039000200417074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 773852257 1250 773851007 773851009
    0x9170f1b190e010603090311011a0315010e06060318012309060f04060b01020307020a0b0301060305130f02041119080f0115020709021b060901022206120e03090409050327 75
    0x300c2d0520401c0c0801d600c0d501d4403405e0601032006e05801e059488000d01c01d0f90021303404a6001520300701c041c4d01a11581c40f011551100b4114814143c9050174902d004586840040101a8001510703040c801c081041c19054a08824402e007000c0c20f04500758282c074480a401c504041d040c004003c805141c12100822424030b00b500e0845901542c420000158140c1c2e4500403491806002e2009400c60f850ba540480c03505da060700994120f07040341d502440540d5031140c400692101d2002d0080204021202843c01443c06800c032411301140841d103982041c61081046140304250810710000c5002c03103050044000a50394114003502d60b01c405e4207241c44204100951f80c42c00351040c48140c41d404a82040c030300c103103407900d016045400c2c0e04881003828440c0d20340d4000d6000640031100442c0a0480c1118038280744c101004032400394407a807003081281e14101f00600104024210300c0d0008100aa485540b103203d10495540580000c41e10384020020050784803910150016940c444115201c540f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 773853507 1250 773852257 773852279
    0x100f150509181f06140a0513050a18150e030c0703020f150406120506030115030b0a150602071412060414070902030a020705010c0c0309170f1b19 64
    0x40541e4400b41440d80e4402550ba9042c0f5041448840f041d058800750a14000c07426008502660074502c050080307014020204503e9551501c03070590003200d0494003100c4120341341d120320350048444402140d1540c400c0c01c1809004513885c2c08841c0030000503010081c6c800e0314482c803408500e2043c010340c940450b0b811115600c00f62880020300ca000c19644010050302c410091004203102d07038100984031501c0b07035006004000910500c00c410340c80c203000101c251805000d52034044004c0c02120650a003503445460f0006070043c8030754855512072880c4641200385a207090001d20135540074140060800344000701a101416030144110120200d0701440d801c003090298100d41d0080341c01038580035002d0090b0500c1603e5000425031813001c0100003080c6900d400510081e84218000c01845403d081e0903150840151405000103422043c00d000c02034483e03000e0081580b100c0c084624103211012002c1c60f040c0301881c00d42a9200780d208a0382142000e904d90001c44d55840c0c00c9000c101c0c109510046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 773854757 1250 773853507 773853511
    0x6090106030b150f03030304050102091e0a15030216080306040f0212010501050c120301060206150d030909151a040f081c03110702040c020717071a0c030408100f150509 74
    0x7214034060560843c50f07a6101d500c9201c550090140c0340c0f649444c2c00c106001350402c008a901541d11074891180003c0d400c0e0b1a00c184c032070020040404103003070114200039900800c1c01501450760030043d0b4040c082d04d8594a4003058481c4030f4140d50381c50540c0a1100342d40d83c1c8085542c0c0c81d80180031101e031090306400b0185c1580e10078600030b6290580014114a0020810343d846031000f40000042900ea6001c03456500c00c2100c200f110081e80b124905201c24001042e1002d00012080381c0207011840d0f50f6001180340140d80107a0250301c1d07440e810f600c280080c0103406482d469200040811a410010068500070070445010b0500100a014607400303110300d0926603c01c00d80c0e503883d01c00f00015950280c541d2160050002c0003c0422440d000e5071321109406141703600030f030842c440048000e00040071003c1e41c8114180c40c981c42e00c0c445184a036a00070407403d52043c00240008603c2c5c9000300400c1c9910a40e2146c081040c1c4601d209076070884110702e11403041c00c600c0403c14041030b154441815 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 773856007 1250 773854757 773854771
    0x303090910120b0406050c16140f120c0c0303210601050409090303021c0c0903141c0c110d020a140a0e07200a0209011a0d1d06090106030b 61
    0x1000301d80c1c5901007008103444a82101c60300040680194042c0260712082d140b00341d2107100104101e4032840846201c0d40540001c000120b03189201010000706140c15882460450f0b1003154000710b4008041c0d410292005039000c00035201240c291044101009131100c0c81c003003900035520b401d095039020b60b0310700490b840d02600200c031f40d0040b41103079200d441150010319010004005104080c40d006019502130747e113001c040101c003061190380010718810b07030345450042d4407402d83c601d18540e20000f508082204402c1c0500500c00762440c0010740c260011200e5545940700e4030781000754641811011400e4044a0103a0751806070f450050300c511441e80700707540c0d50034034101d01c2e01d503500e0001e40c40030b540d0307000700304031103030070300521140d103812445030103003000d6641003c4002035141c0c2006030f48140400000c1c0d80a041500100640e058050607402c3c6044041c503603d00e0301a581545d24165490352044d1520183c5080d00741e04440c506001458114600700020f0000360700d59102c01848903c090086 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 773857257 1250 773856007 773856019
    0x1212060904080f0f040b0f030a0b1219030e060a020a050601120812060303090d0c060e030102070b0402042a09030b0c03090d18121b0b0a0512060406081c020706090302030309 76
    0x901045504d44040d10700a090080d082651542c20b4009040745810a035528800c440c2441841562841d10b10b00002c0044980d070000d00240d043c0081d40b4425001d0b441040d024420030368011480f985449005080304d0700140c00410340305000745170a1389007500592140c0100356141c02004001f8941c042145ea50741428103180711540c032071000180c1144a1118030640c4000c80c48510b50800503074605035412102c55441e401710680c000c2c0d041c0341c01d03881984401400184140e0004005140903400b540014410b400041484d04140f1090364101d02c0f00314500000c1021814200100084408025402410000110300798202032640c0c0d0340c0c07040c00350007035028001c0b0440ca9031003c040061220004000c508414085800c19081084405100d105001300c58411001c0110b5040511400c0380e008444640d5440c1c902241100408016240541a075601c9503d80b01d000800c103000700b0502c00e00072280008080e40505850003e85061102c6c6e0000d418844106d00400260307801000b070302e44085044d02c0c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 773858507 1250 773857257 773857267
    0x1506050a0e1009170f0c0a06080604090c030215070b1021080f0d0b1002030309030313060906050a050f16020a020d1a07090f0b0306091f081212060904080f 68
    0x10f0b52040c10310742150346414408000d4043c100000135007200174801240c1a2102c1401102c140800c045041c050b003004a583d031800f05040e410298809000e0600482034803420303c0d242d03030001d000000010b900b0070203c200403e07010103102440c144640c001860041d031040445c54003084400d40005540031400841040d04c03408144005d000440d4000b0070b2441409640e042c00709202c1004050f2124000d000d40860200c889c1c821380000704580c00703101c07070340300460a696903545000c0d04105155011201c441e00e178264440014410b01a4034006c0c01d01c00c001141f00d1800c0200d01c4010f040080c201c0c21503000003020342c2607032a00071600c0b04001c1d40507210341c2d040700c2c51820003402c0d44950031012030b885400c650410010325844100f0006445241414203c0150746031844945030105954050784a001d800c081068000c03070510802005c2c0c2c030010b2410a141e60381d461756041000c0762070725842e0580c0006035082108030300358000d6842082100d0951a0382010340301d04115000fa03401030034450b200055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 773859757 1250 773858507 773858539
    0x12041e020f12010e070915050607210e030111070b0f0105010807050f09190501080903030106050d0209010e10090f091116140a061e05060d06200c011506050a0e 70
    0x116814110b07584c02180c00751030b0354a201da001800174107a0040d4210094401007520320f840002ca0f01c0c0711350410906c4565070000c030751009007040010502401c1c0010800c00b0005600d003070180c0b9407a03554cd41f1800340ca800f8141888445414024008017103e090080140b1040c1e0700030204682107925807602039100c201540f5540001d11844031060750002602032500040d8a02c4040e94055034001eaa0b0100162a20729025a43c2e00003802044003045003403050800c02030195015118042052402604a0344003002181883c50345541070070000b25600000d000405420b2400c80013071485e564200005e041d181503035041741c05010610a115180a500e40080c03014400300d88091b07080c40020f868024603940303440d00040030480c0401000c11040c0d02d01d58061011032045074400c844c00380050407e45401d54a0000410300c0d1030029201da514100303184a1110144090580e4545650000a000744041044a81e6007040d90004041100800c01d030f1185030740c0b100c1650129102500c0017104500c00031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 773861007 1250 773859757 773859761
    0x30301150309260c01060f14030624060f0d050106031a0f1201020c0303010603050406150302221d070810230405010b06030426210a1112041e020f1201 66
    0x351345075030b15802d18901041e40690003e5010440343c03032080c0000345802400c01e140e140d880c1112002c210b84128400d55030000b681c403006c0380d02c4c0c00d0010140d600d01203950708004429003010280f0f0b910b1a43e294014000941c061154404005e03c40c2e00103111072524100243d820349061441c20302482c80c2141c5400b80780c2094040d601d43d40c043c3c3c020344e41c0740d6846a00050081c50112030540c0e1460078042c0c070078100c44607003690005a03078028001201a4102c0c5101c2c482060510080c58503030b566607031901582889801301038a900a80c50003820129180c0f000075450070700c01c50110303a0424940000301c5000c840c180c00403a1501b445280985c0d40741e41c1c41c01d08900611000400f180c1181c00041040f0400989640c9680c01401a00e01060502c00b09903010280d4041d03008600d612002c0c0750704812442003c10501607215020150114441c40704403241c0c01550410b40a1320241079010703060000304054030b0201c401d4404400d401ca180001039400080c5542c0e03c03100414080c1c0c00116003500c00c0070080d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 773862257 1250 773861007 773861017
    0x5130b04050127060f0501110a120e01080901050108061603090b0705071b0b09040e0111040e070206070e0307050909210a020c0f090a0c051b03030115030926 69
    0x61007003140b983e40700c07110340e560400c64800411094a095004890044600c254030648464481c5940ca02d428080195607080303094100711614411400c400d0001014000790040d4080c2c565103500e00054544005821104080e1080f100f99041c0342c010b21440400040c0c1542c003004030038214400c1440301a090b0300501441e0006094001d40008002d07a240d0000f0052000d02e20801015441d007800040c507404200b4a4002c0c12010b000070041142d007403809400c1015000c84217000051141b04048401c0c0c034a13480b507030003900d040c2100010425440d4050020660142e074070300784103800d8458800001c1e112910740c0542c0307102d0b024160102e00304a20400c0710400c940200451451001c1c1c03e000b0070791403070f08264050340040c032440440d0511410300b00301c43c92900402600c00c10b5940c89201010000c0c0100c010f5510401c4814060b0504c036040298002c0c8407158541c0286a6030b5040441428012600f0b0444205150a101000d00099440c00ba0b0b00c60817000420704407800b40382000ca0202503c98 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 773863507 1250 773862257 773862259
    0xa050913020607052e090c0b0319360c1509080a0627020108060f011b030e180c27150d0501050d05030301060c020112140712060b0405130b 61
    0x5001d081040d24a01440c44958420042034407403170304480410707101c1c03c0d60561b0000910483d2968000c0014400071005150041d08000b02103240d07070202e801c004200e0300c520840d659203c81c00d0030b1a0014074244110b103d216400500030300503000407603c4201100d40c06104540ca035121103035040002c030307104840b408040c04000e030a4461005040c00c2c80030140003001010383c140038003201c2880d0719145007031a0a072402d0341a11014802c1e0780780c03420407440f00308054240d4144100031105081d40c000c0e090b12043d20320b10a449800f8285142c50a11401d0380e038105001130030054803c00d00107244003401c2628160500302c1407001041b08100310314010003000c054081d402160612410760a821031501801603220602d000300001e030707a40c104201c0c210341c0f00d00d00034066400800051100134410041c0d81e410b80d00604007844602114522903080303481c03a281c1015142002401d01100c0780e4001a50304031001c1c80d103800d002d242d05045d0340384424401c1c2e1141e14861800324117107010071403454000b40c900c590 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 773864757 1250 773863507 773863513
    0x20307170604140115031415060f040e010f320409030207031e030e0301051501052d0d0b0d03020712020126060a09060f03080f0c100605010e0a05091302060705 70
    0x181d207100a645d14011185124046420030502c0e40c444c8169217000c0b886501030410480d0034903145424021203902c0140001201141040081940340013008003900914504c14180d102c00d00d483d40a00703524444009000038020900c0846070603000913081c08000000441740001c40280c5032030140e00c0c01c0d80e281c1c001010186400ca00e070102c2e00d90900d101aa05020307803101d0b009080940c3c01c0500701c070011564001c4803040c906601e03c043d40300704080c0402e00f9010034902e50340711141071184820151000c0c011000800003480c07920039180ca0040d00c040301c105440803c1c3ca013003d940c2c06074a98901c0d00440d5401c00880c10143c2c25603102e60809070b800149925030340c034505820304144513007810485016018000130302c0b00144640c4207220f40c2044852964007130a00d940ac41d600d5020541c00240d4645444c8007d100e801f02d90300040c402c40d0250003020300000780661030000094200d06c88400d113a4462803007070303004002d5a100c00d903040b5800b224081c1c0000c4220075600c0020003130300441e00d000e04148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 773866007 1250 773864757 773864759
    0xf0c060f1314040e060c07171b0106090e03070b040b09011d06060102060f1006141c060e0703200a02160828050c01110f030d1401090203071706041401 66
    0x91140008a108101c095800703100c218402e140d1550354840580d50307000b00c21800c07c02000820450302c0e503144004140081507181000c441c2012410012241d8407074080d035900c0394204801004c6107e691107151078040038608120281c0c0301c50809800041c0043c00031446600017039040002984111814414010703a00c0102001c80841552460304560f414054862040403d8403a5201c80c041481020741c80340d0f280e103960401e20102d5251a40201140c250003047c0403500915660292100c0780814101c0c1c00940289821481c0343d00303450145c40c0c981031528284101002c0440446c0941004114820f04c40d035418045200701d00c7d040c801d40800c451b080c004034000c0341040c00402c8200305407610300c2c50142050408640014010360360100144517921558040c3d03255402021010204502c0d0016100c3c3c01c10a500e0701d074203541c0916940c0410b05c0d0342d040001e8031004d62450f1607001d0440801c00b1821480d000d040508050081007900c0e08000000d0f0005141e030340c40741c00042c030007144000525015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 773867257 1250 773866007 773866019
    0x30e03040816180216330c08060f010f0302030606070204092301410c0a090b07050601060c1b060c030e09151201150807030c080f0c060f13 61
    0x35500c00d00a003c0902018072041c101c00e4410300036640c00c8001886000c4241011360b0b01c888000c1c0d81c2c004906900e054032408200d454002905100702880c842030b02142d00380b45100002e01c1754000401680c4503030342146200e845a41d00030100009882c10b0f050061f0303070340ca46a00086090049000095000d410080007070700700300b01440e0039804c0e600210a001031201c10344080600740d8150206a03140e56038944014803100700c1ea000031145014108103000340e400380c0f406540d08400c9084821424401d0300007144014a03601039180001030070322040303481c10515555180d0761070b041d040c4280001c11024009001c1880004003624010520000c415070a80d41c1d5800040e100400d0400180c0c00b099082040e01103504100c5485482504021002081c90401004001c0c000010ba283d1406540d07031050300c02240c002c040f00110185c240c1100030202545107281c2805407141e140c001c02c006422414107115030700d00006652841e200219001911060071440c40c1d0703001e000fa00150700f1031080400c800148 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 773868507 1250 773867257 773867293
    0xa05030705070b0f031306090b04120f05040b1902120a18270f0f180b090d0e0402070624240c06050c0c0a080406170c0a030e030408 58
    0x91103101d03100365035a02c3e507200115101405810781d18008030b001000051016588124240c1e005481100c0c005010465500c804102c50401c40b011200c11000880c1c040d240c42e0420248403001c0b040b443c09514050400c1148206400f440040c5001a4000161130039014001d1081d601b40d60003550b00300d030b1518000131005145085031140c10f0745604d45410b020581c080341030458801880d40146483d0813446012010009010650451000d5580d410624401e9000d5002d01c45111318241204a8a0070a90130b02101180001d00200c00541c04080190f40964000300b03096a8803008550050f200c0746d00e800c0442c05001c4205000240126180421000c040c6402203607080d616881440c140c242c6600e0f0403500d0f41d0040c188818007181a05810a001034100d4010a6105880310b02e090705040c0740d52681d52030b0440c81c0302d048440140224091140c1540190102d9641901600d00207041c20a03512000c5203102d1207061204142d11010840c10f410070420445000700039100846521884108482d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 773869757 1250 773868507 773868517
    0x30902100909050c0f160305040518180109020907031e11030a1a030309091009090f050c03010501030309170a080a03060513050103020f120a0803070f080901060b041e080a0503 77
    0x501c0c0e240c00042140104e0320400ea03150f2485015217640352500e03a010300d2290030440682281005001c11012039161600085c0c4100d110b00000d805201c1c1c181503c0b07484a801c010058200103a241030b8405000d0303500d01d0803c94226105081c006034108551001140304075807200d401240b1400e01e26014402d040038001144690441c1a00b0440c0d02400146003401c28910701500754140d000f0b0088001c4d62424a0050390418100e504503030303885a82d101220107427003000000341d520480c1c8806141c107208082c090400b40346811002081558110794000c1d203020b031580982c03807c40c110b81582c20b20040d401c1000105040e00400901e2b05c505445a008008e40000e00400d40542240a0700c0702000301b0900955050b80c1c0d00030100c0407000070384010f01c0143c0912010000042c03080306580408503422100075805040c0c1a0341c2d40c603400302c06880140c00304001414000c540da2400340100120610700040d1400c2e00d440641e445003c1c1d042031944261142507800c55443d500803420b01004204d40003000304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 773871007 1250 773869757 773869769
    0xe10050a020d022a220b2106010306020c010b0306041103100e0c12150f0f06031c120e0111040501020d170105130f1a030622020409030309021009 64
    0x203144421209012615111440301540100616a5024142c01410400c585410501901c09804420740760610700703294010f400c01c410100d5a0b1b106003207550600601004400c480041e4aa447e0b407000e1024540d102e105210240010f907000c43d800184440a403c1803040402c0101110402e080c103040a07030842e54861451407103442401c2c2d1002070101d0324018442004404800b4080060b404000d20018041c1041b1101450148880d449000085010403d001d044441043d615618040404000804000d040707070344650b022240f49004100d605005030039500b41c51400e50050f801440c40035010b02011204041954205104074801401020203401100e00903400c40d03450b4280d55038207403001500c40c04051f010300c1d0920014041c07414202e44000c14541991000030325801a919000100c59042040d034070800c82441607a2814541005002d80021303002c8007044000c034206921038200a103100000303004580318081e1000f8140030b584100401c2d034000e07142d01c80404074140e00608611084c0503030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 773872257 1250 773871007 773871013
    0x4090213090e0c0a031211150601090906030b0a111b03070204140f1303120204140112020405010f0810030506010b0d05100b030103060207050705100f03060e04080301030f030e10050a02 81
    0xb00e500c0c070b4001800c10710f484806041404918259210200e034000510001400c1c0468604800c4241200304603907900b81001413600e00260030140e00041c80d10070300c7d070f200c01445410003400b4008182c040d6001e541290015000060607050001030340c90600411141c10001030000ba06402248404002041101d108039020851440fa029400d401114281c1e0281103600c440b100240403411001c1500b1075841c02400d00311503c0151b030f45110240da205400000c48400056000941541c01c01100210082c201c0025800e140c05d11000810a0904039500801c11200c00d020a00d448143c102c000044e6800000340c070307101d42c0c640720b6000c81a404050201c5c5c0f0b06107004c0018441a1007550140c2c199501e500810f440d691840e100e0501a4211280548541c090301400280503500c02d5503416000f0f02c00d032554481c54145020140485440f984800c82012200d0108000502c488084030305580d13000445030003049050500315210449ca41d149600b012405a00d8001150403402070b0880c3c1010303a0031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 773873507 1250 773872257 773872271
    0x80102070203280803310b13050303060609060702130207140f060c031e04140d020f07060f02100507031b11060402040c0201200c011113090c03020409021309 69
    0x30003c001c840e6a0300449400c0014920780c0018081070000c3d9000a0344885000881406118503600400740070314203038030b03080280b00c0d000800c90b00340c460f01c0d0320003990044443d045181e9118141c8921008191622840c8000341c4a0720aa59040c240c440541c8c0250064026000d42e0301048000c2d131001000381da148120540d08500c1007400940d8001911407a4050419601c56048030040340e00003920052440100540403424031400d110703028421401404601c00f0b039010703050920300f80b880e0800c0c00341c119007010f421200541000182038003142d0451809064040d200f90b0221b0030525011210b20115080c0418004800c1e8160044030040e42551580002d00c40040d0381a03a03014201c901d00842c03078101034001030141c0b91652041e01103050b14000410800403040c40048112400c89044c0e06a81303000c14084503100d0240716402112400809591030084824602c0e070005005110b01b0500d02d8440c0301c00014540310f07070182c80c01000284025074403400e5005240410070300718003484070007614201c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 773874757 1250 773873507 773873533
    0x3060c12061511070f1a0f0c060a0c0306051804020301020417101a09040b25030516020f06010306020f0d1d0f010c0e0d1a0405030307030c020604320304080102070203 73
    0x300c09084440c0e400303114450a00c1d00265001100708400f01e00864582803101804800424001f41030551a28009c0d050b03621b44222010b0407a82d150031100b0800d4035000c41440a500c03110140e0003c0b00003000c8000c490b6a4610029019100f01c4d0010b01c1c1d000d15441c1541703a030800000d41d0103004c40c40000140701c040e06030b5400300010710300a420240d120f10060042008603641310b04103070f0024450384800c20078101c5c0d1600843c1c0946410349440000380c2d00e100300000c1103803251024605040750b20250107201421080d0300e507201c906010207410a94001442900856100c003200d10403003c0140901a51031800e41c4c4000140f000c110040550090081016000b0010721411810000300d80f501c044440401d000e02580d11401801155880010808000c0714000c02007424440e81c4942d00440c0d60f07281c60b180017015141414030080a643c421402d000009050000340303588100504d0022081004848520a00c10510101c8200783d000010700480c2821040d0001c01d0258000d0b0f045804030310b0b21030b0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 773876007 1250 773874757 773874763
    0x31b2b02270705030c09040b0d0606141203040305070b0d091217070e090a09110402030f0115030c050f03070e090907060212040b090f060d110403020a06020303040b0103060c12061511 80
    0x280e02c003881c0380703040220b0034881c031f459440700c5c1000c1000f924044600c0c00aa664104481d40c40d00503407078901c1c0008841844c0e00d403c1e0000030841031140051414540b85640c1c1640e120a5801032030860103006c01d080e1603078800c41c3d01c40010607030883d1000341c1c030320148a00a442e44400d24403d040c5009414005610140144034148000402400c00340c00b603a100001c078001007448403000c542c00a000905452a50b07254006180203101c01080491a949040f051703241151802c1e120340285810441041d11890300541520b40320107501d0350307050752903503481c3c000c40b58a2403032004954081941c8040c05000840003030700c4e40039100d071a000ca0315000e085101c42d0516004522038201c07100b03010030600a943c101480008000030000d00201d00b0f04245a1b80702c01a02d0152254200c180c001003410425464904c4403d0010150ba0014500d0340c14541c5411000309014003016000c261101100b44809208030041c41c0c1d045500c00d0100061521205903044122500c01c6000010740384c405024030822000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 773877257 1250 773876007 773876011
    0xa0b12060402010804020f0102030f0d0507020f070b07021e030114060a17030423030601122918030d0c0305100f08030409050a0f06080309031b2b0227070503 69
    0x5131070303014072071340c070396007080342d800000703007d1604501040c01034401a408070b00140c03040032001d000200702850400002032601401c0c0790a810b0355030002e0010040d0030342c11411101a81c1c0c0544207954209903000208030780c801d0305542507030103600e40500720002d40404103403180507210032203588207050340e18070720250102e48a541c400600c2d0020070081111214222040d15400e450340418044201d4100019092403004d80c0094500071801d102007081081d86007003411900c41d13420302c1000262009401100a0100030407149051641c60210b008955081081e2048185c0343e580c14000081d070042d000f40505003e5444c0211102c000e8004146280320600c0b800650f05104020741c01c01d13181485080113480302500041e119542d41c01c2a040014560140c50084d0500c1e0b001140d941400c00c00b0300d4a8090360301c4882c40007920380420032820766184c50031b8130a80c041a100000c81c1024150b8201083c00750004002c1d880020118610b80300fa0132207003c580c2407038003118041156510000305892501c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 773878507 1250 773877257 773877259
    0x3120c0405011202090d02180426071203090b1305120304020303030c0d0e031b16060519050906040f170604081215130e10021c0b1201050a0b12060402 66
    0x20141009000c00e0300342d4045c0041500042003c14541d016802240c2c124018010201c00d90420700d0800041c446218070300290100c1207212030400150b801c948065600824500401c924034405148860901c01e41181c030465801c03200000241c00d08980c0c49250031030000c0110b60502a1040800c0ea203072140d01564031482c2c010340510701d5940d45403420500356000032a5a50712983d50386a0105101040015040e407900c6403501c0242c0c40c500b480c10768500100d02203d510300d080f9080042c0100350f03000082e600c0b90155012802030107501400c068903103029002c03080342c0140c00450f00040255a048c480f10480e0340004019800200120825844da80308807030241c51340b0010040d541c01491094001607003e2001d2181c1c021106260001450307124400300300d43c0c0f18503162602c0010703e20b01481520110840c0d03600071417526980d8880301148003440760010120742d6590140c0e19150302c3d210410b40f030441060000b004035180c90b01900000704100318906008200c500809030548500088070342c01150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 773879757 1250 773878507 773878517
    0x20a0203070905091c031a0d020307030201050307210b1f17181507020601050a0501080c1e04090f06060503040803062214041b1a03040201021e03120c040501 69
    0x81004240c102816004e000714644d88100b1001300e89002c0d4080c0d088010380310559011449000f2074603074003010001075101920402c0300303521010043c2c7d00042e881084079420b091070740d1281d841c3c885c161042e0301481e882c01040d040c07540b4000ea980f100e907805651000c40442d01c5541680301e030a560a40032082d82880e0000c298081c0d000340d40d5104061801c0d40c03010042e4280c00900c0a44d082c1f16091030300846841c1410502d803014030071034603010300c182c0d40504415680503a803586441d0008080c003401030a01300c0c440c4000103458034024071030f200c806452608030a880b030340d941d80d8568450047c107115941c0c1c0201e40c0751800205a051150781107034062030704000168219110802041010b9129a20b99494002c03012070200a400180c0036088220301d031864026083e1170142400f180c1c05040b5107214918203042482844003d04c10045070609010307809172140c41c1d903100d03c0141e203041d0710040800c160305d0604082c2e44882d50000700410b05c82d0040c0c0400d030090341703420040c8501406036015940c0450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 773881007 1250 773879757 773879759
    0x30501080a0f050c0a090e0607020c030c06090d051e0c15070605070e15130806041a040f05070b180a0e010506090a0317040e07090f150309051e0d020a020307 69
    0x1c2d02c1011051421405002901c81c000424000140c0d11490b43d807100c8060b030340b150400c17990f848040c030000c1e600280c40e00240003c092420b0000340c483c0088110b851050308045084849900c0b06080c18100c980d1000488007010044440544581894591403541e441986408801c60518504100e040c1ca4110301d5641880402e036159005810000c1a00040000a11204065658240e104021460414440c598804040342e5043c8604099040100c1d6a0312103c24040001c0040d080081000f444100032621a01d880c506081039500c1c4210241c0342d4811450040f40001e054802032103440086000c3d2010b1614000500c81c00a00c188070b403c000e010000c1c01088281005001040e45100003841240442e85917518501d00c01c11148400d40911004241801000c252a00c0290030103018200311201914220317460385468810f0103103080345e40481060308c01d4180207070000c8000560204c02d0700d9008003483d442400c0b4804043e5250010f100303c04e004020240082003203003030340350003030090700c130303203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 773882257 1250 773881007 773881013
    0x5010c02033a050712050c130602160329240909070e3c06010809060403031116051f020c1b0d020603190b1e0d05010204092307030501080a 61
    0x80100505072001e0040c2c50b900f40045c0c02d02e070300c269840340001102c082d840740c003810074500019407641c108005541c044016042091480c812000c02c69510081010025110000000b40105441b04900ca690400c0702802842c0c02c0b046503c1c1451035900d49601c2c0d24884080c10006222015035050280d40c126650610050b4402008981d00500351501e6010104212400c0d144c519605180403040d080080540c1111407030003251903030024000d282941090500c003031000e484040142c4000e00b41613458011300314030044d04060b6840e0604a82c40c0309800600c60400540780c004920384c0317401c2c0761101407090000640920075500d82d0303540e45000b00028444d106540d1010180ea00c819548007041c0c111800c0141d0300c92004500c1003a084000c0c3d01426a10711020b402d41e64001c0d4850300c11981031040100700f08410150300388416084030003151203816070815a00a110b990400d160240c2051001d002100105420800e10340b0381803800c20450f0b44a200840485100703018488071600071520340c2c404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 773883507 1250 773882257 773882261
    0x1107020d060c02071511070e0709060522031104140705270402040b1e090d230303070e0310020322060e060a06090e0a03090b07050a05010c02033a 64
    0x2402c030030f004680529480303144145440c100b400240c0002424841201484241404210003e011041c41c0000e82c0c1031500001d0010889030081c4c60030003c001c16500d620000345030020055040c1c0c00403d406281c0c072810030444408002c00a00d00480c00e040c0a10000d5182c240b1046c801c0d251541e07a5403c20005c01c0344840003070024010f081200f201501d650009940710710084c0010310000c65282c0d41c89240e01001d05012880c40c844110000b81800351541c0c1d41c4a984c151a10315904c00c4000701e840f8483c1000c040607002070f0490342c13030b03500c004001c200c405500001000c040e428214100c13510b107405101290141d00c001c40c0c4c060f84410304400d0f20a504026111496001e074030414020400c02508400c0c0d070b140c00000c032884996079131511001c00941d00c1c541309540301c541c0100301516030711a072500e01a2054580d440380e00000140000c400303040c010203100e94011503500c14000e00009485000c003d689810001d00e02c0e141008040740c10b00324041c0f02000e00840464100100001c80f41d50b844040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 773884757 1250 773883507 773883521
    0xe04020a090302030d0f1403130605060105160602130b0301050a0b0306182703190809011d0303040209060604030b072a05070303180506070f05030708070c091107020d06 74
    0x8144001d20701c0110050b81d0900c12100707580c0fa59591203981e007200e0301300181242c410b450640d03035003c400c100b4005050a5101c02010b415003000c400b15603070b142c1d03c004956174814a441c42140760003c0304010304101941c4c0003043c074054039044804180e52120031841861100b80f14040c0d0000f48000e0407c440e0302588003031644454018284901c40f022500c000310014001c4035420100c10380d240c000c070307083c03a0200c030f203c84401850402503042c0881c007800c3c1d1707141001001101c011701c041040011000d40f000d40000071140d403442c10705a03411403801c1301e980d03407500207480407446104104001002802c180003a0360450340c003c45c1c1d139403003a225506e00f980e012601800c032803041c8140b04100e10320803c2084400641c01d20400081c0109071071410002c2c0410176110071242680c3d07210200f085541d84000540d41590340020802c0580502d42c0740c91481c5104220000b46084008030b0401c05001c050303c411002c4860146051010303400031000c10782c0900c200721000f548080c44020040c04500d113540805 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 773886007 1250 773884757 773884777
    0x30c050402130e3c0f0403020a021e18060a06020d080408070f0b1612150e0a0905010c051306020703021507020d020619020c0415031b12060e0f0606010e0402 69
    0x4242d101076062040444032604038280c820300302c0c6444c050b510555004035501c0340e6201c00d018054102650002e4940e00c28450181c443c0400c6410782c0f0440300940314000da1280c0c002c10742c0b6019805074800c442e0009080319014400e94107000d0020b8518008100e9a042140c9503a40d00300c690f88030390f141903480e0815542601c1000f00003a105c00011340390204940140803452840241c4d0241c81d80040c91005c94040040581781405070310140c034503d41d42c40200783c481e100c1c5c2c402d080d5a02c041d059401085032002c090b00d076600f0101c5907a180768000300202110047e1a20f6078030702c1030310340e40c0591b61400140f00c000e400038561450080e49080d000050501c1a1005201c107030a50364a40000351290842e1105030b001d40d03020760f4111000758040200200c0c10340b0583c0c050050100074122403802110f6407101401f084c06107139120b01a00c4010a40e41c001c0d141140b820040940b0908060780240f04080d22000b480c07013180101c0359030080020707445104001c141d6a06030030519143c02e00c000b9400601040d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 773887257 1250 773886007 773886031
    0x9011e0c02120304060c14030d09030e03190c1502010e0312060a1d07050306060912032203050c0d0305040305060f0106030c0e0f061309050a0515010507110409030912050601030c050402130e 83
    0x841805034004c03000030ae4002d940311015450003004141c20041515100090780070301d90028400200a054000201c0e41c10050402d4142a0800c09038054002040b4074111030100254003407080c401c01c0b070542d001c0c0c1000e4401864958907807171401c18650520701210030031700060b030000b6001d81c811002580d10400140c030320303810034840341c01107000c0c1400c0c00e298180a40001c80c58025004031021003882c12075503401080d400c14038545600e600d031010500c0040c05241c6400480341418005d5044500070340e84401101e0944c40e044080c2d4000460a00440b000030b4208605144030912480d0801c03802100200003582d900030b00410030003039905c0100312000c100e9040340c00040301c0c01d240c4034680c8030f094100c60114007441d100c03e1400d42410000c0c0d02505020003407080a002c82c80040303440680800c15140040c100c51107080c282d8250f00940d2100300103030103500b92007081044c0800c0c070f64103d80c4144d0200c03000f41d8488041005030301031289400324007003600c0390810101340c80402c404e40004040b150 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 773888507 1250 773887257 773887267
    0x1832031c1a0603040c080c030d0905060a030e060f0106030b041a010f120f0609060b16140a0b091509060c09090a02040924060206010e010b09011e0c02120304060c1403 73
    0x2c5511500111030503246045555010800100e01344031400c603030f10044028244d040040140540104c034640126401030001080340c2e410540646e21a1041005000c200c0c1e0b40392030b00780e100101907c403d0049000003402c01041590b581480d00030644001c040442c9180d0140d000001141c40c8690b0039501401c101d506040c5000c0f0f50600c3c03040300c0400c00c0b400004107a4508141809050303900940c040c0420301810044035812040a10144014a82c0040407085501d402682c003843c2ca68540001782484c8454005d00c00780c100300080310403000d180e42c4010089079035001c030440c0d240c000440341140700e01000c100240003032030403402055124204010040c20542c665407031394100c0f524400d001c466072915003d0041200080010003005217014401401c40e581400c1012004940603c6034070803030030f000b045503541030303001d030030b006c204142c101c41c030b001c001840940002d04d06241860280d00503030200f10036000302c100c00b00843c2c1c140c850a40b01e0700880203242da0707a0a48050118141403540c082484 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 773889757 1250 773888507 773888509
    0xf020405130218090601061d0901180b0f15071412090a0927031e0504090b01090e1302010c0f0309090b0316091832031c1a 54
    0x4201070107500c0c0c00320300c01c4506503944180420504940d65440f070540601d41040410310001031040d055036581d2600107405503540400c2080c103006618841d502c0008040003003602080c18041c841b03000707041031040c050607698005118100b14121489900060741307183d1000c209601c4002030491a2040701455410b2300703195041400c0400041c40007060442c00a0150021701e0501760800c003074000c00208022020504050f60120160900c06a916a500300d40790000d240c019980040d040d52501841c06a888182c40010840d5015004490005145c040040025446603aa40041c0c43c1030b4019014035454440611071110003540c1d040b41042300c0c015107100010200d8400b910302c50f100c1d4403a1601c003070a004251f015600700481650096002d002c15817880c001003080c0c401229407003c0001465100c00d00031a401c1c0480c0c26015020b91f8040c2d81441c10380c058604954a030ba510b580350b00d44560b40b00c000d0b80c4c0e1a80b04d1100b8010390220444443c0380b40d1083c641c0010310032031210044804d2030b64148 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 773891007 1250 773889757 773889761
    0x63c06041206090302011b020705012102030f010303031b0203040b090d140d08010515120703180302160e01050114090f0409060c0f110a1410090f03170f010905040f0204 74
    0x303042102c0325070302c50464004241c0c090050000820300c0300e42c041800528060001c0d42c801091050504004c007421a0604d00302680040d40b00b1440681020365403407400300003e01401e0002c6c80202c000a180c0441c0070f020011000000781c3c1ca0107594055807038140340592604141e00040703011984181191030142c00039000c0d40d80c0320020701d10391018020b00329070a0f00141800c1c00591205014824913410705e141041403004030b40004035588080c541d103880e4000300310700401d00f13000d000543c000507131102424990009a441030361444490029034158030750654109080d0b00388960b5000c1070201c281a108400000080c10003d40c002e040e150340c40e485140020b0640c0d1061505072141a0303102c20242c4d00a60110741181c130b180d1541800c02029140307464881da240d8078114040d20f0120080d900000205051204612101e0380820038400c0040034244002c1d00003000d0821400301c0c406450310f00100b850640310300d100d04c240340d50a903003581c0781c41c20341c3c000350400900440d03400d20000041001a507480c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 773892257 1250 773891007 773891039
    0x140405041b18140606030109020318190203010f0b010504051201022205120a03210b03030d020322172203120306080604020913050f070e063c0604 64
    0x7060700914520048103107041250003000303090703d040307002c00108001130b200c01c0100e030704442e002d09006130f6a588950390b0f810302e0607242207407010500810106800b80314030f0703052a000607402207008008990074010118111010314ac1c240d808a00180000c100d0b910b08040c802c2400c012140025140214144220a185a2003c3e1402c6070014400051129050640d400c2c182c810142004100021a40d00c0c0980820846400082080f04e04007001d100254540c018228456018088940750f01801800c44065002252081b140301c4211042180f4041d43c0f41c15200f40d01d8021003400500a11800586041d512070391003c0180c02c0d40d0030081c4000b4007400c400c00000d40c041c40070341c000d41921103001015070381103902480150380700a00344000340c1d0b14019100d4120450f01c0e085405a651780c5416811320081d100c81040e68080c0381c0c0c0018a40c07602c008001d22805003220405c048070b02d00103100c1c07044a0440703221307000c100c880c4101c10561b0040444050030100018566070410381d450400006034484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 773893507 1250 773892257 773892269
    0x30905040c091a16151a010203210a021209010b010e0d11090a0b0d030f030e15060603060301090209040501021201240f05040519030b0708040503030a0c0507020d0b0709050a140405041b 81
    0x51410b403c1e00d00c03020310000000769071091009e5464000d0300d08280310540403084011098081ca440400c098480c158100c4604800114003a01c0500d03060310524000c010000d069408643e4a144c003203100e2409030410129181d01080340081c0040c80814400030020041810890030354407842c0c034819580b03144113000706074800c1c0d03140707080354001c2136009061714000c0484403196400340c4054143c41c05200c2020368045030680d181d81d1260380d07120004c1c0c01b42c03060744c4020307400445201c1400180f000640007021100103500320b0301003590f6154404125403c1c0c603692030203468110041a80803074411800b13489000e0181c54041d081c952240d00041903a2010004184842c0313510104000308030701c41408a0380042e541c1008106807038180c903003581304d100041c081100280e855280b140c02d140600309075000c840e0090030162402610b1b142442d40c2010913900c510105480820008040c54454940d106540b0080107100080410714103101c060980603000301c5605080440d500360008841c81c4035001400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 773894757 1250 773893507 773893511
    0x30f110306040c02030a0c03030b0f1c06151a09180106020a0c1202011e031118090a090804060c0206041203270303050a0804021c030905040c091a1615 66
    0xa100d07040200716207405243c4815034000380a030100440d00011007052071a0075040c04504107540100040031005c013003629640c030072030a01810b42102c0612034503491181c4078038020401c001350900c2a086283c0d45116240c3c03030a00784440110110440c4000c0c00c048200a0702c03c540d8504500400103040c0740c242c012400581c8075002440501140116020040a001241c0318608403281c000805c2c41100c0d00d0541180b02c1c00360325014044d8420b0b0700c80c1c6904640600b1680d00c840d803c8004441d164003007035426220701584004149400f00511a22210075809030200f40782c80d14004bc107403a601c0c2c0d003200030303680a01f05000c0019030500000341c001480788680d0f01c0e25585000003074000f41c140403950084c1341942601606000003500310707040b5542044181000036040c0d445200140307c8010030741c500e445000c01c04604e0002c064100c1c2c0480c056500485040c40710141000003160b201b00540320740100c001d6241404036502100f0b100425001a102441c1141020640c031642040600c00d401d00d82803075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 773896007 1250 773894757 773894761
    0x1c020d0501091101021018030c031407050a02040e03030f04060506040b13060e130b0403030528090b0c071509171201030201021c1e02010b030706090f150c080901030f1103 75
    0x16174140481c1e40d450750b500c4000c0000910700402c500c1c0481c07450500500380302607252940103050080d4035600142109519281c0d88103403614222391101c034102800c90060b070603d180410258008410b40b8442c810007440c101d02a900e64444401414002e41003079002079407907440c211552105640e0303440384002c43c6d50228140c1e141122500c150540104009041a8881042d000140d1075040607a00903030189000308190704c80105d10011240300300d101203099000a15089a0f0380300c180c00030190103020703181d414aa5034580001d9441441040d000a140c200316480207205111a03900c1000c0c2540611221110038820501021013941b1600b0300c418807480300c00040045603410800d40919810720329001200d045001c1001e02840120b42e00403215654512400340307454800d40c04032401d600002d003203400072560b0300d4000d48104190f00950074500401c6001082d14120f0860b0360751165603980d04c800380c1104036290300030b003504490304c403504040d02e9070074003600c60020b801000c441904144405a40e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 773897257 1250 773896007 773896009
    0x90103090309090c052505120a030b10020615030106080c091306090c090b06090a3c080c151c020c011b031407080723040807080d05091c020d05010911 66
    0x420801c21b80c94000c10001c100c15030005601052810040149001c2103403140300b2010250301070182e410040e50001e40101c0b21041c41507000035194019841d80c40700c080110000c0c401e0600340d40c941c1c09130b4000d50b40040078440541c1070400d03196511420340700603107041615551351030f8291045440182d64291803400240040583e600c9034407a11207044510318501700403400885d0700310807503218607a5031a01d80035401944103a10f0908422103880003e4a070310315551015008212251800741d0000d03841b508181d500e2505203c120040081c010700c00355130418000f046d480c10040301a442c41e44080d03400780803070586904240a0161a400346c141008400c0c41034840c01402c6840803c0c200c1d20420000d01403024544d000401c01e0b400c01c201d494450000d84c20380c2c0000c2c0c13240a425402c800701f0b0b50000f0340001c1041c404140070054603600000d59421032111801100e150160160507584010074025404003003c01103d1028400e10160401000710038a458541c210307040c1e044240c81c50081c0c13015074000c3d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 773898507 1250 773897257 773897287
    0x4020d020c1b0f0607050307060c050d0e06011211012304030b06040504020a03110d0206070c17070f33020703020a12050c1c05120903060106050f090103090309090c05 73
    0x516501c082085103002d4081d001540810035005079030b010714030010301c140510505104460300700760450002d1007400030489006065512602c2e01d411110300d0160010004140400e140381221408803030a0821042038a0780c090081d40c00c1d122074140000340035015800080c18840300c0e000b8011b81340c155251851420f081c104808024419031185252a04010060742c2d0080d140c016030340c01c191800c40e107104c5400480c03a02c1c600d054001c0c0d8032850200d0a40300300032a81100d001905e100c0580d50b442042d0390001c46994031b07007502405001c42c202110500040204016a071101d41c00740200890030340350000781e01c021034200e6602a0041c1c003c21006d1088d403c00d10303818401844a030b50031408007075154907055156480400014031582000c103803402d00d000c0307110258124941103410b81e0f01843e402080100d2a510038800c09000740a00c0c3c00014041d40101c0558801000740d05285280410480044000f80358420007202844103ca00200e155080d9200300d185082c5030f901c4090382c40c1030f80d10450b45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773899757 1250 773898507 773898523
    0x2060d1b0206040510020406120b0f041a030d030212070f02070b0403030e0a14030312181e100207021c0620070201110a1a10090c03230907061d04020d020c 68
    0x4001d00401081000d03a521401c09d406500e210000091200080400110701e2a060017030310303a00c5400c1c0b0b409014081742e002a841c043c518202c04540e03a800d5044815402d0303000d44203814084620100010b85094003030131452480700b83c603205490503140c640c244a1a150800d4000350006141e510013000a070500580d60382c00360003201e411505407020040003036a80e2096404030158040b240c40840e41c10280c0d184011486a4114140c0d50100b100505006549080884489880c404c090655140d8559842103901440d0040c20301a410090284000308a48104808941c0c644e5520b1104003080c1c60001040340d2035070004e40f1255611600e0000403c25140b0407200d070855003041038035400003642c1000600d452801060100c410756034500c6001111042030f484084c6040c288198210b050754590701a03000c402c5042640c4d8100c0d031074403201e0076500b08101e4004460350b020600138410715024030b9941c5c600782a00c0c00c0c1c680704034807003031b0128090340c1007001c8007081141c000c50046090042800301e01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773901007 1250 773899757 773899783
    0xd050c2208030415030b040e240606091c0204050a0e16080303060f0109031403040317030f0a052d061f0203160c0e042105040803030402060d1b02060405 67
    0x315150612000303030740764401e5104100194100b8240440d20718060703005202617090040003000f100003020840354580c3c21040c600300c240340794625104503201020146174010071021704040d00b071548400a0251307200400303489070f492817402092100142c0e590b0044500c50b84180d480031406180041d566840c0500d010403d1803401d032522814071441600005580e4001022941c0b007884030160703401642c0d14800c58102424803000122400d180c1800000100101d92040809070040d9007110400d26481c0000d13a44124400d0303000001c50b00c20841500803642041d030f02e0349522101c1070300c2403640c540569040e080c078240040ba0800c00c641450b220500c1401134103e400b044941000620000b0348a124030b4000103116068181c0340b0b4284400f005d107940281c10b801d0926440f41c1014240315595902204c103080130b507c0003107d2100141d1103201035a0031258103400030343c00c41c0c66543c2048040d4001c06d2442040540d61018200c0401d40d0320351140c41c1400c0c507009460582018101030381000b00e240028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773902257 1250 773901007 773901067
    0xa09290d0f060b010e031203010816060e01140c0f01061d0907381804020c0a020d0519030c0302010c03090f0303021b070b040e010f06080613020d050c 66
    0x215000c980381d10103403026030764000d01c0001d0f400c1208005861464140f1840c07500b41c4103000399114042941001941030300e460b05c00b00e07140102601580703c0d500605004441c00036030980540d03901540510300c1111103219021350203090000790050249400400401c0c00e0050f91580403c1040c0140743d9925654403140300300c00186440c000100c1552144544203180c2c0804440700b80003d515104182841800305514100c000282c880c4407012013030300011920300c3c0c041504c0070f0342d4500f403409100700e5540402000103044040f041f40c01b0400100413100b002e8a850040c0c4003000d404445901e01100610720980340c00b1001c50392410300030701b140c01a111070b031305040c03070010044013141c00042080445645854003694440c4c0c42c80514110124415610f0703918400c0c4ac50100e00b811104015105503015440d174010160703a81e5801011095407440380d440400c498801140980c1421100f01d1440220420007525088420b451300303086480480e41d503c80d5200200c1ca5200c3c6040c00f0285580c500045892 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773903507 1250 773902257 773902279
    0x13020c0106051207061701080607110c060a0f020f060f07031d0a060c1d09271b01032003370615050a081602190b1611030d02090a0929 59
    0x8c00b039500c0c0300182680003404101070500b40c58940c10040d41014400140c80f4980b038603440b02000d40310180c1001842c025025200c20200000b200042d0b03540700e90184040140c16455561040c2d0040001000487d0701c50007e0303091040c40d200030030484d0212403290000041c501c201100003004940003103036040001c8844480d8440a41c0e13a0380030035420084480e08030110040307403481059040151000c100b82c0b03000c0c000c0c5200807403241000b00503c42030207807410b000c0201d06441c3c2c0c059066400e41881c500c10014408961403640d03011074101016600d140446900900c0740d46002d1210719a028800181e846101c05c6c007200500d485d408c250389070765040440c01e0500303145001d80010350061a0190503c42401401c140030b00c00c01c0040450750800c51024440130341c0e42001d4440341d00444e01d100390b00a030b6000b00205107119008059425411902450601c00300c0c15100001c0c1d40070700c06095112110400215044a44d0300c5192000d00f0850036443c00303d5080585084505074002031648540c0c60b03412 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773904757 1250 773903507 773903519
    0x7050307061718010f0e10090b011a0f0f030106030614011b0203070512100b1516061b0203090f0108010b16051908040306050108060613020c0106051207061701 70
    0x15905000c1c07a40040ba969a00510003000c03521401414419824240d01168102c900d41c80307001c52060140a039111022000a007109031808450000c050781103040040180f4000d125440e0403030301429000f1464500d517298594050341009486455049002004102068043c41400024100400d4031814404c8143c00600140c54040c005803120041c4c44446085640500c0746070042c09004180480c019140c3c11969940c00c43c807070ba611400c525118204604d45482009119064003809249180444d01d907104403003002c04007012221680c07110651020100d21030b0483e04c0f051800d80c02184c42c0c61414040050a5a00b0117034a41444a00030041c402c0b1400c10045910414041401e421000707101d2919a10b0024900c188001580c0c820345d164003080207200041c0112400740c041440380d6600c50101d0364072442e055410326400090000000c98441d00340e0007822541c5500c5000190715640c8801241307038800c40000b485101e4104a0041c00340c20f4104000b00305d4064828407410096051a07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773906007 1250 773904757 773904767
    0x608070e1e06030a0e0f10110c19080c010c590604090209030601080f0307231519050c0f0f13080a0c050d110f13021b0705030706 57
    0x205014010302c00000010482c8000d90840128007150b0b008032800c942ca180d54440c1c607030081c000305140c100c0c10403000401c6a904142910f40d10100744d0003a24a40c2c41606110907115024101111014000d00c841280200f0a00c9891040f00040c0c4a14139a003240b0001040c001000e03200c103074001c99400808d10b1400000403c41c41506603280340d002100d4505030340d03001f5001c501c4031b00264001400200840e4030143c90f00074089020041e0b00302d528603620b6001868844258412039829503200f44420350100d4403a95100c071600d60b0698462901413500c240031400c14018900c60746500d8020f03c28041480f010402c0003521490b19001006142008802d4a00500c24902d10b8805034501140344056844014101c550f500c00c4c0051f81c00701c2590340d40401e51240c5258500380c0f1282ca01400020b02d905040e0b440d82040ca038022420541c0498000070050021451200c45801c03100704a40000d2001291006014140000950481380c0302c46000301e034074207581900710394000e0700601e8040000603081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773907257 1250 773906007 773906059
    0x702060c090a090501290408100b130c030504050d020a0c05100e03060414060709030b18010605120307020301061a0409020a2f061f0e06030f01060608070e 68
    0x5050140c0e50361000200140150800c3d80010300804d01d08400003c4841c0d0488480100c600b011890020361040c1941001c00c9009910924105401c1044845064601c0354004c201a00009140e80c1003080b1590402e01181c1c400034906000c06e59a10620050000801c41540d0407140303031000b40002c031150380e900c6800c07007050f108641c0912802c1c0300d2095101d01900200c0c4210034044d0844442d40307440d040c1113146443e80c0714040b8103406000082402d19105e0001c040643e07400860009031b5854a0b034006112190020021025561300c080108155071030400e803030003110a440085445454600415003100d84a41c805c08980c1080c6940180700105202910112100802c00607200c0c560214241c480710421004d010425820360810404400c04140c1c4ac0414072294084410380c0e07503601560b0f0480203444503910350648007d8801c01c031000c0814500f640c8000003a06450103030242045040c01e40303a2981294002c2855041005016075008004680b80030044910000c1703c50902c8800303c8590314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773908507 1250 773907257 773907271
    0x21140904110c010c120b061b010f05270705060910140f04031a15010c140a1218050102122508090907030507050301031e02100906090605040e06040222150e09070206 72
    0x3c400030040c50000e40c005a0030ac51094018041403030100c600c0042d103000c119852b80c000e14404500d051b0007000140040a89030017900003032a0104010070080c0c02c1210204c00b10811101000318030300c901ca01c0c00034150440d40c00780003a03295402c40c40c06515240650400c40481c3d4007542c1000704440345414100e140c0c2c8000c0c01c01e8003001401c2d0804032171400f03220043c0c80c040e1041403c0707041000110f04031015294450b40d101c40c510010304540403030800451241c41d0042c1d000380d010450b2206d461000700141d10fa85078188411258854200c221015029000e4820442c00b1811040722f0400a042039444883c07440c04001d1032506c050050828001804058032402c0d01480c00101c000c134030121980e00d0f82c0c008040003203003040b00c00700500d0719056025500004441c01c000203032440c060802c0d1010348100c2e41000d9441d907103080038070009400c4028004e9613200d80c406841c0700f1044487c0b01348090104440c0003001c4000041d4050200a0f0480d50f25001e03800c00010030803942e43c0401d0103600a03070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773909757 1250 773908507 773908537
    0x10110c0d0c15090f06050106080403120e070e010b0406030b03030324040e0312040303061202011409010203130e0f0105090f0402090405030904061221140904110c010c120b06 76
    0x10490030302c001c20894401c10020058030700750400c0240480d554500400c107204160a22050783c83da00e00b2107030440705072001000f20750601c500c0c21500321144c1100709403000b28000c407100301d5618603540054083c281d00030300503007800140134040305506001d4940303070041c2a00150b04d9424041051745125440910240f5030803414940541c40740d40d150428001406200704581d1148142c0034050f1040009075000c0380468540074000400003045161040416016120f050103660700c0103003200079030702c058001811400200700e611809054040c20002409000d8082d0030949000304000320401c1041e000315201d00150010462507181296034540d105d0b83c180d820920741e884514025142d40100c03801c943c1d1080c10800d005c94403280c04d0031001d200a004441540c0d00d8440109010700420103080c0840000e4003003070f2061074080c0d4070740042800100207000058890901c1440b140150000a0b603401140d444031001c81031a0342c0320b80c80c0f001401c804074042010300b00780300000c0c2e1b180c41a50089d00c0008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773911007 1250 773909757 773909777
    0x10909050c04050103080c0c042021040c0312050405150a02100f090c05040e0c09070c0b04030f121b032f040806090d14030612070810110c0d 62
    0x222050080460000001c0c2c01400301c2d50b100d103481c0210303400c440d82e825a03500c83c9852041151034640258001c4a041030560740e01400b01a01c0100503512800c0e41420310050426840300d000300d4a01c41c01c4c8114000c001038805d50f810361608a0100a10f01880381c10804248003d1000303903118500408100000700300159a01c88048060741050030620443c0a190f2820b031501e8200d500542014802c41e220381171641c0034a490f80100401c80b1420f264040e034030713404040c0e40e8907182801e0f10700c241c001c001410300240342e00d09079455480c40c030b03c215022400079400c0e115148009400c901c103144100c5403208144130040d5029000c1c0a0701007156950002c041d280d484203070b4146400a484d02054100b4a0410001c46402c8004c4070b40d40c0c40344c03142c05034901ca040006410103102107010b4101c4281c6654125583c0e0001191409a40015107a070b68001143d511342e51601108020b000002c00408001d072080d190f0500042040300c000b0108400c07080010004480203030f802044e011840366590604102035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773912257 1250 773911007 773911013
    0x604032c1302031e070f0e0102071a0a0207090c0e10080906070e190e100b070b06060304030509040c0f09090e070e0405010b0924060708030a1d0a0f0c08010b010503010909 75
    0x2010b4010700c80c0c000a00108140070340f20b6888100c10340315100f59241c60b81010b02c502e0049030303505014418100c21054044580108019404c010141600d051040311800d90315213103002c0c201c07000c0c900f0344404104d0154900b401410b141c92c5d0050035a22174144034190303242c0303110202d0715554000d02000c2045884802402e686c0d884064600c814903040c1074010565440350102500100142da1142c0102404100080d4110401e42111003181d80090708802d00e880300c600740452a0009081117090050600254066440301c0c81605140482c0d42e507110a9920103000c0a090100140c1042004070300b480c84604c4a040000b035000200d4a10f01d410100c00d035250300b8140c0c010300b194008254041c4000d400d00030801c03480038122018070145001c1c503040d641c1c0c1c03d042099520034500e0007021100300388005162414290300041900349550030044640100b0841c0707a017400d001020032181c00024804550502803445d071a00054000f4074020809e913010b600020b00709000c144920071065459182d05010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773913507 1250 773912257 773912281
    0xc0d0f0608070e180c0d06090206040504110d0507030c3509070e0601020a030f1b02150d0e0102041409280e160303081b0702030604032c130203 63
    0x101035803000d4903500d5844000c07800c00304805a400c000c4a016105841390f041c10003080518110748000c0240200384031958501d80680f07031018007030b42e000b0b00034440040ca80e101c86c043e03403480864501c012a9100720746803144045400c09002c002c105031500d04102e2200e43c02c00322400110328031180c0b54000c00d215001484100084902812050510030180300440800244a000383c801c41c805008150303844200481e40c42c3d4030000c0140000c0c800300301082040d40641c41c5c2062040440c4413101a00c0b0844e004144440c4c01d1300c002401090380080e0302e811402c458400c401c3c80880c000e00942c981031034100d29214101e050511588a044104c0200d000400703510084805c1c07414100300903001007201000100280116801c2445500403440b400d865410300345840816070703505440f84005516246809800d4030030400c0c442107619010031a00c405030780c0420080c1e20440c803a583d846030160035030801e5807080e070300c500340c241a10b9044400382e8819a10b124416405404d0304500513207a80e1204402c0741 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773914757 1250 773913507 773913509
    0x9081e0706090b06030f030c030d05220b060a0f0302030c011b1e030807020115060e03030403060203090607090e01030c0302040b0619090303080903281812060b01080c0d0f06 76
    0x15891514028030b04001d420307081240f05200441c26502d005410080381a05c912a00d0401d84198000308003190a40c504d42d407119400c4843c4001d503001c2987c0030840506281942842038600300d041ca000c0205520b03040c411900549814000c2000c5607243d54003080d51280c6840d0002d042c4100200541551403220110101064008207142c90500100a41b030216002e409029000118407000082000d0f00500a601c2c82c406100c0071401c03140d1621500300d520042541d03100303515010411000002c65018000f0303500410255001c3c21090401d0314002d01100542d50002150118403401040440d1048100108681d010307100883d503283c03c000080c05920640040c11b49101101580e1a0b00c25070043c86a8241d078801c1e1140520b0b0349490443c0e41c3d0324002c9404015840c031030110002a40a5171044001c050380c1e00c4d041001c2056900c0b06c0704100549950461601c003081030808405010341c0b03002d0317000880000c1c00c0c00507043c104103e412005100e50308000040c00c5d19110148650b10075a80028 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773916007 1250 773914757 773914763
    0x702150a02030114010f0206041704090204031401050a0e060c0307031e0203060f040e0d18030b190f05060a031112030c1f06050a060f09080105041a070309081e07 71
    0x44180c901220344400940003030282400260380b951050f144d0b940940c04955900e80f2540042140b81d4450703450011400540481c003182885c00e01c400100400f590001e00007541c841c800d0310401c2c0d05440303603007821901c008140b040c1150400000480809001c68900e410503100f0706d003141d03242e944034000c2e006400d007100c1342d581d0007100010b2100b2440240d405940251812980340e1a141202001c010640b0103000c040d40d1140c01c1080b55951403400f403120708000d21071401d1101090340d502d40b40d80308951800c03907540c1e40c3c1404590314015001b14030301c10400e00300b1007603d042200b82048c1380031030020005404000d1240c40000d5612005649042d14400d4840d4028216030307036180040d0400740c079000d00c10090009811103108804031503801c4d001e240c046d580054241068a4070703042e01121050440700b00c5d44e00f404525800855010800e014040c4076900410b04502020100100c3c8460640d000300800c0816190103183c2d030003e4600012170b4024110241c1e0301c0c211111448170782019200301c1c1401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773917257 1250 773916007 773916043
    0x3020903033603060a0b04090f030305060307061805010c031101060f1805040203250e09070302090702061b0a02010e0a0c140901060522030f0605090d02011a04050702 73
    0x10361070a500d6041c1e0300241a00200480d240b03103605442a01c00151012281c0e168001030005851050701e580724132070301d50307005102044400245e20380750f001da00401d506400180c0c5034000c00c209401c04014040007402c10f0700d48030041e9040b50114001000c0e0034040c15040203010513501c018144102255440401600f000300040341c1c0d29071868841202ea4425a980f00e4000d403902010004540700d00781c03060f078020340a0902114004152140310708005070045070384181e440049003e07440d5034110b40c801c44c080c1c8010904541140100400080c2c0108420b0455003d00208039442240e5030001031603c0001000c681c45032000e000580c003400307600303402d5140751040b510001e09000412401d14112585c511850512041400900c840c160b000d0158202080d4104188500f91031229100d0320124000c6110100890312030752030b0030502c00d403104e0075102c258a8100340100910280201807071200700c1d000030401c10004e50388125580e210502076500c42c41e901e8002880aa00034803103018072104107956 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773918507 1250 773917257 773917267
    0x60c1e0f02061209060c070314090103020412050309040f0501140108071e0503060f0d03020d0507110604080d090603060f1a0f0c072c0f10170c0102010b030604210302090303 76
    0x501140d0b150103c1d1006154850038012801908418084070401034141e030340d12900e15160441000c1134ac0c070882038503040507820000010f0282d104e120005c0c41d00d210b10043c41e582e1802c0d008010540311000d1840794214a0f18004003c8000050340030520284207081ca40c499580d8003170700b5a14414010b01000040260714041c0b15159413050055115003021100e0f0f1002082020520441010703800e401070150740282500d85000b4044e5002c0c0141038487c0d1040301010401a02003051034125a000d0442940124032500703445400c51110000350542d85410802d2034503090045264588501c5404116610f698035410010141d0040b40e44031040c4d561b589a84118a2420503643e601d6481242c0f03000130420050980d0024106034202c02090a039080d4804d500c4000302500b00140240000c807405c0c040007000214006510001c15101200c0300180c004001160000f900703442d002203030350307100c2c2e0850b00402001944910317400072016100c0044072078419051009500070311403940a0380e414880410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773919757 1250 773918507 773918527
    0x50702100e151e010e040f020d0b0105041409060a020d060519170102160303020c0f01060902090f1507140f0f0109110103090512130e01030605010807060c1e0f0206 72
    0x80d0240d22140003400b21a0340d0380c07641c2c00030508aa0001e00c9410b9035042100401c160101101541d400c02c0c01291258a003480f90f50006880340c41a4504940321015503004000341d24181c032a00d56581c401035010005807078060710554840000400d00a1000c0c1d01240302400c5009540c0302c0303400741c800034066000c1d441a0f400c901d812250203208000300ca800c1200e91840701c14043c000e039410300fa00441180800d182a690903000f0750804c1c045120503104880f25070010307001c00d004000060259050050351031400109200034810300d00300690140c0000002d0b05040c1c041e0104441c41e854000c081180800b2444000b98241002d12150080f1842500c40140342100c1c10b500c1004142d1240d0480280b84d00c42c0c40042d03055034074000010317000340c0000c501c1d4903285e554040144402c2840340ca140c12866160310350500940c401713030010b540e200e958000521040c8000c1203910081c00705810700c85d201c80b1041d41c0e034107035802080d48404450340e4440c0c0a002002070030000380450075402064691602c0104c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773920863 1106 773919757 773919763
    0xa0e0a050a021324030203070b0406050f0c030922050711031611030a030c0b070e0604090b01021e160b1603110f0a0507090b04050c0d050702100e 64
    0x1805801d860790800a118004e940b5602c580c04515096006042c078040c0c080d00318480400c5c04100c00e0000e1740d04441592100502c01402c42d9440c89503007052403d40c02a05081c0e50003841d491240c0c851500c003e0714421031640400d10821040c4e99004046801001000c04140940c2042010607880d545150a096582c1d01452640c2c10880300c010221349008406807054001480b6603070028100502c982c45650072075014600300003030810341d00005030759102d94400c0f49582692000f01480b80d034001d115030209005143c50840070f035044807171007603250f030000001d400c1c404e4220040890a80e01c01c1054603c034620190241300070380c280c4e580944544141010f552620700c5225414940102e08008a42080b441440901001403a00195205807159030b41800e11036410310003000325000c0c008043c2c80085801070f00100d4507883d0640240c2c00c03c41d041811224031801e013400e603030f00c3c62000 = true := by decide +kernel

theorem cover : BRFrame.Cov 773741007 773920863 := by
  have h0 := BRFrame.cov_init 773741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773741007 ≤ n) (h2 : n < 773920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
