-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1700
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:21:19.206978+00:00
-- url     : https://prove2.me/submissions/4f32dfaa-32ef-4c3b-9cd6-54485a47c709

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305575539 ≤ n < 305755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305576789 1250 305575539 305575547
    0x70206041b051509040e0a150e010b0d1506030c0b04030b15010f0807140d06030b0714092106150a0f12060207020d0209160f0503131119122010 63
    0x224800081c2c4041406c00c2c161300a1840c0c11a401421140e81d03680c001d21040c10002d40c40350034400003100d4000c4c884041c90314000340c80802803400140402c5405001922024490340c00480107581c811a1030f03070520f42c1c03009640c0d0260080c1c8010303074002d0100000100702640740c0c6000c03c003002052319070405107078851070100d0700038100800130418802d012000d5104061001301502844145c5032012407102d00314a00010350100c003500c000d06010a00c140041010040700030755400710001e0790784c00441d5800d580706c6200c80f03a4800548040340a070350700344003030700400034542d25110070291b038280c08040e903d140d840c5d07841c16180b24541030380304005004000680260010300c4801d000909041b51140c0310340005085072401e80d20440d130725070b111414150141e04a250040d103440141095030451404189826001e894100010a01c0c1c2c03014014041a582ea05d41410681c2440141c1c80402a2503001710b203019100048155000d00c0546000c451080c1e110356416040f1070060710341c40414030038902c260307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305578039 1250 305576789 305576797
    0x905060f0a1103040b0702011d01080f19090b0405210a080c040305011a10110c062203110307050a140d0c050d061a03210a17070206041b0515 62
    0x101040703401d030041d00ba03a2900b00090800341c0340c1a10540e6030340c0d040d440050251060300307006800c0e20b0410f98060381e56a1300000141e900c00b00c00c44070030f1090750700c0c46a034100148000103056002d91070642e850b014403003248030413440f40348900c08840380c0769400f001d481b40011062081c0c080901080040900a511039113101e0303003003100803c580c1d080c251a559101c4c25250340c02843d1021a146920948151612096080c485041c5040c12200042e041d00d909440309406802940603d000251a45450085d6907412071130304000150a00000d8903490864050359000c11158402d1044200128151070114810421a44403241417211003072000c040c4840d4100d00c3d901500d0440c4401d00000d02510354404260340280308503800030740b1120004540400c01d0000070b5941c081d40c03140d09805244c840c614803060080b55400c0310b16032100c3c0448411035a90341c4144501c040307441d0200c24081040d400003210b500581c0300e221900703044070708980d9200944400703100e0503a000c820f1418940e425210700c8028 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305579289 1250 305578039 305578057
    0x904120905060f1c02271512010f150e040915053c0103031b02060403150e06070f0e06071407031502030114060c150106050d06060905060f 61
    0x52032129580d000022500c1d00041804a1025400206801e8000140c0f09551209601620450400c0c13101d038000901c020000070942000021217251820b90390710901e43d0381d401c42110054503641c0c8090f4860030186c2c0400e10400c540c4480002c80400d1410000008503600107080d03030380740c00000c00c0b0340400000c0c261000e8183d4044100a03100c41c2080c0140c010107104111031001c00300c01c0d45001030745800003803854050000d00c0c1c0369a941103540c45903075100141100d4152503c05100042d90340d110200200c00c1800a51101c00007a000040000c203990486092030041420030191260b08007039501c070102140c030b220000d03170f03484800c003210350007540a20700d2440090002400c0166599402040340780c090401d0109900641c1f0030406c201d443c1c000843d45241e0040c0550640d45024004c0303000020366814603104280202d035141007640200702c140790650500541d114156901d501c094210340c4030700d401401c620705111001c07d40d1401204001e00301c650161600386403403003036001d0510640002e114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305580539 1250 305579289 305579297
    0x21201030c050111060c1920060612070b0a1808031305041113051201020c1504050c01020a08040603050c1903150b0f070206030603011b0f0305100e1302010e2d040b090412 75
    0x1010190342023904512480010440041c01541072100070040c0801d0031451058855015840a00c40030864406031010b40f0310030309219162010343c0003503194400381e030f03080420130744004502c030380c0c010107100e11803402c036076054071f041200c0c14500d87d0f0325031140703e1001d1182c070119030a0301c1044a030400d0b00d180d00c44507003020001401c140031108202d051262042c013850040c05114144000c0c06002c1c4042074800900f40020300c65040315036030300d1486010780d01c162070078103940300700180480702008201c0d100c21100442206051035016030140081c0321030f248203540500302c00804601c0d000480205d50350808101c85040c01d100c055030801c81031b988014003258065484110300e20b0070300340c48079030021044410380b128461041c80c0400201100c900502c0041c5050003130400300b00ba1120040715a421a61034010300044400c2d41c0010385040c28403001d4950819a06480808829038080d00b0b07082701c00c03c54482d00c61041e40c101c00c1100341c0b0002c141c400d40c001400408034002902040e00100320382c0d42820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305581789 1250 305580539 305580557
    0x8010815150d05010f05060f31090503031f06020c0f0a08010e0601081912081e0c130801060e0106051c020f0304022107090906021201030c050111060c19 67
    0x201082584920b410122a84d80d110012114000c0180c0641c075070001d02540c0b80007603550720000040c100320b0225010300c07031440b103095040345030f030a49140301640f40d000c0c0d1001c0c001d09140d840c0c40390b40da078801c0701c1e603240c070402c81c83c022034124030a40d4501003100ca141d4006d152400001003002800e0740d5030103c041d48400d600d000010b5002d820701882002004400281180358509050a401c081d1a20084c060007820968183d00044000310914800c0f40240740856065440c03403d0707120740c00036490410150310741c24020880c0700c001480050000482540341243c406542e0380d105802e9449038020a68071a50040052062a1041c1e0140420000307080b1000604044644000d04a034040094217414120001c01c00c400d605101d80d140210700d1407a9002d03041d9a490041c01d54442e4281c1c01508a40740d120303900407082c0400b03501a1a4854104401e000848d42d482c03500950a00c428030030940490780d01d10003001c00280210f00d46d4072410602c0030302c41c6061039480e0201a820071300c0d003130603003071042d111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305583039 1250 305581789 305581831
    0xc02010e22150f0609030b01060c05061506120103062019210f020d0b030307051f09060501080c030f060c0315040f1e061203171008160303030c08010815 67
    0x343c403100003803140e52107400e4101e08508011120f040141c100505001c40303181201c0000343c002829550101d00952403580c000781c0d4500042151180d070004481000c004000032080c8580c550140301c0c120364110303040c1800030b030042c031240b01801074840c07418201a001c042419140d00404005490f03a89124615514240724800c1008885281040342c1105038080f8018907840b0086c030506402690440c002c504185003030b41c40036501c80010441d9054480703804000301d000c540c541c00150216074001000d02c125070f11040d04a40d100700e041c41903842403040e180149400a4082070090044005060b1580345a80c5e43c030318002c6070116440b469801076503524980002c4030142c410303002d00145000b9548401882594140141c410540040c2c1400f21100c140a000a40081040e407008000000040c0550f441600580c208195680607040500510f8200c114003008000060292032190700d0403c000d05880e02c041f168080240900c040e00e91101022040c3e40e0040c81001d5401510985900c2201d00c0070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305584289 1250 305583039 305583059
    0x1e1806110f0714070f081015050a06110c10080f060d0c141306080c010c080906031609090c09030204051b0a030b0901210f03020a0f030c02010e2215 65
    0x40801503e03141d403000d016000001c414000310300100040282665100c1c240300f0003540f5148905960900c46541c0c900d0550017010f4a12150020301d401441c0e5403c8541d280c00140500a13154002e841c3c2d80144011500c0c42d14000f402030031700400950366180c00d03650f41030140c85074003005812258405550010f041c005262101c1c0031001c1d26070541c5045205007580d084c007090403c0d02010294050812500780000200056294400340003440e240c01840380f1424800d40c244074125226810282c000700300180000c00c2d451040e446506030362000000369a500d414002c03038600b041c0110009252090030005464950021a04101020340340314407409801c52503111a40803030220000b290f21600f07005034900d84640403c0c010f104840640c1001c41d40640c100c4641c500c6180d00800c1808807400410605100b04200646203510200c40d07030761070000741000b400c114044041280012007184407501d442c280318001040c0019806004000d50040542c9100580701281d03000c40100c249040004001001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305585539 1250 305584289 305584297
    0x40f0b030c0906161221050405063903010e090a033615090f0f0909051507030204091109100f0e0306011502060106020604030e061e0705011e1806110f 66
    0x4240c1755001020322506c910602c020351605030f14801490a010080032400c04a40a607224510032040386040038028490715814114802003041d014081ca05451040100030095050b0f03210030561010036920307a00c402c0d5031180c6c0745000034000b420010390b00c00c151083d9881078010003948060802c2034162a541210522202d500c003102242680d04203403041500311a1060150a00307c808014850500713120b0885002c01d485466521039a8400c82010700c4014000d9080700ca200d01441e4015080040c1f00601a410600510140d9840c0c031229102c0c100d180c40c1100d40062028140000e20111034030700fa01c0900d1044226401d02c0f8131046860881d0340d06002a901034800d0000304047d001c2e29140082c50400140c00c201b080d507116000748400319402c031248185903802100c4041c2c3d1228500066411020f1079585000380c0800840c01404121064000000320542c504c0d1029210310b410703078064240c0c0c401c0c9008415041c82484c200020544a41087c0c465034031400c5501e103080c050f000340043c640c4c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305586789 1250 305585539 305585573
    0xf020619020106090b03010c090b0a09080304090b040b10020c1306051003050f0708060303040b0a03061203050c010b0604120605040822090e03030c0316020f010f02040f0b030c090616 80
    0x156885003444031600c01c2c4500010000158008c00071940c0141020340f0000c11406269103402e00482c1e0300080620425501010f0f001d010700307903900d80d070b83c0d010120081c10000c0b160038031035402e040c030480035414280080c01c140c05541e4010075661a41c030b0140101d0b810b03a10400038900c0d440700c0c40070600e52034400741c03090303003031920f03900004d0600d4002020751807843d01030086000c1021510030302145030360001c00d5409680d0000c800540e00c12841e00260010031081d03000d0000c074010032152200349500700d030240007201c0107040244144070301036003007001c00e200390300030800640007081104002c501c107580310a41c8140705665640c035203043c0c4921880e80001001c4501000e04021800703100c84040ca0042030340c8511500d00440c01c50900da002e0703d07010300009218800200090400a281600c02c02c808a070100800000b04440d28458105e10013a6106004003e4240c64054000801c0c05240c4116842505048156801e0469400c200011544510701c403000500341a582440412107090681c49815 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305588039 1250 305586789 305586791
    0x70308150315131509080921070f080d230d0209033c030703080717010801061a040302030a17041a040314030310051c062c190f0206190201 61
    0xd2010301d000f8114901d20704044c041c8034208500500010711000548281030402c030351001c000c65140740320700c0c2d5617480720321411143d101354400081c2d951910040389040e114000140c4802c04486401510b40086194051401040d2101c5640801c4492400382c40c07910031010740540303410300c8000000d00d025020000700500480d0401103d14900180800c0c01021001d5185248003d00e98a01c84d41c0340c2c040c6c2003000d400c0c001240d00040842d0f00c20b03010312201804000b803090441d40c440700014002c180d14003410108041d00782080060740204001c0d5812664010020b220b404800e64500102c00082805d0303140e07140040c00041013010002c00b4a426640d2031039107080d01c03240f660602031410103103d070040c102c94108105204a00c035a200344c0b04165141a610070305031140b000136203030819121044c05000103250051045a140104401036141d0004200c0441c54512942196807152543d14400441019500d1200300040030f0300e170510343c0140003d15180c1441020350340380202401000c1074100503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305589289 1250 305588039 305588071
    0xf06080f0c0118031709030607030b030d09050904171c0902041b0e190803160b01050108060102150c040b040603050402030105150307060507020f0a0f0608070302070308150315 77
    0x105004110301c40080000b40f810078695510034907514880d908074040030301a074503d109040c4600c40740c1d10844030601d202078100c170000c5c5000318008004003e100c080c00d10900130722140843ca5823040754aa0f00707480e001030070350060343c40350b985040b00207002d0b0940d844d626500740844d8900f000781c0b0070612500c0441d200702145400c2144100b0046038a8006014800801c4140502d6055800045031380000f40a03100c0d0070a00b89041c459407055a59030740148514030000560751032010030640010510b40c4500300a29259884a0055503000004ca61850044e4010707541403100041c400301c15034004250789446840c0c19100c203405529580903402ca90003083d228410700086090902c83d0641c050320030112101c44c1c041000c006034079604036101d00e9003005000314098003035644000c1207400c0c00500903d81c0b184a9507404258030001818410790010803001000034880341e00900840d24019496079a02c040c9946042155450000522450b0303014031a11484800c0100c860490a001d0200c0340446140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305590539 1250 305589289 305589313
    0x80405060702060115050c0c060a09050f0301050601050f07060b131d0f0705010302070203070e10260a0204090311010906020903010c09030506130305070501110306040506090709050909010f0608 85
    0x360240c0070304020115031044004004020080381040304201140c0761541c4e90300310440020740b610008200c469400036002400d10f00c03864001d150b88e800c03520140ca1035842110010105422100111400c1d80407034002c205402d44203250790010b04041d4491180003ca06035124040390214010341031100c03003259188a042c481c0c0340c0039044803249c2150b04000380740301e00d201010b06880340054130680741859001309500e800c5540030b00030303407010303103000a00d07421130703240c000a81060f5955030306c50b40a44080307801d180c0006103488050140c9400c5400002c00084a1540c00e0100601e901d84083c3c0812545402000048a081c0282c40815010f40710150311000580c04050860310740c0400d08080c4551400e04000050000c80d005510840388140c41128100600f410345061207800c0340103025501c0e01c0301084207902d81d80051805440160341c100540e545030402d0040c480e505540c01d6002c40d50708101000306250441090b5440181b0000201e070031801400103106031022508054102d400464a10203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305591789 1250 305590539 305590543
    0x9020607062c0109121119080910020a0c1401030e0109050a02041104050310050a060f06020609070b030603061924050f01170703020d1506020105150a0b041e0312080405 74
    0x40c20b40d070b12900030000203005036203484040040f2050781c3c060103401b440c42503001c902030000c10a801d298445a2551802a103000b144a60007170301014403d0748190000500181300265842d580e40d44082c2c035404c0903043c07514038208075100e27482e514100360312841d9a050404081c000e181650748500000e05813901d080c410001510344042c0c44c0c0003010004e00c0200420b030380000716122140700708039000030162241515140075204030340201103c4881340310300003441640001d0807403042c01c018090340c113103603240c0c2c4003020310303210070354403c0d40c9a800003011420000014180d96200106488005444080820129003118a254226807040d1418804100c03900303040c28a4280180c0034641400c0316005016845d110000180c010b500301540440c1c3c01c05010020344c029954141c0400da500300c20b80c1c2d1800d009010302802c85480c508000c410390310300d40f5414a004000251341c6482e8669060900700801030700e0307541c00f0f06041c5214904041000000c20341000c1c0c01c0c60500c80703a5940d07840524190070954 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305593039 1250 305591789 305591861
    0x3040b09010507050703230705070602010f0203070f05131a0403020909060c25020a0b0903011b0905010e0109090f0203012c071b060e010203100504050c04090902060706 74
    0x4035569041100300034100340d202c012601a5036140c05c1540350740c84403441d0f03010000c181c1c86042140140018160090203000642c032002c0390055402031040c00c2409034864241e000a0f2400e1020030359007801200344600a030080c01d0b6045180c1810820300d541d400944224144600500c200c8000000c0c003802941010b6044550040340b0200034105401c10030b107080d50910514088017540302020361040300b04034000061144458008240c503881e90f8a59880d5101c0342e10078080d0741d02c01c0d031801c0b135820310b06900314003c0604202e55844003542c045c038040040d0381046907440902c0c1000351030b80b40481c140400344961045554901c500684a40c10414009419801203003101540500e03840c003118040741040c0810b9100c1e40d43d14141010344820200116111440c10b40289424144080451030400c1507014600c900c8541c91204c920350307554820b100440d8400e417103c1c00e01c1f00d4100400d1090880b207410001c0d00602c041c2a45148c0714050305c425085640411060403400303268580804e0b855200f00586c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305594289 1250 305593039 305593051
    0x6120b030601230607020f040902030708010203073c0302090102070302120a0302150906150d02090f06090604090314070c1508190b0619090812120108030910110102130b03040b 77
    0x460b1030211740740c000401203084026030a2195072540a03050841d1800c0c081c0320000c02c0d12200039916401c01502c060300d0541c0402c000040d900c103c81c000c00100c0001040601d000040400c900008001e80038202c2c0654001c041103030540c0301d00d010020058842000c291000c0c69900c0103466010483e2038024141039800c112403000c0b5181c0d038103219416801240d101e07000300781c46e05103510b0584840c001c10900f0344100d00c041d600549020800800002824071203110780b8007200c0f4a1003c3d81c4420401085901260029000900c030700701c900a0740301128020000c1500030081070588580d94000c158100c0c415a00840c0052040000d01c07018040c101c02002041015101c00e20503a4030300c07400300d034071809008140d00c1c0c1805403502c5004918040e06822000c1d00309202030741c0000c02405100903050303221071100340b04440300d2000042c003400080280c2c0c184010040000f1079801303580c0c1080314421a0b00310040340b5958200171049154040c507a409004010f00303244603480c0d1400d030411004c4075070001d1103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305595539 1250 305594289 305594299
    0x40902191701050601050903103207030f020c2505150c0c0a0e06040506040b06030a0c0e0a030308071821030e030607080c0c0709020c01021b010905030406120b03060123 74
    0x40e905590114400801d92000000061000c40d030650315013071b4504c000d0200d24400300c1030104200400e622b200d00c5209802a407010720007110303909007190884c45078041041d180d4000c0d0b92081714003141100d00090342540d07560b0042c191a21000000c828288181c0a40c203044400150b0861804045c440c80c04141001c4450034011480c1c420554103000000300010f104a40e5000081e10700e903285d80c00040305140c0945455106d150480060004181501a44c004503c8488642c0918608105086d055036855924020103441d40803059546034540070404c0ba0241700c1e10008150302e4010306003003050540c04800304e440305010b828064042c200c041d1800b80a03402480420007440d400c4180143c2045000d0350f5a0790b50103002c03414038141800c0ea049405250700001e500084140150040c2a400c01c400700c04503c1070051901c0729080301c0040700010f10980051104219050007180c2d01d03007000e2424680803820b00594000207040003426007000c2210042d01010900c8202c0807055070201d10b4064503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305596789 1250 305595539 305595547
    0xc0509070201060602190c1a270a0b160201050703050f0d05061305040b010506031807080606012d0305040c0302101e0215011401050708030c19091404090219170105060105 75
    0x280d80256030480e000388c0d058120709403144464251200308440c00004900800303500100c1025100080b0040c1200d454450501039502040307941c1d10314111440e18910855810350005a5401580c160300401d200ba824003000b0b0180d00c094046140061074188150703803000943d40f52007001c1165104030080c2c0700031240e1800c0d00300000100d2270920141544c801301c900648030b6440308511110106100d104414038001e54034005040280050158060482602ca038102180ca042d41c540303003c8090701402e14031101c0800d100c0d480d24001c0e8840c1d5000303800f41484c0b403000e60301d076004100317503d20020103540000e081d04460f011500104110400500c01440034222000d41c0c03881c6004c1c00c0304180500c0ca0740c16030100c00d00103168051421120381c1c81c0d120884544902c4c220b100b05140343c00002d0a0004080c1010350511058801c060300030503074006481a00c0e0228a480a100003007000075030498010381c241080e200d1010390b035040080100910005208440180740c1c440e4291034015013194140b001c184 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305598039 1250 305596789 305596793
    0x1706060a2706020313060e0a03061505090c03041203020c1203060a0915090e070e0a02030a06030c170106140108070c080f07080405100801030206040b070c050907020106060219 77
    0x2411240000c0c0645002900000d1062022001484612101032025090035000a90302d030044098800080da0352119180c09603119015030310040001d000c141c0c8000f12000c241f00288a0307501c00000a000340c4081c048031600e58010880004003581c0300c41d51120080f00b04410070040c81341c90100e060a51a0550401c54110301060380d0710340f01669015010380100c001000c0f5252200101d00070304450005021411054182400b0200c0c503000d12a441800c1081c0f030301c055035000521800300d6152440d241c0856a40301c0c00c0c4402508003a047e03a611740d84078003000000c685054843d40240c000f011204800c0304034420f56908484e210f074000140c4d080b40a561042c1750b81c2020b10342e64804d03200d041c0498890001e1803c00f529109491075070341c0041010403540c082c8543d05028200b0350754203444150039016480c0059849401c00d1000030741c4040100005d00c40880440054000c641c03181c103141031148d40f51800500e80d4041110003e0060703641e00c804004107607041040440302c050340c002c0d10520001d15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305599289 1250 305598039 305598049
    0x90c0510030b0f1003090803040f0b01170c01030507120f0b0a141c030207230a1d150406090501030602030a06060903030f0f0c0b1e100b12040302010902090c07031706 73
    0x400094484c1c82041d01d001c4003a40680c101e08800341d80301040c1550f0303140600d4440714080100405451000070381c0004225980c01c10341c81200600c040004010341500d04c0e0044000e45001007285080091440150041c0f840d41d003d5030761012100072000c100d208442c01032015500e001c1d4080084144c03400400002c0391505000100c90b8440144544540c803401d00b8141c0c6400315030b074041c910718004245200414160080100142c220449180a282d40d580c0030558480f00c0c968102c5058803c11008540070080c07103404000354140290012031143d5584040784200d4409038170070766029400008001c0d000045200300360141c8030604241c1005800d507100100100802030442c401e00c039200b003119400c14001c0d041c0001c12a848110b902041c5000c001d00c3d030409040000c011071500c510340104c0c1e510300c540104002659001c1e000c580c10800882d02c40f00301c000c0041c0003a400d5558500c3d690001d0780300c80c9001031250b50307000c091350340e2443c4a24004190945400c52501556030082c1401601e90310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305600539 1250 305599289 305599309
    0x3100209011b020f03060f06031501050f0d0227040c0b070816020307050406030305070b07090b0d021305030a030c030210021215150a0207050a080a0305070321090c0510030b 76
    0x22015901500342c1c0300d101007402d00403c1c03603e06500d8898001013210780312090240038480e00080c2e0130707200200340c2085a601544c100b0300034680e00c04001c2c1c0c501310950403d9411800014002400144402d1284000004a00021209072031003070303c42082005001c81210000014241420510700e0703e03034030351512442030141c0d403403584007034030020003003000e40d40d00b0032510002c3c00004004024040d50780c6005806580301e1401202c0718040500054016805580d0840c122400c60a0440c80c0c0300448200400039804241e0008007400c030280e02003655181003000949080c8641c0780c2225070200c50034003928049a0354a12801c66004024011030b01d0213558103507401c107400c0e1301c40045540710030000a4880c07070100341c0b5090700000440c903901044e50000300c00084134026684007400e25201c581c51502c82d0400000030b00491010405840041d108000c000c1010001002c29145040001448410784040345d006542000c004801800189441c01c10003840e110365040801420844c000401c03c0000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305601789 1250 305600539 305600567
    0xb012603040e0f1305030f07030e040c0e01030905031b06010e0a020405030307060902030a0f11100201090b040f02030a0c09020a081815090a0c03050a26182d0310020901 74
    0xf82c020081021a1308050294010315407100589868544899004a0350307040701400707a0008450800607960b03820a4400c4030600300e456603e4060319248040150007506a403201102d0912040000c0c1414218500d480b80a48071384002800d200d5150030040c052100f0b010b0070042c0b0041c41040200510b56000080361403580c0c0c4010049a103002071b0001908000300400040c0214001805410401c000301021000a20040300d03500400c80c81c2d40c00c220b00f22003040300c00030031001c0107001080100303036203c151885641c1b0040c00c484a03d401959004112a441e5010c000015008612032510a802c800920f0340408114214516801d01cac0194954420144642c5400c0c00706010100348003d2003403019807059034000c035025003004d580e46005941c4258401d016a200705c20103c0a4609107400c4944049000c9111042410100e10802600307100ca0303540410f80c1e00800c04101c420741c40d441001e0101590051801044000303d440003458104150303500c203280d090344104410f020503078004045504500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305603039 1250 305601789 305601811
    0xc070219261c090b0a0305060a090c02060c13030804060e03060a0e1504030207050a06021c090617131a09010506030c150d06081c030606090b040b160b012603040e 71
    0xc0c2030744181c501c0450f40d00414004d200004004000c650150002805003100b6100300345a655503514840031100d29400c0c0c100146c22807808142c1c059000c1c3c014007510102540e40d107c08999982e50407855502551000e004200200103103a0705207000d10229600240d840c80c140b18500b507904120742c881c4211640142c000400c803020400703144c0300b041713481d002c0c18000e00260302031915600081e50300c00360007040050714404104c10368120781c8180c08503c2160800e8443c0d132480d4006801884001d01c00500d400721102400821001180581d00716103502e900c81c281da85a503040041500d401c1d100c0050070b0500a03485898034038031607240c40c0c0c499128a440038203540c0c0c507841c03000740140c00f50109a1014205100d0040d02c10b290004802400e400301545450801102e51b80d03120036554480c4500c14202c101006010070000c610000c0014410142c9200d20102c1482c01c0d0754a0950003102a00710762004080403010082008a01e031090700341c40f6030080110306052400b2401c42d40801c004002601e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305604289 1250 305603039 305603083
    0x1009050f040b0709030209011805010b0c1c0e030105042001020705010f030b03190c0e0a11040302010302091c0606090f090507090e0a0501090803060f06160b0c07021926 74
    0x10620801368031000d1030740100315515950b9640703800e07079096400700015607195103030400020305104803104071281030798a10060003044000c08090b441e0610702070031a2041c00716801040381d05503820301ca8148a148503a2000342c481c00308000342e0104104000419066501c4140c0510481c0e0304101180603091042c5004a801440030300424140702c5002c2209030501640201c40c0104103100801c5019580100590450f95684810301c200303992110180181d031410420041c03015521a40092200c0c03900600a40c903240d99101a1030030709006a0000d90b04950390300010300c501e40544c06151907207161150f0900058620b44c0310716840303040511841045d551740d010035040442003405880300300c5070450020049079155080c5032100d54000c566242c80b82c48100d500030101d1a28000741e075603035034207083c44494404465850720181a009009040420418444040103a41d03100c1e4a0015075007110032490560b14100340f41d580d030040c1c40300d0b003d0340c0f80a444000c2d034038030000503000344440c40c3c1c58030540c48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305605539 1250 305604289 305604301
    0x306030614040b2802040312021504030806060a031107051509030901090902280302030405010b010f021b01110102070804030611030f16030b04061707060f02120706140403081009050f040b 82
    0x82c01c4110000c03400124004500042808140208c00c1001502c540a0f50200c4184985aa403000c004660080118000d00e0114140c0c1c20000041e00003248a4240050880147c80c46001c5030f410080e0b0132250307079000c039500c5248040000070850708016940c000b14248111100040d00c072000500417009a00d074089004c0240b5460141184004110f192892310110304d4020024040d5000f2a015101c41d0f0a112a103500d55104100e0110358480c030380d01a1101e4814410008080c800a40c941c1c1d04110b6101c411094410080c40145070362449038408940c1c071403031850003000b13031105000d0449056a040c0201b14101440e5200141c0c40f040703085581c180c00c078101e2800d40041c80c0080c1940d40182ca000c20208050346000301030b96800524070205d4640a03610001150305050445080005801442ea440c0d091040d90010f880103a02c0f41c107010800e070401160480340360000710b4040c1c002907000000e00010540b81c0800b40050016601c051102d0318100a40469076280a8402042100c0301d2001a41d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305606789 1250 305605539 305605591
    0x30e06270c04060e010f0b0a050306120f0d030603150c020d050c01020d1a040b040b0105160201110105040602120907030c060813060606110d05120c1b030a0306030614040b 75
    0x14071000020b00c01c0040549aa0b04080912000d02030011100d5003a600415068001404e40e45114026602d503803450303507003205011411029000560540c820b84003849490041880003c0200c00584e0b00040e04601e5400c00300c2081000c0d80d0041c003e6407800900b2098030743d000c035902c2513025580c01c126642d6626221018020321840c04400015031404a441c1904d4460380d1140c0a001d008450074003510000c002004112401703401c0c2c0e00d02088042041d07400030711501d160580c810340141024a2841813002c0c0c0607003990001c4a0441d00b050340024003c602d2801d0b002c0154200b0300c90340042c1700c41d0b8116070302c0004034060b900603207041c000b0f41400501855080b0900420031940320005004040c0c1c0c841e40500341c48612480c03d6014024491005c600701d20640c143da101e69040c03412143c0680f241800e041c0c05500c441d0b031001980e0701181800300c0c81d03d020030051141a00716900051964a1410301404450343c916500148049032818000030442568056800c9900e0700224001c589030107100790 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305608039 1250 305606789 305606803
    0xe030c310618090318060e0108060603060d1103010e03070b04030f140d0b0f0303190e220c030b0a0806060a05040603081215030a080304060509010501080d0302070c17030307030e0627 80
    0xd20001c001400105865902c500d087d00d500c20282c0305d40c455a00c032142009202c3c082202c200303406c0b02001500c1c20100e41464505040004040c00006076020704194641c195840003509541c03180c502000d010406511020601285680b49002600101c6604d04208a03201d41a110361503662500400c0041c2d9a50417143c03005102c0c01801c580d941c18046999101c10161201c1074804561400043d90075402c0c0b0410034070300c501c8046440039540361100110001006034203000001c25079964040030320380d29030701081c1000e00a2280200142d180c01010003049a01c0ca40009010340e082900820000c0e61203016550700b401a0603002d0920780ea940d240000e16400841c500e6498817a100c202c500b440004002180210701400051255a40b003940c60b5090780c0082c462000c2036030101d011012294441d6000c0c011988c4214504501e6a649544070410241c407010001d4280c3c000100b8400301c5074051041c0c034030a41d0364401424080c45e15000414200c402da0300f00e4078103640b01c1c007004007103400184103035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305609289 1250 305608039 305608067
    0xe090a1220061b0c0c01030e030405041e060506091c0f0602031006030f060e07050f0c03030a05010801050f04020a060e010903060c03050403020709060b09010e030c3106180903 77
    0x4403200300c4181d5546951180300390340301900078002d156045045551501251a0809020000c0c500061003200450090142e60301d00c2c031140c001400042b030a42e65902039420107100c1d0304443c031188155500302d42d08441407a0b120f207104003c100a59420780c5c49140c070801031006058220780e0300035224101440500007071030006003040e03c0042001506165810700b801542c04951b01000051030f402d0320a41110100d00502d001003d140000820b0540719130010064200c0070001207080c03c40e000754135451500180c82c0c6651403903d80c0d006201001092044560100c000b10014032a41001e8010402081d95030260500b0010b4403030798107109034081c544d018002c40d440801000802015078000300200740c25038080b00140500800004c00512600647c2d05450311004098580703034014005403104591003089941501411300c800c0c0303042e941d07030f0140f5444556a21059084c403800e0141040c14501341d40001c468149850300a0140038055403042e85280d0030702c1c100140c8c4020909068034110002014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305610539 1250 305609289 305609327
    0x3080a020a05341811070c060206070f030b10030e160335030606090f032e020a050904021623100509061f120305130e090a12 55
    0xd140d0b4102480d10114448058400703000031a000080070710039188104c052203980c0c035075884c00f81030b12580440c3c800c409103c15907240020961310200c0d01503440e48a4009a0803080030811318581081805401d0865880c0401406040000080406148040220806aa840395001d2610007003240d081403504501c0359a100070365a20b4046403010809954800508040481d0800094582039290b03c0c9242c1d090410f0455564000b808410b80103100350341d9014010307401c0559036440034802243d584011184c00741d0287c0d12046503c41c54402c0805224207288108a10314803907034442c059421942046802507500c051080e81c0d03504800200202034aa8221900011619400403183c0e06440c18150180e41c07030710155408100c00c4540442c1c544120350040400140c014200c00140500c801540503240e440c5612082820081940701101720040f0703400003800b10300c22a1506811008041c5500c0f401254030b0018100c03602c3d6004030000410031040400261011801140d101075800c0c811a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305611789 1250 305610539 305610553
    0x702010605042405060a0507031b2a080d090302010e0f0402030c04061202030103020a17070b0d0204030204180f080d0b1302030a0e070509190b0d050304050102070602070f03080a020a05 81
    0x980c1882550b011580003d03803000154000980342405010386450b00c803075444050500503162000c2d12038424801c0c1341258100318a0000c0009141c1c0710003110080301c0d00084e040d2100d41c2d092642d503a41c4032034000c10740945c8621032040c4080c2d8052044e42c2501d9081ca011688003040c2c0c404210451090b21905500c2800442005280d800c070001510884034103959054460400c084018100e100c20f0201a4210590000038044400100609041c1040e0304088540c4241d4a1103296402d4015041500c0c4a0703070001020003d5140600840c0e83e4a072030700000d000d00c201117581c0c00c8040c8940b0703200103248443c0801c90210300e82c9240c1c0100414000a04604600641a5000c1000351700c121000c4040516107007509516460000c1c0311400c0c1c910141c8500b1440c2c980d2402204020140c0040c0103849403104118070041d21240308196030584600015a00d481c10613001909204080d0002d0003107610811003000410910000310301102d41182d041b658490540c00d049040083c00764000e070041c8078883c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305613039 1250 305611789 305611811
    0x912070902030402031006050604090b120f0d0905031209010c030203160309030b01120302060c030619080d031b08071d030118050705040c0503160908190c060305041a070201060504 79
    0x900154819442102070320034407800d082d10f51b82100c64074061503800c10300c20300003444000c006900121400c8001440c40c90040d4811022a1415600140456040c0c00c615115500c01e0b40043e02c040142c10220094203600310340c0c01c210a000c0c0a01e08030a0b04201080e4441c9042c18028030407140786c0000825242d07091841810060440300c001e00c01101c3d89800500001080c000c40d1011048031585503003d001b040d11900c28034802a04003400050f805480501c10400e803000c21900765004003454005001c1e019506032014080300c0102990fa10707001ca104030244800ca070300203091680501c050034013180e4010390090401d403030685066070682540ca0038910006801c490154021100d21550031110455107c0040c4026500920b8000d00403c40900202e0070285400084d0001080b0b41d15140e00e0460b600c1c6101841c0c400d40001c01c008000000a03240144003840705010b021b07006506081c440341c286540c44801030907403140e2071061510345101240c1c000e03100703400280041c03000420510841e6444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305614289 1250 305613039 305613041
    0x507050c0a03031e0629090406030f1a040203120d060b0406180501090810020d0e06040803070f030c0e01050304060e03040f05030105060d0b04140316080301170f06070509120709 78
    0x60340c075184d5614007900c2502d6801001e405a10305550042c440001c80141b104106408288122140718038000103105102c410b488511919000f907024551036070900c403003410300000019003180a41c44036280c200c10440541c0740082c01d07000890460310166507d8226510300c1000b00040e800c00c6090040001d800a0364030740c800d40350312400449091a050340390b500c5c0c0c01945c18400314407910302160020401069089510b50140050740b603840004103000903c48807a070f05102085508946582011091045081d8070625038010541e560601700680e01e68400c016004099001c80302e410000c0000020301081003a8001e41d9807504c0b9141240d40715902c070143c42c4070929850007224025840c000000f44140b6041c54165401034000800e09540d440b2515000b1902404036042c060b244000c10040414041c503030200f002580c058161240c6a50518162071030030284410b0b8403084d54030507076614508020200c1d22a81001c0c0030708001da03682143c4c40c003181e00d928490380711450310300038588005100d01035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305615539 1250 305614289 305614301
    0x10c030614030106030c140103020d110a0908030c030301032003061017060f060f0105070b010609090c02010b10030f0612050a05060601020303010f0b03040f061e1109130507050c0a0303 81
    0x103203100c80046074014205140c200c031034030712001d0120303001c0040c10041800c184d00c02c4040290185805482c1410210302031040e0380341c0c00d02c90200c00c4d00025150200d01d81c852588405800800040c500c3c0034012a209a07480c0410300024040000d11120507107174403407080380d074580d24002806030b804a24040903403c64010316032040c1511840c003180c10030b00c02030f40400d54034411007030701603c41e42985900052107812a5680d102605001c010003000f000f0441c80c50b500c0f8001c1030a581c82082d103504010b0030b10709071035212040314256030400210540c10798580d040d214101c0c03491b1500181640103080100080e00b0315038030900520441c03800c0b01c804d2141c08208410440c2c000d0013110550344900004a076644000d202d0b0310000558110240015100c1800443d085801905214002c01682e2210700032150118602a1080d602c020803900e405042d000b81d904400a000e442401c10600c0c0c030108454628040e1f5650f1070a940748006520140500107407044d0741c040500300c80c0900748900d409401001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305616789 1250 305615539 305615549
    0x9031203050604180b04080c1f1b0323040204110c0c0a0806010303050f1c0219110102041a090604030f0807030908060105010c08090f12031e0421060905010c0306 71
    0x41400e07911306802520420200009901000f10b50850f074450315107010395084207404444a01586210600080b02c906001c48500746000700082d29145010345100f0402140c01d140c1c0070715041c502e000715a01781d000c0b4040400f1888003a406010fa03a5440080c0082071400040a002c2c01e0101d40c00a0116001a036102660700540c0e007014507079207910315596512030074400100014000c1299100e84407850020704041001c05000c040c0c070150800124059802034904410b130102d05c6101600f249600102400c981482d00000b140b91505082610513416080c0c1400710001c00c00282c8880c03141c4402e401c8400440e045815084203c2462410b4807131548501d4003900041c1d1890000b007880d03100030908504860f016118594008034070b9865281ca034100b6189268032003003071040c03400b40b038403640400c0e0a842002400f96076142c1071900d003000040c5c8110044441e10b0f109201c10700448580c01000301181c4864414035240e0030403484d241028141c2108000c0c9194288a0024101d0740c058001c241511 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305618039 1250 305616789 305616791
    0x1081b0c07140306040f0f031b03080405011401080c010309021201050406051906180b3d03020903100e0717010b0a080c03060a0b0109080106030b10050604080a03050a09031203050604 80
    0x40e41482c10180e4810302a2000340410440c0003441c0d00203507000781013145241c445d003410070310b4641e2000e0340f1400040100c2c007a0040ba10603020041000b0013032180030140850365410300469410246ca003075607405103900031414166131710044001d554407040000c149117841070080c0402d26180c90040c000d40303c05d540750080078034101000503011000f03001d120141d400c03114a41035000c206012035000350060107031a07030700440c2c0e04003100d03040002d81d1518a00201c0f03100081a60500d100018100800c2e0340383c508082500c1031102c880280d40108500c1181d030303850a00851682c1d03400703028604000c1c1c0b562080d4403000110f41c013005002410f40008260341c0c800c44503414046c0da90001d6540303810304985501e9054020304001403103503296074000041c00c0018540034200d5a2141c1c03445084404079002510030800d21400c0060715101d1440d00005050706494490401d490000c06a5079024020300040910001064000c24184a902d81d20f00954015244001020030024051b0040109a07181e40c0a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305619289 1250 305618039 305618069
    0x721020f300103030503060d060204050d0f02010e0d0c090e01020f0c0a02030607170412203403030e030c10050d060b0319050604020c0a0b070219030e01081b0c07 71
    0x1d2028910604072501615183d20f160364000030440c0c2c250304800211032069090001041d00d440d40a102d12442e07109041c0c01c05003000d18000981302402420030039100da9148210200051442a2094212006450301284109010816902a00800c244040c442202084104140100140e104c5010b4001e1702503072607a40300c0d0700040740e232081c40c1c03030f04400061101c80104d0001123001d59042803c000e9860442100301c10180721a13074071703d00324030000301c594061003140d02103005419080d01b80c0300d0b6088440d84100c0c1d01c140c040203050301c14400a018040041c40c01126610240003103442080001d0550055007000d51015000c0d030456852240031500e000b2002ca900d40c400780c110384c0135000321584080000100030020000d032400030303c2e040d049a000e001c2e0501c260030820041200074450000c0364040d01d00410001d1030030503400070700c2c001c424419464501203600444a954141028601002c090341d60000010218200c0e20480c0c440c0e00c3d0016038090152000300d40302c026500b40c285c0c690b0034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305620539 1250 305619289 305619367
    0x604050f030c0d0f151401060c02011202040f1d0906070c030c020307090e0f0f101e0f02210708010905071814030f03041508100807030c1d0721020f 65
    0x41b41c0c038a05c1075011000c0c0000052040900a226802a09205142035100d400194802038140e80180d440f200c40d409010005101500c03180542c00f000220002034440680303408800280c0d5404060316610502c11680a940281413044031030b440525000307412a6815542d40e282f00c0010007800c002c48480e8055a01c21389007403480410707590703595000840102103c10404105400401030b002d50a00d2481e450400384180312074500a610304960002401038513140000d0091007e550f00400c1c8071200c5651f0400c02c4005508550b52038152210340304002410395500300f0555800c0211b03011120285204240003032110710612500d1105081907058884c000540d20085582e405140034003410354030107000b4551100c1c0f040540c9548840c96007052540c1d1952900000c2c1442c01a4009481c042e0748680140302c0c0121448419030311840b5044580308610b1f00050042041c241000c0070a118800c000c0115a094102e40661350300040c1078241c20380d00d0910074000000d00d0000001c4040b91a01c0c003e115007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305621789 1250 305620539 305620541
    0x21120906070e03060609010306020315040515090105060a12020702131802040c020f0318220e16050d1719030e0601060302070b0c03102102011d0604050f030c0d0f15 72
    0xf0003010098210f0b406c030303401c59440d600130790001882081c0c55001d2011442c981e82c0c1d240207a902403001010002c0e01040000148141c3ca48141c00040c0258400c00600300344030350080d65900580c1a005005031290742d10b1000072444031035411001d4201d420002074840c5050102c00c8440ca10740308490411884032180e2050b41c50303c036502419035640d0400c0c4a40410b014050406429620004108042031840014028030400e030b01c1c0c0f503010300c0325555001c403420328000704000d005a900315290603802c1858030000034007920403071800a1003203080001d20b040c02d200003410784110b040300e03400300303a682d0400d2138000b0003d10208071262441e108481c00064503900900c00c5620071900310b401c04282c0e9030344250074040e0743d0000d442444400144400024005001c1003115612200e400c030a1b185210310b8000145280e012048211542c802c0f81c0c0807907034030b69908044508a0300305a4000040c49041300000e0b0a0140c1426855046404e00c10203a0820410840c982d0403d40b0881e0111030580d040321a10b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305623039 1250 305621789 305621791
    0x2060f19080118090609020909251410030f0203090f010b1f0c030507050724030c020d0e060c030703020f120a020613141c09080c0321120906070e0306 66
    0xf6201c490000314014492055084034207070320f0242d9008204460543d020407071200c02180c1e036050316040b10016410340c480c06100143e0002c1c1c0004c6800e40d19041c081c008062002c0c41409505c5640c0c84001c0501d5203000740c00a4094901d2a07030708540781d181041d446507d076440c800340c1e440554a00050f8101502e8040c0010092051032032160741c02110192058076462582c65043e0103010382403200300c00113a800c0144001402c00001c9220386e01d400f14060288000d000c07442e8000f4142061050700d00a940054404840c0125241170300403035101c00302090b01403240150303002c0c4c58000020f51000303064002a00ca95904901002c0710480c15000c65101068010700400300c0043e041400401e00c13003201c090700c04204038001c004070684c1c016007a85441c600700d88144403410407551800546401c542095001009040d0440a03080346809140001d85540500030b490b11a00700801000129143d0001a201d14000039040c0e0806804c002950640d03503242202c055002031500361085009060104480e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305624289 1250 305623039 305623049
    0x8010908030103060507050d0504080403021c0218060f040f0c08070504122018040201020601060201140a092d0c12080d0507120c080402090705031611070302060f190801 74
    0x2070841e401c0d50b6504014210191014007044024000310005504900c07031140a40d1040344140d90301e030310f5841448407c00d203c203c004801c00c81d104494000d030b200d000989060510882002802c0c1c2da1715800a502c03c180c050307440e500a440d28241c0702003803034a507000542e0300740c607500c8042180d0307036440d02240c0c94411ba004010790041100301820020305140010700d01c44543c03c0c000718810201030042050036003800a00210850010140401d5503014010745000d043d00d44000d0000c0c650350790b800741c941c24002e0308801c1c00c03503030340d038041003d102100d00d00038810710300c8141304090980700d145400700340c0700850002e9a80d0340d00c0f440e00040d00b20300c120404102a81c440c610070b0030303c1c00100d03050700107000060031380044c0050764038000300d56041c80c4110420b100050700c1d5402d29050a00502800181c010100c00902204001380240e10081d41740201e803800d1140790008044070a0b000d2281410800c2c1d00094200d540401c003540c0c001003010103400d0902a2a0f20504012000c6d02c0450b107982e020302c12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305625539 1250 305624289 305624303
    0x31109011508060315130c0e070905091503030c1b1819090203010c03090506090609120a1205010e01090b0306060f04090512070b0603100c050d021c0e070f080109 71
    0x1440929000790b145660004000b01914010410741c0110021403000b01c4120011140c44007800c010065103128080107801c610212004c0d42c94035031400340030003c042c02500d206003455400250020000951541c0b40d80c03024003a241c441e00c4294042e0f50b12034401c48070341c251350020a07880c81e8a05291030195802c0655030a844420380300e1007840495000c401c1d136215840358682d1051005a1005d0050041c1e8000030758000511817820700308141400030207099151550802010b00420350b40010360030481826055049a80344183c41c4141d441f03459009541c101c06007400c000049100502c00c1c940d048036180d9806000900740d02040548541040714500d0f802661810342c0364403400e090b4130000c6658450300845030400030a1046100c50340001070221070880003002000366504090214041c0003019035814032041d451548081c21500a0450150f8200c2e4081200326070f00201820242e10300190307060402c00c10b9840012191620400d00400a48201c1d42100003440070051090070055500b200c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305626789 1250 305625539 305625569
    0x10312080402061b0c040624050c0604140f0d230703090603051902030f150603040f060f180515100b070f030507150605041103130f03020f030a0903110901 68
    0x4c2d491502c0040b55880c8100d031280e8030408110f41c49501c030704000341400c41c1c09401c1c0c1c1c48440440074a40600724285008000c0103100800d442d040010740300c1c0d0440e9008000280c400d0b0f00d40e94035403420051181d03030416441642072011a0f650042c000e80c0c214502c60400c4030321314a0003401a5940d01c9005401400208181020410b0910a9101c0392f0000400d80192408401c0c04c00e6290582e00252640c2d86140c40d0141800b89440350106480003a00042d80d029045180584440c040c4058506001e00314070380b07800c414040c10150303900c5028034050150386c0c0701480240782041c903a41c2020301d6130800c1c00c8600d46c0106000880c0031165104031030305040f12a150800380e540c1d160600e49000d1040f002d0190600c400c000140382c600e4941d10344000314000040080c5484104070640c0d4622000c4ca003050020402d105c1034042c140e08002030b40703400c1820844040b40b02c3c42d08078580f10402442d0b88242c0004212240615440324030a0112805130550b90b0002458030104407101d8028420a0b4812040f02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305628039 1250 305626789 305626807
    0x22103030a051008070306020912070e0705030402041103010605091018030f06020d020f19170103140f011b030506100e0904030e0607030c0302010f14130507081501031208040206 78
    0x50441a4448500c1c0110000250b8a090703c03403910300305810880307207d5004103151259003001240c030905012414001c01c552460074040d0142840060003045c00c02500000180a548868000c0c1d09100c6058096903a650381d50304009100c0d80003080384920480000e02203074481440b610409640d00712141c44411100e00e0365a41401d1180400404c580c001e4091152158068440c40a0000852a14015503540e0034890b908021804502a50001e225402d225031030380880150409042d00d90000c4181c880d0a80746003114a041864105850f4640c200950840042d00d0003598014580c03160f2010321840c0c890764100b1078203a0300244504006010703041200401d260030080580c00c940a401d080c880710000b14023094517a841a070007030700450800300c0c00004040d4240f0501184403071307050040091180281c0c0480781040d028019803000d81000000320103210052003544003d045080440d038602400c40f290f43c0b010b001c00d00c81916014160245415418028078981c4d1043e5030040c0081d1510000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305629289 1250 305628039 305628041
    0x90f1632120a06021201061202031603020307021f0605011d1005070f0b01030305071518061509060e01090606020604030807031a0d03020f0f0304030c1403190c03022103030a 76
    0xc804032055108242c0c0050224080380700030141051400b00481507581058806003075121040c50042400d48100704200005240702c900d8a5080002d140c003503943d45620900300d10700240061161510381e594140304001842a0f8080780841e5020707200d03040a120140380024482c0030070301006800c03520b061809544339100d100140a502d00c10040c81d80e801907240c46156115000b41c0044000c07400015400b400d00440424900b02a510800d040c02002e10184d41c030206110f50b10350003004d154487e080b80890109044109001e041101001c010032036541e129071880f14828842c0c94292860710788003080c0c00b44085500c80c4200d4040e1030b5110140c0311084202e000700703e0307d504d10102811110a0340140d03a601c0403600103141c0030f5401002c2c80c51540b405203050050f80507400c00b0780d500402003000003c03006103955049441c07201d400050050820007080c00c00b105462001c0550503e455860100480c0c052280d069038025150149200500a5020542026552880c03041d50007480010190019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305630539 1250 305629289 305629309
    0x5040621060905030a170c040302010f12020c0f06061e011407080f0307050d05010602060601170a270311010216020906010e031902010215070f0503090f1632 69
    0xc601c0c000148a401502c842d419500700d03000740d200149005480984050042540c280c03c2000c8540251825245600203411800c14400708800d11281c102c0700b8291045030360540314040c440c2c2081d035041540722000c1e80c0d100c1204641082c81340c421a00000c0401c101c480708050f0049040e160765040c4980500901400e8204000031191103c040108008034010200514003ca040d602c0300c507141e00104c0c2c448402eaa105030008011035101104000c2d140c5c0e0f20060000411080f20686152915002d40c1800645800421084081c0c80c0140700b0115069400400352403a0013039039403401d2200180c0200d401d0380310f9a10300140316812480d07442d0141c9003040645030071501c14103050204c640040040703400c184000c1401014012010038031b40c10365030103201030754880401030030036215441c00c0300b005441c01207640444010090003000142070440b0410091101d04405811a81d4403003100010001045507805078000404140301c0d1400054544211040c00110710801d668005124074180f08420324 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305631789 1250 305630539 305630543
    0x30c0403120305010509180705040e15010b07030908010507050702130209090403030204090b01050301031502031b0304051c020a1713090e030304020102010605030a151a120f0705040621 81
    0x40100000000070701d800000e80c01c1e480950301d000c901507142404114001e20000c2403003440800e280d00a02c41040085100c109664045a000a05e2080340380b5040c6440366a5043c21980e40200c00042220107405010b00350480c402e40d1a801d529031102c0f605426520306643c20700118605000d100d00524018841c1c00c01c0040d03080005007050000c03000201c41506c191016404664006014040b80f08540107d43c00e00500303080040c03440d450340e9240884180000c5440d0085680031010501c0303405040900c1c04600f130303a15100f84d26814242006a1501d50f10151201c0002c0e211580c00307542c50000c1010040c10303401481c03103d0303c0c94104010341803552104000c4114041c2c40c03103001c107000009201d01c2d00e010602e4802907480785070600c0007a00315280d41e08518071036071100c110000029001d003100d007580d2809040203c2c05400c41c02d18141f0516400e514143d2201e00f0000c0d0300348448001070300e0504401310108454030b01c1c3d9079005000403101c5034010b00c507100050380004a210f820031450f10b81024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305633039 1250 305631789 305631811
    0xf0601030b18030310060e030d0203031b0f0a08151203070212070801020403030909111204080f1c0c02210403060b0604080708030403030201050c1321060e01090203150403090b03 78
    0x18008802c100d00710391084402022a034002c100c144a030f20b40c0300d1503054251600b64002c1050840071032029549000040c0706600c01e4a850940e00c4055140c002034072045940e40701c80e1038840300c1080000c5c00c0c1c10341c03c030f070322070003160002122030b5a078945890012000d03401c9002075072620440c0d4091003180b4980340e29280562041a070009a03283c001d20052000b180641d41d4851900d04043c220003c2d54894030045c40b170810705015002b501e280c4441c01c260440c0e4403005680d0f0b900503604c501545805003031115041e1140301c803007080c0311071150741000c0d010404540c01e655043c0c4c01a48140c1081e0424201d421050130300780002d100081c0254001000004000c10070350615695845135464100d0540152525070070108007001019024081c0680110312402d001d400c100c0602045569003110b8071a41f50307140811010071410383c1d80c00842050060700f00d1030520181440d030344510301034039800e5000ca009104040300380703846180203401c044c01030f5403650b11403a07920702d0b2407002031307954002401502000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305634289 1250 305633039 305633071
    0x609190f06210201020f03040515310905060d03050a1d03070b0417061b0702012d120b030c010e060408010c09050a05030307021f090f0b0c0f0f0601030b 67
    0x1a5000304026641d00d4400c0a081d55034900c2c920009080214019250041e03510902061000f1740c1d828104510f0b1340c040809480e1600750000365140b581003041c0b481140e41c42d14000c0400c03007202039440102621104001031046484400901c080c0d09100030003d40082c905205c51400c0354810302e45007102c904070203503104610180d980040d050446036441207a480318009020080c0c22259450a8a01c1c01c11001500052500030781100c43c0350710148100444080010b01d6104582c0030341000d507041c100d40070a0500100071400040322502540480b000131440c2682103080340c0016000f142c070080b8014000e02048a079110064800e20380300144554044001c2c000460303012400d1050703c0b90142542e640d008480d00c0c010030310502e040319400c103038002e81081004d40090b0b1949203484400200c040c01c4803114010072036085900035900d410101c07a01151540020700d46032000c0207030441007441801c0e03c501c0c04641a07920707500c144000342c50b0245d0304818010404111070001d010307848400c44a4030455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305635539 1250 305634289 305634299
    0x3080105040b031513020102010b0d0c0e0415020c0a030e040603170a030e030d020a0f14030f07090812070507170d0f020102070204140906013203010b030a05030706050609190f06 78
    0x13075414100c94017480481c504200301e06641e8240101c1252440c00d441020780d100361521040603040042c040e0000007040000424100511308030b4148804800110071900d4003588440d50391118107520341500000e80140031404180b030144118800c0302e903c215500c610844496002c0300c282c0140300c0c000c060590f03401d940200600c080c00207006a00c0f0504c00182d8440c12803001034040250891030000b000503400070184040e800c001200d8101104050320980742d0b446283c115a003140d5900301c513456005021071940e10030010782c00382800034403440603a40140e480342d4071107000d50103a46519509034001e07181c0c101d81034003814003065440200e1001520703118043c0c0100c1d09590490380c903030030071440032410080100e6080c4407940c050010f07010307401a210803210340701d103c0f0441c150010400c19201c0e000052035907002d60003508800e40107029190407543e141001ca4498008040039181941041c000902c030340340c14400c03030b0300c21000460801a56130003264900010000c40940c0d07603009035a40b0380890 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305636789 1250 305635539 305635573
    0x31e0507090e010b040506030406090c05060a0215010b030c1905070803010e1e04080a110304050301090501020a11030910080a0207060905010c1713020114040f0801200703080105040b03 81
    0x48124000e44401c180140360506203822840c050b80000900715052106201c5517840504480e003242e04000040344100c510708025130400801d50080d070340070a00141c2c901c2c400780c0114104840182e00c1c000c41c501a030781da0320030842c10700c0110f410f480800340400588a66000488040340c00c0304c1a480c2041c01c1140f20759039071035158030070303001100300e410580b08224400b090b822030b2004030f078502c2c04074180c541804e543d50000c5015406001c81401098180918407801c20000c0d60b00500004009021070016414880c0c006e40c812a86800002c01030201ca0f5180300000080300e00001010b800c1c03409110441e8012501c016000e45083d554640030003404020400c58042c2d0300407103000d031f07000058402c2c503844042c202442d50768500700748035464010403c0303a01001080049407602030a00c0c00c001c102004825002e840380741c02c20325400003200030204910105500ca6800008000e441a4552000410144560040308402000150306030700612203803c0940040c204114060100c034490307614100125 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305638039 1250 305636789 305636791
    0x609180102030720190204021818011d0f07030f09050d080609071b0f060e070806070f050309030d0f06050303040e0a0501050603060102100e1014040308010b130303031e05 75
    0x22001c506501c2904440380e803401074034240c0030007040c1c0c5170b0800300e0754003105080080180c4160b0b40841d14144071340b11414640078608000384002244c1840803024220795600303002d001000030104001407400402c28102501803d03d2035600c07142607aa56030220040e00c29000941c86103900c43e5060000100c04100e01e1200c5034154407000c03154a8090244844070200828201c100544503094211111000c013444032069000344c0c106280d900c0b2811720382d025083d04030f0003010512511100040000000c11000d01a9029a40350001480d03032400c11201c501080d031360a0b102d0703042081030940301c96055102d640aa40c0c80440403882c0c503600d5000a0030760b08142e121a107100395072820089041c8a41c4101c5016000c1128094294100300300000e41d22030401c5c41020560f9a698814201d4a00405c1504003903000720300c0a0002603c04604141050410b0310100c011070601000030512400030415142c0c4000c9900101800d01e01c0c58400701c0144c0241e0194000450001000200c0c00e2228082c613 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305639289 1250 305638039 305638051
    0x40819020c180711061003062f0c0607020102030c0d0e100c0203090103050915041704090507030b011209200a03060609021e070503090f040212010303210b0306060918010203 76
    0x2d80340d901c0d08a40c080c0281c10007025000c5503070010420011030303016100d510803c0d2034100f14002000c20158185005079101f624801605243c944000b11078618907800600b00c51908000f9180180ca0307286041c0e082c0e00080c2c91a060107901801810654001580118442410902103071403480403d10707800200c0740c84041c868016040010514941d50f010b0040c2e5803c000628001c11074004d401115192010000c0c0005021030400e40d0889600522802542c0150400380000c00c028100000007030001d0000dc91900d0110780b8440b680a0362102d284280900242c00c141d0120f98540c60208804d207586031402d001c0e6211501910200118a45203d50400f400c0d034064010782d643d05d4511508814029409400d40c5050f040190400142002c030941d08241000d541401c800c60781840050081c3c0184d402c923100104154000109066001c4031070500d00f580000d0268080000702000025200c204980c2d40c1c150f030091000c92800c0c1031640009902607400c1e04001e400b01e504101d403a003660300035114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 305640539 1250 305639289 305639329
    0xa0903050d0e01060503010c080c0f030601120f02070c0b1e030c0c0a0b09300a030902090f0714040506090d0309120b01030317070804060b040e031b070905040819020c 73
    0x401c0c40f560600b4400c1901c1464103080c614030601e2b0580c6c0b90000d600c28509000084100800800c03120390150700c0080c0382e540e1007202407000303c104441e500002e4000710420b1f40d10303003040d11001510b8203030b032011140080e142156040880b02409501c1585a002411011138000b04029004140200344514000d0300d1103001c0084039420701440052409010a05d60542e03c800f00e50f965028213000311004000302c2014410030b4440c0c0d42d100c0281d0003003001001c0a07400500c03100c100030140c1100b17503240d403280d0541d445911141c40141e004c50918001d82c022240c2018041040201c1450500b80d23103007903d0305c2032900140080e215120a0000c20311844200d03449075104005008040c0c1144030070051507480b030340703041040c503044100409030740d401b0b01b001e080c2a42e00c150250302500e858001d0002e81a8500c200e91340c0303064010001804403c82488405580142c5001081c84280c2d409178501480d0030800304c0e03084c0781e00300c0c0070328038421688120703d02948190351407449651a005081c2d2130395248488 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 305641789 1250 305640539 305640551
    0x12020706150b16030c020f04020304080a0810050604090b13090506010303030e0105060f06070510020f0d0b0906030604172106120a0332160c0902120a0903050d0e01 72
    0x1410005030342075038002d07808042d014094003255425403ca01c0d0101609840c0541e603904036400468100c51800c070405401500000400c020300000d08010300101525640d01c01c40343d031342e41c0607441000c603041c02100c2d4410030801040101d4041ea802c91b06139418001c12488103545c8401d40581181e01080b021111500a00010401e064052003420100340d00304000b40054500a00021b02943d41e00d81c0702c503c03a01c000309968050000030004000308581282d421559100150f2400d0b00c1343d00080184c5480340d041240071000b5017804e46d0312601400b40580205031640781c036a40c54004214840390b0f030845490501010310700364a410f090208100c00c0250700007035410400c042c406c1c006444c0e0081c0c02d65501840d148000240d01400e82c07607040d111070707120140920f030300c0e0300084680f001c0d9900030940f07034404101c50303020300c80d000d01d002c00d403030b01c00c0c044040c440750344109c0d1406901500c00013003c42c0e0107220020b50355030325035000344040600c2442d02c2442c290410405608842c900d0b141504180e540716 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 305643039 1250 305641789 305641811
    0x10501050a1e0611030c15190e0c010c021c0c090b06131802040e09100e12091c0b180c0301060e160c0c060206161d010e0112020706 58
    0x2080540580302c511800308075a620a449a07507904a00e1041c141041000401d039a540c0506000f9105032024120650704182c680d005804c0311450165088880e1032080f9170765562069280c42101d0540340d440c4c0103011044e4074031004ad10b01c2c040400c016038124022502180400706011152520580b05400c0d8182c4c50781405404000c41d00b0f048031090080f20100700485e0350301035881e0700b0811101c1e24640c031542d0403a1004484003a00444d84900e241c081e81c1810f0099411011500106070341d4140d10810150070010001645c4a400c0324454080c40010800e9900324200220000003882c150441c490822109030f0b120521b249048402d0b040041c41705400300e00d070710002c0c0721250301c0e50000c80083c40f04600703194540b00c800f00040d100f5280500c3c01309500d100b50f802110031311003940d04980c4400440c0c2d55020080e4640d40112600c0840c520030030340c000c201d540078400007003041000c40940903442103c0320040d40d41743c121880d128140050518020102500b500081c030041748aa8008502444c2c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 305644289 1250 305643039 305643049
    0x606080106050f030402090c160f2a1406251203050c040611011503030f0e1005090108152106060f0f1e031009021002060405120c16060201050105 64
    0x68020400300001080420f0440c03054605036504a90100c0344d05581da2520644200d05210305801c0988000520542106205c0c01c21404030703410380110503050142c2c2800f030300111180c40d081d43c0a29000c041090900c4464146e0020a04981016094500c0c0c444130059244100b06d1007400101c0c45404400003004004207001101440152810705000500701010703e682d0b540200d018003420409140b07585004203600350000c200c00304042c9003800300191a4240108009803000050010801d1024802d11508058841039558916a0f442c0c80c00c1c40910310044808400103801c0c0950044240a17440c1c99550700d440e100c03500036201c0d0125072041d0b141010241001001402e140c80f40348007070501800ca0300c4c0d4003002c0c504008111061150918107045440200b0b4082c54156014411002100066a09640030000c0d181c002c8a003d0a821880d280c1265a004c0403200281680c1100c221040380002c044d0103400c81c007298000351042c00c03420300d0040f02141c1c050ba000400513919440100024104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 305645539 1250 305644289 305644291
    0x30020301092a060509120a060c0207050909030f03010b03041407060509010207090e0c0409080408030406030b0a0b1e180306040c0608060d0305190e04020315010305180613020a0e010801060608 84
    0x2d4142e000d80d0040c0b60180260041c0140000c10780a00c0400880011142c41440742e81c851030f40c0188100400301d00b92800075647c3d01c2e1070084501a28201c0003040d03880c5800401c3c0e0320302c04541e030800391843c0c0c00e090308860075400280c0125002c500052a0b12011403042c010100901855511103880354000c100091600030325600000d14070789411118061003c02040790300c4017500075540440c4192441c40c1140d100e00c12075005900070300011501068695241d00142122241122031148050b15840190381e144505025260000140d00c0c4907120b809020019024001e20320034141e0040055002003400c0c030400711411603030007420031710038400181c000d50541d41001040c0c0f00d4013030704c1c0502e9034003505a106030700210b115083c0003d944044c883c45900c01802c2035102401c155180d041411415007a02c1da100d0b00c0d01e02190503c00029612192082e2002c40c21044400606603600ca0000442d00070205030380513038011800380c10125030341003142074590080c20132034000900e09240100062000c030f4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 305646789 1250 305645539 305645603
    0x109060506010905010c0b0405160902210f04030809031b240c1e04091a041116061802060a080109060515030c09040914030c10063002030109 62
    0x29102c9418449668031051035a201c0354821f40448164649084c01e0b032034614082ca811480c0c2c2c100c3c64001c6102e1071315401500c0e82c1c80550100b40d0188840b89500044020202ca005104842c0c0c0302c005404079100744200f5820596641c1500e14050300d541004255100380d08540070302da404040c44055007000c0440d0b1802d141e040c5032001c140f500341001040210300c1224502034100700c1710045862000642c0080720010642c6400c100402d421080301e00300416040b4550900c15860040e0403000303200e00740c04540e8060710306462225425803684e1810020041041c644107100c80c0c00b0385120042c0c50306030040c250310800340c89a1140e036141c4001c01040d100b0b9034202798041d4074231401210350100c00c20281c075040350342210348a4440003084c000c24010900d049000e00411049aa40c40030400040020700310740c4d0205c0240c58556900c041c0020030f035122403082c918440080401d01d01c1200004d0104a8144144912030511128640000e425210807440c1510780391910240d000c091000303c0315843c4608 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 305648039 1250 305646789 305646797
    0x7020a08030405090c0a09051f030f0b0a092a0c02091b0d05060f0a03030f031505060706183807080f09031e0405090903041503021812010906050601 65
    0x1410440800c40040014010580156010800d0b02110380500c0b01c0c100a044027030090f4207002251528442c02a800c1e006460100e89011b0008072090014042c240003010003410614a203450002440d0040c41c441d800300c65090f81c0b043c52500d811040000185044100303036140c07100c0d40c00030700402c542200b024007030003188548008290044d28104c0c003511400c2140703080c0007070345a0310f96000c00d032205460340304a44c0c80000514080f003055080409001e441e0203d59041186480e086005c20100c2c9243c02542d90101041c0411000104a03030400c6001403035074401c0c154001020341c0c03445803d00d0400d9201103602d4200708403101c3c0e0b04081300303a599602d500344014501e42c10407090140917280d0141c05038410b07400c2c01c0000f5891680800403100741003907030781d2810340d4100b500c1c41d20020381d046400fa00e8450310854011900342d00001007698262912290b1480c004403c550058009601441032904104441d03112100c940c0d075100025100f103034040e000465039402c0392404400b10f07100100f4260501c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 305649289 1250 305648039 305648047
    0x50d110a020d0606050d0506090615030601031b0510111203014a0405011a010801090c180801090606050405090c01030f0b030d0c0b090d121e02030a0207020a0803 71
    0x10020024420185a40550700820819007505281014051680100741c104c1e61190954003001800160796110b00d42c40401c0d5429a01d038080d40300160907a6600840d4075602090060002c030394206502c2461080c05400310307600c07d6503100480c1c0d441091100d04000b10300844c9842290f450300348910300c0d200203100091791039581041c1b0006418002e1051500c1c1110441e0b8003180d451824400541850004400c000b4855207005641015054201d4040300c265081003034904040e1504842544011170586503034282d03030b090207030200050445603082c004020b55001c40d00000b0f607114415401038810b05001203180394490400000380e510707a9100501440c9440c040000d0000046030440c400340d82440c1c045554007000b00d40c10b0142a00341911030303050003400a074812160300b0142c0c2d101c06510446040200f5039034040c40544440c1100f5407200420741b03002c204032420429134000d03041c20f4003003090040704020700c0c1041d038200e80048608908095001824100358034225840c4001403503c2c01c000c61038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 305650539 1250 305649289 305649317
    0x2512030504080d020304242a02040b0a140108090109020607120e030d0915051b0303010e070216090c021504080d111606200a020105070806010528020304080106080a050d 74
    0x131011b0b000405c4c101d0000da01c1d48807ca4601c1510507900807650304480b040d80c0c021914101d11580c500c9a004c81c0310700e140c5032141015080030040c0000710f03002c283c0d00f19400300c02540150707080305004000c1c03003c40d503030b07070070a030f40180e81e40340c040c1444a0151a580c00100f401040191102c006111082d107e54000000b404c400e607840107405042e1307843c9418030040c2c0b002011080e24075000705441c01401c03a10442c840300348418000301130b50403201d80c071491708000e03203580c002a6156a15070800d25140c21000d00c003880345141c0c42d08402003600162040790700010f0290301c980d000303e4040e10300700d41c003140005625400d07c4803401450005a82030300340a241810040c04030811100252000b00701649918111410000c0c480e40442c03a000e44050081d030b01c8241100003402050f0449421010032028004a070040d40b050301554200c87c071144076040100e80000940303007038110041c444000c40c4810030010a11850a00550b00180480c1000742848092490240d00f0400701050400c00c0005201038440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 305651789 1250 305650539 305650559
    0x50702030a170610032d150f0e0c0f0702190801060605040506120903070f050606090a0603080a0c0503090d24020c07140a0b0a020d1d032512030504080d020304 70
    0x406034082c14000b81d0f040380004203c002d0812049007400040181c5039020240c46c1da40c01440e91040d040541c0c40d1080d46074201e00c04034200c98000d02c2e050814040000d82203030b40d100000c02d0701c40100da24035403c003980da0f13001407100d40414004030181c2c141c4a8080100c4070090141e0ba01420507401c1040c00c00e0304140210f02e05008011102e13440d40d00400204030084001c0c011190110303004820500b480c02d030381c2000c5641d08401c0d1046802135140000103040601e0300c0c42032805480d07008101d580340c000144021030360f11015103c1625280000c003d46507c56440070344d0124103900c15510b20f01c00e20340c103c2c4205c025a40040250741d040d80100440d4410704004072705101954040440405081c0d90312000c140001d8550300203c490880c00075401c40c104d500080d0400c0c800300590b40d4102c00514000180050f2070780c54400d10381542c03208600d00c40c0c2d0140145c0040c0c41541d1030541c03e070074a981c3d1502d401d11003030312003041c0d011450004090284034020f01c004081000c041c00214941850000018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 305653039 1250 305651789 305651809
    0x7060f0e1906050a06031209030507050109060507060504050c06030a061a09092d0f0f0a1104050d060f050a02070201080c0c0a080307030e070902030901060611071e09050702030a1706 80
    0x40c202d5680381c000608004281c0d0051010b10b420081001d00300e122003c001d1310044180c081911540304016001500b58424000e000c01d90f00035560745400c2c840940c0e00d400151202030f000b19294046d142c40710b00191642e074007452241c2c58842e00880c044e4540a0ba8100120412800401d02d420410068015488400764290841815012035440c0c621040181c1043c048401da01c0c20380f0440a018001400750070007119004208250781d80c0c0e240e40b41c80e94100212200c0700c240303c0508101f0702080203035140411142c1000340c0501004942c092524010104462046890720039455001c0b0313180081d564880003c1e40c0c0202441143c5141000d080d0b10941e541e03c1480b8001c0c800e042c000009410503200c0c1d006500c0300940001103c01581d11003103400042e400c21907921030300e90b180c80b800040641c4200f041050209031390300500b001c1d0f400d080400d008900ca06091040b10608100300040079005132088a00c200302e03950242da1540c8900000a00440c00b044001e0003181110040c0170301a84c840c4090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 305654289 1250 305653039 305653043
    0x516140a030914030a081803030d021611060304020109060818070f08010c0504030507050405061f020a020102100204060e060a032304031e050d1e060e010e09030a121e0207060f0e19 79
    0x2480c0f080f00c07e0710000349144159102010054000300c0ca0340811059045c2882d0994880c031001c248402c800c0040c40581c3c081140c019000545800d400c00030580109142600501500c02005501c0c0760b60501901c0d01166a01100201e000ca10081002d00d0083c840c01082520900e0100d20301441c50300c0d800d40c0c40769103014140c40b482c0d40340d021540700e81e02d2201910041384019a802c4810f008400c01171b446c1c0b40c82c11070580c00b40c003e01110407241e001c1c610850f803c1e07905a480380840c02d00c07a0414840290807101943c4103140d81c60b003500e07810b0707204a5010814001201c0c1200601c1c81c007450000c01c1d801101c0c4103600d03d50504003400340e83c01e801c0800d07130310b0715070076510002881c04e104045c000c5156032812148100602c0c110000c140c0d00000701d0014181c0d030f840c1d002074075607845500c0f080703076a8031a003100280000c8420004070b0001c000d80d0001707800c8040740d021640b02d0803400b14002c0c0c100c0e80542021102241e440c00d5441c2002c1c86801840f42c6144080081c11aa0000f1004842e0b03000000d040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 305655539 1250 305654289 305654317
    0x510020304170c0a1a040f080d03060b0a050703200303011527030602220602030a03050606040e040f03020a0611030702010b0f090a0f0f05090c0a08010c0516140a030914030a08 77
    0x1c01c14405c2c104040e03e000b402c1958a078100280e941d614140c440d8025003280340064100700300402c440a41604489412055503030300c0c0d00c2e04206840c2120842007000304170902c04089044a4000c040400203103005e003480391024841010b40701c038043c2c03000742d0043d20300303030041540e001428250a04800074003c40350813440140e81c40504200c0410f0000b0400d007140071082d0b00100100b1039030b0f400805814444620784082002e40c42c1c0c44200304241c000c5102e081c031480135840000b00000e1020380c40280c454400e0040710341d0805243d403620150707410240d07000a5000041300300320300180e090082d240320701e0080c0c0c0c42e440601a0440800c20035030b001130000340001e031030f09040c4c12603504960104041c00b9030380d1001c000da030401c00c480d0741d00c50310080b80e1907101c0d0070b0b5000041001c0c1c0e810f00c202c05414107952210751a2010b40d9083c0222401004015102c0f240d50b1581c1da102032000340485c0d2060b600c40d40d60300360aa81095506007916138110380242c0a640030303080490004004004480d80d5001c2412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 305656789 1250 305655539 305655569
    0x1e02070501050307032403080310050402040b04151205040f03090608090c01200601030b011d01060c15060905040c0e090705011b021c0f021302090607060906060510020304170c0a 78
    0x12400c000c44a0207103002407080d96006e00100340945100035600406629020040a9544604200c00d0340914000c081a100d01000100588120000d05042c280305a05000b9a02e03030f048200302c000c03500119010f4400460300f1800004240d44090a200980040c1c1003482c03035810000181907440c2001040a03060000c48612503c0109220380c011007a9282c42003159110740c2c4a1602c150409400c1c843c01400e5038030740062003c004e8100c1d0303501c0e060b1603480c0e64400030365885498040340050b422054051a550340c06000c64882294002e89104600407a48581e0042c03a05038901d4040344001c1c40d0901c0e0781c06c5030000380030b140e0780000310032940605240d8030404015240001509583d240042111951508204070100300c0000c0b02125100d000312945403660b880900d040040e0300c141c40e20190721000401c0200001145130b40905a000d00070702c0001484c9444034049400112104076480c0541d002042c104031148040703400224003e0f20101508101c240d11380450400c00a5008113910071800704 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 305658039 1250 305656789 305656811
    0x507080f071404150201060f060c02240706090605090c030102090102070302011101060b03090d0201290103180507080c1207030804030b0403050d0606030b03060a14130812071e0207050105030703 85
    0x11043c0e03000703040c0c90a021241c01e441558068000c0c202403080004450100000140071405041c88198030f0341c001d014002010b05103d2141110749501e0f161034116482030103020042402d40c499600307180d110705400034a60410300346c3c1c145071841c0c08800c45c7c483da0040110b081300d41da02040f0601200e50a007840d5250080303d09005014107101d4100c1c061300200401000250580010041903138015038000300907000320503140070356551a1118a42a8840d040b0564002d54481d0303006081009070316046c1e010a50741d40d40c541e42000c2c03699100e000380d548103004541c00c52a1070901c610342020b9800c010709902d81ba641e40c1d50402e0207144030103030070358001c18002014580550125859102d2401041108546454000e8001d0044080c4c45003c6d10490f8000b650319040c900c00c1d52400351940d55801525552050a03820b804038903a000ca0340b40380c0c28803890350420000400d42d400388695032602d588a0641c0e02e590180042c0c18504c403003c561194200300f2007070f608402100c2d0032071f45501c1c0c04660540e1035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 305659289 1250 305658039 305658077
    0x4050c0f040e03030703150905010f0509070309050f0606120309030d1428200a02040e01090b0a0e060708040b04020f010905060a090e1008070e060102150a0c02010507080f07 76
    0x1d4000b0140c0ca000001c200521590702da445051500c81c0c949a683c65282c5840310700c401ca401c240100e041c00b0140746401c0c0080d05d400d00129511007264607001c076040c112a60350904100d0034155003401c0360300c40010301c9864640001d043c24002150301c020f40c01c269140d40000ea4640000b420101440340700d03d1040c0d00d100d02501226425040c000381d48400c2441e88800314100c01906014900180b81b0318014a0365070200d4580c0e8013412485401070504000c1502088010501841f070300c00259079a15281000403d48590380f40708440103c400034004003d0003000e400c00300010024401c1004810401c400034064454681d006901075aa5a075084240030060381d071000c003074200c980c1c08130300030400c101020b910008542c09e40f00e00c074040150365150585030703800d04000c80c02200d8142e0400c46041c07105466000f065a0f01000500c1168951600011902d0720031005448188403240c4074500c0c1c00c1080e4090080740d4108150b0303d08010980340802550310a001b014050304c0401003c000d000c804c507050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 305660539 1250 305659289 305659301
    0x406090309050d03050901030b0607050a0201140d0612050712080406050306060d02030c1b01060510081012050f060f011208070c0305010c09060801080a0c0605031008030f180904050c0f04 82
    0x1028110f44032040c2c0d1400d02415682080708100c0c00030303040c1030007118642021003d40e1301b62a0300c0b01c01842181081d038010b451030840d000690605034030038019400c8003180c6d40110001020303e1140c6000603113982c10b00c1410003917150040c1d00e01c082c0c0700e5101c0c0b00240c0300350126003c0310580e260130340e00e80e100d40d000202c0c04e100f11501e000041c2d002000388201113007920000e0042519404600f8542420300b1405800e8417000d103d026881a080710200908034058100c01e80e1148400c486045080d4070b0301203240749407008200039182c03540011a0094207100c1042120b4002050740a00340f030701d40c07400c80d44403c0c1c0424a074000b401e28001244030700c20001426401c002a50b4407900a1013010309042000708100707407030b01c600000108514000284181c011904540c00b41e00202101555402d000d4142c4590f40b01a10890420004550001d0300d4207042c4041c00c110f880660000b40e5455820f101c1c4503024010055680c86a11b40c2801d001c00207000107401d620054054500c007007400001c40014004000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 305661789 1250 305660539 305660549
    0x3072a1214090a090c0e030607080c0a030b1002060915060a0b0a030f0903050c070603090f060b011b080409050f09280602040f06170f150a050409110103110a080406090309 75
    0x204000020071303070701d20542140740c11500a80d206035406920008044c0e441b1001d0b162103001c20342010104103081a803400500380741000d4103001c1101e41c1154080342c12407909040341c00c0141c01010030310401040621000040000c0da1202c0201f80c108400090406010743c032460350b03110b000140d01d0032418000d41242d8404045c0f540c007001010694240a00180d1100c0070807140d6001e402c10110b40180a0300ca04580075420984803c20355290ba070320400104a550328080c188840350348a801a0300740300b050b00744c44500c1003614a403a545014500c03c29a480070381001030821a070313020482100d40010b508040654070300c034108140c400358621f44080e0352034075802070055800010041103088420121608940a640d14200c0980103a50500c90018044d243c0c1d13200041100f000c0307910b8003aa40b55138083c0c0310f0002d120000b9075587d000010201c2d10100c0c0700300e826860305c00e9081520360b05072107564050808001007a2410710800002005000c00070001400d0030b07502d10599041c10300c030b801041c001c0c203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 305663039 1250 305661789 305661799
    0x6090803070c0201120e0705041a031b040609090203101e0e0a0b0601030c0c0b0402180405060f093903010c0c060c0e060316030e0303072a121409 64
    0x41440000141070410b0703034070264041101c801c088119104103103d0f078100308044401600016007850108009440500345401c40150301d690f0f03c074a44d1b5000d1180c03101502d0540344050710f20000790140416980340e035002204285c580b1280340d015807000714800b03c2142c1d03500740002c0c507900a40c4000c25483e030600c60041d0700900c2d120380284000750018512140300d0081241000650303500d030046090710400000c05000800c0c4140400003d507074185030726006403006161198504aa00c8510802c031303000c44080d111584100c0621003000c46900511382c12184c0d04010b004c0e0900001c1d50340188075500c8410602e600182c61000ca464844100e5012031110010f0091090080582004201400094007501d100c0c0c582000d0f8100180920303010010408080c02550031652099014040810088000001c8c584c80342c40c10046c2c0c480901c004c2d8481c4940e42c892103000303001400c42e8002070440721408080c1c1d1904440900204050400038000d0401c0c0385042c244030940840c2580311405803110341c43d089 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 305664289 1250 305663039 305663041
    0xa090c0609050a080102030c041703040909060902041b0503060f030a1203090516060e011202070c08070f050d1127014121030414101d06030406090803 66
    0xc2a8040241000c5541c00c0f00c0c000e54181e1290700342401c0303200965503141c1c03a61041200b003000207110240f000b1f00c480020203490409aa030840802036803001501140c035540d0f2100e540302180703014441c00092034a10030812075001d4003404003424620010388054401c85403500e46844c3e40d5020071075000ca032540407078201c0c0610301180014000c2c0403446022503960242d000201000614901c84e40211400e695450010f030110800640d40d0a00103c1c43c586070640070418503010544449225009081c440c0040007503620740000510125903c1d001213200311010001e42000c038450b410ba0072403c00d07085800d010a1800080c0700c001c6120003290b02ca01181c01c5000025920124941c0b91070103601d011100c0a00307880c1c8030031128481f204180e0700d075072003407101040040340e04040c90b0018041130180144204c0c050b980f40e141d480c60b081540708000000040c80903044038240051682c6906210b4240f091100707110031414010b0a204401d0140100400301c0000d060003220381000c0c0001d500108010342d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 305665539 1250 305664289 305664299
    0x4090503070b0f011205060109050c0f3106050d02030a09140c0a15081602010b060d0e1510030f030e0405010602010507170702100b1f0203041d07170a090c 68
    0xd80c0d0b8100e41406080c1501400000d00c1040c410341d10f84440e44c844081c001580c2403200301d60083c0070260030b031220040300f4468030508001200c020449003091402c49030a00d84080c400507914030b2100c1c0425807403003080078100001508102034651240540d040540c682d0ba40c0000c900007003030481030190414018a011400c20f00e00841ca07683d05820549074500c4054a80918580000304c081c9100c000481d0755000541d0b155069150284139480c1d0b20010428070203860000c0e000b0740001c0050019156100b04041d19507604201c940e0400104000c1e00f907061520700c4908881506611000d01a01605050681014800d03204044c0341e0784010020807495840c0d103002402003404848001c04140e8409000c24244425440c45100d40000d0340208a294200d141c3c44c0c01401d4103155044e00103038104000440c030b0344415150a00d1003a16401035031035518006500a601080b140c443d007000f0001828011540e80c0685c50020f600380342d2071164103d0f21495074501c003d100784840030380801c43c41100231407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 305666789 1250 305665539 305665553
    0x7170a0606170105090706080601080a090c150e0a03050a12030204050a0e04020f041a2106040b061c030c12180806150303030105090402010c0503071502040f09021204020f0409050307 80
    0x1c1d840301404000c2084d60381d00c480c4640d0311501406104013251041c0c000885561282204642c8004994408100f00134180d440d6140038500340c12030b9150390110024809002e9005110b6a1002c0040320b02c04034881c61511080e8880c10400c101420303121040d4040c524460094040b1401030a01078004100c00350313a12040d940b0304405032400c80c03203540e0744241d4099610f03150107507100d4060071000307208000f80c2c1c00342040301c000c0501030301d040da644600e0b000d07011404080c803416110320700a0304a025940703807990420008942000c41010300c40748001c44c200c003007a03020f4606080c0c640c0c044005100c3c0c0850380c4d416036510300d20103540d030101314200c4808500c014002c104c43d030140c4610b26040e8009107000c0c0401d40c50340400d018940d040034010000501542c4501a04c407030650060040c0d901d06400c0d51600000100b66109a114142d000181002508081d0803848010010150110b05140484600480c03141004d0300c047e10070401143c0f04c2d81942c0c0c0d20f80c4003000c1e00781d100b012a0340c1c4040c5403810134 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 305668039 1250 305666789 305666819
    0x60f1106041109011509180e1b040c020a080f0f07050f07180b06031504150303031a1f140d1401380c010219080406050a0e07170a0606 59
    0x160041148400020f171011085056411414540d11000f03c01800c04a11210f80340da100320a41c4269219100b80c3c0000c00c0034007622501c045484c0c2041c00080440c000d1000303940015180e0401c41d030201c40c407840454040300985019140030100582d07100d000c82040005400356000203401805803c20034240100b000580308112084911a0303130488c28100e4010702103a0000c001c141c3c2185d0104001403864241d01d0340b86005210041c0009a00c041c10481e001249001d90000c6003c00e56502c0c01c0303081d409402c00701a406240481c4d4240d0402d010403e003440c0170f090451450144522521034240b00c2c1c0c0320209845d049001000300308500882400344071080344081c0b1880303101c030310305000742441d2070304100100d07507031b1140c0c812003181100292001401c0ea601484504213103560030710001c0c00c032001d05407640c0c90300d016607982c460785030070075040c030404031381c406820140e2191504614041000b004903400c0202d40d51041c010760ba805030300c03907090b04180b0344030300c01007449103002d07800f0400c0c050005d0341c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 305669289 1250 305668039 305668073
    0x31e0302060108030a170c1605150a021614070e0709050a0503010212010e04031419031a01020c2205070819020a020c041a0a0b092701060f110604 64
    0x210020790f614140c032903d91240c8a50040010204410394061a54407240300d500174580d520380b5840c4c0f41c0c402c1c90315040c042c031790401250380ba00401e51801038809401041e0b41c00c00d03200c1d0002c5150098443e2800e2944407480c0000b0940e0540c40c03404458210280070300350041803000200801c1c0e00d800702005102e4100350007030501c9290f1088010940e4241482512010002006d030200c940c0d00b8a9040c2031f0340500144218104000483d0f80483d0711010390181c10743c7c4c0110040701002c0d0004100c06025901c07038a00503151300c2500301c8490506c0c0e07400202003400c100305550005003240503090280001015480c41d0511900745401c1c0300e84c2c590300046140c8101915407854034042015500c0300240d108403095030380168002da0030a2001d2a0a17481175250340340081d1110301508032000450311218180e0301800c4034401c04204103c180c05c0c07100c3c01c440200e81401312004002d000c0c070262108034406014440c2008501c8211a00d49402a807480c0e6041c4084011619589080d15161200108103002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 305670539 1250 305669289 305669293
    0xb04060609140c03070e0a0b0408030d0c0503060f010e010309050a050c1009180b010528110a03050313080702191a09030309011220040e0f01030203030307030b0406031e0302 76
    0x41200c002d5814903514042d1030310b003500030300d1074a82c001c0c11146104048842940901d15580002d24107980f080204014600c0d24043c43c4c86600c0e40c4440400c42d00410540c0d02071010800801010781c1c2c9441c1042c4039a002424a00085804540100c00800c403503003005040348502c056032800d03c00c0c0020f404501c1d03607045031401840000703030b4011100415103100c3c0c0f507004484804402100011600940e6400c4070615000781040700d180c6101c07a0080d0070000c11442c500070201c000c1d03400743e0301280391205480340c00d0007403400c0e8000c0d46d030040c10751000400c454614031140480c03074200002d60b400c0f42e0180350020081000020700c030315004154502c038480c00c007800e141d100140c503034004413005484008070014040c5007000394420054900409008101c05d00ea96500c0c104280c2100184680700d2800e40415040d443e982030154644d0200c03406007400600300f19030401000107a90000840b0390000c0d1516020030304003030304030124001e405190401810000080005081711991803481c034642c50080c3c0c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 305671789 1250 305670539 305670551
    0x6030501090b0106020c0108150d02040516021c0504120204090503070812060d030c020904051005070f030b0a0f030215070206030a09120c020a0b210903070c0f06051c090b04060609 79
    0x3809a80d6034001e00c1b0001d01044220000a403107015040c00645d0344400585510b03004081c42d40040e045480032101d0071900c00d500c45420002a81c100b10340b1000c641c003c10f088501c2d000c0308502030142e0003144a80640b800d00d6801140454860b60810900c499201007101c1d01c8490518100e0a907410441d1240c45003c0c108001030000d03d01300c403002a4050b0161940b50259146070240940381d40010800d48203842248100da07a004080e20403207105508664403c2c2102a001a00030b007a42c3c490000c4601c134200c00c031418004190350082000480c1c2d4100c131900d1f20029810281503150141a2010398020b00210030040d042c801030b00b01d0064a44194440c4803070504400c01a501e220a4000182d0801041c1d00b0902c1076074980001000d039034122050001481d02c1c035482500c40900e0458240c607460b00045500400c1103c0e002200000d4081001000149414840024000d00400c1641c41d100212810035804c030100d254030942d1b0349034004480588614050400034041d00c2c5910802c0c48680c80c1031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 305673039 1250 305671789 305671799
    0x504150e0c0306090711250807060309120f090806160e030105040b01172a0114030f160309050307231902041a0303040938010c06020d06030501090b01 66
    0x207084a229610007400c0303080f41e454202080b036481d11641d001d101640b09210f26a03640462441901c070359240f0410f8010805400c1c2000c1608110b01c82d8407240500d410705142100060069000e01542d600b039141c142212404400101c8401d22180d12040860050710103000318103407824010180056a500c600c102303414140d050600300c0f0400c84000d04440c050400500218555050f03072984801c00c0b4080300e105c583c2000c501c08400055400c10f41e0400d219003016051560409100304090340c4800a6904515003180381d48e4009000078000b98a06103400040208503009505c106081034001013181d850b90024500035821107041d11084602204d500110010f07580c0008070604c1c04900c01d681c0c03040c1c40743c040d4244005000d10f042a5001d41600d401c807081c054904102410042c11a84804612440c8101c0c070b00800704040301e5400d42d440d145500052000d00c1c1d00742040071517042882d2034606200c103810000002e0180c14805c213802d9041034000400d004054004041c042e00524894940d43da0324 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 305674289 1250 305673039 305673061
    0x1203090313060f0c03080a06050a0f05040c03020301030b13170d020c011a0604060507060605060f0307091509051003060810020c0c0d0b1803040b030c030a0510030305030c130504150e 80
    0x200c0d1003100059a10b50760130b0002803180904070340045210b0b001048154440001841204660b0400b010340c0004400820651415020b14421140c881c10704500d11750454645841003a00101a000c0001c1014007160400c08404040e200201c442c0d40d5941c0c40e0314000081a01950040c50a04265800d00410300c86101c07405481c0003e00c003000740514a014074000007581d0603003100f0030964900ea40c8140002c0d0540f2503000510036601c50b400c0c41907580c500490702400e0352490ba08038180500d14aa80d615030350f6007159141c015600d0440304444480c0070258114054152038020b84094022140103640c2c0da0182d8010300114034107030007a950b1602d44881880a12804600c1c050030300106a0080b078012509500700403080c15100041c2c1e4507042d1618035800d005d074800e40302d900c10190000200b2010743e280d0f10800ea04402242e03d60400181b8540b8024420300018160960f0000009984510b54075240450b00c020580030303005100b42490b885620110111a104e10700ca10110f000000c2d40d95055 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 305675539 1250 305674289 305674307
    0x51201050108031e0d0507020a0b10080a020405041407060203091e09010b3105120613021011060a020c06100612110708030a05061203070c0e09120309031306 69
    0x1000c0045050a1041201e0b403130009206138a42549581084824100d90046c00740d94030803d8a0f030020071400145203000800e43c0402803d070544000d02901c01d203d03180011810300c00b010b4045070042940c0e211400c082e10210001c3c000c00e03102c3d11030310000180c3c01ea00400600315010702143d4800c00e1145000900754218007654419a10404010041c404007008001502003090240c0c1c4001c1c000e460142035800c6001140700340039802c607048201b0480d03468010f5080199885003000761009080010485044908400d4000d00c96001034005ea28a00c0c460410381682c02c02100c11500c641c00c0202c0c80100950003009100d22600a42000450f0003140c000c101044881903a6031024200108020900403d0074141d0038924410800c0351402041d2640080c5000e41030b20140082c1c00e045c60020000e00703400849811040750410700008022a042c410301008071004e1400d9645a60340700c1e49401e08112404207240c03006400801409120080000908444c150580000c040b803900d6080503140c03520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 305676789 1250 305675539 305675549
    0x303140f04291f081225120c020411120f010501030903020a0f1a0405030c0f1609020c010b03010203130c05010203090604140118060c0b13020d0b07020f03130512010501 74
    0x501000030034101a056400f0b6070101855568030450140c43d04115030a02c440c0002d00803800501180c0c211b02044d6110041c691090080340141165081745d441c0782e01320b84028004d02c10308c050480d030401591a03540115900079101e003a000d42d5003291078444001d00005466000401520400200b8154068400c0c0c104041c0c143d0014180f0503580ea58140c11a8030070b001c121440d1900800001117003880300d0b20240030301d1040001e0758541524444403850100601c8516103c0d5204104612103000d815501e201a40c805490140e524030095070060f001d440b00c0c5602c16055840001045189804850705841580c0b148003501d14242c1e4075401243e0340d00490100340d5100038100801c003c4c210803584800300404060520303491108401c00c18940d2b62200d54400c0300801c58202c01d0300108440b21114a601c0903250505103410709854000c02c0f00e000400d20020300e6080c03440301080a99000b00960121428620210b075500e0f2030b002d060b10402c0790702d80b1400340501c450000a140c69501030142905841d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 305678039 1250 305676789 305676863
    0x308100303093f0506150a090c020c0a03061b1e120b12060901060608040503090108040c0e19060602010b0915010c05011a1c0309060305040303140f04 66
    0x1420000c40d1400f0001100c0d04a8118801140707581c0f00102c03c190303000c03a01c10514002c00140400342003050030680c0041050300591120040e00300c0b1039641034580d005695400b00000f500302c000c0c41e026450300c0792101200386e01c0380480b0400410464260000800e08228104c0213074028228901520240303030f1174100900c0b803c0b03e40054a48188201038040460100740c0000c2450600c43c2c0c0454043c50311804131400540140742084404d950034025080200014940010700785481d860f09600d07800351000c0c0301d0401c10880d0124007848035504540d006090740742a4500241060710000650700314000420071f4136800d00400148017030041c07080c9034000700060440d198075030747c000c1c00504031400c81640505010341c844404020a90901c00d01c10881804c0c8126840410b00c03404010320780f110040d145c80e01204020311100000d5003c1420f001716603560501040e0354846284c1a009030600700320038400104a00208180340904094240c081c901a40050031001c5407002c01c0d0005101d1344182c12410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 305679289 1250 305678039 305678057
    0xf07060810030b04080712030504030815030a0212011104060507330b030f0313030b160c14070306090308070e2430011802070c06031e060801090308100303 68
    0x714640300038040e4001d1140010606d0030f00c143d9100404549450704001c006540e0b1000c000805810490f043c0c0c120450030000001064524000381e41d44480359802801061407c2583d10413120035000300c180000303604880e0703440700e80340c100081c050f401185056509403111110040081ea00c121840c00c098120384c80d4401500450090030054400006020703090711464550340072081090000c1c082411400c400f40241c2d0707140d030402c0151580301400c8021000c510000b1640c0c4241c02c00f0900c0601b0794099103c40345044000c0303456041c1040d56002400060911190324101580300182510894042d02c85000440348001800303c0103005111415a2144080038a04003482110280200c000c60005101c0e941c403142c0589001c1c080b042031a000c9400c80e8500500481c10b102c4038000c2c44104e290011801c0004589501441c90310301c5c491101416079441800c481e80121031040030070b90b44811401e000a555640400d030080c0409002500022800d034081000c125521040b48201ea4041d40c0340c200c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 305680539 1250 305679289 305679293
    0x80a17060a050d170a110c0301050f070c060b0a0906061e200102070213020a120c020c010c02060d0c050306040f02091513080706031e0203060328050f0f0706081003 72
    0x8941003002d42984c2a0892800b0301d0b4042400c0300c010302c20001540d0ba0030001d81a682d0301c4514001003805203134440d905000402503a4401d070100340340d0292503490940398480403800c060b0010120529580c2c4c0240d1170141c00724882d051038002d00304032140303641c9100c0e500140c0d414034009031f0b114a0740076000400c0100c1c00d41050560020b03440301081c01c10001440c3c220350354001500e0402c041141c21446401080c1d80104c250000b6010510346040342d4144040c002d00c01c8025200d6140c00e14460500000304101d00641d00d8000940301c50460380e550800464a0150f009003442d0021995a8448c601b41840c41820403410300a9a80b850030181101c9003040d12a580348285400c036604000240e202c0b04800501311004002d20802440f2544001950390083c1c0001c404880140c900d190381c281c0100140100b0351800114036074180500d41841564040348001c1881082002c000a00244603400400320614004540c101d2648003a208032202d00c0d60b1602c044e2054a0115403602d41d1040000013040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 305681789 1250 305680539 305680549
    0x7170906060904030305100f080a05010e070b09040c09030b04050609061e04080d022b060b0403110d05030906130807090509070b0d060906030b0604050604020f040915090504080a17060a05 82
    0x1401080030b288030340f0560340b0740410352400c8c0c466604c400c0003544100030720001d010017031045a44000d010006086150f007008103010061284884090045941d03140744840940b183d01407201650f405001c4a60342d003003c0c20700a980e45020b64000856004070404070b08445095540c0008000d007c03003c4109a69554444a1154118580d6000071035020002c1040c0c0c0f40b0b0721160b00d00781c444001c00081c1080f40040741542110a5500001441c040c100018008241000800181d880080302d1810640085240c0b450075802010317840741e04198003040d107404408211107100c2c252a821400c0f00c034040e40c1d0310400d40c10384034181d40d004020f800003e0144020001d0718000c0c614414011804502d0ad69180300503821501140d10640f00a4440000c0c17100d83d240ca17001d01030708144c040300e00f94202141009403816500c05c03803017095000740d6110901580e82107101c80c0701e4000d01c0801820802480c003070a21280c1984a150b11600180c407440440305100c02c02d5084030300070354010706029161810001402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 305683039 1250 305681789 305681791
    0x11d090d0f0305040c050a03030f020f0102090f090730050f0c12040302030f0d0203150a0f05061606090b01051201090f020f0d140729070b130b07170906060904030305 73
    0xf490f0004d03110313000304154403048a00b1002314402c0e903840200ca0b5002100900740f81550002070581e0b40100030407a0760741d90342010070481e01c01c00c0300d8482c0f03251262171003035030b00300c54864a1015505941e00007501c510f410803e10008440c40800500082e0740d00da107151440390302100c003040da002d4140811a0201100c150441c0d009100340122031800c04150302d0303210140c100c18040d04080e5000810002800d00b007007103030808000c0640c0c034289040d00301400a2162481801464040c00000c55081d081031000180002c019800c51000c0001159504007042403a10034001c03503014158020106503c90014480c5000041e004000f00d64004050350030030605100440d0110391088480403d00c001c152440d5031001c2c04110800104040c515140c00304120200305140d800c0d240544403028641c201d0100e0407200016408660b4408680d2120180d207000c1000480140034189030804105440741c1218458038480c140e540d480d0029a104081541e0f90701085840e1500505071101003000240240c100e5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 305684289 1250 305683039 305683043
    0x150406020c0d0c150902151c060b03040302062412060703060611031801170a05060a0503031c0240090203040f0609050309100507020901081516050f03011d090d0f030504 74
    0x121f10914003280d900f00d1035042224500c42c00ba06800040080745030034410701005000e581c001c5821481d1030789001e0748609000302940d002501800c03810030b195180d41e801c0040c2e560000c1003c0c401c40306004e640c541c0d075441182d070080401e00c0c007500880c3d42e1740240c024401c10203041c0021460090782d00d4108011082c0b007240784d8144980e00301c0300c510140388030207a244620904480001c6519058007001034810203039200902039081008290500792440b28a803e0b0502003d801596403001c00800c005841c0015008545560b0560149621001e2012007641c0e480002540b500c0b03480d032550345410403440b083c1c0f8028507104000c0e09950005036550030000c8100e02900980e410448130001051851003035441c2040000c40c0010400110310b010f001160140c00904000e00413602c80d02c10785000c11102802000c2d2b090555180c1101c054468400c55481d030501e8000c003912540c0d43d00b01907603600000780b04201081c00c028001014030200151541c2240410341d504034900b40e0384c40c0305038002e01d40a070003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 305685539 1250 305684289 305684299
    0xf0611070905090606150a021504051005090d02070f050604090c0c0c08030408060a060302010f1215171b010906030b0f0619080f011a0c150406020c0d0c150902 70
    0x4006040c0207184645442001e030480601043d00d01382d010040d0240d066000c011181d10107100754100c1c03541c0014001c0c070030a40c0e007403031440a0b02c0c2c505005191442005c4041040c5040c04108240d90314081480e85903807100d502150303103180d00ca80c0c81c03459a45a900425800600500c42041a180d41da004010408010b080440c0418066152a0406034041c1c01a44042c0d00c005005c0241b804100f00c62503000406881c10004036007951b000804250341e407500a020400700c2c0c0f1a4002418450344203506003410307015655001641d4003828000198012411b041c18081c019206e65400107014902540c41380503503c2c0d0746ca0354140a4182c00a05800b06003e4118504002001880d00e41c0d0000302040343d60001401c00d17107038503d98001c2c02c1d688010417031f041c0c000d1030a00410064a0703215448111882151000741c8038682e1035400747c44c000051400d030584e194400240014802158002c0413044644401d0322000d0020103816100200385800050542441c0b00c10725140150716801011540d20081c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 305686789 1250 305685539 305685553
    0x1507030b0a0605041e120803091c03050601111b06160c0b030a2004030201031d01230907180e0c060d0e06060f0105031317070f05010c02070f0611 64
    0x420100384240d003000003c101c1c005014011032200c41420740701d0943d00701c8401c107024100780d0380c0d4204602c5900000c20202000c800300302c03040d40602000e80041b442c040341a10702c803080c580040240c042030351150301086860400346282c10010070004030203100c0d00d070782c80b0f0022503100901100d07078840e80511801803a01428540060142d0341c10382d008004101c9099101d00b007121b00c2c41e040310004c040c900550142c40101c0080c010502d02982e00700c94090070000f41000d00414480a42d880c0240210220b51a150708503005403202c149403081180e0782c0082c001d5654a0305002d5584841a01501e0080c00041c1881603191213581c00a80c0f12072255001e6849150383c9a01040c410380201000b0b2206c2d648a00c0034170f40c00d19040200550001040b0780c1c520b14003d00c000081c0140c80083e00d94003400d07101800c02001e00c00103860300d040b1480005642e41e55801d440c01d16010300043e140e42142c10f5401c01c12084030043c80003c2070b4003503942c4840c0c09031a051410328144d50400f4006101300709801546 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 305688039 1250 305686789 305686811
    0x3020c06040305060a050601030b150a0905040603050a060e031318020f040806090c01090e0a020d0e0304080a02040e0d091211030601060302040303110607091205031204050a030f11150703 82
    0x84081d000462144000b0029801e001203180c003035810050045e4101454481c0c48003081d40c0740c410b440200300e88039007000c0d07aa07119103004032181ea0140c1c120b5500242443c1c030000c100b010000300a0102c50040c3d1003003100808a0700349a07124401d801141c000c11250724014011040803506200280e801c0103001880c06c86141001c070416001980240d03020f41000b41008002c031418007445604d60790918000842c2418041c076841c100102904104002d40d010aa000500ca0164030a01031400898201c0b51520f55804003281d8840049070200d00643c00c00881c0320b03142e00001280c413056a015240c48441c18240003030f100d0100200c10303054603c1c010285072408951410b221150191040b0742c0c015a5450660030080e11443d00106e50001550094040050716607220800f907050390714205035040e0080c0e4038200203107176001c0c800800c0c4030107030b6880070300041100002d446084107201c1d850f90007140340f40c21401d46641541e00341d02062500429074500300c1080b011f4000750310929034200011a04a65 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 305689289 1250 305688039 305688049
    0x31b0c0a030c05010f1803030c0b0a0c17060d020301090501021e07050a02010534020103111309020a050408070b1201050a0303080712060806043002030f0702061b0d0807080403020309090403020c 85
    0x10303030300a0340030270720206d1500140242c05410a61004c205070080c04035007031001c4018000040f401711a002038900e0000b043c00307551901d00380c00460b50024001d0001e40818180346000758006000703001040300a40c9208404502c401c02d603200c154002015040d529141d400540701c80e48200f8009004010110340603003400300a03010308984294110b5070012000b80f610000d07044802d081c00d100480c0e00c09111403170f1402000d00701e0505561180d1800343c0c81d4201d888066840d8040c641005070103016911004c94591142c0c009080b01080886074401c007a641d0b40c06001c035081107404083c001031116000100042d005050b1404500320781e00d4009509581c800c4450f05000c0c3c1550300303e41540e0242c0031811011190058402c07030b05503082030048081075040d0301a41e00c1c410400300b8000e901000c1481d40941d80c2d0340d816540220381500a08d080e00c10310a2015489042c0410701390b0214400002140d0107610688181f84502d51540045190202e01001c1000120700100118210700c034000105034552a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 305690539 1250 305689289 305689337
    0x180917030901020301090f09120c0804080106080309040c0e0d08090d150b030c010e060405120c04051303021501060c060506120d020c040b191511031b0c0a030c05010f 73
    0x1281c000140c4030350500f21418265210480702440090078400c4203008211100c07584d0800104501f08001ca404031441c0c242d20710f018683c0190f030554130b045400951810048010036105004480411098041d10400d80c0c5d11707800c60f41030756007000c0c2004d282e90000d01000001d20740c0d584010321505403204203075100e0041c42e0140d042d09070b495864500165090034100442500c0d5507003401c0c00e02820301e691003c9034180c0243e10842744100180b60072100280d00901c9525581e03034002d0014003c130719126501140031104400120700622071840c015810300f100e6480c09060b00c190366100840c0003100c0d100d10000d000041c00c03290384001000d800c0c8100781000c01000faa010350075000340034084c0c241c03030800c0111844010201d000d084410b158a285074003505121040d2000c04e2180200400d400e0012a003c1c040711285a03200c0c800068590500f26100c0007202c0c030004200100d900b156248010310402c81351520004080113030f260b40500556000303410f050f012280d185001007106440350408a100a2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 305691789 1250 305690539 305690551
    0x3010609020a030e15070c030309060617070b030603070302040228091503020c062706011e0b0711060d14100e0606070803040204090201091d01061818091703 69
    0x103070001d402c0c941240c16010b4840d0b0034580300c0141c0407071151904540030b00c05001740342c20108490260102c04060103540b068005c150400c104218032a100c42c109680c46103102c2e54008244224900000c004003083c0c1102e21528018000d0000185103a09000c080e4205505400311504085d0300511030071901680540e00c0c4003195180480c04e4604440001c0c0352000d983c46d070040600401c504440c007200015606c1c2c010410000d00714440d003006051108416000140983d24020b1500008500000344003240c5461112442d15140320b40c1c03000300c1c01d4248280d0000610300c0c4607030906c1404510b401d00c0a44607a8103030550106038007495035802e0740e5070042140c0d143c442c904025014040000c4401c2d1040c1d1042050b00c8642c51708005480d18903c500005100a00c195122503524045901c036214450041c0703840708071001a81c0407595a11010030090040c0000a4000c1100d6001c0f01e52060700780040f1204010141040303059041100042d1a5104060711108102c09070348500d502c80400844c4560 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 305693039 1250 305691789 305691791
    0xf1503030a020a15090614010609080102090108040f0807050d050903011d0d0c050c150705013c020f0d0b010815011d19030302030301031a1b03060d0803090a051e0d11070503010609 79
    0x160504500ae40f0a4120350411001c2d81c1c0f0501003c50319980181c0c980380c005e40c2241c840a5101014540f60280f03104201005009000381000d500d01b0b103800c280270700b040007012002031003030f40302a006001c2c10415214203851b66520050041041c24018801520b005001d02c080e114550481c0007c90212201054050b1542c440010304005001082c03041d022000c00d85600081021f072503421866a0620920100a001030500d10781c14110032207a044803800f100c5180300c0c0d03880d1051030402a0082c404220340d0744c00705582400042e104a1903105071240743d07005844190b400b091034800702054803043d00c0a950800d065101340303030400000c0084400194840c0d80115580d44c11861f050881516820010a05108200c2808881000b5892441c1c0c440e03218103607291070b80e80b00d4000411000008078042e00c2c1010000c20b110031544040b0b49040342600910450f00b078203051804040f840c03003182c5605041c3d50000202200c666204840c2ca0b104505442d08490151b5102c070006421a01e1a0748007190785 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 305694289 1250 305693039 305693041
    0xc0915030b0115020322120609020405090c1012111911070f030803091509010506102c0d060f0c080112050c010305071101050f1503030a020a15090614 66
    0x70140300407150260481d0070a00918498040c070180d0780e4096141c00800c0245195560345680c00040c1c100c400503c4014821b84050742d00f41450743c0101301c0d04505038001ca040c00c000982203100000d003860300b00000303088102641d104460031202a01c2140ca400903258950700d001c58814402030290070480300346035068030341c4403c04401070b00d6004070b1001200b0507040b02400b00f10061051409030212034211241590300e81c0d8241d455030920180c203914030007400b250400c0c0411420158003162080209403015000c440003200c0c1600d003301c80c80511030700030b400030040c0c121101e00a01c4192100c280540700a00b4940396958110035501030840b5082c90070b6492010018136a441003100c0d004184c0b900008400d010152a840d03203d0000d070281505054440000c245003600c0b91a0700ca0a000c0603900030061410006d00c015205e0900b941e0341c58107980920035010032460701008840300071101350020000c1415030b079904007142d424000c20040c40381d6251400c030042180e03401030038a100e4400100d4111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 305695539 1250 305694289 305694293
    0x309041409060f0114090c1902071e050609130915090209010e0106080a050c1c0905070902090603011a07140c10030e030a1803060e0607140f040308070c091503 70
    0x180400003481c0e8900108050300400c004044ca802a8402c40016652401d1658a1032460819072241b52554070a400403400c64400941d40441c800d400c0e1810001080c4030240c0b220780384c41d0301540c2f030701036503071b00460400a40d00d0a141245040c8802401200049000e00282d00c940c03c1035642d0004420300b090711183e880c0b08515101c0c60090260840796618162541094001000154000c054544455950002c02c0402d08154151840c03545003c000b030342072098000244c000f511181104451911506001181400d1030b03000b641c1d00240003030300060440c2e1910000440c075840e0840d000981e260300b04581004655034000c1e058400d10a0001003c2c04440402402844058090702c00101490045062801c02000c03084075080540c2d403804080c40052050319911061140e0700042c00f861501341494030114002c5880e40c46801c06865003a04140103040c2000d003271040c441d0304550928100000e00005080c0d0740540800d40c0528481d12a15440741c0804088841107000000b0282c208401001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 305696789 1250 305695539 305695543
    0x10c1103060c030f07021c0c02030c060c0a0302010501080604030e0d06020904091a060405090c0409020a1701050115031803030207110d11030d05041d07020a17071a1501110309041409 80
    0x50000d045d44010701d00b02000c0300120150205840c8030104004150307032205e040d50f8080180d00300d11a0010040d5649043e2010a99640c004042044001d07508050001030780349004a0500d20507034254480380c1d240a0100100440a60191000c440030740d800c1c8811500d0352214401c9554181c480ca03100c801da135040201446104000900d128411418441045a50540481c0e46031001c40700b91000308280b0100c0c030004240c0f80c0d01e5080900c030403030700c442111802e98054004504903518030b0035600005500040c100c0030348840700220803996203815025400644070341d00031f001c0300b070040c00c3c29113082c0c403201d00003080422201c0c02941d20688041400750246400d0040c01e508a441c0d04001c0d01d424540603912020301144040c014107804920001021180240248180154070820850102440140c1241a03421140b41910202100a2a000341c4403580300100e015000108401c2c0c4009009801115040c0c003074001e0b150540001c0c40313580029201c90040011844e000d00d10760241d0304e49520494 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 305698039 1250 305696789 305696791
    0x2205040c061e120e0102091504031704151803060c020709060504021303020409030c0f0f0c1d0f07020304080a0309051215040b10030c030b1e1005010c1103060c030f 72
    0x1c8444480e101e28500169044908600100c0f40d840b8040b84084a480f84103009002d03403080d040d04200e124040d1060180b009000384192071142555200020361150320300701500450044101c5100211141408103004180c4d43d01c621061018014580341c40303a0313459054815441c050303409640260400e01c075078031321405080e02401043e2811800c0c0708102d04410506101c521011303015076030704d110b0201031500c1181c62400881d0031039070144144d61249046c20a4025200051721450045034000c280710400b503850f40001146082007611640321840c0035100080007510080039480100400a071000d0f00f8001050078a0094413410142440c200500000700700f450070454a5400c42c0c00c102410002c00680d01d500150000e2408011350b941d0043c4070402603d039080074240300200300d00001080b00b801c54551042d4410170000c1e1a06481940300355a6110640e01000302d000d40010034001c55200e030180e0551240074082c042c4000d9004030100b801c103081079402c55a1044000108040c1c0c0708a04652 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 305699289 1250 305698039 305698067
    0x90207050706022806090602221d220213020406030e010908121021050f2a0109150e01090806092d01061e06030b0f2205040c06 56
    0x500041180811225001c004d0003199902141c0668403920178071003103500817103407154484001c40d0f5504041500c81004911075125501c001c002010119038038081040d114100c81646d8000485501c0e0349403000120b246070540000c9200d00022002c015948500c081d003d034858081c00142d9076402d1000003019100c1c6920a418540c0c1040e040d000028401e80032111008000a40070507903846000000712070f01560390000c1803100c0d1505222010501181034041558031860403100d4034141c1c8400c0d03c1c2c0304c42c84c42284031a0440c40b4201500d0107540c1c501d007030a200c00145842940c090701c4200c400d080b40d40f10840c030000a40d125049003190358010412501908224004001f00d01e00000d069a80348030080d079900d40d44101c03044000c501c0c81f001740d44641359003508000340003141d12940c09600c00d401401c1d001410740c0c0070352400103216000c0d1003030052910300078100d00e8070080a50280b0000f41750b211300c20303451450607802c44195484688201401144244c02a03c038440c40c003840141000700384244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 305700539 1250 305699289 305699293
    0x1e0904060e0112030525050c010e0d020906060a03090b01031208010807030b0a0903030906141906030804050409020307080703080d150524130e01050306010605070f060509120409020705070602 84
    0x103000004000c840010f04652600e0025a2152500146001c0070b51101e15400c800c8041014a4104100801c14503a0000b00f82d94002044a0341c2042007000c64500c04041c0d0071010420120f00d070381c10700c0c030700a01103528142000f04201180750b50f4040300e00026403054483d801c1801d005514030798410030700c80c0105076000040488a0440d11822002600641165101136907107240100f014025001010b0050700000c00700130341059000c14052000085462586042c04284a091b6a95140c804e940641e90022062400d281c00d01040c407001b0103005000f42da05126200c0c000035414010814407000e14400c40c2210f44a01220300980241d8110b0b401c0c407515540703100010b01154075090454800221b14240c000700f001010b5440c00d603544038082e1445102034100310041101c1e02c103a14058102c1d90700768116000e507070b60384104507540d01030044000d100d60031003840351000c95090742005800c8907008003a00d04640841d801010240e1042e40040381143e00800d0440901c40240545c000804207400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 305701789 1250 305700539 305700541
    0x1060807050d05130602041e0519050d02121e0c0d1a04032304140409020a0b0f0c032b060e010b0c0f1b1212030a0b061e0904060e 57
    0x800903201d4050b154002c070005641d5800104c1c194134514103040e4490300a4001c55886441f12041000c88031170504100d400d00c80044001801d0516083c030210018110f403014020501302000c201400e200e0900036648401760704540903c594050020100b0001c80c54050842103080402c4103041540c80c10980303101d074108c64180d0020480790048642841806000c1c072660741c0c1c0d00d24003541c00c80c03e001440505e00415400007a00c68070f4201c020420b407401200c80c60445070800d800c100684400540c02900200d4a05041150300791107005484440c0400f04040d0804420b500e07410b103160050380341ea182000d458100d40d14440c1f9618030f030004d500140c2c42d052044ea802c1c40180c1d514800103220300e11039280001190b1404d10010710020864101c42016110400b21008402460b01c4403102000e201d0b0402c0f01c2c2e9002d4403078000038036600f0340c030f415102c81d030848d40c0350003241008280365803070a900800104100740c454110f055401903c80660141591507503008030a01084402e41c1e0051006810324030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 305703039 1250 305701789 305701801
    0x30b01120503040e130b010608010602070f1802031e0f0103065405060a060611420a0b06040812030a1d0a030314070f0315171005010608 60
    0x441103030f06480c400302603425540c80b4540d1803441c0d2000c211019014044400002c00c50300e071f120134581d04030380440d802c4409085e103801c1b240f01c20b08164459880c0303118000118100b500181d1b000303940d00c620207c119008011002a0088a01504031004414124600c005204100f814403403d5695201040124011260780141144200740040300340440c0e410f00c1c00c198007280c03498240881c200c03c2c0011800c501c26042c60280c2d95450256040c0c0001410001d020610380e104030001e0007400c1c408002040c088940d4050805c1403a9401c0360829020110a0031117804000864424011050844640243e2900c20442c00c01c840001011602ca02810081000050300004558441440c1c010601c0d5494944000c0100100b5440c0c100c0742181840d034001c04005503000c101c10326002d00989003809122803500502c200c03050101c0e943c5002c181d00601d140c00b014401d43c014004800200c0451601c90744583d040300d06480d5801519509174803802c0481c40c50300c018010b40340101440c0c00c00d07100a00b442 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 305704289 1250 305703039 305703043
    0x18130c05031311030712060c050a020706050702010207170303091b011d0303160f0c1d010308070c0f0b0a12050103082b0c09081504020603150609040204060504030b011205 75
    0x1411596285011016070418410400c81243c1c42010040440303079403507034941141108000526050703d090345040d040c0c00603140220211101d52030594007402425041007020740d0340da00300c403105904500c241c02012a159140100400448010100070b54881c43d0049003d8907040380085080e5485451a8105a03e6600b0401102804c6401c952909000f28208007181c071b90300401c580264004113032849a02805480018845040d018050607180b460300c46044401c0400303081c05a451319150705004101280b852030160030305901c156102c0c080240d45001d90351808046810030000300314000b41d02c41c401ea0700401004580fa002c41e10070320681d89540c44044640c0074034ae510701040c0300490400040d222400b4440c0c45505030f8207408011080c0c44a200070041211401819003610494000c80791081e204450680b040354000c14a51841da035048500c800d410310405140e80004050001d4002c030741d56400504080d1017691303115915580386040c46418502c06070f00c10704040c481c00c50420301140300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 305705539 1250 305704289 305704291
    0x150f010212042913030201080f0c0d020c0f060c0901030c030501050f040b0a09060603050114030f0d0e0111060412090e0c040311150d0b0a0503031c150b18130c0503 72
    0x404410801c3c0f55030190350120b0b400540203203502580b40001101a0301c01040b591403400c1d44c0c001c0e41e50142c0d03030352001d19580c0c803841c06440030f0824400500c503690421201e50001d06aa410301d00035902c80e440c0541490b131a0080513181c401c0c8d800000f040744001d40d6030522421100c2101807078103009651410000ca0500305041a032640aa6151425040b0a0321404407101c01010402c4c000c00619a0360700b4010004c00d002c5c0143d540540180004940034a80050512500200c80c0041c0c138811140b09001d031007803542498284d06002415200c8002101c040c095244201d02500100107038854810340140200c804d43c000b4a2205e0401c014070503010109400d59050707951111030340e440b001a5400180401c1441c044100c070b0702500086083d51101785030400082103103340d6100c020a603d80040507100d008452103142002c0072543e0b000b401004641081c00401042000a002580c0ba020010383c1c03503111100c9003812108a8804501d5401e042202c425800c1a1102c04c006540100c2c60081180c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 305706789 1250 305705539 305705549
    0x50a180f050319091e08100506190806040b0a050f13210c02030111211305012f0406140315060a031406060405060403080d0212150f01021204 62
    0x2880005108010007041100c0e10000303104a030302210315244000a101c02c180c0d001d04401e0000c14541818920008049001503581046c05090310418039035008000345801800142d00c604069100302d0850440401e0b4409413031894040e0030307145050f0905458619010740311740489403030501000a0180c5506019400c41060740341d02e4585031960034a40c08007041428034091440c60482ea0110041c1c016001d01c0c000743c42500203200c9a1025480c070f01d60b5001d0b840043c00a040310594040c89604610f411560124801c01d281d00344000d6600d5140c00c55112a0180003004d49401e90588100c081c0e2a09240c00040303904c00620703041c03d000004151440c0704251301284400800481c60782070545601c4061800042d000c076450fa0800000280544110501c240190048401044981c101402164156900030b0070151400385107aa85440c0c0c5e911500f000c00740b0310740c280010760b246104914410301641040c95030f8280d00c010a420440250086007440341990301824480c08950180070075201125 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 305708039 1250 305706789 305706803
    0x105030303192306030f0d1e0207031505090613150b1f02010213051c030c051501080106030201030605030312060f010e060c071403030406020a0609030e100e010201050a18 75
    0xc0000d0450b00161629480200000184640061002c0024801503210f204100c040b00c1e0448250030210f078840f956050100c000804540088078010340d444210005e40c0c03080e10444042e00e07944e4a03a07003211940c000714003c10a41b100d09004420004200040c1c0022403550b003131603204980e0361500100507000c08000c2542d610750030050541c0d62144c440e84140201300d42503001e14004854001d000398001c14409c01900342000300800c2d48d042034160100c8541140c0c864040d01511a101a10b182c001c0344421651403140f101c546458070303c0e91007100d00801c1c0201c004100142135100240681d00d2030340103280294010b0090110f08514040590781000040d211a2420b03041400125807103180c0750310180c3c101000089103001c0000002e4407000311241c0b9407003040240c011204050300e074402c2d07210300d50040c1c1c0f05114a501141c141d60104407040d203e41081030120b4030b558040340b04500c5c0309140d0404035488001c03861541d40c0a0040581c0280c2d0840200104c8040048900107242c00c0d00002d8051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 305709289 1250 305708039 305708071
    0x3030406090c09050f060406080a080d09060e0d0905090105100c150b15030406051308041502161203030f0501050604031103101b0212030c090d0c0504020f070b010e0105030303 77
    0x8404602d418034080d06020070240010304c0d000b01c900964100c01e60304640120324212002801c01d2002c02c1c00d0080d503500070b80c140d141458940402000d450341020644605941e441c01c401050703402c100d0500c0f00c020139101d0080d07040c80d00c420040617240580c0001d0041c100c02101c684c1442d80012030040030380e44112100c00c0070358001250000ac0a02c4042e45401500340e180055442043c440518861480703120240919603890160000c40d0b811881c0042c20144180801c0c401c005000203584030130109071046a14489101e410480d04079015402400641c00919039481030580c180500c0c10403180d008000c1c400c80d490000800c00c6803041e4400a031000611044041c01584c0c140b00740200703203004400034407501c01024226440f110904040c20090b1042c083c04442040100007600c1c03007491901009820040c5420900480c45611202224094508030000c960f81d40c40b4070281050480c1c6100781c540b00c005c0ba103410b1a40c0362068011070301150740f0704d0040101c1e5600008403503000d03801012140b88 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 305710539 1250 305709289 305709293
    0x10b09010c0c0e100e0604060305120c150a090618050c0f0a0e040c0501170702071a090a0f0906060c0209040813081219030c02060402060c1f050a060608090303040609 73
    0x148280b203400540c5051800400c0c00043d80c142d80303000e030584000c400c207906180c4801c0200300450b01030303100040072a04004800780301020108041c1020422807401d503910442d0000c4210700842c401c07507141d1441c6135500c50000c01d0281e5441400500407407224180c00965a5480301940c848801d4002440748038140f8507042d480e2a040c1c010740042600814010321810a0b282580a1266a018182c0080c185c0403000907681051002a4064489074014041d490304129480024100066414a81160400c81d24241d6100c5004071801031181e0745140c4219030074200c0403c140c0328a6400b80e401c21840d22098405652250039054000c1d500c800000e40c1d40308003400f58900111030341c1c03244c1c4950144c0c2c3c443d60040d4150100500d40c41c000400d4000320b5040100043c0c085071004120070380143d004c0000240141004c9000300922042c20003211030030031b0508540340082501c0c0700359031102a201e10030301954224038020b92018120703030b00706508249402501c40340e40e80802130014004d181c0f103640307100c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 305711789 1250 305710539 305710553
    0xb0a0b130906090c02010e06072f0a0609030221030a02090d08040f050405070813030c081b0106030b06030d020d050304030509060f1206220f150e0403080a05010b09010c 74
    0x801000141c00c288429030752210000010401c51a1410255003400d011090712040810b08500c14001d40d01c0d426007642d5140c25040300b46900e1901d250a075820a80d50070480ca4041001c079610130b2146401003460041d0f46002410400b190000b40028000121058200c2070f02100b40c90b4020020240162141509800601d45079104130340a400180b000501044030038030380c500a0203a40d01940c06000d40c1d02d40840488004000300c40c2084a060010301e4480081c0c411500c00380036030b00a101050425048113011080c0c0340c840c1d140400f080c0c1d503620080081014114000343d020b0b0044024104040000d40c0107511603041e0952103042000010015007054000c4041e07416426010300400c0d03d52a540c00f074006aa402004c14200c00e02406000400c503181604080c0068801c983c44641c0d850000c50b0400301a00a0346c42429049d519818064100455080300038002c100e503000050450030181006054402d01601505480307003483c0050001084040880c2c203203520070300e00b01b0720707414041c18214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 305713039 1250 305711789 305711827
    0x301061b0c0f03140c010203091503060a0e0a06090b060c0303180f2a0a080d0f031112040b070503040b04021324080f1501060315030f0b070806040b0a0b 67
    0x82801c5544210110900c0035400031391241e060b4031411556203003004401a80d4034054804415800141d0942440e000380c01a005141c11134005801c120816450341c0540710b0b0540200c0303c51405035642d80c1300300203812540c050407002c1030059800b1480c000004007081d03180d00c8000c01240c00c0d5501d15604078030300341c03007009041100c6040b03c0941d0000d001c1e11801c44d5680c03640d06402c0c00e80b0120000000940e15052030b071007040703640000c01410020071000003034941d030850164101c14140d9880c5101003804070040140454003246010001519081c030b004020250301801003030412100344100000030b014000c5070780d04141c045944094001140355200c02401c40a01100081403507280860b450000e03001204041d02e1101055a280b017400e4124503984844c4080800c0448106000411403d80079500503000743d811a440e50320304580f2a15040200305280c941111186118801c10074036070fa20103d110341020702214240192081c1c040081e103102d54034011701d11001000501c409913182c0d000c07108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 305714289 1250 305713039 305713049
    0x1030f020f03071802071103160e0601020c0a030c05100c110112111b0601060f05040e0a150609051905010c020909010b190504061406030a11070804030b06150301061b0c 74
    0x1900d201841300c11200e01940011a0444044c0420f00c000050351402007181414001140902078503149042400c01e03262102401d800e065006d100361440d1141c444003404800340d07015010208407146401c00340a0500070003c41d0300104041542c090000030400c01e42c0c002070a20900e4480051440004407030004c242c04110818408000a842d6100001c0c920315040c0300c502d0345065070481d0781d86200555004200b201d8100002c2ca04001c24820080301c210342941184050600003908010b610718403007800415008200841c2c031442d400c200d40e1a02020400790b038500151410350142c603007000a0715414003220001d01c64440500083c240150941c80300c03030781e440c00400444002d4407a580d01d01c040704150142d50300079410590302060030703034207403000d400381c80400b0785011701e580d40d64038554005242103038000410040130002800459500380107000039501819285038903041900401024400780f9450600115050004001d103d40283c030410741c3c0c001d199a03958820b40c252401465000300754102c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 305715539 1250 305714289 305714309
    0x106020d171b1602090903030c090111030c01050117060105060f0403030e1f033207050f040305030d0c020120180f100507020108131203020d15080d02100501030f020f0307 75
    0x104010386150b01058401550003a1544112070700c031b2044940e101c0c0700840c0c41d900c40710380c20440c234000340d44242015100e865000d010b40b8180f1400c09082da09498081c0d204c0900945010f01800f031060051182c18014076048a210780350060102d610007003070050740b1014080c401c64040c101001e0b1169150103c0c0555103958a0101e5801c07608050000c14104481d503121017141350038000800e0b100d000003808905a03140b003e00580e0b800c581159541d0180c0807c80c10110203120000005804201601e00030203e00c0d07010610160001c1d00900710352280c1c040c00c20701c1c0003404000c1050100d490446490102c00d2040c820782d0589100440c040d500c14081c03851704210b44889030b008255001c0040c00019200360f07644910b5880d00d451511a505e214500035200f00c00c603980061030103010341d0091103444600600400e88a9440c0101c00a43c1e07260b61244000341c2190b00700443e4158144452071401062480801c83e95040d078036001001c1307088080c000c0c019070084d200c20300940d42c1008001c00801c0e5242d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 305716789 1250 305715539 305715547
    0x30b011b06050a140408070b130c080d080c0a08010b09060c030304050303040614070915032405040e030a021c17100f09020406121d0f01020c060106020d171b 69
    0x1070048010481100d01d1001a803070040c1e01071a2002211015002c0c5400c0140710303080041e280c40f52450003001420111a41104124120000d59440c0c0c0000c0201404030140c01200300301e11002d0001680103141c144450303820810460040d4001c10b01c3d42c151404200b44076126040d40d00070841603c518130314600d680c44080108810400000011071081e40305200511145250382035400e100c1a007611088040f0307540100510000300241e2310217400102500d004a00e00d4124a0701020145400c0401c0cac1104901140900c110304060040844a5440000451034600e038804000d40310207001030b00d0201110304960005009110701c106c102c00b01021400801d00b8141911100740030700031446019800000101e00180356196031084d00c040350b10640300c96982d403144c11001401061580714201d82040a64000320081d9000c01c00c080e0010700103000165178040440c0704c5498074505034803060031580400c200c008241c1d400200038103030740f8400e144124551110207140c0c64800c0c4090740700706181c81c042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 305718039 1250 305716789 305716793
    0x60f1d0616052815050a0609020403080304030f020609070e09030d0c05030108120406140304020a180c18050604170118030c12090609170c030a060e1b01090303030b011b 74
    0x1180b00b0000440a1505800032102403c0e20169000c54600240094250040141c0405105c0e000f1903070000c1049400100030781c480c08184201e800c150000e641c0d080c004800c000030160014035005440440c0d0000700030a00d00b1000071581c0f18031700e000e801c14240d03101011450102d002c100361035102032070b8072041c05081415039000300140c10910842c012071140d41440440c46011900701c400340c0e2066601c58401e0581a4005462540060310880c0c01280c13419001075100715a5800003170483c1c100b580400c010703014960051100400104a444820740d26400700800d542d842d0407a1b085400c0d083c14890420850000c11780103101000d070300e81e90040590480c10401d45d003c1c0c3d606007203034440c0030121440600240c085039a01d10502401c40862407541040c4441d40d03d10b0300390303084038a50f5000c90303000419040c0420700b0000c68100440e0120744030990351200c0c040070320071400401c140b4600050110104d034002040d403c0148005820305590b11012011030740708090321016101928918403441c8024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 305719289 1250 305718039 305718043
    0x4020301120b010b030f07080402010c120201020912011103070807110d0e0111010e06010308090d0206121005150703081b0715050a151a0909010b040e01060f1d061605 73
    0x202074221204039a1100202d03d141c01c030740a40380503481e01e60301e0100036941e4a60a81f500c80010b40140e043c450400c0c5e604d00014200f054540303c0040f40d40c005a1203603070507018000800c003040414210303641030500c2241d0440e05501035a500005500c0c02c28425203c2c0300d0300340d51414102c07200d50514011500300c408995041030520030300c0242030766800c425140c0303030f6000c034220b45482d8080540c80c2c2103c401080445d981801408004000a241c208214040d40c001000365200c520008201c0d94114108041d004d801d04c001d4006120540c2d49030800c035007000c9045200d00c20340c00001c0c280b08210b00414440c043c22900448425581d030111641d032105800c14a4003501c8094504203860b040800050502c10344d400707a80003400c0c0100b40b820f0300b2420302c110303d4401c06000003403908025007849600100d0356401c002d00d008045404105954a05201107001c5624050b003155040c080d102c102400308650122250f03580c80c0d2a8201382c44204003010016800d48100d0107101003200b50106560148000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305720539 1250 305719289 305719319
    0x12091903030305150f03060402011823100503040f0f0f02060a02010b0406063b04060b0a0306060201060315020c0109051b0f0d0b0c0c0f120415030603021e06070204020301 75
    0x24210310422209604d1040241042c4010065601504132001003401940a031115190486400540200840d1a556a90780000102d1140e00c1500e035056900581418a01c0907550b880c4580e14020746549015115103042c5031041034000e12080440c078503041449405c1c210411400e6006000c0c6a0354040407200034007a2000d5100300e4812417400ca0002659402600010107658660a6032000f0b00000c0c1207041c46010440480c10a402d0408440b8926580e680b00350405000408074842d00c403082d4940007022609203030801c1c2c0540e0315120040c0301044506010b040c680045200140e655442440302901410171250014124401c50040804441291f00070204164054a5100e0920240310400c4050001180043d0a0f031410801060308201071030b00800080d5501000c031040000800c045a26044800c7d0551222880c00700301880131050101d150b440c191214a4240004c0d404d50300000d64000800d0070a003507400f1481c440c40819100d1a007540c24590b0018400c544941e9604604811604 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305721789 1250 305720539 305720551
    0x3060e06030601081e011404081b06130221102016060b01020f06090a0b060f0f0906030703020a0305060907080d0f2a060b0f010306060212091903030305 67
    0x24880000e5000d0600146050484010600600080310b01544000080b1103085000305c65540380e4000c000c0c03400d05144440d01882c403a00b13400790381c0d0f4400f1641c1c0207100f070031807a80c0e91950040824000428a0b50404140580e0115101c064048c0c1c101e00035004810403090b08903541c00fa500020b400029903030701c0034661600b0340542502094042040403518842c04110300c000859075844900030a0595110118041d0180102c50b01c80020b80546803404008584500066002e820000200021110225080707135060701d00c00f0f440040040011503c1044856a0b8001c402040018030ba980c0c0800840005523009086c2c007060580300c4c10480e03160391044070a00d0310f51140314030010f030318140050400844441f035640c10040c2a4059411291100706d044105450702e0f141d8101001484510001981d0510034140081c015906074140410490707030b00001814545040f00402040b81c01046010300076450940c0d4076511078a441c000742d0011040d80041010356400e4101104141c1c050b441300e13014003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305723039 1250 305721789 305721809
    0x4021c06060e0f01050301031e05060c07030f0c0506040620130f1415030c040306020a1d030d090b0f043807120305070e0301180308061002070501081e070306 69
    0x2c2c941c406108120040848160000e10108010404103068441c1d81c801c94105000038403540901ea2104d6181900c00d4400c0c8551a0700081c1107401c16810000485082c0158108000d9001c0d45858145c0c1700c010052010704960f803941c040841d58040c039002520032101072884181c462010700780301c6004644c640150900c402c1c440d000421034101c825542c1e0680c240082c51030001c02141c0e00d000a01d50805400303c1760b104000d100100000b0001e00251181018075619411150074101c0201c03640809544401c3c0260070030880c082100d540016500b09a4522204c41650360800e80d4106400e07115603480905c0c1d8094070306a102c81d200400781c0000308000d6600d060040e2001503a0b4079911481008001080e50f008501d84944075806034015507804a8075041c07450304c960001020900b500c0d25043e481c405800c00341c40701e404160704840385c0c0340c00940a0340e00602205410b4000307592451540901c505000140d400541420600082605e400f50003d40c00103a604082a026000c0d10113802212424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305724289 1250 305723039 305723057
    0x303020a02150903040302090f0f07050a0e06030c030f1b031602120c060106020d021c0c0f02041407110606060d09020d0f0b150f030c0402031b0f070b0903030411090604021c0606 78
    0x41d01c6003501182c080c000d07000d42b260140e2203190040d250756001c6107a51050000420191900c2c0d43d0303040c040c521400c006103100d13951b45071500c110b555040c0001e0051800c1d1050301d0304803803448085016a5440700010184040708070401c031060740b1f4800c0292990050140c001412801002c011a0003412144140c0880f501844940d105989455042d0011180c3b00c0c151070300b0448003482461001300d0305004600307204900341d094020034180c2e00b146402580c40c80b00c550a1109048e481090f23843d0001c0080003034629030810400107a001c0c07280750300c051061600e40d56000c0566a80c0e4900e594840c0d40070b0142c140710106441c0c0515807841c11204c4100e9045065010400c6007040c4030280e00025008026080000784181000025000604280004800c28140c0283c2503151402015141403c2c84015100d00d10f910380311a80900040031610903404c00d1081c44000b0b1401d11746450000002c4811600c00e40e02c07100845e0080c003500101d0f61103401001c01d07282000b0000d07880801a25290b031341784414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305725539 1250 305724289 305724301
    0x60b0109080613060c090b0c0c0324010b0a0203121005011706011e030b060a02030c0706030912030504080909011202030606090c121e010303020d18030f0303020a0215090304030209 79
    0x85030b008840c240d50751004120000c0008215a00c03484034074039681040d009040d110001c4e82480d421680b110589540030101e407001c5407904000d104c4410001818000c1d039940626080c0c203606406101d9207200c0000401e001034005d000b40151884580604284000740c42c140440d01c03000c01003849020302042460f01c05c5468105008031041c841c0d481030b1a81942c600c1005045080800000310400816994802100c0c060ba500300003449454100e50040d5140c18046281e503080c40780303c0e4869414503281c42020f100140344a50700c0d001c0e1130001d0400244607981c5041140052290024890344203590a001040c80e440a420600140380241c04896481d5a40c40600905600a40c0c0c20414070006001405144c83c0143e04158403031070040c1542d5009058410004810030300783c0084000d600541030181c255940101c110304403aa801c0c451818140c80c60300c40314801c041c143d502a040680008040c2e100600130000340b0802101c000700501c0500d091400715031240c0007804201c2c411140700003c511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305726789 1250 305725539 305725543
    0x1a1c0908092112120109051501050c0a0204050115020d0c030203043005070510050f0f0f090916020d090e01120201110d03201801031505030703060b010908 68
    0x100859100c2081440e00d00d4070020404200001002054061607910100c80500710600a007040c004440314015201c410001d81140c4214050b0060826146410100103422104100c401c0100c1001c0c201246e44507840803009003044140180650090704000c0001b900011190700c0d409101816402d0351980d240b241400ca40b641600000940140d0060100344602052140040100d09070705508840c10003103005244820300c0310b030f43d0542e0320ba00141d8041140f420000700c01410038102d49007692626048141c0c4aa180c02031070303032580c80c038880842c1840704100520112035564800508010035440c0651140d00c0c80c0816003101401401100000c4101c00c0c00780383c89100782d070904081c0355940d80c204096040341310301c00d5006034108554000d08100140040c048040200c04641d00030030103401003080840e0703ca00000c2c19100200e02005040d42da0303d02000c600079411001d10f80070605e0313045034002c120b41d410a41c01c0071b83d00d4000c0c0031000041141d5035000c9585a00c0a0301e42070402035841c8001e42d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305728039 1250 305726789 305726801
    0xa08010603020a1713410627010f0f06090902090402091b0c1606050309150a0f021809060a21060914060601170106020309010c0c1a1c 59
    0x20488032410b852440305a8000036070310840c0780311600160103091b1110a400c007954540010042c2151140c8011149602d5100c031b0286409143e40c0e0642e440310040e1591104003c1c1011700c10040e041c6009505074000780f00d909103100b4a402440000000c1c41d10400914410110300e81a80c03400c1310024003403c00740110480e0540040110080d55119000d02001402c018510461a90840d408401100894020384402e1040c0300007082c110b104030841c1c04002101d904501c00f800014000c001e25407070002030040c1142000780d0b9540c100e03160107410b64043c01e611031000401a00108207510300c110501009510f0140444c1c1c2d03003149807150b08c10701c0362502690103030b0b22181c0c001210841641090011091000c1d210b10800206a1802c1d01e0300391680f000d2841c0c819a9400034801c3c00b0b920b69226024400c07400e1100c00b410200e514200c1c000e5a40d00c902501d44d0b0500200000d440f09002185005500074030514884004890048440c000241d0180412424984c0600c07140c400307501b03440c4107136 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305729289 1250 305728039 305728057
    0x50f0606040b070215030c07030306050409150903090803181e030c01140c01140a0b1801060c020d0503040609050111060f060120010c080a0f090c030201052802030a0801060302 77
    0x20303a24082c2020070b0520282c0c09110140e80066032444000452240d22004600c120544090301c0e84804051500074103403429648541d1041e802c020303000001c2100d543e1503000300300390301d200002d640c0703c203207003d40391003480b6030141380680070200c2c001c00300a11408019504900454003a403c540707181041d840702c0c000807202e803901640a8030000102c0d5000d680c00480c1480c207100503d0808608104460075030b150b45014202180e010b0060008480d10b0b0300030007248501c04c40d181000a84000e621058410051003030310100030080254a0540d21007107150746045800030160781d641c030f80b00c0b03070040d0000100b480f440b400286420580c121461000c50503e00940181200b07495a454001c01150411503118024002c1002e8000b210504d040034031440d07209207000c0c1c580c1340e16441e00e1039508044410002460440034108401000080c0d9180007a5007600d609023000b41d152070f22090210007141c80000021001e03081901601103a50300000039015400c400d642e500000c1e0788a0104030143c0c040d013500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305730539 1250 305729289 305729299
    0x106050919051f030c0e07051e1806040306090b0601051315140d09150213030204050711060708010e012114011107030e042307080907030b0406050703050f06 69
    0x1d0000828070507040107410008031180c00c1c1105420000800046185030f204480d402d440540420190741024112a408520750900e030381800b01b10b8215020051042d1040c1c00000c000144520080c000c17105a00d4030000040d14061310346d52039103011001016842c500355a41c2c900b010016039598401c100720b40c58042c91103c0717040380c145442034079283c18180210f40c60507c120752041c89001000348002d045010601c2c440452400700c0707814005001c070046000600e240c0d0042200010f20a0600c001104981c0c0c1540e001409035030300c02d0200c852040b05080078400f0b00656040c8034003e50f00c40c111034161090194800510799031000c480c101c4801041010101061109405010800c03882102e5000807c101c000300c0d901041d942481410388c0021002c50100741c070304403a002d40b4100b6104010791500312010700c201e09640d000c1c0e0600c203404020903140c10840e00000042c20f0950a1117500011540548402907030b050610348a40588402c564240000740341c03000084000d0b00300390016000c1d8001400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305731789 1250 305730539 305730571
    0x21020705010e0a05100510090e010c0806060a050708030a0207050f030a080906041208060d0804080f2103130501110a0e1201140606071e03020a03080703141302040b10030b0301060509 80
    0x2640c000346c00c001300702120401815100103030458081c0158031544403041c00004034400b158001804071000942818060401880744440881d0080125811140c1202b4425103e0703450782c3c60f4401130300c00c1e11002401030050f0b9050087c960340000203001c8180d103688800b069590f40140090381c1d440101e82c040c1000c0949004102c02900401311141c1102c0050b00710740307100c401034448481070703405a800711250368005031148450704014013901e84883c0c06c2d1a0960310f0b88071068420304540c080074050f4500000c003103544104101e425880b00b03c0415605803410b45608200c00090800701482308054019003104c41e081d505040184640440a00a50540c210a03100e16060100603000302104851604948011741011640101c2d00000c080c42076008020f0880786140040035024060810303c103141c1031008800401ca404020a98095038244440a408043c0d0001a025004d80116a0b800030030064152074030307641c5900510038035407080d0002d1160340e03a05c0f0140440342604a5030100c00c009100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305733039 1250 305731789 305731813
    0x209120f0a29180309032b02011b05130305070312080606070c06081812030106030621080703170f01081c120216150c030f09050307030e0121020705010e0a05 69
    0x10580f030182c1d41840b01242e0502d503050000c00e2a0a4070740f00b0518072052100c56040c111102480c004070203031041c0c4024400c14128100c0160741ba5002d081100c11712802103003044080d039035112003e00031500002102c50b2590780f41490344224a032480404001482c0e0000990642005411150034550101500e08800d1500e201199120400707045040b1041e21494000d400380400c0000d4100411080300c0140d40303524041c0f002e002c82d0804e41c400a0700e5000e00750502140381c80d0428803809940c100070039a0b138601c00761400302c402c0091342e2000040c1010311818000c0b040d1407411014182d6074154101e4070090580d41610b06a0302062a41d00d00240c1c22046e6000d82031201e4020b004445042c0181c9211224a5600c400b010041c2050403052680d66501464003268140581c122049460b5004c00007804281c80d410380b40c1c85280b001030706101c0d0880d91503015900c564001d000c42c6000881d0742d64404440074100019600180c1d060314698245030001390340c02004201d41c400309501c0030092074019130301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305734289 1250 305733039 305733061
    0x150608060f060405030307050c0414061014040e090a03030b0303180111010209030a38040303150503031903060e070c020d0303140a0204080d080402130209120f0a29 72
    0x400305030760300300000340030000f11a1404c0002c2c0401038482c6001c0e105000721102403104855401842000c10203002c410310656413106034528048180031f2078003242101605410050a1203280d10000b03a540c80e520422241602c00715440d010035220b503805010040c0c054003096070700d014590210980292403c11500d079580100c0481d0b1501c7c00780400581065600030000b030900010b0041512980c0d000f20072089085502c0c42c41d0701858a20f0101c41004039a0800d524280c40b50080c002000c0c580c1d1803550003580c0e0707181b000c030344010030005084995a0f1b12007454042c0100c0c20103079000100f420300b04080f41c3e100c4010040c41c400d6165980b50813001500f43c082181c8601109400e034241642e0706031008420840c1038900c0d20407070501c40b015980c0d40c50300000a15051500b94600c1c1000038000511005a88500c143c04c0c8960030a08050b80700c40310403001914030040d00030650014810045990303402d0b6004500d410342d2a009841c4846100c0040d07018141c0401207a2907020486220b0001030001180c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305735539 1250 305734289 305734309
    0xc03020f0d09150908060108070515180603040807060501080c10030b09070e1503070801050a05030609060415270b2d04030c0b09060105120109211407110415060806 72
    0x14601311141e29525403041e4140007080c0c0050901ba040b056060080e41803040160058411200780705291100b008141c0140d9002c070418641701d50740001c08a030501c0114000e80d1089a08280200000d507541d200c07180c5d490a03159000e034040d403c5500840701300c40c0240f141c5281414050a0303680b503960b52103021510341d45220001540407402d04032000310b1090400196104904a8075007182d5075062208106030200c0c158400c038860b41c004000c1008417039003c1a2103800070707840900041172104025105000e03060100b10981c502d020100301101c074803803440386040f080b80106004091510340b00380003c9040705040b0100003403411511600c040e10b44c1500354a500034001d00d4150380c401d20550799a00f030b0031030540e80ca0301141d001c540103005914003100112545940140200942516a0750b0608490030400b0001402d00d600c50320003040030302840d0005606106031120540d50815843d03c44101004c1c02040c03030086240c450100c60242141118406035126500d0300d00e1a81e9031142000803243c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305736789 1250 305735539 305735579
    0x306081b0d1205040810060b07030c140a06150e040b04080a0e040f020703020f012306040e01020c0610060c030801030b13170a1b0206040e090f0a030c03020f0d09 71
    0x5411070480011403404203404103103000964840f5910b620b0324000358900443c1c80c0c40c00108501d1f0202c01c2100701001002c80f09029032504044001c00c5a900b40601843d000c0402100c0c81e0141498190412045500c0809918201c41041c483c903505c1c1d5141c031900403011600104060400c001050100c1d4004002c1d000e10140342c034001000d02c007584007141c15182e07501d20840b031040e0041090f404158041c170824550102501c02005081441c5024007001f0818091407171641400d1004070700303561a9a040006031203e06802035648024000e001582c51004031640000c006e190400070078201d2003175055554040c1c01d6650500c65901f11303142d82e00c0000020f0080c1b80e20410440020000402c10300d12001004c0d588012151200304202020301129440c06000d00d15445007400c4c4030040e0350303080641d029901c403000c2c405242d13610070451520f882d43e14a1200c0c4148603041e410800c01da441003486031103d201c0e83c02c0d9a401d5400c0440e16584440c4004000c000c107100350b4007130042ca500348440c04000f40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305738039 1250 305736789 305736799
    0x50d061202012f0d1124060d0206090405100807080705030d050a0309050a03050406030605060c03070308100905040c09060902030709050f010c0b0f07180321090512060f070306081b 79
    0xf0301d83c4100d0702d0314141c00ca51074045a090740d11815001070501150f12131401d0030f0710640980c40380d0019646500b40042407503100c0c1000381c0f10fa90941d11080181c4071100405082000316041109503070341c1c20b905d0303032051181c24424840d010400f0301020805808462020b4024551000010016140d40c3c000010000c20965108000d101181c42000309801050007500c1700c65482e8100b51004080e10615044140184400c11000d8030b8540008103c07035031540c0602d805021030700d4018500310a00541d6103c042c0290070b010a01007803241c030943c00d4084400038002084000e59881110040e80000c80c4c822000c03401100f802c01250800c030600b0914030405160140c003170300c000d645500714840d0540e1485c4c10303008500b04111540c0e8000010b81d01410200d001603444a00e0b6030341750042c46040b10b88204020311052550707a4124060110341010b418000e182c07000100c07028410039030341d40382211002441d000c00d4012170740c00c81c040c1c17041c201614000e83c0608103504610240606003240d00c16003079000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305739289 1250 305738039 305738117
    0x30504140f1c02130606021908090a08100b0a122d15050601020c060304080a0207090c0507030207170a020103020906090a06110601050109060f08090106080607050d06120201 76
    0x142c0d1140d51000d921030560440d0703101042d40340140408a10b400140741c040f41c0c0340000501c01c0507000106180a400350b80001201c10003103141000c81d6003e07141d44540c00507054100803904910105d008a11245c4080c010407985010f281000b510210030b00c0f84013a0240e60402c1c61010400c8004218400c60031078807000c51103000d900c1d18800e1806400001d540010014103d000241d216000e816000320091004104a00410b00010014880038100400000000420804a50083c068180100720b240c0e41041044612640605140e2190108038014091103001080d0080303150245041162124020005001c1d10b500640c000e6124480c002c0d40700c5401d0025401980d99050201d02074500d5580d02c07600d028001e07400707518101041c2c01c00c0b410302a003c0f105000702e40e030265404e04441c100d807800480341d03120031135094010305468100000300d00a507030030402c1c0241c0160062034520b00300c510411046039a0404907000900543e0002d00140c0e15581055070b8400c01d1002180340d1040c0303503002c3c482d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305740539 1250 305739289 305739319
    0x3030e0307051e030105010503010605030c0d031103210601140f071a1e0a020f09012a0b060a09062405040f0303030506010806190611030c030301170c060703050414 72
    0xf040144039290207011900c0e0f00c48103481d08082c0681c81c01014254001d0103120f06080c0065120406900031600403040d1b81d40e00d00034140b0640b480328540740100c3c00d6036a910440d4071000030125020780341d11002c8440300c000c6540b6512900b000503e08240c0c804037810801e800001d04c03036941c01990140d4007422841001d541d100308000d0b0f03581c050014800038003018811081c02c0740b8914401024a8507461040c0020b8090384c0c22141140d591420900e008603000301621008200c030031030508800c010500e070703070790003c20090010685030140d8000c440c1d0860540e95034a040094820b2070003000b0790f081006829504590a060096400300100d0521a041685552800c60250f9040c6e006074002501c90741403003844c0d6000b5800d03d820140550701c1e020a8a0303240e003000071807034480c03141d04100884120514000300c0c050054820340c99110054075587c1d60344448043c0341c10b000020480d054011040d48450f2450110111244c1c640c0c9a154141401c3c500600d01d0018a4841d440942040c039544421507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305741789 1250 305740539 305740549
    0x60f04080f150c030f01030209100306050420060a0207031211030d05190b031f231008012d02040906080102030703060e150402090303070b01120b070f050403030e030705 74
    0xc0101d51060050074003907240c145050041102030916101d40300d04205000d000c0c010420741506507901603486d070005886038040000c01815582c40544a1440d201c140000c020120899980300809e81000180c0100e40b04204856885910201d1016074046041000021030302c141c410441006414070300e031a614140d0000b41540e00901001641e10380d500c0810004041c44608200303c281041c03420403078000918040303aa80e18802c40c0c60070901274040c010002e94001e94101c40b4074600421445a1000d2030707180c102144180940303c0c2041c1c2501184041912101441440c10940f48170f4805505003030307014110000104541201c0c14950f40801c00410303140014010a00102007413000140c3e28902464002c003168601e070004c80003e02084144842540c0070255940070004c2203800590740e94448000030300e0742c0f2078260003c181a42c5a00001340401c1c0091a441000c0d0140301110450f0399855002c480c81443d890000b030115800b0711080c00030030310900020b0900ba2018044a00c1c403511100005c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305743039 1250 305741789 305741803
    0x50c0303030f0109050a0207030c14070512030408011103130f05030408070b0c0c04060302090615040e0c0a0809160314030c0f1608010902031213030f210e01020c060f0408 75
    0x2644041e02d140100302075071143c420554001283d1a045040078002c0c1c0d8002d00c203502035240508440c418100c0d0f0036100c2d806001c2c50004010040040d140500e1145850384c0740d40041c1300760003580d41707442c01800040365404102c0c1d205a941c1c130b183d10b60b123201a03a100420400f0b000001e99440c0700c24400480e211004215200141510a000645800c500081540fa200e01c80c0c02c800e009500706182000142ca601e110540c111004a030f098003480414072400d18039002e942c0c06039401c00380c00700030322810241c8d80c00141180c200303c2e42e40801d240d49041c550380d0354030700342d240e100d441560054040011502255840d2031100c540ca0650f0b14020581d9041852300c200c2c03116040c0c1641000010241d80884590f02c2d8008243e0040240141d10180d00000d80751441c08508886c48000003411644282c80b21182402855000b0790740000d210090803d500102100c00b0000c0b2401840014164810700a108d101c0084d58141d0040c8240a0f4007428464140c0010120140001d002e003c007103036444d0140000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305744289 1250 305743039 305743051
    0x715020a020312061002060103112d01030c0c11010c030314090c0906030111030f070c0203060a0b0f0616030c052a0907050a020d030207050c04020d1a030d020c0d050c030303 76
    0x2c2d0b8441d41c0e07401c01c000701e95401074001441114207480b000305182c1c000c02c500381144c2c1c020f01c200c140f8034030070408141101c02420011051421650340c0082030140c0b95a50340c032a44084c1ea0800c41d90b028281e00b0341c0d800782c0304d450141222540420800343d542c80b03108803400341c0b8441d203404106030301111a812100c16080ea02481d89070040300035034140e42014401241c0c00242200240212004d070f000c008000d1001805c142e51000065000562040c0a41ca801c85900e9000e01226010301c2d08011200080ca9a0954035102d141c00c0d40c0c408042d0700d40001500d2422182400030000412907540c191258005601c040381c2601910041400024071a003802000404041e0201d0052200300100f01082d18020f003c4402e0110900031055002d034000340a042e0070340d0343c0c01c00603592031a03824814a0154404501a4403a0002034020718120301c40e00030303142001c0751501304241a9250ba0401d52220114030120700142d1010000d03401b10703d02520328001160103101512907500f0f4800200341194400c40da0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305745539 1250 305744289 305744293
    0x307080c0a120e0d0605062404060206010f050a0b03270d030e01050106170a0207050319020c0901030201020c060d060902030726040210080c0c06010906090b0a030b0103080715020a02 80
    0xa840c240894100803560b0b690141c030384407440c150304800040080308100e10243c04646e03110000f4206480d40c00d092086100b9500c81e040340084044051000b039400b90003001c005014640c0006281d0198051000a90760003d2030380320307107030300701407141c0183e8200038421045500329810210b001c0b035003000c41d041c2e11600d010280c019640b000344083c050315410108060300f82c2c5800c004014103030f48403a810350301107040552080e05443d400000350290060340790141c00c07030200280018140000e00c124481c011520380030340703000940729410071004001c00d100190141c1c01801a010079883c0c00c20003050360041400b000203441e07407103100c620100d07003046880c240480c01c85d290039004c0307180c8006c24012251800c1440105440c0c0b5a0200d0801c00303108240500b84400390010540c0204403005490203200d5000c11505203603510039840c800f4004038414109401c0c07411a140c2c031750381481c1c7ea01c80c040ea5004501045c90b030b440c41e038950074650f0040c42d0507100e600c82d48002d020001c1d05400140306503441980 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305746789 1250 305745539 305745553
    0x1c0b010f051e0c0307080307030614220f090c0b030708010519050906062b110a0e12030403080d0605030d0903020915030120040f0501080415050403020307080c 70
    0x1400c0305240c00300c014144030007440841c660019182c841480e0200040b18a510b82107000b00c2c90f403079401070781c0b0014500741001c000c2001c10380d030540c0a80704803035500183d0801c1001c12000d20001107440c1c0803003a1244040d40001c500494190001e00d01c03c504440300190906030394403101d04080c259000112640000002c2c801c0741031344030a0351800b40c041220100c00c5104040c0440860500c00c1c8034884c06013201100088980ea19a02a41c056900400c3c008902c0408003484d40c03840c48200341844a2145000c03441c3c83d401e4005000d6940340d81403610b0344525001c0c7d510401c0002c0e2460310071280f1a00c020400840029102009415602031001003c9a210705000415091010040e200b0f410010100f10400159641e04000c42d004003001a026120026800100b4094100c1c0c0128003108111a5807130724450241500805c100c82441c00c911030351a4a40c030044410802c02d440141c02d50303071b0f000e11850b100f20050307000c3e0350400d20a0048910700b40719aa81c400b15138024192215054002c22 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305748039 1250 305746789 305746811
    0x2809021201090515010c11010c080409020a020f0d0e0d020607140d121808130312020a020a1401020303011e0509070c120309021309050309030114071d0105040603111c 73
    0x406030f00e81092a028000021612602c0000d050320100040907107806c1861038401c8403039010704046000940c111055035501c2c3d49840000b07001c5d504c0103042ca0b005105002d040505a14045000b02049800307a480090601d140c0c0100300128551402c01e0381e1080082082a0029030403590000c0c541540101411400c0e1900c400500406d8085601d031002ca410042a1411006403041110050380d00c10000e9841e03544850b441c035050052070b08010712882055900310b010741d030002415a412842120740601c0c154460f2010300f03a40c0700c00c1802c030740503900601c0107000061814882101207414003c0464040b40c2d170703a00240d202c40f010382d00540480d4140540d103041c04084620000c100c4c140e41010312900300c069001c1025088444e001c903144076515030200c0d0170003801b44100c4507000c2d0014000c0c040780fa02400c042e0300c100c43c2540d500c0301042c0b509c1c5400c010560304141003040140c058446504040c500802a00a8603494044480c018401c200180260280001811401010b40310014581c1c00036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305749289 1250 305748039 305748041
    0xa05070614030f0406090c0303020c0406050621040807061103010501090602010506030604021903080d020c0708060702120a1b0302061f0b19052106030c060702280902120109 76
    0x1a0011410002441c148403a2030001100701d0303410110056031411a03035582d0415500030b2100c048010034501500c0000418140d00140303425131800d04507800c02840d0358030400c003c10b41c0b00380030340d00e55016030107000e00c0d003900e6400440940c03040c0205c800902e007400590794141240d400d000d045120f0f00c004001800556030001044002d402140000c203e1420705c080001c4d514880180000d20410302c8444141480e1301c4007204030001c5500c0081c1d543c07a420503101000c040e40009507540f80c42e11500c0000508900c0c00a8014042c1d40380d5009000d211196014449032540201c501c0300c10322011085401c66a03e009403041c1c081c5020f903018150f2303070814504112a1aa940c42c002044100c030030418003110030031008482185104201070301c11103410802c144c0b081d004442d189400d1200403106860103c0d250940548601700c201c0c00d68801403500410080789001e210000b03908052600a000b481c254003001110206070006032081606a40d0060311043e81d03c8042d0b9010340fa111100100030390301312 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305750539 1250 305749289 305749303
    0x10e01080c010306031128080a11030d08190209061606200f0c0c040c020f0f030f0706020306010e040c020a031806052506020a030b0f0f0604141f020a05 67
    0x910782442254a1619000c09030b088007806e00d44070b1030668142c3d0183c485c0144030b06050000c40482450015540c03408282c984101440656200300d0a4907000315600d00401ea24141011a44036080a0b4817503070030440740ca0404114854a07a58200008603882e40c855000d040070081281205912510714581002a1040e00612040041400c410100c10603c4141511080054040704035112821144840c0c074164121811582183c178200003108140d902054001c02009040100c4091642400003a030342e034030460b0a01095150184106000a440d9400445c0c21420504d08545006603140000d0110303100d1401700b00c056800343c85204101074201e0b0320480d1101268250000d91860440f020704a8854418040d0b086088602d4005007402880405854035401ca1421500c039000b08101a0007440c104810b50310400080c0c04460051900700c680f01210b0002801c01c07800c0034600b450707504500d04042080f5602411046c0c154289180501c0c410104010301e030700500d00c5180da410041c0c18124 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305751789 1250 305750539 305750563
    0x8030103060b1e0d0218130c0807060e06070602120f1f08060f0915100303030506030105160f0c0807050318060a05030103260307030f06060c17070309030209010e0108 73
    0x103040c6249884056082d100d40318801c8040d91500500010fa10010f0145110800c03642c018509081c20b01c100060611200c0340418480c441c0450b06584a0589c255601001d01c10400003681c641c103041058241080600b41c40781c0700d058054203000c03034038a102c0c814080844111608010550130003400f2510601600110074102002c001042e082c1610551101c4006000403581110400803d01c034034804c1001d881540210504801241001d000321324071200c01d07200c107a00003810540803440c07929040c807030240a10b21807140484030f030039450746c281c50035131924035103005200c0f5512806000c00c2501000b884600e116101442d074a10b00d2058a04100012111140c0036030000d0101290040e00701d4202c80c1980e8002d03a04042c41d06006a820503451403981041180383d00c04800c2c00b1039541c0680000e18500b100510500c0215100d202c105c1d0304504003400034241850182e982e0390704c41c00300700040420502910303049441035200c0d00421030b04502a4003807100d686145004100013003082c008452103c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305753039 1250 305751789 305751799
    0x614100f03020906210a050303250f0c030e0a06051903090c0308030c0d090305090306150a06112b0207060507021503150405070f1106012103030906020708030103060b 73
    0x90075900030448603a0700418950051a071211000380b40c420805400d6070300c00c501001c0341c413003c03211718113261a80c03c240c070b1a0302e81c0e20a4964001034880105000001c95507141d45117a1117081102080b10101c150020075018880c12165a8070640c8801600101502e4076480f81c03035440d18000d108018118005074410205440d004000000480c0ca200d040308480e0089440c54403900c90f1910045c00784640b02d40c0e40305184c504540c40b003c00d03800c5805444190401c80580d400e566034000c815010b21110070010740d029498060601c07107540210165060604d5203411968504842c134802da461520801c40e0700c1d10701c6444c180722213046604010403c0500301903e05a414880c1550114584451200c001c1440b42004030008101c489031541082d90a84020018007050801d418050204854074100e040020141c004601039044001130b00c0e4104c41321003800c910805c80030300c40c0030b9828034403c804a041648500124000c034045002030403000b4040d2240668952561418000319402e1030b050701d004d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305754289 1250 305753039 305753069
    0x9031e0209160c030507080c0627070602030d0e0708060403021516120203040213060f060e031204030311030409060f0609080d09030b1003050a0602040603140907051c061410 76
    0x4283c0c428410880c0d0b940c1350425503140d0000d450f00b100240206103d0b82c11601c140740821025a8020720300b51840184011090400e00e07045104540381e001c140542005a0300402c500300c06402c4945c07241442e0302c2001d00740c1c5c4801c1e0315001d00301c3c01c002e0b096800b42e006070701c8241c3c20ba8803503d1004403c1d81103140e510320304881c2d41a107000544083e10404e051200340d83d011000905544820f0792041d0310355080b810400c501600c40c0e04442140c08a030003410001901040c83c1215814001100040c0e4081c0001103405c09255a400700e9116280200142890005000000c1c07103040c1800703450060500ac030b4001a0850030701e4030044c10a01746030701c82c0c0a1948400d542041c1c8541001840d41540d4107c52160059603d8000c84001c0920b0703640010204c0c494555221b06003c840d60141003500e066550a100c6070381c1c90402c00c0321402066507034203800e4020403020446031410105030309000303030f40704080509a18140c441d2401c90340d45409040820300310400b0040c8045205c000b400181861311102504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305755395 1106 305754289 305754331
    0x70314070f0c050f0904080c01060302030a062a1e02030f0d050a0f05010b04060807021c0e0a0611150c04030b130b06040b010c110109031e0209 63
    0x100c2d07100e040100d03180c40c18420304508000000c2c10481030361284c5d1035415140d4040043e2060640da01d990002c0103032070500a03005240d0103010b00080b0340d082d1000e6244120740c6008850b4a110a281040745015003118203501d0780340302d018403030f103540c585003034182c1c40c41c1300d601d00c0082c00c8500451100881030b560f801042c0301f5105800c0c14800180442c5803001540c03428000c40c2180d20301400300340071052213100d2040e401001d80c0304446a00c001005015548001740c0c40c3d1b500041c6108680c10342c503040000050000300300d180303452407282c03c6408070503031030380c03540e9808040552500011409060204040c0e030082c5402c1411080c95041110380c3c0c2404027141c1808440300e08084000490300d15040c4642e4003d5501a15641c41c0c154030380e568003c1c84412960441e041c05213028021000c00e0040c00c034000100a601a400e2a140441c01002580340c1d004043d0003c42005815004c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 305575539 305755395 := by
  have h0 := BRFrame.cov_init 305575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305575539 ≤ n) (h2 : n < 305755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
