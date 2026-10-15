-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4585
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:05:44.305705+00:00
-- url     : https://prove2.me/submissions/1bb96368-1628-4fd7-b5d8-aa0c2ee16bb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 824460431 ≤ n < 824640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 824461681 1250 824460431 824460443
    0x70e0f180f06040201081003080c010203010602150108060112020a0e07180b0901170c13240311091201020c10061707030f080715180201031b021e1002040e04 69
    0xd121004419039984004051a00c182c0080c2c000c02c0142d44646419a88040000c0100c10410380d41c1d40e400000b90b221403c0c01c42d0710395001c40140700303069040c82124110440c0c06038611155040010540d03c5071410312900102412902e003034070031500c071400500010b08150b06164080d05d0701c41400b400d400384104040c400c20001d000041107100102c41580c0f010681030303403030b000c1025045403035099521307019200710000e203428401407064412034402e80d0050001e10400140c015400fa008202ea0740503010101d003418240884019541090b00945801640440386003180080180c03a490091044451140f510300540540703483c061080e030400001c44a1100881c80b080312366002050315058a400009c0c0b0001040008002084d41500275081c103500421100e00c0c028010b05000e01110744c1400140c88030085801440c1c1552380510444500540103224400322400c1c5001c020f4490610f140711202044410a1650b655441001078200100100703004540c0ea070344075010035066031000c590032112 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 824462931 1250 824461681 824461711
    0x1e030c020a0305150a0e070b03100b04150315140f04090618021806010e0d17070b011404091119050319051c02280605280e07030311070e0f 61
    0x385d06201d22440940818050107840c3d00790410416003200c2e48060030407100001004808100000824005c05c020300360f54982d0803011000242c00790680d1102010709001c3c818280007001075961007900301114240881d95115003018440014005088070074001c0c007841d24006403540c06c89118001c440f0218000c40709042050002001e40800220131122280050740c07800d10102d85007030016101e0380e0307180301d0b8141107a00511841a400345421802d016a041c00604004102e101c1c0c1080c3c40c400520005c0d00d05001480c3c86884460030751500d02460341c0581c00b082c188600144038810b91401402c0000c06644d0f11201c1d8242c400c8a1000c0b03820252454000c1048030041e0300040e0f07005690800322600580422644c612007034420051040c090058008036400e0100011424818580314a40d1300c404c0c03261070354414600105500750194078114441c1303005400e0349007000001d843c804807039042c940085814102c3c8420f9003001d0703646d0f011900700c420340010300c800501d000200e5071241113003c4801d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 824464181 1250 824462931 824462941
    0x303020d021e0714150a020309180402090114120a060f0e1609050c04090f09050d09050607021306030b160f090b0714120f04140405041e030c020a030515 67
    0x261071424902c0016031503010641c02c01400640310025000b0200040c0392440d110000400e81840ba4000306007540182c1000810000c3c0c1d290041c0f8034140e0440800500b411032800c0c2d800720740e40c2e80d818080d41c903210f039002c4401c4c0259690074040444800d0740600b6101002083c1c030f0300c0c5016008840c8402c101c01d00340800340391650340000c1d0f0004100140d4800441d0765181000c010000e10002d046292444010440804d0460060286480480d08840005911a600d0422a0418007215169020086010010409503589109564102e07404a45000c0f070001d0045498000341a16407004011301030880400c008145400c410b200780d07210a4440090350200d11004503250340c0c02d401090401507050002e00c0104480990140e140c00c510f90440b01c66500f400c19403d00c9403c200c902256400300000c00b0300000500d081040c1490b8420b0340e086c0410308190380c1c0c4800b0050300034a4504803c40d01d60191041c5441604e0404450341c01920b4a16159103070305120351510f40044000c50011020b001241d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 824465431 1250 824464181 824464213
    0x503030d02090f061e0a121e060e15040b0a091d010b09041a04060902032a040507020a0f03020a1b06030507020f07120311031803100b1e0414010303020d02 68
    0x405d4030b003c021002c030301c40b511482c3c0c071801c2c2c0c1c000c01c01e02400c002c403000040050001504c641010f0180e90004058601420030311041900d000c0e0b00920640a242d009120f03921401410110500034216800302e0404042e0005c928080e00307552050504905110940301000010120b1405160b1540000c0c841000c8010070b0180901c800d440040104a00c200004204140c42c10381c0390304a4407403800814407a440c0c8c0c00091030020b070340b03591541902d01c5d80041030b281c0420000140040c0000e480500440c079050700f0294032132040c034101030300702103c0c003a10404052081c0000603071a6801428110304e6004481030310713544140c40c000c1101007031230900072072112400058100f0944410800a00c03015050030041c4000ca03125907802c1f014410880441c0032000c60610150108420000d12030b0a104281400c0600d46044501ea058401d4a4004080e1041e21a440412002941d481040d40701c04203940200380284001452030007141c2081002000300740e80403440c90840080e5a00f1642e180d81948840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 824466681 1250 824465431 824465437
    0xd020109021305040609050f10060e01050904240509030d2f0a0e150c21040e0c0d15030302010f060e180f060106020a0506010f060806190503030d02090f06 68
    0x694418095594080340101a030880d5502034482e082c0810010510b1f610b852800d1385440c3c28036a203803c4001032089400340e612948004001d081803041441d490710012070b454030b10181c0043c202c4081401d5540c850794121110f11390790040305000304403d1038441d000c15140c0d00640b0303001500d641000210501d08800d41e81000170700391481400021440610103002c00342c0c0c44105480b041c0000806040c00303d560300e1030403c421a440d9010240e50309008000d503810078520700d640c1d404a81402840e10400c0741980d06840940301420241d034003d0300c862009075a940280440765040070b0409522040c0c540800e083c62080764840e4000784411544000588103541e194000c00c6004100100003038440d01c07418074552289079441054030340b4003010b002818180341090304460702503440018108200300040094a00500002c00c120441c0c604021004081000150603503208045194a406080340c0601200c4003d0100070704503a603031040450703c1e034040d4000c00c01241c40741d4240304e5688801d050403812 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 824467931 1250 824466681 824466683
    0xb120a0e031801140708090910060f0c0219091d0129060403020d0b1902030705180f0406090b24031b0904090b060906030f07051c080d0603050d020109 66
    0x59802c114440d00d40e00403540c0e51084407410020444c50138a80b8101c5140281045030080380c80a40e550503c0c1c0600c040c5802c043d20b400c003450b80c2c5c0e0001300b0401c5c0d0300000c1c12000c1d40c294640b4001c000c950780009044501100f4803401405860380d00040c0c58a46e0364842e8018102d507010400b1120310f6105035600302c13480c1c00c056001c50080c003045c0e58050183c00c2541c52040100415060402d9103a0700484e2205a4a44040f81c0001800c1c040c03010000e200f100b240a14000d0800540c5035280c844001056401440c4107144005c00805d01290980e98204903200070860140c0100032242e503482e21100035110502c0440d012365408200040c031400300403001e01d600d90541110034515150214007847c800300740e00340404181006d2000c5078140d91640500d10002e80940480e80d81420070408100304031802800b810302c41e610810039000e0001d00403e01608076402103074504540e0580c0700702c132004c04404000091002900044420381500c090303004100b568019802c59402c2d90740c04005138200c2e106120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 824469181 1250 824467931 824467933
    0xc123402090c130b0c0a030909200c031c060906061e0e0a030501150e06060309060a020c0a0b010f0602070506130b0f090306070f0806060901050405280b120a0e 70
    0x3440301e030249005211070820710804041c036a6132918444000d810402c01e0305919000407aa5400b45688a0050406000703c0081008029200e000500d244040c00000900b1040c001c104042002818016100076a0508a00c1d04943c011240074000604181c064040010310341080030801c10f116441d034a0121120340c407021511445104c00f035a0325424070311500d0340321440c0c29000c00010702c00e0145109005000868100c0981041d92100c8a00d00c01810180289414402c0010304000045c2e01904000482e1005945106550304a03080502e080000f41400e0b4401780001040726001c40c810040b1003041d801d42d00d00c651508100207a034031421b0100e0394103400041c4c0902c00400460000c00d800180c0302d1031585841c103410003003030034170314200c074a0306c0032400308641180c003c1e0300121100c2d4811011207031a0b251010320000a0403d004d68004d50713000707171030241e40d10000030a90015103143c86211604403020300d039a802c5000755030340002d9030304410a00b10030114001060f40d0240d8038407903840c08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 824470431 1250 824469181 824469199
    0x140304151410180608100e16030b2205030a0f0203041205070806060402070f1106090919050c0901020a0b0a180506070212090f0d1a07091403030301060f050c123402 72
    0x1440074000351a401d461487d2500684a5140b144c0405d40020001188140001c04d01072900683c00e080b240c40c2c00042c110399080c1d1901c00350001d200401154540941800c00c1101c2c00d0322030300124030718051504143d02000704000d40074144900092040121543c000440b103195880200384010b900410f14024070b04440c0340301100005030305840e0300f800b01d0000b4208500b4440e60030001b0b46450341c1074540d0b0508a60001c0c050807200264081c09501586101c14640b4042032040001d41e80d06400c40041e040340d02c404040b82400701145c2000c42516a0391a401801450320700740741e0b45840094441001601c074880300c80d03011041e124150b540f010700c020304258100b02600103001891011050440b4801c6180c0f02c2d9019580071400d9040c000e40465582c2c5401c1070500d40201c450481080340e10b4400d500a1004001d4541d1007240c3c03c485001600c3c0c003680320804045c402e0318200b68018018405200800c0000e181311219503a01e10510042906489282000c101c0072049140500060b401c00000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 824471681 1250 824470431 824470453
    0x1e0f08010b01090e0c0d0f05060f030a170a091d06030610050f0d02040b10030b010e0d120e061c0f05180a0209130c0f05010f140304151410180608 64
    0x50f0140c107900c0085e405c40b45140402070034420b021169903600c1a552143d941d0f0030302105050025258003030400c00d42c014480814151950186030611040c1c943c24444001502064a44aa01035070300a040110450b070104800078000e00341c28004030b500c18042d21070480096082c965595401045880c00760111828581210500051003501c00040e40c00c0380e20385c1080621500c4103051100c01400d690f40014040721410001040310407107001040c411012546640040743c0300170000c0d1a0210603007032540c10340e0441d50100e01c050207059030781001c00c0c0e20600004a140c619070000f0400107846c1d80108515a200e21050382c246d40350035481803043e482042e0b90301c0141408007071150003000e40c01081170030700c85560703030f80703800c2410f031b80042607406c102d60410801c80d6041407102c081010a41059640d00c02081143c084c1400010005001c80000000c0801d22003015444191086a81d070201c80c4949480da10302c600d80c82c480e10844880d079000220403100c40843d442035030103407007822001c2c005500c91 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 824472931 1250 824471681 824471699
    0x1080408041806030f1109060609030616090f030b01050a0f030b1314030a021f0603120f032c0c0306090709020306040e010603030f0207082d071e0f08010b0109 70
    0x1c1c85105a82c00382e942d05011022a2040c816068020300c641001400d00c0035001c1032040e403c8010f464039010300b07003d104044080c2d0b00840c110381c2c0039070314a8002c0c0d119034000c0030480b1925680c0d403240d9803125204a020042c8014181554165442540c040c00c06030b0b078640e1a4040e104140c031016000e07a40000101e03c20701e064807840e1041a01800360040102d4112101d01e0665200020541c0981e00643d5070380140c403445803c0b0890202c660750100035945c55900c0d00c6004115190301e082c20003c03c444a85500e501175803140718000e045402071440300c11440107800020760307074620381182071183d0212001103180000b580d80c0b01d6901d080c007420405290680140203500040c010990242e283c100c9002e09000910030f91700294000d030f9480c040380030030140c064144411900540d260b500060448040404900b60f6158190700803040e050b84103071b0b0340c0486404c0c20354580020308a008101a0700959180c2d0358407031025036421a07160201284e80303410043c200c0b640440c12030b020071a072034020051528 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 824474181 1250 824472931 824472959
    0x608070c080f0c0c060d1a040b0d23010f0518060106020c040c05040b0c161a03011401020102070b07050a02121312030210090f0b2202210613110108040804 68
    0x2500508441c004c1c43e803a80007420540010700c98800b1641d0b109403001a040000b103003407031000c5080e1400c10982c110341c004600d0b115130700e46000e800000760643c80d40402114150b000009821000200082050700b00c000010f44005e450a100d602c40480205c10405008111a8120340703181d0010440c0d810410148400f4000103070381031043c040e05210001d00000204010000040150094a604400072624041c054400d401002c1c0702965840c400c0c3c0c0c2481080100c2e0f0544004040346a510310000004038068498114000c01005022041c8031a45420602800040301e4a07003d07517201e08940c44030f02840740034554a030160340c038401c0c804101006401c145020100d000740305070f80e04000c46031054016034190100c22113a6184100700702040c4000c00000c29002500265200901c006211405820300c0003d04d010b845424050a514104000508100c2d0b0304103411050704c05620300301d00c0850510985e1081900c1074010709403605070a41c480d1a103a441542c1c00364042e0b040c0750071710140c601100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 824475431 1250 824474181 824474197
    0x10090b06070b04050d02060702123406060e090a020307030f05160b18010c0b1b090a080f100b0a03030c0813090f0b03010c2003040e040308010608070c080f 68
    0x20000040800c84120a00f4400d80c040c600504e00d01c00c09000007403038030704014804011508010b5080c0c3d0151545000c82d4540039000c0c10a295140f02030000042c00750301c142c0c190749603100303803c80c0e0f00030040150400401c945440300c034402e4699901010588404001e58001d615821195080c40040c0c000341140d0344180c01141240d0b04082404142544603525070011140e200001c200d030001c5450070f004c0003050b0a02881c05c440d8410942d907591800d0103014140c040c000400341c401010f8904000291166018028a2000e07103603581c40c1c3d00c40d100c1c111515501080d0080c5070900200c01c895000d541d0b11100058410a8418a5510101e454404281c0201c40048042080315108103074a160340c400791815581c001101400d400710481203c0e48080110302036414100c4e10802541c01007917013413070800e0781c007a2070314041244116a030030351046400c40d081359085101400b0070f02d60312000d0541030b50b20907121ba4415071500c04043c4c0d0315a0703080800800189041040784605481800a44100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 824476681 1250 824475431 824475439
    0x91c140703210201060e2217090f04060323010605041b030f0c0806011b02060406050304050d030b1c032319030b15030709030c12110102030310090b 65
    0x40640815141040415402581c0c014050145200d0321036100e2030700c4140054500003045038034504190741c074400c0002407460703c030380300e00085402c04100303080d002480c055400502c18940d1034103040004526005114868080c1189155807981420300c2c0c032881d0305803604062480700300c040400003013800010603042c94800355258a800242912036010768407040c41720540000c030800d01c14500034201c81d986410039000c1410035800000c507a40026810760020020302e89070100e07a070340142c1d0341d50303414803000002e4000c80c000900148035a4802c010718003a40c4500140c540c03480004101302c040c0caa40c04440b0b64481640c0740010805100750038201801c1e80300c0d007407028601d2206030150414000140c060100c004000600d009074484002082401046905080229110b042c2c0882c0404071100c120050344400000032803850703809807140ca40155071040c0c03c880c0c141e03152440421102450b080c05c540307642e06c80c40c0c3c582c11980040240c91107924094525124103103014110006012a4138840e600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 824477931 1250 824476681 824476703
    0xd0201060b12071206080a0201030c0203030f0402271812071502090409050607020105070e030f0a06050a0b0622060503070c0b0402120d021c05070b01140f040903020f0105010b091c 79
    0x29290045c000e0790300602d0f20390094444070312079000150541d40c40f00304240031074100700100f0006401c1e558416402076015500c280101c03000784503804a041c5452444114492180c041004440c000fa801d140d60550100c290340c42c4920580d075a2451f801800d1004100088031004031040454543c09099003100c000d201180c620904c4e150796082c1881501c81d400140d440c5e20400003101d4102500c42d01086043c0e000300f100104070207006803034151501c00180a10b86a101089c0c0714030321500300f1000000011300c03280d0b80f4480000800d071040a40340840310040c0c0c94500010f642030007401564130402c2280c81301c8045408640c0e400e4a10000180100d82c499502c80980440100400420000400f03c1d001008629000e885082090700c12017844001c000c020402c01000407242004a811205c8140a003085804c0c03580004100070400522150064a0a5204402e00d075000400d41c0c0307182d04c4000208240d03600c0c0d1140d45030b07906c00c0310000ba8124a013001d01c103884854000c50501c8203800b404407009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 824479181 1250 824477931 824477957
    0xc050312040620090a08030f0a110f16091109150a031b0306080c031209090703060e07030911030a2105070c08010e15040c06080919080c0d0201060b1207 67
    0x8010b4512180c2c1c0c40f1000081050301130f9091808070f0310060050718006500301211030b03003250b10502c516100082048000300c41e01b02d84080400406001d9521a01039500244001014036900d46151240078103c45c1400c41d10310080d10104200d40200e0b601400000c040da1502880401c00d6120f24546020140e40d030085c241641d4041041c600d07888610ba5011440528040c6110701d02480c2141e028403a030800c2d000d910175440307200c084400041d02501c418091f5030f2041c2c01900144001c5c0c1c048000100300034204108540d05a000c0085c680c8609002c6a1840e22030044c9071f075400c0445e40040039a1407a6050201c078988194500780d1000701840d002e0f192074441c1e030301d00340c0214141c0d105207000da442e815042c08008090081103d440f10011540c1850710f459101d4001d20b40d29031013410309100c2050049405501d061201034840c0000f13050051841020b03103442449640a51000c2a0900401400c0d001091040c01060102d50400000e40d04041c0404c108240111003e440503041c4101c06150701c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 824480431 1250 824479181 824479211
    0x23010302010c03052a0606010201060b040e04021504090203090102030414160513110408030c06090a080702040902040609052e030b0a0b01020a05070b0c06131e02061b010e0d0c0503120406 82
    0x5d0190f0a104016260034280b50740068251041c1b5001601101c1e802d000074041a0001c0450b164010780441d11500d06091901e03036000184200c0c0c020062043c0000100704129805400450045124108228131608400c0d0240d499421030341c01c4040029400804029a01e0040e00d0300c108640c3d4150009601c2d4245000742c82240d00540c04081c0a030808140d00c1c1c4803c10510040303508c1050361015104010f0389a507052480e00c60400c00910507030b550302d040700664699601c50006410030800800450404c4801c40d05060700c08200310200062107050034100340702042c9110211b0390700007400c8909d901e4905c132100242101041460451181110340c1c1d01050007002007400070146101880c1c0e450206411040c10100001c1112417000320307213910900003d81c600c0410044400380001039600340d07071510009115114500e40e000004400100c2102c480406602101104001c07004035188990a000191945070b441440134100c0c2d0001e2000c800760158480c400743d8401c0c030400c0b0000b00300054103103d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 824481681 1250 824480431 824480497
    0xc030d09031208010b070f050715030e0f07060c15140f071b0309090e15010b131e0e1914090606011e03090c0306020d23010302010c0305 60
    0x19000034040c0d48100180000c49003681c429242901d0124015814945203031124840d0b400000d01581181c0201c4080c40800e00500001d01442c403042c5038500003600700100944800d80a400c9075000d176050a85034040c000900404842880e228409507189540b50522100c2850310b091949035200e800c141e5054000d00304162260400954400460030080801030001351580d524000340d50300000b0241c003180d0001d41160480b200b044003c02c100c8498449a13080c452044480300c80c20301e140002241110040019001c0108411040f20358644e0300c510b04000080c0d04105c00d2401180c405051000b40900c2941e15800212620100140c641035003085049590300410300945541c1041402030000d02484041c0e0880c10900e4041b42d0402204042012041c1c034803ca0030505070307183c001c0380130000c841203203400031034001c441103407145001020100500003440e1600000303588000b854400c2d981218099050ba40c0694030798540e000e5940c2e00780d8069004007086880400200303100c040c9085001d1032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 824482931 1250 824481681 824481703
    0x20c12100c081909050307202e0203090a031e150516021c120b0d1506060527060c0d0314010f061205070c140a030e0a12060903020c03 59
    0x311401454203a14110380c0012400036200410b06004e0010b02095000040c1c400d02030f0451040c020781103130205100f0300903260000c283c0e04034542c2320309020742028800300182c48080607140e40c681c0c80d424990407a100c1c8200b003c0c85900c04503822051000c201d280f10809926400d4805039901114151505c69120303a004d0303001030300c030b039251b40420080c161031401c0116101da4a0008001c2e01009150407031a0101741d5896904010f40c0d241002c41c882d030950407400d080d01002c0c085242c01c007440d040c10503400d50b510f000400e00a046c000300241491140c4200d52042c1498983c0c2d40c40074040c0c01d2440007125680c0340056108406000054440006000c0e40c0b092104d2618009501d2095450620b0442c1059100781032080d0307829801c01105801003031440054100f030300000b460b0340e00d928003030381d540c0402800070b0f01505005540e013055200c0000c0030720710329004c3d488414400300402c0030001c601e100c5000c0c000074000e040c80032000280e11354101c10788580c824016a141c04600c1c5010920306000054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 824484181 1250 824482931 824482937
    0x408030d0c030b1513091a01121509050f010e010602033c0304050f010b031905070806070f090902041406031b031005010e0301050105010807120603080d09051c020c12100c 75
    0x1a100d009281d10001e071500900701e440090003070365100000800d1421f99085000d0621080302c2041a1030400c1da4030100982c00c1141c0c00c0e000007071f280c99001005250846a803001d55103010f001080103024240d030f0a0480b00303141d00452619454402102e60611030620500450320013800341c64040601d010040c4188100500e066100d1415003401442c01c4d90f0805a101145d00d490180f100680b8040b9044048000c6903003500a40c03c1c903440c0003032400c01164010405c0e030050030244030307095600c849404594011965007521890300e807040701040744620700ca9402c880c100d03060390452a080ca0006544d002d02d00b02401c2c800c6031600d40e170481c0300b40e0040380c0c6642c15000c1e005040c400d560b00640c1d071941c54881a40204029070400e4000780001d400541080140805100700b10308000391900b01d140595800549145c45176072106100d409000b004900b2100343c0244d410300d09400e032010010b21851030003075000f000304190b03000602c141c0c507500039440400da016882f540e400460341c5004203100c0d002c46035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 824485431 1250 824484181 824484187
    0x1605130b060f0a170105010503060d0c0504020703090302030706210b0607061b0215040b0406050415020c0601050126070806010203040803030c1201080f030409021303050d08010801110408030d0c030b15 88
    0x30f0003044001d21072041900c036010000140b000d40d030b000d000c2e01e41c0b00005440c0000e1911030381c02c15203136880150741304036800b500014460041650160074071007207910079011203500f02d0310b404003545c80000e06041c1c2684890030307000000741c940709504052903200d0090800c07031810301140c480394291545108001e0500030000c5034840070550400003640003080c141c502c1d0089040640d035542d01c8410181002d8001600c0d04046410702455050500601c10990421551000c030084807689604d024401c1c10701140101c001e42000c1485402e50001c1c820252008951507500c2070b50699042c04003a000b541148000c0c880411092002c0000314051508000110703151051807042000fa8403058010391001c0d008138100c09039845000040e00e00f40c4201a0300561100e80b0244c42454842d05a4809426442611005600c1d9500400c03c14142d40b080340007030154130b6042c0401c6140384268440c0f00c03030130361040224202c82d0003e64000e0303025940c10b24001c104100702100003042440d03510b0240600c04000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 824486681 1250 824485431 824485447
    0x607020a0507050f0307140f182a030a050403050f0d1e1104060503062b060e0105071d04112704060605090d060e0d0f0801081605130b060f 61
    0x8100a0008000484010310083c6491000c06c0e2182c08030311071003030341041c400348102c490381d01c8070071000303007500050702d0040c20350191075001c0d045800c144e030110b10000d0706000f400601e2079040701d07034101c44018844032481c580b50710b2514001848001c0059081190038045201c012509e00300424030060b4148010460022a01030b491082804045408102d45840003d4409103c0b490079601140d2031420000c0d1260307185004180c009071001c40045c5150302e01e050300385a14070700c04101420766015960030400c101e0b801d11018220354094402c0d10210f1140f510354405401c4c0707030501051741c110150010940c00c5400c4803204841d0440d000c48400819039401490465002117804801c11908490501c280b0f450010094214071802c1401400f84800c01080310510030103030807003110015260300700c4050380a07003040101140c003121903030b00001307294100018038040c00049400e0240d10070b000144100345007208010701090030192807201d243d219060b60360a55501005801e4000030480516520128 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 824487931 1250 824486681 824486683
    0x409150b031e1c020703172a0309100c060f140f010303090b070602070b010609180203040b061c0b0705040603050f071d01050909040f0c0602030304030e010309060e0607020a05 77
    0x101441c0b414080203807401c00030740e2400015400b82d0200045070680707007030103040d00200c2c18482c0316040075102c01000c800070340010365080000c000705103180d403103096010a4103420310008900c2c1481c1200760b501c180402c10144ca0301402081d0200c090341403209009419a07104416203c1c5030707880c072000f5540c4100040500c01e141032529801911905005d010b50304541c0c020700b240145003d000c45a00000ca005c80420803a070b412244840e4003d9004050366941d0031000780aa0b401c1e004902e852410401d06080c1c81c0400d0007900d0013180c5c0032030700b040e040d61100d05000032505a1440d48885141e2100041c0c081040000031070b0044181d944c4565a850800e84084c040d61406001d581120340310400300400c00703600c08565800300750003010107441c040e0303041c00407240ea020b50116031713500601410600c010415002e5005801c9445600080312203941c990080c2d803a40011a406804a0514075400c00c580d8840e80c040e280c26071040348001040280360324070a1500c68111800f901580c4041300004c14460 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 824489181 1250 824487931 824487943
    0x40f06090b01180311060714060601110109020904020603071b140606100c03080924090c03010c0f08040503040306050a0203070e120a0602280f0e010807080f04020409150b03 76
    0x2001c0c20070f845040c4414142905007010ba22000e0200c425140e402a25641c55104803080c0300c2c0c1240d40c524103104500c1450392115015179040b8040380350403080b805004018011445c106070000c10400141e541c2e6000c0c40304030360008052404100c45610048110360b40f1450420751503005550f039001c038000e051252803030100c0240661344942c81034901450301c41e81c4401c401c8400d0754540341c01c412325281c41504c41d2601d807842c2c21000c504107580d240d5415240c160034055104031102e500b11081800340c45e080c50f080714103140015000584100c42010850700810100e40c01c01c0c031510450303180c143c1c0c0383c80350412a2001c3c0c6002c00f40580020a200182c0d42c000c0190b100c0c0d010842d080c034020884000195522801240002c0080780c0116900b10407405c41c0d042c1440900c100c0103410882c54010500801c200c407100c410a001c180b128104070419440382c14039038800d18041e100c0300d4168803400d60098a0440080041344d020342c544503d6800541c40c41075100f8a440840804180580e0400800d07080c90 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 824490431 1250 824489181 824489201
    0x237030b01030911120a0b090d0206010f08070e070e0d0812060a05060a0e06120702070e0f0f1306020c151503151f081510081603120905040f0609 64
    0x1030410401c070021503280c003407010300d1460403240c00481c00d20f003200300c1b0304001802101901c1f9807607840c200301c0c82003c041403008000d0343d240d083e91156a203421794154107016501908855520034182840254001092035821a030a07050040c1c00b481001c0002c3c1c5103255250b021544d1900c0401c46903200180c012030b080d040441110450101428400410228026081d0a0080140502c00c18005899040c01c5030300c414011041c0b0f0141d03141810019540f0f40d018864080c805508000180b8940f0a07000b40a02401c250100a00c440d00c44c101a0041c0c10300c00b40d801d039413182d400c019a0071070344800c105802103003040211240c62844d0074030513804200494120103001ea0006040c45202002a00e00c2c0c584c0401e0503480385132002510390450b06070142c903400c0703001c080c8a40c036100050683c01803207552003840341c2101c0024854984004c10b403190100034000c01f0140315440240002003607030084286000c07032450b043c0d1460703a83d12300103025500c0c1d2644500c1002c0d40c840302801070404a01030040c1c81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 824491681 1250 824490431 824490437
    0x717070609061b02303c0a080f04150e160906030506010314070f030f0b100b090d1e0807060b0906061603050f07030503060918100237030b01 62
    0x160304c001c20400340d1050900301800f9822081c20603003002e41c41c00060342c0b038030320b004100500203601102d4034107800d5610314100207604120030451b501000440c01103419400165032051f140f62a045242d4007000000341080302c2e20040c6c04904040500c2c07501c42c500c8509050340040059858098090713203401002d401200c0c840c0d0802e0741c180045580000c015044030f0b030243c1c0b072261100030100d10a0512000d90803c03100f08564034000400e00c400d03103110016071401001c3c032070415103520001d00c58440384c074400c4040b1218103011480e410305d8403681c1e59038254001c4000450040d0b100c00009041001034408650700080812440280140fa00c100540d44d40161510038050030800300290281c040c0c00100320072032031000920010107120301c0a4034042071803020020f48520a41c580507000d9002181c006000b420510002180f030f0030441500f006408000010b03000c1c20628115400182d88a0440d045604cc075221b81c00701da5940d0b426034018041610b2042840c40100d15070000d080d125404001410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 824492931 1250 824491681 824491693
    0xa0f23160219020a090c091406130e13021c0303060e010f120311030a03051f0e151f0804170a0e040506040b0909010f200717070609061b02 61
    0x140580005414821012108101c100b0403a2440001d50510458104280443c1080c0746100c440342c0051111050b82d00d1510904140304215051120500030f814040c07032541d05a0801300001c00c100842c190f0400c011441508160685801003990002a04512a0070010324140f84040c1035240c45044003a09c2c011039007026075403419000c0310680c90103029100f9106440c07280311040501421051030b0345010034040d00d4581d015580c0c0500100811030320111010100c041038503088030508070172811b46201c014840056214242101195000c0180064106503800e03110051b5400710028118042d01030f5a6000c4246403500c0c051122800300ea10a0030251405d00c0101d440980100d205500c000081d140050389660328030004010704598111a60405295000c3c040b0009042d0411040f03030010900620036032541c18035a007144020048440c7e41c00005100030000500740118401304402059821400c2400d140c44801c121a1400320440d03280740e58120940e0080703a049100045407000c0c4c006011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 824494181 1250 824492931 824492971
    0x507080d060308092d06031f08030403020a051f110f100504112b0309170a0b0601091802090a051302180603090a230a0303050f010504021306080a0f23 66
    0x516081c4843d021740c80b50300c0110000300b0500d0800c001480c044240308040301000e03078800d07060740c03079030f100d40000d0707010b046030303443c04106420441e6802e0284446499096600300141508803000600c00c111a1014081c100c00103020030000c024a0343e818010981c00111403d052500351000c04d10000c28a0050034201800c03064000e08c0c0e0008501420f0100d1605c2c0103101900d800c4581d4090350b006030700d01c81541c01080c40800700010383d043d0030a104503460a8a501c83d9001520750f00c03841c2c45038590080860102c40b00348802500540004500035020000841e00c90380041c0200d900304905100d080d40c00701e0924561407202111003c000c0c003c0c9c841929609060700525250110341c00003800140c0e2445440c0c601c4004410040203120703405003620034440c2d2038680100903106c146c80e0550306500c14800030419282500c201c5880114220200d83c0d024901141076586881c02485090f007103544544c287d20300e0034a4050501600307412072640e1041140380060144101001c2d0070110140340c14441c5407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 824495431 1250 824494181 824494249
    0x4060b100e0a081c0e01090e0115092126030415050601030204030b060d03020f0709060e150a03030f02010b180f1503031e09150c0f0d0206070507080d06030809 70
    0x10801c4c268980080424040c40059684950980c02428442e80c3c1e2800000c1e2030821580710500c400301380c2d41e41a4981d640320b04c07a001c1e6008010306030703c100e690b00000314000361080540c02030410150328429100d580c90001c003c12500200e0301a50001850749000001e003045110303069000d607090030210305190030f40c0c55030034516000401503402400f0141e12902407600030024203100745104c03411142c51688440760080074100503c039525501d581c81c008034028080e8010340043da41e50180076401500c1c80c6071411100421102180410f43d50784500404881e1180340809400380c001c003005c1d100906060f8409160284003e040c0000e170f81d40e090800820781d40200031034810b503c1044181d40c228114018400e410320402c2c0503a03074403104a030074000d00c440d41d000c05002021048025035031751442d00e201c42615050591030400058202c00c0000303181c00c1c0201d020f00940f9001d00d0b00c450a000c40f081d0341100719000c0b82c109031000980402c04001c40d29240b59002201800103040030b0407026000c0c01c034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 824496681 1250 824495431 824495473
    0x1201030803190c03150906051f1202040f0f0e0402010903080c010b0d050c0405092e0b04090302060a060b16061a0a090e0d0f05030f04060b100e0a08 65
    0x200210350000c0030070b100d04040b2010551a10711000e0401050110364009002407880058005412840c1c07080080c030382c4094800d4104983c005400d0700d80f01d410b4103032442261031a103410340c0c0a00401da1622100f600b51413000c0c101800404158401440c18240780380c1a001c5190701003403440726410200401030340e105441c41d080704c1c0e01290407501d4012103a000c50141c8000b240542d003040ac0b00c00142c0a00c580017030740510003107090310704001a07118086d01c0c640f145c5900c0403d500d40401e8551200d400b940404040c00400000280007500c100c145000070191942c2000940069000790140b04900d0034600c81d800c01890079802443c90400c4d65071800744a55451440508003690b9100040d01c3d2b00c124900030964540c0080480b2280390712190030000404012005008500c07a9101180b011342c040c004215040c4003c0d00ca0070b0940c2d41e205004404520010002c4420710340b40d90b0800120303256401005418021615850301d0352200da400d00c440260194070014290b0300c0601d1490807a8490064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 824497931 1250 824496681 824496683
    0x7020c130c1232060f0108040305120907030b0108061806060f0105181207081002090105030a090312020c07180924090b0c19080603060c090d05030d0e12120103 70
    0x105500c03d14402c411141c40d80c80c0c0c4421000422a094281c0e4190120422485044100d500301c44588101c0700440f40d440781110018003050b000c10612a081c1845407020781d000e286001101c1a49407642c4e1201c403d42c401707a101071510351100d0700b4030104041c120100305030384202d031000380f68900d000c0c00051102240d80b94140d0500c00300140002141c2c80d0300700150354521018140403840e03131030038206a641354224481d09510303020f03170804031002e031402d4001c070344041505a4450b42140c4420050070020701c0722140840621052001441c0440c019001a082d541c60001c040c00d11941f4100c621038890300e08040c2c03402520302e0301c00081c00081c6052075948580d0941d406009002556001c1c3e04010700e0f000802030200854241000003a001950080c2002e40160002d4001504046000d07a0110019a000b99058000c50001562200768601510f1214002402002c3d000c00c01d480b039508540c0100c003002581c9480311524140c6d54010406000045041c0020920303100c10450034003100003041c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 824499181 1250 824497931 824497967
    0xc0409050c04110a0f0309020904111809030901090509010e040605100b121e0405070608130602120106180e0c0d0603060c23070305071e050607020c130c 67
    0x110010320030108110240104050b0003004a40d440d00c01c004010303002403141e1400608101001000517101e40180821980c0c088c25441c49600c0390703507a1003282c0102890403a0406240c501c00144a00100084e6020b051507601a59403081418001003110402e600124003a2000c1c00c01000003d00c031098050f4040e802000c002400d466560984540c141c142d8826100c0050104201c0003078081e0a1341940104556007404001240030440104001e41c1280c002d03100d03410000e010004940034900745036010841054810070501a99103042c103e070405618190816600d20041c40100d400c540f40505554025281c0d0301c0e43e910b0032451000c0903000a204600281c0c000c52048100c20540e000b410185a018000f4001c842c80c00301c0c010702200f50410012202005454028a8283c50004542c6455003643d100c0b442c0c0b075080c2e211521400615510340080810308400080458000c0c41124090b61840e030161142040703180170012144040412081304074545030f000b5181c0c036040056040308080b005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 824500431 1250 824499181 824499191
    0xc0605060a030506040c090506045a0b0909100c05120901021e04060c02040b0d06110d0f2705010e0708030a090b070b06010804050a12030b1e030c04 65
    0x30003190544400754001003080c49014140400c02034040181130030f41300c40d11002c11540e40d0b08004c20003031300c9441049204040303200038900039116014003016450f10412601c040084100000414505440c1704500b10004894a0010040b1424002c8600d2050708644503003180c1010a41d66440f02c08010b2003240859135200050143c03400b600540e589454801e200d20f510745400c040c1d035400703540250340c500503000f10b00411018a095180a840595050381d907650015020782e0700b48402803030854052640403850700c20020002e0045e0046542503c40c1c50030894807030403924111800d81d8040058032a003e8203000b821060a0303048403001221114003a44c140d014003d40c02c01900404110500c0030007030151080201d06101b0020040c018000c1c69920345071010b9448010416600902c0001401c42d000c40d004248158410020a40c000e0300070f00558803a40441d5a8034069010941f1034600400d4444006c040c1a2421500c0f1005101c0001710f03050f001d0002100081d11800b140004e5840b4903070700c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 824501681 1250 824500431 824500441
    0x30318100903080d06080c100206010b0a020a06090311070f05090705090f1f090506120612160e0f16021e0a0203010e0c03071d07050d0e030d06090b010207060c0605 72
    0xe00d0308500943d004200f00340d0361680c010003a409080c80340244880c6104003a003a020350304107010548410040c5038081c01869080c000c5540c1e031070b4817025041701144520400c40c0040703021841614031170740c801d8803503107001d03020411031904100c0c0c254003589052981410401040d103848480325840b40d110f01c0c00703d50740d0f00c240c00056040c0c0b5000c421139030030154031444108c40340003095032032450000d50b80f10282420365900030404248682d586c610600c3e0f16000118100b8144200300001e0603007044261607403441703481408031400301c0580c000d12105c0c45c142c00b40301d40c21006441598002c9007043d9071070311000180a010355201d13010325840c54100d8141c00e180000f440d080c491966101d1340207000384025908081415a102485880540300740078200002844d50100300347d0301104920b40040c8000c5586c3c503082030f1600d0304004017420015840f03d0001401103000e00c007c2260401b8003000044c0359041c549407a040710030310a8140d05540c8414403c0c0481900501d03420b0381c0d65032009011520b5610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 824502931 1250 824501681 824501687
    0xa0204050705160c030b0603120706110712051207030204030809010f110d021c0306150507050102310b03010b04050f0607051e010f0506010f0f170106170603031810 72
    0x5405045400c0d083d8141180304014003104080c084034003d034400d50007503c84604160301c607449159001e05000c81000600c0010b400ca81182d007410405600306400c002258032410318000080aa000001e000020f480300d40d42c05440d12260042e030b141c40e0442c1098196a140c010b14401c5034a0780b070600c100216100021480345180000221003101a11188140d441010b07584070062001505001141148d64144910a101b0b240403500000c440f910710382e101941c10348141d8444c000569855400708581d041602001d040034285000100c00c0c07400711101c01c01e142c4981171a9801000c0c0740340081004010b454414415101503600c12501c480450860030300207078080c810404001c1040c050854009030001441c0415011000020000c3c400310006106401c21100121000760200302034178240d81070240700e401c202d0782c10303000341c10107800c0044107820984500078240d12600c0021219158500b1142c146111035801103019402142415030a0120403003006030007903401c0c0520f98001904a1280c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 824504181 1250 824502931 824502937
    0x5090301110a031418030a08070324050112090803070e010306030c0b09192318010b21010e0121060606051b1915090206040b0703030c110a0204050705 66
    0x76603241601d40c1c0309120300002e0301808540000541c00516a07000808404001c080c4e0510746001d04080c515011070700380c0a03500d03414003410203010503640e0206c0c02c1c1045c41030b60742460840a800160f410b03545c0340400040c00350b5400c00d00c0140090521f0380c0321002800401c15284c04c04440c1c20110b03881c03540740c40101c00070016503101030030f810b041041c0021113180a6000344205141501c03c0c0c65440c00540c1d4550008403140f24285046101090701114120008003070440618024600d50700301030702c1064540445400e03001200c6c81040040c0700103031002e56070a045c034003055000385090310758035102c08404070300414459000c000a0400a14010a0418100700c4038294060b400300003017502c6900c000c0080d0041c25801010440e032100040c43d0060001c0e01310a05010ba038500f900244680c1d4803600620401401c07922203d4031031a0703410050b66203c000d080a0410320804680b0380d0040d00b801000e0703035132150040c0306100352194541d10701c60000c18507400c41c580688001c1890f480d040d008940c03c2c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 824505431 1250 824504181 824504201
    0x15050a0f0e12032802070e1609090f0b030c30010908030c0403050706030203090c13020d020c0c0f10080103061a040c0c05070501030507050403110d02090403050301081504021005090301 81
    0x30100041003424150a00749010300c40e455940c0b130002c0d9248291040c4c1c1d030350b2000e00841b1443c10303501e00011402ca1103888940c0c0d004c0001c1c80e0821120b9510b030b41c030606444411004000b03003900e0b6850040942820440d00d000d6000403140e1800b550004d40e0b1b00b08465904191840c1000c0e02c0041039041c4072001d402100c0c8032680300c0070541c0c1d2458404d2424013143c2007400100c44500a000000a50521900a89009071100030181c46901000420041011840354641e026150240038283d808a0f05102400d04004014082c281d1425000708000a10803250fa9862107401c080e10740d8025203070720004c91030540380e0000f0002141c072100311001e00c0710f60000c00e02c154089d0601c00c000742d2441e44004280c01d454891800c8904990700da100542c00d440d000c84001002590a010420203c4c0c800c121407800d5810140c94480805d2494012988601040f00c0070b402043d00040108030100c41013204604005812441c99642d040c241e00140500d1007608440040210210b4449001d0341c081d0322100c0c6c41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 824506681 1250 824505431 824505433
    0x1410260a14150604061a09010c06110a1b17030a1514011e1d180f04051501050d06020325020105090c0108010503070e07021207060615050a0f0e12 64
    0x52201c900304a40c0e00c01c00400c614030704060550125007982030034041c0740180da6081400d406481031348015039841c0c1d089940800d04002c29582d0001c08150f2600c214414030903401905a5191044c5030041d264041000d101d282c4c00e085900041d0210f541480d200403040c0c01441c03c65900e482e00141d0743c000d40040c105495650700903110020300c021620442000900003a240c007005000c0d83c080300e110000a85400c0400314156031006c10300c3c01880c5c024a501c10000400c894410540860520342614049440c1d40503e0f400d5800d00050040c208090041180045101401d540c10540414202e1810400080030320b03401101140790341e080315070500555004240c000c4911440017000a000c0e200540e0030700320780d0003a511200034030f5200f114002c3c107031500640201000c0307240140c01c2c81b2002d0001c200e4011401072108100341ca80c0408000c043d024000e460200709182810001c01181d400000880140503003045901c003001d802c80400c0e00c1c090154108601c05a0890001c80d40d80703240b55892201c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 824507931 1250 824506681 824506703
    0x7050f0a02150a05060d02090c040b0f090316150c020d020306070210061a07020d11091f05091302090411060c0a0507060c020a03110102100f1410260a 66
    0x289039400180d07960491010b0680690544030114500d00b259400d607807040d04140001c1c1d00001500b03108500903000113010b1003c0b4600356480510700300c107401c98003c00d81e0800001540600601e42080381a03d04481d5805804215141c900c0a900c01d5031001c14400070b110203002994295a2030700303c3c2e00111a0007a0944105142540380292034584102420240c186880030214041505100c20103100b44420b901e145060704e03940821000004020003114030440404800b1415100c0c104a540502800845020100040c0007010424038158000c2d40c090407000080000c4140c2e0964400d21640e019110a030f06c80c3c03a2400c0444001018900b1207820010008030048040c800003a0031107000d0040d001d8860094490341d045401c0d10341c01c100603501c100c00301c90900210300c040b4581454140140126103102c2c0f814513005069840340005402d40d960743c0c0e50425542d080c005800c80d0300811140910207640d0400c4048a400a896100d141c1d5401104141070703800001000ba5101098200300e400c0e03c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 824509181 1250 824507931 824507947
    0x309050a0f0b06090c030903120603011503141c1b0615180b06030106020c1c020a120302010c111902060909090106030c0801020c0601090b01170c040807050d02130507050f 75
    0x581a009540c404d0180300790500081100707100c03005890007142440f020b036140c8814804084070094020b40f0055045d5030340c450024401409502c0b41c4001c5104100d026081c282c0d503001641404078940c070b0118994030b000d042d0341b0321503030004103424203052003186138202409506181d0300a03e840840c00038161161100801e440c00392148141d080310000c0003d01003580010305002c054002885420003603072000c44034a100c0e00d0700b40c03850754003560280c818081c0c0e10350580007e10744c1c040e00c0c1d01a0350111031051180041c554203009510360090703541080070744504c00c030186550707c2104031403140c2181c0000d201d8804540d82e400071145400c81c01011301c0d07840d013494828140242a9844200c800300002c450010b540c4006009031004c41c280100504a242c0c2b03407070603010280c0403180c1c1080c108024a4040c203a45c92581c1c5007280114681400f454403103081c808541d00c3d015039500907a2003212184100e2005a48003104103148411401e00803405031102e650546d400d018480202c0052040403c8103c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 824510431 1250 824509181 824509193
    0x80a090506010e180a0209040605190603210201050709051e0a2c01030f080d02040302090f06030615060f0a02160b191b030e030f010212010f09020310060309050a0f 72
    0x907020358904100d4101900310072042640c0c2c0d041007217000790818403000018000c142954412644036041403100a070282000000f5800c4445a40040340c02000d08407201610050307512440c1c0c084889800200301c2d6040c546005040c50415100f4030b481400c0b42c02007010030800b41102c5040038030010307064509507a2206181e02d0684a0001c000d51950034a102070034035000409400c60480c0c6d08110346d4a40390a40e44c40c4c1019513070160403400c00150f020040040107031101c40103140300c0d20500314110214204082014180200600081243c005143c84110306a0340c00040303c05041740b015185550f00c405440a80c2424041c03140001f80030b440110001e8010f982c48000d20034003102180c3c10700c2141c1e807540c0644410119240c070340701105400c2d0041002a00a60b006201c820001b4111003282d0b180010003070999000940065580d4010b6004000c00128085a0380240c20180c03015030030751420030303005c4005800c0751040c2c108158035070100e10280070703040c0280a00d4179000303a5101078600c1c00303003040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 824511681 1250 824510431 824510459
    0xf060f050f01032105041d04060f02191202070215030402040501090b100809010603080a090e3d2c01080109110d03050706050103111c1205070c08030301060306080f06010f0501080a09050601 83
    0x156927031810034044000b1031055108984403180c882e14015948101490201c81d04100c165003084481d5082150002680d1016450044404204411030b45c81c90284140801c0d2103040c1e002100190800e8951040c1c1e075140001a00f240015141c40c0d10306986003650300780981035a40c0b004d0203103240007805008282c0d0080841c010f45003d2086000c0549032210680000d4810840c8264913030290005440b1940512040310243c0240054131111309440381d000d51700030821042d2410408841d0204910160440701c0824010840e240003000411610b880e00c0401070b6003521360602c01c0e03520074101d40c1054011000d0311200c1c0e4101c0800c008640e164500221122924266140b09680c49020388096080e4075480320310740d0347e01480034941250030070000c1c0d44940080400f1250480f0044000c00c100c1c0c4104040e5009207407594003c00c0300c52914041d0350a0081001020907150409401444107540f5124100116082813809a000d80c4d60a01c422000700380021004109000c0c04000240d0340c0451104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 824512931 1250 824511681 824511683
    0x10b09030d090305030714100606030c02101a0d03021504031808060702150c0f070620030108032a0a0b0601300c05070f060f050f01032105041d04 64
    0x1c6441021150605403000c08141c80002c20b41da01c01c100c22400503800700f140240c0b90b1a9030b000c13924007210315510b03913040c7e5040e6004280000e55441c11416050b504100b0908003800c050001c00184611401040e07901c3c0008500e2401000c8500e1444100f610030841d602c0000c041d01d184100c50305080c03500074a520f0380091021881c1c041031001142415000c22400d000d4041c9400610806000088414a45100a181010582050108280399a5000000d1000c41d101e0a00082c0ca00000c160070306860103042c80710000d404091005004c0c1040000469030349a01801140c6031810041295030340d2100030082c1d80006001d03408115013009184c2104901845003605d401c80041c241c4d001e20308003c4c0707546080c58409201260a0302441641d648500e111142c14a800303490b09881c1e40341c142e0b1b000c8a10f40126150381d9500851140c8880510400f1740115240710700d825203502d1605c0348c5100301d030b845040e6980c901c2c4080360040101d002314202c4008242031074030483c9541c036181003044804801c50b8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 824514181 1250 824512931 824512933
    0x12010303080a0b0a06020d0c1e0305030f09030307140d0209061b0120090108060a150206241503060a03060509010e25060513030b0a06061806050f0f12010b0903 70
    0xd5001e510f413500d00030040a540f259401402070900c58801100c7d0703404900d40a440f010280505028800d6944030010b08890203903c41d99500c0c00c0c0340b88407a00c10100100361640507082032040c00001e42d03003c91010700c4002000441d030b4540150706540b800900c41d84180d03541c410360000c0c000b09115004107040e00700380e007104001c015240040d00b6a018403614032050f41d8181c0c10420004c040c0b03601400f200c5400c10005032010302442e448404204528000d2041d100141e4004020442030700d107502403203145203d0103804900b0803225200407927841e00348944800019500440080c1d040d0300c82d100700c01d00464005805214505204900a008106401255a050080324004001411080310119410414500124861740341800403242d64003c0680c0408402118200101190414601c2c90182c8461000000d9a520b0b180000d000c118041840c034031507080c200020070405800000b0303218421681002599140e0b007502101d801742c81200b2003403181d041d9820000c15a500c03c0350250140540c00c2d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 824515431 1250 824514181 824514191
    0x302030903101a010905060d0f060801020d02040e090a080403061d250902040f05150c01020301090c120e06070f0c0b01030c050111030712030207020a081509060703060503120f12010303080a 83
    0x83c01141c0b070784450f0180582100040002081046603584407a1020344032100000300325032181142800daa0058155040c00d0340c010a0521076200c003002c900c2d4014052070000c03c104001c07566242d60310300851201800e076956a440b5400c1030246c580802d442c1c03111000580b240c0100d2002e01101c4924020b0b8103001082c2c50590104043e452403080b102a00c2000311038414840c9070204110301c51103280c205006500c028056002c5a1000340080c60103405905c2001c01c2c1d040080b400101229192901108498106114250000d001140340c980040044c6046400061001d10644030803074400d500411720000940004213210792a0015400c0c0c507000d0340c500c500d401c0b00341030700303543c901178510050498901103950001c018007a500805041d0300c003074140d009880d41e0341d10a82c1000300950b940c291102c15030042156401c0180303e0554010250709041081c40e04141c003003075070b5070110800a000c40030f00190004444a10000f40d41001c500040e2140083d0b8491038003c0080d1803e403412038050b4209 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 824516681 1250 824515431 824515481
    0x604180f03030623031515060403080306030d0509131d0a08031b07050714040b0d11010f081b030c0403061d4e0c0d081608070c030203090310 62
    0x10700c112944960017401450f44d16009140c010145001901c480329120070034400d0b0250303031562400b43c0001c5009005450310313850000c050500340021007000c402002800c00542200b5903811852010592030502c002a41c80302c0e10400e00c030f01e000d002c1c850123850300c18009501308110f541b0004510541c2c0740591407021280e0101c00e0680c0d03004c1e03508014880d4004040600035100146d5a0042030400180081004045040400c4002040d035409446150780c2e00d050a11950b006071790107107102d01c20714101e880c500c0d00e80e1f0010000754011201615030b10001020510108155082da0061600400100703c102c00414000448026000c494042c41c06000700130f6400202c40f10021900821402d0141c0c03100196680115149611040b03400300e02d6071011801074400c8551000e0500c0c2c102d80002826426032aa0000d8102c01c402080c04442c01440504c2c0307116a41e00c040740303d030130900e01e0074140400080c500d816800c60081b61038103601845a2440500c02d82d83c2500301194030f00f00d582e01e00c4414103603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 824517931 1250 824516681 824516729
    0x801140601090b030c04050d0309091a030c010c081c090c0b030c041503020714030a09080316120c0b040c03200306280207080409110408060604180f030306 68
    0xc4886a0218002c0c032820480922044004d51388603020309079213454140c540c2c000a104050512050300090560101481117400d01c1c410320b1034103507548580d141070381c900c41c0010b0b42e2080a0701c0f0890402080110720410810041c0130ba64024071800884099034040c0205500100780000c0306850501c03803418005080501a02203c0c0180c120003810b43c44d0504001014031040645a200e10030103034200044004902c0103101c58a00002000280d555400210801029000750360808150381d00200101d1600d021a1004254055442000010080c0c2410801c0d030310b217215480e002d000748a02c030b02044200f0000f2450300040e2840f403405d220000580003c0040790304912560103030158882c3d004a02002000154030108140d4400c40c00011903500464900342d8104c0306085441500209082c800100c03640200c0803c0b00a2014003400d02d0316106980f55580c07400f40029020b0341d55018100c404250310811001074503000440c58035403004601e0000c004101a20403160b07101c3d02e172040300c580b02035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 824519181 1250 824517931 824517971
    0x150708070e010e06121501030506060c2a0a0e0f070f0e0120030a0804060c020604051b030a0b091606020d0f031116030917061e09070305010f060801 65
    0x941541c840355500301010040d07668625100c0d10382d81c020018407a600100044116044c440c0401743c40030060b0404000000d401c1c1c07800900500e11a42040c00340c0c101c2d600300021a10a60001050034500a490054640c06003000d2203020030340000b81444003051981c0c084c0d4065004405a00c000c5d2003e55400e48110780d984510610800040c10b214041e00003584640717440f8a210100b050b1500f480044011554515402456100b010403001c90420040c03100d03901c104c2504021a0000c0c0050345056034a540d25102c1c100c1c008001c3d2102c200c11103060352401c2000c101d40f5075200c0401c0e040b40c00c190401c0d036a510004010f00f0405585220081032240c03022840b01d0740440b80741c4402084400417201a03001c2c0c1205003401d5190b00003805405500022845503540303450007602c44690315802c0c00340031092009086501d40302035100d00184018402a4403841c41d802c864840c1010450300e0700b15400c1e00713011950380007410660920041041d01c482d00c3c0d10080c2101c000200810426481041e00b400303541d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 824520431 1250 824519181 824519191
    0x1e030312090b070e011103041401020c090f19060929040b0a060f0c0506100f080601061b030c2a080705181015050a1b170a120e150708 59
    0x42c00740011840d0180a194080012079050521610300d00000004074550307081940000d4404c6404d0302c0014042d601884002039003c4140d824044501c2c2c491880080320700d014050500a29404a84100c9020207500500282c42021000d2041d84020070112400340c0595070100407024040f0400341d0b00340382074440c003401010045c180c8508645498029144400b099035191705000c0c181c2c12107400510b042c0030745845400032019845c0c81707900b8065000c4861400d6040070560341d000380c0040c000c041c2c00904aa0082444401075040180c0b03d14040b52502001e050051140a0f1099a104100e0014030458501c050b0f03102d030300c16516a100071031680c40d80e0b03d10038150400642d2403010360786000e08907481c0d4049040c1c00107405a0f503803141911041840482c881001480c00710310031403956030000048520040051060702008001e489103c2400741040070b910f050400001d071096400d000d150482c8100041c00010011041000f02c2580c81d604403001a00e0404510000102d5003401902c0c1a4000c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 824521681 1250 824520431 824520443
    0x123030a03030b06040f150809030703090308030604380102070e0a02031e070c020a05100e01111204120b07051e07030c060c0518030f0a0605101e03031209 68
    0xd103041d031000d8004026080c80305401040411001c510340f0400c00840008201020f9500b003850020b410040900c0805000001d064004210032404250b0007024001580d4000000d40c0d917070303110f40001034010012003401d07032402e040444a5000c000748000002014042c42c21402c0003510b10440120386881142c043c100c0d1184507400030806c0340c6082c2d405141e001843d0644541005105030380c403035100b602100c11100280760942647c0440c10000c6200c8000c03d0195443c00740607160440c050710f000c0a003130000c4e04100c2d0340ea09039003150b0341c10007200c01c644846111980e6150385074689200f6111050758142c40011084001c6011988500112000600046e070361a6000c07060200c00300440d40070310801d0b030400c90f1890b943c00c0822010b220300c00d1002800d0703d400303070703242079120f2a07615440f20034107082d119030821062a00e04101c00301e2409900e80d03100038000703540d40d00d10340681940170707590300900b8581200034002401116040b240c0404d89019858035801880146000310542d45851002812 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 824522931 1250 824521681 824521693
    0x20406230705010501030b0414010204030b04060e0c0a0f0f14030303180a050d0801080c04270501091502030103050f01090c03020d020402090d2111030a1404080312012303 75
    0x84450304031440540d420080311149400394603180c00342503c0e070a82041e21150661014401001700f0700b54521043c00503000203500302031450f02c644401a40050026028580392094004400c00c2800310032000078004007004100b544501440d00d0603c154003884d41c1c00704148001103005030800c00761242401006000b94030b155034900070711080c50001d540450300c030321615a003000056000d1110550b5903005541d06006503140080c0c50b860050b04503181401185002112880890404c0e0f980d1180c041910804003034810b145411030040070b014002030070072488000d00c501c0443c150780096040741e000c2c10484060300c3d5022000b508030341103982c006025207c002d00420060510041c80100d140c001080181440b40789000701e5040c4682e21800c548485c502e0f03605451a4044519512540280c1c1c60684203082040c54169942d00c41d04403080f0610000400c01d40c1e0000180048502802c00b034000e03680c5440c081135452083c0d401c02c1c0904114035601c1c0100000048588800c045d00c041c1c01002418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 824524181 1250 824522931 824522957
    0x6020c06090d240501090906180c03080f040b0f0702090f0903040614040e04060b100c0c05040203060604121101230307180b0c06150a050d0b063709020406 68
    0x3045411503078107543c0c00005074400c030b036140d00c81d84182e9000740125100416a8000c5150500c100d071145890700503086c921079210004200b1842514007030303035808008a50355142c0c1040840050213940c2c0b0810541000040700d2042c94a82805016540c1c801d840091041c1c035800c50001498004960f81102a8401d000820005116444624007000100300c0207141c1a1108481076020904440c00d507211034a800800106043c503d1403a686d44125150015110041d0b545844803500c8134460144129004004580143e80314001c80d002000c90380144420034501d03117401c44500b00c0c8200040e020a4002038880381c0003511050340c6040100302c24070b00d80b4695800340c0a5801d4004003180c062680303503400000c01c2028810000381303c0076400b540148400d1405503c1c40250344040e4130124041c40101c582042261248101600341562100340b200d0a07640700d10116500c030700318605c01100000a041c00d401030b005c00707000810030001440c441c41c4016441c0c0a402050b80700c0d9110b42c1c0f00089401400354 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 824525431 1250 824524181 824524193
    0x30304122a03030f090b0a200f0303190501060912030c031106100806010b090a120510110a02060a052a0f04030303140703060e011401050d0509030406020c06090d 71
    0x6a24620407050150092032040710880403030a10303400460202e1030000702e0080c1e154115090500500380c0300c601611708003d24000800c940c011007407071031286a400018895820060201c401c45050990442c2d8036860001d0200000340c2105400c60340481c42d00f0b00102d5201d1280c18001c06a5456402e040009880e90350100c3d038102d40410305a0070010700156000314400d047c818540550b244010a4403c60b0524107181d06001040c0d01c0080da4100420841c48640c41303000d40081150000c5064501514240c04c215060411084624964510b48a1900e5104003014064400c104141d801c607406c40c0c1d03440c0d0443c01214410390740c10703480d9601d01e031010740060142c100070300b045400d264060303042240b0700b800c0d01c0060b0803c2d001140401c0d180c0001d5165445000030303440d4800d45a01d000d0050529000234180345d06018050340707000b9800c800806403164040e80881e400260800c408001e036103009444603442742c01ca070013070700c005015100105645141c84002da0b0910b400051004040c040155501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 824526681 1250 824525431 824525453
    0x90503032e030c051e030d05030a0b01080f01060c150c020a061413061a131a010f0503070f11100e120c150a0e06101406030903030f040503090402040801061403030412 73
    0x540c1c01174411041111a80741072159040072001510f5507a264100410000b043e6018003005034104049d07241002180d10b0b256200074110f4541d803c0003601240542000060401c49a40d090b07101814410b0040710755a0010f5184825400341d031082048103070020900e601d4550030760320800da4440c8543c2880226605a0040300b00c0b0034003441e800286d2a40e5400300d400650703c81c170307801250707030350b4007c44101c14082c005c40c40020300003440c060a412280b0325000c4c3c4280005000c4508019940b01c510305200e0003804004079003410740088900068194401e41e0140284224251550090b25943c0c80f1080001060f1200910840050113905c11400390304559240020101c4410039280c1003a0014408140151406803803802c08405a0b18148201e6400b411640c001c0c10740601400c1040190008000c400c4d80c1d00300c4510905060079803901d0810b945540182a5041d034006d200080c000b9a64005600840c111071340c489210481012500400d80c503030050380b10f032600e403280b00b0841c00300287d444003076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 824527931 1250 824526681 824526709
    0x5060f09032b03141506160606030203010507020a050a1119030b0a060602011e360b0f0606040e04020d050102220b1303150219050c1603051f090503032e030c05 70
    0x141000c0d81602c203111059805001507501d556127080c28410744c2000c0c003646500c0641d03030000b086088032a64030780350b0b2001c6114018101126030a021070640e40c030a0045000000b070012607280498403418203e41e4200c2c01c3d100c44910514100e40020014018000c280c64100d2a103088560064207407002c1d1b01601d40c2071a011b4400024202d04e8000948126111070b074440601e64049071543c0034502405415406005c610010241034200002c5039100c0c4c08a03010b480d214402080a0344541c408108554221503005000b54000704000c0110b4107031f08090078010704140300b942c3c05542d0b110030404541c490312608940c550140001440400e10111040100c4042e656005140680d049084401504a81405000140d0001c1c0c104844082000081454804a042106c03001e2440e42c42a81d075807460340300150490b40c099129610713401581d00503500702d500407050740d5407450200c0c07038845c000360921008902420440710003801803500080d0001030301e03808118002d02605050400c0103244130946 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 824529181 1250 824527931 824527939
    0x15060a0b0c070801051f0b03010e040f061d160b070b0408090a08100c03050708060d200301022208060405101a040216020109080c0a05060f09032b031415 67
    0x6000203c5640912485100311111511000d007030060914488583c461a4032655000d001800140f00d00d81c0750303501e000d41199008000360f401803554a8010060040080c801404d120f501c00c120942500c042048107440300102e4011030070545841040d4410301429401400419813940080c00040e880700041401050051108403c00e07507505c241440c25a0072444080855112080c0e0200e81d90580035858101c0c1a0b424107014500c0c01c0d0003c5141580303010300280041054000392580b8441c03102000740141c071301034000c4d580c440514220384410304404103810200049000000b5100402040850249900c04060103405591001c0c5201614114002c001c40040c1d52800030501d80e200c1c030052540700b181c0e81c0d01c024201c50385d000151070b1004942c00f510710f5802c86080c03a40640d03280d4120500740c070000c4aa054861114a6240b003860080c031070b010340c051190310401d40d1003440c0820101e04600102460b08482c16103080100c0c2903552808015580e498200c01248601c1424100c803a05000050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 824530431 1250 824529181 824529193
    0x10603020909031c050106120506040f06090218011e0c1b0e1f321c120e0f01051b030f0406030605060a02060402131803030e15060a0b0c 60
    0x10300040d0710038005481c10440ca91002030404060705003901d4000c1480200e07a01080190316004010f8a8005040c2a04107010b40d1200010403a40d1103a21680c80c5c90300040081000a4444860a0003580003212800341c40500b1099070358690310031407035a04c0026104000201a01540c2000c1d50803001480f001c9440c41c407900100c0385140c1071032012100400000501900c07509242000746002071510700740664107508000300340a0140d081a01e80d0306240700d000b1101c03d2460b07054542010075882d0301034650040c0010885100700039804c0e003028003140909030010040c04aa18291200c14011018a4112800c3d40002d40d40c0d600036030242c402c01d0607002e1400c0d0789200f20a805819035100424941c16050003080503c6880c2c0d05119400190901365041d600c2c003a0100406503840100500080c881c0b034280b50009502800c2c1e4100c2c0325020b0750b01d42800116a0146809070107401da8201c00c41d0303140b0409103007856020f1681c49090080030050651492136007450000d0045900403428060148103103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 824531681 1250 824530431 824530433
    0x909091216030e180c0c0f0111120a0603170d2c07060203040305070b130e0109141f2102090c07060615080a0903210e01050c0c0303040b0405010603 65
    0x4500400c0300c0712003070514500400c0c1c1441d01824484909030700c0e038000d0100e2460f4281402d40300c80850740000820340310720740380c000303500500b4500503100c0d042255950a18140030207144180700941074944000b00260410380c3ca900b0b5600c103d83d414880600b00d090071354000003201100c080144070040c409000440d007030001602d03090340c1c003648101100414030300034281c0440050a00c000710141406101640c038003403450315015660f005c607008990b100d900004150450301c1d80600032000070000b0301601344081d80e41e480b0220003408120510b8060b10a42c0d4001806045141980403c0c0d00c000b441032140307e42010207080941c000401001e03009508a070f200d40244e036030820660710501d40000c450f41d494203a803501a044d221a68418424034a20920354100d65800151503584902c080100083d007540d01c0c00c040320a000320a103200c030002c0b500381e0fa0070305041040d0007010340314031464003e00164840084408003481030780c00c00035494000340b001c140003810240307803160400d000d100042213164032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 824532931 1250 824531681 824531713
    0x2c060708070c030b0a090c14010903150f0c0f0c03030903030b130605030f012307052a010b0907020d050f040504020f07030306150c03080a0f02160b010801090305090909 74
    0x140c0402c1e59030070041c4204004104900000b964000380c01c10041c0714100d410703550000d44c520140110940b5448100240100d644034107900c0d001150031011911626600000c6440101017a040e0302c1071081c10003043d400c86600484003580a8a000c5e610b00309900802c0c2c500b10700521500004404050320398108000e103580d80d0400700508030621100040b114034013410540340400010325000340ba4140318100015420103000d03450700040c8a003a556103a81c03004e03000c035020721603158109048030702c051000c00402c2d6540954484401c1c0e6000070844441e417030007001001402203401c100143d00404107800118070460140c5010341c001c10f80749040c113880300001014ad03044460f03142e0900f40082690014951b01d8010f0b82d000b00b2007150170b8003441304081401080c0c0903c210004d0180900e00c0c0105402a589610072148509000002c5455204501110f001141000e505540030301c0180000310710781006218091600d940f68540b1860039203c5024061401030040541c44940200e0040d5516048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 824534181 1250 824532931 824532937
    0x6290c0d082d070f20031210080601060819060e160804051209010507080406080403141305010503090f070305060907060e06071106160f061415040b0301091b0303020d2c060708 77
    0x6141c0715007900f03a002d91f0f9103a004100f4102804104010801660041426419105607113041d85641d51400c0f05204804406035003050000e107050000507020000844843c040c10100342c0350205422480740460b064541981d000e419500070144128075040c00c00000c000603c01030403c40e08081e0940c4503134009804c103a014402003840042004201640031b5411101080f040d800c07242441c40707640500c1d101030244e0049605120380040418480307007040040031243d0802d0012107025603120700d401e030748490094480c60045c4c85448400b00b02140565080c0c0100c10f400350035182440c03d07685503c4a64003120f104a9084201040fa0251000980028108550003101045802813141c50440200c552000d0300d6100054028203018441c8111101031280903001c03500801c01001030300004e030052190490052090340b41000f07542008d840c01e010f42c03044034020340940e10312500f648001d407500a0920300300300800080542c806000107205600010703c0001501c014104000c80d80c071a64207034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 824535431 1250 824534181 824534237
    0xf110f0615040e071a030402010309080c0c0f010306120f080c120c0d0809100f180f0c06030c21062303060a06290c0d082d070f 56
    0xd410061a03040ca42058007543c50070b6030500c1d00505401d07143c841000005008244512090400000490305580c42600314031405904140129039a41e105610581d50324980d0001a00407038580c000a43c4640c024418002200c8646041003001c51040e46c56400d0080307000310407a107000050007180c3d51010100800041a8448041c950b55460703124141c52905445292980c10001c46100308081d091012030f1071350301c05e6801d0fa000700d5000160305848000c0c0000e05889030820a1040d041410300c10700c1100c0780c140b180201120b400f90340d1a488100d05980c1c03002406c20102d500d41c3d4070745a0542e5521041503035444051070018000e901d030340c02901482c095460049030b8107601a007175401407600780103c60b00003034a44010446545001342f61901505900000d00c0481f20204454140034a0f101c03c844420b012441514400c0c0d0010300e003e0100c0d0415210308070301640512b480b04581154a0f0300344a00007000480b0102035650312000ca44004030044e0090810601c491400c041c2c1400d80a080504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 824536681 1250 824535431 824535451
    0x110912030d141008030301061e0c0813061404082508070308040518060a12020418030c150b0114030a0b0d030504061704020a051512010801050f060609010f110f06 71
    0x340c100b0500c620744041c5107400c407130340a40080004008058000480c2903052625541602c036007200c1d00e90550f1f448030303005000381a08400182069150302c40029240607a00d0301e80340d140400c407081c1c18003001405203000d40c030059808117100324a017000a500442400521182c204400d588403014141880c2c0c0540c4101d52040002c03030305000501c0c000003081c0300307104020450922880e1541c005a280c240c1c1c4e00c514040128070410038019074550b03400540071481c2d10300118100071981e00d40104840820078080e5042400141080b9032085680120207101c20140c0d07031f011801c0300700400300b4410f5102030102840c0303030b0b41c450b0742d07041c140c60301c00203103035607901a4a076651102c0c0b4054025000e42d403414654502540d419003007000507911443c400090750016210605850a00c151030440c9210b111044c0e0494000c1c0000020154415004107101d5003050700302c8401c40d16502c0601c015405194034040c0420003d0304038282840c41540e0008019401d00200c071440c402608413981070032429200b0340c104c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 824537931 1250 824536681 824536721
    0x1815021b01050c0a12090f0e0108120403050d0810030b0405010c0e010912120908120d110405060306040c090b0c030d0621060b1912020f04110912030d 66
    0x40c8494410650140d85003030a0071440d0400c0c15080b507440d5400c0f018000d05050740a40c8030146103100d02881e00103890550501407509031106124030004009100710302e4507101c0c01d03100e154068003001c191811242d22030300400105d40e11040c15584848003c1078180380c4610803000101007050704414078003441c05800002600c03d101c400c020018120701c5260b5040c004001400c01041d400141c0d107038403013038008114402c001d41059040712800300a41c80070501d8441c0080c040101d032014401441101400d0783d081004d0b45a49101b082c45008038418980e220100b8400940342c0c1c1410f17003000c01c0c00c074010310b001e000b00c43d2146001402c40e0001c09030302030b481d0302c0840c00c4a140b00c00c80c4909009001008000034032415601185c80b1a282c40000050115488400c5540c20391182810290740e00614038008c50700c551a210311862035090742d03001b47e101e003400c4003c410390350400e40310fa2030900d030100010503e880500310034070401001c5010031751040e1108100055518030355104100041d200c1d0304150503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 824539181 1250 824537931 824537953
    0x30708041b0501020a0201140c12041e0e07030b22060f09020f0a051b150702060a0902062d040f051002010e0c040c0c0615080d030e0a0201181502 64
    0x80e030600041c00310404890781078410700031a0b80010307482c0c0009509203880709500c1036030502009140140ca08660051040d50000084e9612600180c400d8031610b0300e48001c4292030001043c1d211440f0303c61a6015204000803a140030300c40d402100c41480c01408849c01300003001c01e844421041013140031001c50b41c1e10801d000494015807000004e041c1d0103400d40c1810441801000240b1902d4610310902c00f002410030880c11043c24940c0500c0351400594110850b600c4400342552001c440000c0107000c0d61001500b80303005031080003949600038001c1410300901c541c581c0740c201c00d0120058000b24101010940020602000b440608240e4065458503032500086c131240d111010302910641e41814000038104400144d030400c42c0d0030407038001c200210b00a40540c0e510f02440c030f01a10399401d02c10712510340c001c00c2c40300c001180c43c52170803114054814002181160200e07641003895802144a110241d0b11401408110141c44a00030448a656102c1c3e00000c00e015103414001d6001000004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824540431 1250 824539181 824539193
    0x2130e070f0203250c0308041d09160512030405210111070f020d02220b091b0f03071404080c1e091308090a030614060103021c020a021203070804 64
    0x40c5007040107000450503c400d040d48900d200e4140800c000d900300b400b0f98090180860100c24070001c5412544550341d9580383e02000250324041d1100307840e00c10820b17010981c1e0300030015200d000740700310b0b01000e41421305000800c8100001201d00907407a01c010702000c03902c0e0782e0705640c1542140548000f80c003054504191a07003564943c10048818410034003c26001c11001c01014580d140d040744e1010700c00720684000b51107100d1206c25444a4006107500c1e10400700700e9030192500c40802c440d0691265124002c07004c6c255241c0c0c1030130301410800d11101c0303820380b12000515000000750078003900d44560112092110b030400c0d03110b40351642c0008940c691a0070610b01c0e0506124180c0d0b241c041912425011810300c1d4009003065107a060401c0e0280184440d50003500e86292008001c50360403940c9041c104050520f107124002400c3d84980824195030081c401c40d60802205113030302e141d00f404884c600707000390000c100c3e40040d1b02030904444581190030000314440c07007503602c4880d010308040c2041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824541681 1250 824540431 824540447
    0x70e061e0108011202030304030b0403050c1e120d182a05011403060a0302120a061a01022d0307030518040e031c02070501020415260708060402130e07 66
    0x8102030003459900c882a990124856066440d01c4849840300c1302e0038800319203184520b41c005003c122007803007031004065106000701644c0000100b1a10f08200545c00840c2030b4074103a00030003090388801c0b00c07683c09810081c0903001102042d080010340b11284800c030f00d4000d2014404607000c10745150564104804140e0320b100f00e40c3c01c0184484140d0902c400601440810110b003081e1140100024901e940c4040b03c103400b80d40d0240940d0300d440350710003440340e50b07030f001c000104c8400c1d08210842c5101030701e042c40d4480442050b40100002204100425500c441e042c400342a6841841c682c0508a0010402400b4803886645c44035541c980203a40031204183c02445d56102d9400c1040740050518000261040760303504984c45207000d408244444001c0c07148081c001e0082d4000f10300080d0058103201c007845900c0c156250f030310031110011801804131448000c80380054143d030300840d80d0380d40706483c21580300e10050401444c11004c045102c0c5510307c0c1c0c1d800a1600d01a0000300040b5079030080784 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824542931 1250 824541681 824541709
    0x90a060c03170106050702150c0d0f140310090203131a0628180209040608060a060f03051504020609121f0204030c1a070209070c0b061f140c070e06 65
    0x205507400d5040c00401005c6100348000644142c440e0f80060b0a0140d0b180c0444901900b074400f200e00b003e00041025203010907101580c00400c15484007100301c410600c0459101d00000c00320414a1418051480020341000d1b1002089d807001400d0100050411030908034503500c1001901c4030391030000200030100b10700013010511340034040c00a81d600401c40d10b651040e10a0704d00044900f0442d001110300a000c0e11061581c003070b003801000a40f032080415041d014288001041c044240c4400c01c881210b0603d11000384242d00400b100444a4154106c032504140b004241703614040b0114001151031844060500c074a400c02e009400300e03250b0102c094002c0048407202175040074699101c4800c03214807446103e000741c10808079200000341c82011503d0030b80c2c3c024401c044c00c0c02c2010004100c0c0007425400c4610101c1c0d0400700e02d0628104d00c2070a40603c0c134411010441d207a028007212400c00203600454114414400c190340c0c614180305420240900344082403072031030668200b000c0002e845c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824544181 1250 824542931 824542967
    0x7050d0b100906231504030b16030c0516030302040e01091d06060f010c15020705070e3409030203010c0f0201110910050c120301140f100e0f06090a060c03 68
    0x44100044941c03481c0648441c08480b8046030381c8001c4c00f020500c0c200c146241c0b078554040000307021080202e000c030a030380107030001e4162402072030103800e0640803110001d586e040840c5d42840340308100041107008040c1d85100c2d290150800da40d41400b0a0030a80c00c0e088090440e032610b034061182580a02108007040300500202030034108180411a0742203504001410032100e848044180643c11600c040c40403180c039011551a00d560030007a4a034601ca008280480b901600800d8088114040c0201d0048100b520703035a100d41c1c10a001d59480f2991401c3c0c0044c007960002c00400750b5400c1c4100529004580c5a26141703003090032009003150751030101031284c880d09229020303247c5c84d402c80e4501c15039481e050803a075500816442501c2c202c95041d0140c203d075070010010519440d43c854200380c014003500c080c5040c00c965001c100480d4004c940c0000095014070321440c6a181c144441300300210064000c5181000101c045a06103074590030900c085000d40035450704055014821101c0c02001d11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824545431 1250 824544181 824544191
    0x50d0c24050315030114070c12170a020c251a040f0902030618161202030906060603060a09020d05060a05060406080112031e0806030d022d07050d0b1009 67
    0xe03006402400083c1031040c4071203101860103040d4400f540111900c40c2465000c1d8854079103414010200414003004940000c03101d1018400c80340918040010300c078402c6200d07075581c0e5851410900a4200031000b200c3c9104d210850035444144401822900404000340e000503070512008030040c200020364150b0008080000300b00182c1d0000384817065400c00040980c0e85e890b50340001d0086c001504000d44203046c1801442003064206070100100c0c0303016240c9444d1015030200c400200d00045a50303100642011000482e1703441c0800003107070710110003070800b03200540b0f5440d81400c90f003080e891020a5907880050020a1618041d10b20041004450b060300d014201080188031120620030124002145000c05c0f0405000c1c1c01483d00c13407070b00c3d10a0130191048090740280015029030780c02d03020303010b105002d482c3c081c40032403158425045000880b600d41d0a84200b0428a915450000e009002d01c100c049241d03941c0c03140640d05140a1007072400740d420b01c00e402406403c055441084c02610300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824546681 1250 824545431 824545499
    0x18320304031403040e01090203060f010c0807060509030408120c01050112170711060d050703050a05131407030c0b071704120303022101090c1b080301031b050d0c 71
    0xc40e001e40780e1003050701110a20380450186180140c1d0007080404c4070910022030140c40c1540554401c00b000c603131001000c0201030040d1b4421140e0038001e00180803c0020401240180d04110740200740c101c00c580c42c2c0f940d1114103d060000040f4810183d03400000e40c00542e207001d0040e240902080301c40031980c200c41d41d444803c0206031a0f070b910f00d40100841d00c81c00780300fa42602c880000c5006402d10fa5580070b40d001e038400402003201c851000c00e1800012440e07080480c81604c0c45408100c444400064150f202e048201c4d00320030007201944a4500c01000159002000d000100106405985c840c500342c54500f90b046810078065640003024001040114407943e21004c00e5601420f0059407440c2080b6050307031b00441d481d00d43c40080300314400051071201c2a03100c0700d00080155a0210086210860f10704408010345010301003d074107000600100710090311411242c4541011640400e41e103802003440500c40140581e8118040f6808000c90a5860302183c011443d48564881e02c070b101d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824547931 1250 824546681 824546683
    0x150e030f0309011713020402160b071106070516051605090a0c0206010b09030c0a320603060f0d05010903020616030e10020d0b03061f0503190f02041832 67
    0x135082c25101103522200400d1000851180004940703130040d00642d034a644007041d003050a0703034000c8112102c1d840034000a0115100e100360b20741003260300c0c0c080c0c0039603154200c0480e051341200c84607400d07400e030312160303400014020031230205803e1810a030750803154682070811248200052203115000d05204080105c075501103910307415200384055007629284401301080c80c1c106800315040d080020140c02103216001629050201d040c104402c0341824208859083c003071808070b0009411010900205444c1e20b005102d1a11400000d0031070507503944e483e10b03810b00391001c0000c154090780000d018003510300c0300072541e441102e201d420b00344021545402000e59031000d50421000742ea07400728207040303040290780100d865900c00508691103400c01603046590185600360070045003044a00004d110b05002c01c8511107441c005446080c42d9069440301c440c0e02d1481542240e000f035482c10000c0e00f4008070039014041c0d5005036075190201510500c40702c40b440e01a901e5615110102c5488241000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824549181 1250 824547931 824547947
    0x7110f030a08151801080601060f0203190516080405010f080105010e100504090f020418051014040915150e0c22080712060f060605031f150e030f030901 67
    0x6420300d0084110f50320751080c00c1e00320010f041003c2c1d03c909242c03202c07146030560300d0380141640d6850082d541a81da85900607a201d202801194026070024401d0491118134400c80c2c28464103181842450400c0a80402c1442d020103081104c54845c0401d082c0050f59202042490100407800c01114039410701001030004a503841c40b00d0311511104c18485100c174820340a0314000c0000711818000261a8069080690072601910f403000340407044034000c40b4824040c45000c0d40c5a90140c4114600b040b208030200c1c007072400c1c3d440e00b19849905000005510181c115945408848009003483e05200006051000e540c0900001ea0182003030002c0142104101d07950f052451400c03440d00d00304095200c100302c8955001402502544c100041d40483c49092441500e01c0317028104100201c4603401c4048805900441700068001d00010b040b80c09400c0040c610507215103410005d440d601c0300d50042c0541c585408000180000e1f2520096080821140c0d18600000000d1810811800f0000b40078103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824550431 1250 824549181 824549197
    0x120d020610351e0c09160807090b031e090109211709060f010e1918062c0c090a09020a080d0518030a030c02090903040906080607110f03 60
    0x208181d00314007801c8410502c0e074500c032107000241c505102c0c1c124101c41804030344081d60040350154000b80c0c4c3d46498034200c0103102d22003c02d1500c1d100c8100800c200c8150304000d0a4609102c007008000c1020019500550300c11002c0c980442950050b11030144c004000c040d00c41c1020781e050045410018154207902408104d003c400300750f110314000340c03c444441010b07203a0f610021907082800070340c0001141c5240318444503103045015981c1d6030000c22081d00c04861141d0403054284064210403482e400840c080340180740e15074a0b403141510317140700700d03054403000303103204070801ca6070700c6501307aa1038007500000301404041c0550b40da80101041d01312000800c03d4907815510100c503001c55440030101005001c00b18121038070800c030040043c0450b071040d00790319841c4d00d000c07420310305500d030014207010315660550701c041f1010420350030720000600150580015003c2884080340f4444540319800082a041004051509100e02c0c0034008000300344560880c0d0704a421a140e41c140d001089803404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824551681 1250 824550431 824550479
    0x109020a14091e0411040806090f1c210528140a020c0a0b0a141003020f1e03012a090e0114040b060703020c0a08061b0c0309120d020610 60
    0x1100140000740041030383c0d05c5194100e060224012803058800201c0c0f92041c5410b03000c44144590703281d002c90fa0740ca2701891b41251b40c20b072000e07100300980c403801c00400944600101080040e0b640c41c41c000540d0b00c04c850303a04504441801145060010509441a0104040d070402c00b543d4102c802d804110401003086861613000222909032600411034007003540e4106500300d01c141001c0c105440a07080a0300704000d00c020380004150705030201b550580c22264000c000054801c0c801d0180010b188243c50030b20040d4464160f40300050701c080c09414100005001c0d201c030003039800e40c0c500206080042141c810042411004d01441d00840550b0741034865044042c03042c00900c4001402610078181e504d904120003180c0c00d410140c00240c40c0500407421031f42442d4507078861248540da50401c540c1c071084240c1e4598504c0d0518203220040c800c1d80031040c00e0760f01d00410100810a415080d40e0a441c0550107d003100d13405075410310020390040e00c031400ca440054a00140d1b1900c0d140d0a0b00c0400c12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824552931 1250 824551681 824551729
    0x16090810020702030307050703030203071a070507060f060f082a010804080d0905150610030b100f020708030403030c05100b0609100210090b06010f0509030303070f0c08030109020a1409 81
    0x391340d0100b05866009a1210849038402e8480c070b002074480c1c000441c22640d002c075020250329800d03015003095110f00c0840e0781c3d01e406c01a445d180d10021b000e800300030344200c503940c0401107117030107441c1d035050003400414004007003807415044c1c115a83c0c10840500031603085400246003150780d10515442c0c105401800b144d0f00e5041031889100200880d4800030403d2082c1400340303481280c00341c2114881c0800305c80b1a8080d01c0d20620541c00d5071804d81c42d41e6030080140c80090305190041084240860080c81100c203040c4d22840c0d100d01d59070103a001940071802d115860f0040140402091064000c00b034028410002c100c0081a03050040070200e502c41e102685c0d00610141c801c06c00c0c8501440294800d124407242030030410800d10040e50542d0004400798845520b1502032403c03124240030280c0110718542d10340c50111000d03071101d00c0480c10082c4072001030340400d044102850207400701d0000142d64250900001d0401192065040341d844002c1c4a40982641c3e20026250500345900001403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824554181 1250 824552931 824552933
    0x10603020f3a02010905040509060c0c030c0312040c05010f090303261501030e0304050a050d0501060e10080c011707030b0f0406030b10050a0e0a0b01020a020d03020105160908100207 80
    0x46040124880301002c115048030020300e042038400d4004603000382c89004e40301d601c071001d1005950f4200d07001e00b09644651b0200e411035010500520744031400c201942d040c0303030018400740d00710703803101034440c0440c1c1c00a800d00060000030031014008000034204a401d03c10030100c090841106440301a09005440000032698001c0e040c58030a05e10380580409458030b0000b02c4040d1003a06003100500091920342c81c10342d2840c00000725400d4900c0106804111840e150420240e07060a440860b01c03035403106000101e484100b070196024044143c410b005150610280d01c0c50b000d04c0800035030401002d80710a2003081da6901d050368021001c3c0c41d020402c0d601102c04035500260480e4210342040c64a01c00005001c080a0b02c3c81c06190100951005031381c0d12410882d0070080c0d030003442820503420002c04c41c0012258070001c1481010300540782c0c06082900001c141d002d182d030707061380982d45072810010320404110841014449908220706868184031201c6e9460200e811039180d80e66000541c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824555431 1250 824554181 824554219
    0x4150f1e03060905030d0507030b010504050402130b0301030c140411032a0a0c06050603010c0f2a080a03050a0c02101109120304060207080703020d03030507030207151a0102010603020f 81
    0xc005160042c6003403120603c5480c12903070300e510000001c981c5a19140210b08501d00c40d005003905c1e007505030350300d03410141400300b040001c0d0b0042c5401c016403030311031303400140303e0800c10007443c002c40c01030010103206841d1514420000e104036203007610540c54030401c2d60501d458501a04c0c1c1000c100d40949a174111203401c0101c482880000300351240703802240c81d01e1040e038030003070442c0c0451003403109104548030101071500743e074160603442c001f140d004450250000c1c800ea041c5103030074210220485034124400500c45030303820327280703002e840850002485441302c07a014040c40ba0440c00030b1500b0852081055402922549810381115402352030790304854250700302c4000d0309c1e001da20082c501c40071002040c01b0385540c2d030300c58032901000d03005a00340041e40c0303400454074004980c1c014110050b1042c66680440041000030314440a1507428080318000c00c1c03ca0301c5a12411060382c000054001c00310396100c1c250000c2c4d04034075046a05141d400e000589a040300c4c150300349025134540d501051041c03010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824556681 1250 824555431 824555489
    0x306020904020d09050102090a050910051017190c0804020d290a06050301050612030a0e060d14015018061915140c0f01020904150f 58
    0x440683d50030003881105000c010f40c001d007100c5a007141c504400560b100140400103404403007914145140190401003400c00d000c0d98407400e0040e02e018030303070108070203610700c1c5804040c0c036007030a900045003446407000d4103842207940d08503803828a54810728240d400035044d10051480207044402942c40d5a511130500855214030748002e01d8040d00514140d0b03590401001d4074400c80d4482e40c00c00000c10b0040c180200c0c1a1010200c001c095843c0111748201520400c408190a5412400070012100315455901c50401c1514260041c131a189d4503281d140440c001c0342d15200661030b84180080a00d00e5014041c82c20400c02c4c07801d840c031804180d451040f030311580400a05402646400880381c59120f00c0804a1060300122603c20a00c0078000f8102000202c0d809440c0c1c850403c1c0d03032b80d80501d85c003407541d406c3c0399041c0405039450100104c0d40d050401042261f94000c585d0042003500c6607250030701917158004882078400e0102c03481c1100440070f2820134400c0140114610034850b0403103100f8200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824557931 1250 824556681 824556697
    0x3060f0b1c1b030e19080708030601090b03090f060604060b0409090602040e09060a0606050702060313110a181b02032b0c08040b0f0601080c30010f0f0f030602090402 73
    0x40403040b001440d40034000d00f1510046a10a000341c0c0100c52004640c0d1169028440c0c0140c04941010741c2540d03418015070001d041541408a600c3c40010000c0c1580e000758440c3c2032103c041e001c1c85114038511442d100000c1c1c000c922960800030148603030f202c900b017030b00e045610120700440c0882039420204000e10132500f1403000d03c0054001c1154204002482034002c07400b41c0d034200f00c283d5a8280840b640c1c0074800000f0760080040001c12054070300080b40f14446030240909107050950800050b954030b1003640300c001100ba0358000e03000c0d005118400c00c1e4050000d507207008104110800001e49074450680c5100152040e00d2480c20b81c81e0000305050021920040704100726000404041c0902c0030803502150b04894010001c3c054941a074681806224180c440b49029225001c00020940090348455103200064642090300c01d9481a54040300d110140e0800d00395041c030060302c1070718805400110a01030304203010010b9074240200001220340100e0010303225030b44400004d02a102e1520 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824559181 1250 824557931 824557961
    0xf0d02040801060b040618030803040b06040b03061f0b0708031b0d0204060903152d11030f07090b03090c0d030504051e0a08010c271d0703060f0b1c 65
    0x900891504e100e400100280c4250f912200700c40ea40c08000c025103840c4074000100605c070b0510101c0d00003555030480c150081402040410f0059070a40802d1424904aa0105000f601000d05001107884040c82d400603241c004112407801c825501c40700082d100103401d50001652003084c1e07002130569801606c0c0c540d01a00010f55032a955600300501e440005d010a84006001c10103150000d09180304040e82020384505900421a41c034604858400a03d000000750640303444001246c83ca002000f10b10a40741428418982c1c10100c0380100394065980008001443c01c00030300c0505240000c1000590301c0407903840c80041c480d443c040701e9500942d4030180e004149440d0301720040c0b21a0034044440c103c01d40d400e00e41550f1f105061400c0ea400c0250181c0441c42c1025405040d401469076003020400802000740c0055841c1070010b07684800c08805c401c10324200c1c041c442029898043d40e0010b05800d1940000300381001112040740c0708008451050048040c5903031400744d101c1e0055804003a07148 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824560431 1250 824559181 824559191
    0x10905030a0f12091a04020f130501030605090312011401120603031d010e0a051504050604030c061d0f10020106170a0c09090c051309060609020706051b0f0d02040801 73
    0x800103000b2150103038801c400f044180643c0c030300d0705626104000c102038000207034048603007025500b9984880041d2050f80c001d4603408030080c6544401e1000c4d03915541380400001c05604d141040411561301801c0a98207400402c0000f908401108009056a03116160403200440c02d90043e10980c410a86103405141840400030138141c00400b40c08058000740040070803207e40b070004541c20b034060b40e19254000810036041c001030409010010b41c071858001602c0c40e0503200d00000f89103070440c1d84200c4009011403c00d2094903031003107068110140a003a424075420008001841c05900105000d00680e140c03400ba994491003501b04400a1000760b00f00e800c0c81d00001c2d0200e444d81070a0600380c03541c540415000440c00224410b481d5031b00e8001e0721083c80036090604101e0b42c1c11004100b0070300070740c0780c1e40f494000c00c03102e12400000f00152140140e07103c20710314000323060343d000421015030034041c01c409401100440080f07940c040882c2220581d0340d000700380c2003c02405160801d4046610784 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824561681 1250 824560431 824560447
    0x10e060a03021c0504200a26010f0c1d090105010e01021c030b1513120221072417070302040e010b070314030702030d200a030b0f030c01020606090901090503 69
    0x355001600590260f0b500c5206e4045d501082c00a5540e08141303103400c299010740401030006440c6840004442d41c902e08003ca8a900080e5820755a4441e290b02e0300315030b1541d00c1c0c50742030341010f002003400700c290110396801142d010024031140380504c1118180001c4e0307a50600b55070320900640045e1031501e1118807182d10b422100030000c1001100031402171031045440640d2040000581e00080c21610000000034104442111001c3e004181244c02074204943d290f00056015001121205103100034071071640b50200c2c810007a6200010704100303c65403403046140c02c0e445480860070b0030300222900c01780c0c0c43d5403200728003d220b260310074445031905100104801003203000904015009a071405501180c8000748a0f00340303c144e8445026071300030003c1602803061a000149105400c800714001c0144000c002080c960090f140140001c0d900c8401018502d82071001c41c80c01081a4020031108800000103990b650300034002a00c035103040360000392030f041d003508980690f9900000b625104c03200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824562931 1250 824561681 824561737
    0x302090a0e071d04110607050a11100c03020c010c140d0203030405011103010f0e04150212100e0c0a05070807020a0611060105032e0609050c27010e060a0302 69
    0x110701407540090040101c009000c044112002d00c90048039804152207031101d6685410815452103603681255043c09500d0204605018041c10320b401203443c0041e080c9400c0400c0a01c864100e184414003441c2001d21000c42d50000d1035202e4598282445010401c49080540159202490681852082010340c4d481258040061400369100d00000d2112080d09a00e10740270740002d00407804050035465080105040c001203054006002d4041201201500350b402c0051764003080d107000008850f50300f1700142d404200702d41c0d0020010704140d40500d0404070304c09101403090001840410a000c81c0f00d5040c094070790f080300c0740f295000b89044a0195203041c083c0183c0060001147c183c02034030000038490030007244000c0700212010241c100c0e03200d0701110b10314005014416407001c1d960740b007021070807050a01c9014001c800f2208c0c4c4940707403410581c441043e90034080d22880401c000d080c1007a032990308500c070307400d852030200d80450300c4500c482ca00300c8c000d005d4484d0700382c00804032404038103540b0b103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824564181 1250 824562931 824562941
    0xc0905060a0b0a030605011d030a2009150f0d08040b07081902070e0c0304050a0b040f020a0b032a0306010c0f0c062a1109070c1b060905010809070509100302090a 71
    0x801c0c2c0351a1881c1310b01400c50000381c8d5003149565090342181c00b4500002d29000040c089000d500004108200e02da1004202034810403680b5035076401e002c01050b142884d0407040030403401d10460783e44141c2a601c0c0d0f2101220300903445070302070680d0701003051010012020b0903203401300d02880c0c81d0303500030070403c1c0001d65070f8600b84910942c000320640810300d82241041100d100e42d4000c402065040340039920041352040050081c0e4002c00e00c500303c0c00041c0e640d50150002400102d0049403241401c2d603e061700588010201010180c1c901e025034030f2335145100356a404002420000841e80441c1401100041918001000505c12410204580303400c1000201b1440c0d0344290201c403c003046080c024020300c03012010340f5a45c0e22200340d407203a140120f50a9030200c82454190381d00560340e62000144004030030070b480324076000d0005119466001c02510001e100928200c0524101000310759110305c882d0042a024006850000c0c0700d020151080c9001980e01402d0b12200f0f00d440d014000040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824565431 1250 824564181 824564189
    0x2090c030f0108030711010e0609060a020604050f010b0102061306060812030115050408060406090606170307021201060b0712021e0d0201141005060c1c080709060504030c0905060a0b0a0306 83
    0x7030100000b04090b0310000646030040d900040311004102188019280103002ca6100c41e4480342c02c00c1414102d07120b07100134085810a0390000d11150800349801c50415040d0000c2c1200e03a8503040100172603a03030025100740c11001815465140e00c5039070078400c0141c041d9070040f414921643d24010801d00f8140000c4d0304880290381d4ad5050000400d50440705842940708042142d4440c0c0d0114010a8070380d03200342c0d602031250038002440b5075101140642041d11426055007600b0100303412003541014072104421a803a00001c020b0507041c404407202c0c03030141150181040d41500d00c00820746000b0880714400c07000000d9000030301a600700c04540e55000000501d00154280709041610440940881e801200c01400d05003840c4e044c2802d00c546a0030004115041d44100000240060341c00144182201c07002c1d9101d0545282486014001141030341c801010014100700400100e2000550f4200f0750b42002004580740e120100020008441600490b090f440b0009141c1c0a5070b0305a0f002d43d04035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824566681 1250 824565431 824565451
    0x150607020126041209090915020c1c0201090c09060b03220203010501150f02070b0901050a170a021b03030f0415142a03041208130c0f05090604020702240702090c03 72
    0x15680b5080d0800c1603c1e004030000707140c0c448c0031308000c401d140d00350013a00d841861182111101e40803803185000e07903044146076502503507640e0300050a02008005a20207405074074424480039282001400d000e110041c89544074036154450040c488100450144035150028024030555850b122700468040882585030082060010705010403400481d00d5400c031500190a681000c3c1008019940b5601c008403820070040301801d102c07000c14000c5031260003000d05100c01615600807c01c40004ea8480d40001d00705e0364028030400030812480c1d2022039120f903001003a0b0106850300b003000b07009040e00d8a01e19140818450400450007203a044051681031080c40300404104443c0a4032900e10090b1405040c9503c1c03203120000703060144e0743c005d070092048601d4184150f0755844ea00910b5032240c000d24803a400c055000c00c000e240c0000720b03a0700124100d40c11032400b84a9800201c40c09008158a4072442d0618100080d03842e040b0142c50b800d640113048800245008048158181d1084540c0041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824567931 1250 824566681 824566697
    0xa08010e06040c0c03230d02090102010c02032718090d03150e061002031309020a020c100509121903020106050907080f040602090402040306020a0c02091506070201260412 75
    0x507440d0a000e680f07500c3d4429100d40c0303205807150b24121282084440c522804404d902c0f203001800b074a1100800c0c401d210400d00585998044000909646014000508652050102003000003a64068612500303402100c000319019001c0403800c1c1d0307aa41c2d0b2480111224840c1040303100180401c1403a4001c1e0fa681d002c1090b401208509000c0e0300c424018845149013a5000070f0131418000b0700c00c55000150300442c0d081c00394070306c004098280720b600141500ba4010a0082803240c04100c82d04000f0b508440c164107805850000402c103016041d9450310840e6009402452180144158184140c0400b00e100388005541000b90103400c0c02c0c03180601600c891030000b04a240300d4840e4601550002007000707116199901c0343c0c80690081002ca070781c099401c01c40040000c14030301c0104800d8016480b6030300000024010800319010080560301c448102d0131180c4040d40d02c1100f02c1d4809a824206281104c40945040c002c542c9002e491243c404c44050600042c00360580524500034101d9880c0c1c49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824569181 1250 824567931 824567941
    0xf06030f020f0a08100b182d01062a05030a110f060105011b051207120f0e0307050111010605040603060605130c02031206030a020a0e0601090815040305070c08030a08010e 75
    0x45000b25032003080d9560300490310300d00184001d0b4011b903a002c580101100340075160f10160003800d440555003072069410b206c02070180f11010700444041540080e01c02d000d0740d80360010141c684030b40380b141c004181581128900c85003211704440389181d500b040489450f080000000340c0418076240c882c00080c420b10f04040364003000062550b040e03c3c0d042c1d440c258042550003240e18144036100c030854860040d4007041c850001d094000d010b106002d48981c20310f0b031180090140661919071202c004211944200c20000d88000412404031102840c3c03011208005028150052078107420155100307041c69000005c3c0310325a0030020644100f2500c2c80a441220341c0850125a00b1540344005030f0803e01c205c1011490410700f0950082003e4150f40e14050280c0c00290307450031035046109010300d004180010b550b4400050800303000c16200a00b0781c03c05d1101140c00243c0024001803c0100006844007080303510300804005040c1c680c200e946440c0c01090180c040e0209020b900704405055000034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824570431 1250 824569181 824569189
    0x60801091205090303040b0d3620120102070b06180402060315030a14010606050a090e13300c020d060b0f060c011a0a1809060f06030f020f 61
    0x80300031544a80c500d103055081d840107503000d400074072040754507000070310000681d001c600c002451080c081241c0001c445403c035141c40c0c41c0710019030b0b42051282d840d07440803030f0804410407d08030030307600144101200081071083c150700f03040d46071501c3e400c0303000410221460b040540181001034851804410541e032407405106600070b080100e414007030802404140582481030045801c0020344804126540a080200c0e2401404d00412110800c901c561281146c0e0207108000240216150071407800d51140d0b4014000e01d9540a0250342100c13100100301010400203400342001d0703024181c584683d9100f090700c03210151010150034501521141c010001c1e00c1100c01d001c04503401405005240c546460303100040c01341411160300400c903810072640383c1c0d86510223041007400503800447d4440e803413414503100ea0100c13090300c0c1c080c1003446414482d200d0b50107060060400141d10003d070440ca40c0c200a00508400c82c00503070b0741d6241c400040140040001c000100c24000c1e40c4000002c08001c042c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824571681 1250 824570431 824570441
    0x1f05060303071209090513110619261608062409030a17090a0806070801050913060f0b010e100504060f11060c03061c12052803020a03060801 62
    0x2298550401c02054001541528010314000083d10b00000c4041d261510700f812200c0658096503244009040c90041103625030300c44041840a40310340d400c0800c0030661016155058503100300b8030462100345505038400b0319106203114500555a038103402c00600303000200802070600b5000507025000920036041440038000300e6187c4004026001c0c2c02e81d00d5161700c5800002820303516000e511800b4002c100340001c09841c540c0e860090540e00c0720480304211541410754021961504480100101c082d04900d031641181c4044d2400e84c0305940b020900c9004d1010303402d004105518041c01075484154540c81030910030310a03264840342c032517404200880040c0d03403115180007610800060217482e04c6001c1c00400d440d05420030000340700403100e04a0800d0811036170703200b4012010041040914068400c642c803405042e03c440010115a2074604240b074920b8600d40601500040c803826290f2000c0c40e0f10403451424001000702c00810301300070083c1d441100c880c0006820100080760050042c855 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824572931 1250 824571681 824571691
    0x20f181e060a0e0a0e16050f010905090609040201020307240b06070f080f04030c150801050105340b2403120412060e030f0901080a14070e060c0d021f05 67
    0x2d00030b807071032600e040440e0304900207000c451030b1034503030500b02c01088040000e54620118000044111800c0c1020310100719042c0704101d0400500010402103910b5405039a5085070098822280715030781d0b0700060749507100d000d07002490716410327414400030902c45649511454000e507005015002e61741080003218041e05802030722004011580800155000000707060441032120107508040e960b0700c40080240082d40411904a810200a800d0075400300c1054090103007404e000f03042504540700741003142c0a80d090300381011108440d0a211081410040050750b0780302940744240c6c40c150143ca018421209842010304d01c8a01013031006203400702c0c0d0040c1100038501403d08151070100041c0c0e201102e1001603800c03030b91342c5092050440e024402406000c085161456464010200040002d100103200312043ca103042039210039407280244480e004019441d02d0b1780e031440182c000948511801082e001244960311006140d10303000314800b03424000361b030000b40d5001c442c54040401c4c0c50040303407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824574181 1250 824572931 824572939
    0xc011707080405120a021509240702150406140a0c1725022104030308070c171b0115030f02100201060f14040f0e060a0207020f181e06 59
    0x20020304500c0c4a24a02680b0a000700b080f50320141c11114408199800b4010f0030700103800500440c0910040320305031a400c0302440c002041d4005441070b11007084d030f40c11424128030040070030214002c80d10810500c03200100500c022800d904003813401c080108540d818560003181e02800107405106241300c0e601113981d11342c035000c43d0320564200941e0354000081c24550504403807081c41001d900c440700c40c5103144445800406800300c0a190341d40d07000d00c00300d0306400038200400040c00000da12460b5036400402a08040b0140030442c81c00098611005103850145100403440078a080403a40c0d1400c1300c0032010008001c190f040030011225145c0500000e01500400d892000050401d800c40c0450017180e84000101a40c80d190303158a1544c0c240d000260382040d641c00000685068440d07107441000300031f07040201007510044241c80c1c0000510041c081075022a4003410754680d040b881000880041c00c4a02400125a040d440302200791480c44409080090500c40b0b08059030065000b444010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824575431 1250 824574181 824574227
    0xc15030a0b01030e0a03030b12061b03070e0409030e0f06030603070b09130e1e0312150111010e2401030803011505090d03080105040c1d0f030307020a060c02030c01 72
    0x2142200c00342080e0340c1c5050400d81c4d5180b13000b0301c141c2c0911030108220300c680d40224071070b07490f6020480c2c0c4030098950001180c0100c000d1165a00800d046520f41e041110000e9440365071b140c400b07030f9a0707a20300020242c0043c1454404801c0550001d55140010170803100a480e24080c20180583c90204491140c3c00d0744c0140b02c148401c0345e454029240281001303207500c8951003240c25113070644d0040f50511180740c3c041c92000d0725a04072100c500182c2c202c200011400d02085508800d20000098581d2140720104506260b20b6441000e8082050305031000a020f2079001d035a00c1da40d590080035031000c00c02c0d440001c84601c050b004801c58101c03a0003c004a0543e42058014002d000c8400488802c0c008204039513a865211102c441100038006d071500d1541c4d600d40710030310081d940c44044030070800803c5191402000c42c0f07440064801a030544454048030417001c042071a61260510103540400f903040c000400300e0380180d00260315882502a9241143c0820066403038620b9000c42d400a04000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824576681 1250 824575431 824575441
    0x3601090e151005060d02090f0904050c0d05070506070b010503010509031c0b0109121101031d0706140d15090b0102031603120906021606051803041505121003050c1503 73
    0x40101c081d000301e4810007040000f07a40754000b0343e441c3c1c410070400c1c1804e900407400380d01c6450501c6005040300802e691240a9103059552640c541d002c41004030301c284011004402400001c10005020b042c0240c1039079641d51482c20501034005092145c18840d41c2060b0009030318107004820340b0100c800b0b81241c0d440d40d10740743c401c1c80081c00c500000030f410003201c0b030380005850514034501c104c1d075030050004e00d01e07011781e83c00010166003106181c60484844100722408840e0005494001c07250300e031901d600100881c10312041c161060508100489052455020740301006440303a03422103046000402071064910f00580e140d020b0a00050740000a029a82010a0040c1140845070b2042c40d00000d4501043c0ea40e0812030708420000401c111498414508100c0c1c0c3c0c0c407a05401505c0300780340c42c2126602950f0280c1c4c900c10790280c0d0702501000c800c072030a000e00500503504c40c00b81c2404d005c0550b00c3c02454002034140d241c8010345061160301d00c115100e052900c2c44071807410700b10448030300d95620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824577931 1250 824576681 824576713
    0x10b060a033242040510050f01030f0b060a0f20071401030f0c05031008190201051617031b09010c2d14060c03070e010804023601090e 59
    0xc48045140b00140f0301d180020a07414624107202031103410901001d0044240d410301c01250340c014101413118000407400c1c0b00540c0c458002c3e0380010001d18010903004142d101000141a0b1500c640741c100001094041d075640d003202501185601a96074241c860803140c0888006062014005080d038004603001d0150750080c0010443c858010704010442282e6000140c00300c510032800240000ea011003446001840e01c84094000d141e640024a0341e5041414646801d00c0c03c5140241480b800048141e603140e44407047d44142174001c455000c890100c0b8044211700e600c1141c0200f02051000d00a920025410055407124103042c1d59000903105c2e265030320043c2d01c100ba40d440c00e541c13010a4006131208104104c5212091180b05180200c6000860b428a801030180c0303c8154103d0078010000381e96407000c401c42540c603091820f0700f12500c42d40082480c0e1600c82010045034904041070fa500920604011080c4810078410035011340e91341c0071004103c41c640151b819860b00441505405000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824579181 1250 824577931 824577961
    0x1803030f070209130b09010e1606120504020f1c060f050702150903130902070c0506040302010203121506180a06093501051e060405040b0a0c02010b060a0332 69
    0x1280c4d50b00901c072120945174a480d95004440b1000269110b54000c120340400703010203400c9582d0b0703068501d8028100308000e462001c0d4211100c51480d503e10014055580d00000c45500c400080c040c60110314003011500c2568a00c6c0406031107144c20107041c0d2902400603c40d41e803103010298080d003007460600040c0c0100850244c9100118030081c0110201c01584840d03010042c082400e0050303541e5400d2a15500070000f550046200c0c0038140001c01c0541d8011040701c0001d0303450600c1040542d02c480396605448480c0c900690032010101c3d01c044a6569070401054403001101c40b4001e26a40d070604858400d414003c020142e00c1c44a00544024000000600314480020010661080d0021011308440d400c4a260720802c803841e40e8600b60515030312110750402c0098509208501c0d00d9140d04091200c003400800100342d807200c101d80c0543c400e602101d0900c90050456540361010180240901aa45d00000d50800f540c84074800c2d1080e1007144199803000da5002c1c6100e43daa801015000c0b00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824580431 1250 824579181 824579191
    0x6010905010b0315010c3206010504060b19090f09091a070e0d06020c010e030304170a0c23150a0606020a0b06010e0307080709020a0306050126060301090b0406021803030f070209 78
    0x110a00740300051f0340c0c441550300d09802160f0080081796046101440e458405d0603401036000d246800d40c240004503141003210004074110b27411424174400c1c180112032406c00c44c0d02892044000f03100204586010b9000f0041d8503000d59100c81d13070748603c1801851007440a035200340220b108200440c10500340f6000145031280940d6005060603d240401030a645034800101c88a40001007080708002c04001e106c2089403a0810050519102445c09050052101c001820b240700003512860340b94904040100c64492810030303110742505d2507044e211003100a031850b4900078217210340484d00e13034400205d0900464001d50080f4080e02d40c1c100540b43d016040e45915003500440402040826080010070300912034101c0041e51901d04070001011a01c00b07411490400c1006c0141c0461308660ba6006200040c00d483d00e000c1c251581000240140f8070341030010121030082042006201007a070151006c241e10003c024003601c2401c0415889104040182d140304c031003440260050300300410115401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824581681 1250 824580431 824580443
    0x4050a0b0d0c030201140301030b04170d0e01050a18020102061b09091906170303070f2016050901050a091e09080903010b09100b0310120506010905010b0315010c 71
    0x880c40c04041000c4100004003602d00c00081c210030000c55a21031103800442500342c10329400d40d41141d65400b442d800161018254030b417403a1103241034118101c11960b070a0441142040800604401580a850103d5008010600c0c00244d0400b1440152140c11790a505038098001c4d6034820031090744030765031640101003400040c080ca41c2181c0350000042d014084401c12414440e49020465050b1101504013000c440700b0369000742c4010030000207481d0030554030b041035032114481c0d01e4211100240324900030070312100440d080c0a03801000c501200e468851104d2006440e4603035003031010302903081c894a600440851030400010401e580301d04003443c080d5411045169601c4004030a03100000002e40c2d184000040d917001c1031a0034811074402e04d405031454032107880d00d00071403210a14140301351030f81c11800000040310501c24480791750142c40788900514a001d80c03810700303a6441509010701c94030300c0c2c0b03000c001058041403401601c0c441d6070001a111803100c2101d004550744c040038541181c507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824582931 1250 824581681 824581691
    0x1051e240304050a0c080102040f03020d1407180e0114011214030d0e01050901050402090604020a1103041d0108060108030d0207111e10082202010212030f060a05040c0e04050a 77
    0x116a0039880114000c0380100000e1020444a007031221407180a5405100d0030b82c81008200b02040424022404580d01140c1e4080308005038280301e56082c20088000800d805004e0000c03800001e100c1c0f949512210381482000000c8581944500b00c41640710308043c0e1031192001005a02d0648910502e4540f040a001581c0070351030074801e01d16080b1103003081400d51540d020b0b26000c14240b1503181d1004802000f809642000c1d0042084403070081e2806000c1ca0300000c00183c10380c0105243d1900318038220403643e960381d07100210412190b4034504001c101d8480f00000512500024a49042c1e850300c001441c50540368a24042c020f61009078211808601d00408403040d503140030754040319000c0310b803010074441c0e4000d01300a03c2c40a000d50010070f21851100707000c4a08064560340c05501c405c100740d40407400d5103000603441c0c00c5025015124000001040054242016a0381c5025180030b5402a03043d40c0c4400411003644c01c000c551f030f000661041c4036040103182c40d420568006d0803003030300050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824584181 1250 824582931 824582989
    0x1e24010507060c050406110a12110c060c150117150a060902070c0602120403150f020f130501140418050601030609180c06030203010f063c0801051e 65
    0x151981c540312100451804607040000541005187d64441200e802506c55134016a8643c42141418604c100400603500c03801c008031102000407184102c0014191512880c0110215a1b1201c158003041403c0c04100c00004a1490109082150507460401351691002c0703054040d01d40d050061040400326241c000001e040c090070310040510078060380444901901300440646040d22080e02043c000f14100810008075501900d020342226107082d001c1400daa40101500182c007400003140e1080c1c038000740e1070311a20400030500084803401e80b103095942005d06241241402540b003040d19a400c00c0007090200095580601e84c0b20505040000310300c0d03120350a01040780c2112241c2c0c00d0341401c1e2000c1c142400300c01115a8000c1407149410b61856061a507048446c25a0744910010b10400000c92044002030310342a410200308149503154154801c1c555041c0584120324000208064134004901824407040c0d80010003060441c0328440c501000901800843c000002801001a900820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824585431 1250 824584181 824584193
    0x30406090b040503120c0301120602311d0c0a030902011718100504080f03040f0f0b181b0f190303020c030706033b060403081e24010507 60
    0xa4012400380000b1515110f46420b414240c80d00980003106d481024001008507044200409802c50740c001400b40e00c0da8005402007108020f501c280e10403490f4110401c40016016072100320856150382c02241039a0a001c041c0c2c0b5080400303407808600c0800810041440c54025041040020310602d4507a102d8203860802405064058410500003081141c900224000800040e4074a0011080c20002401d20360748440580c0b20b4a04d03941080304005c0001010300010341803c0440d5600f10f40b02d03152046c128500a01101c10407502c40b02c505409589511684a00003490641c90a8461005c421a0364103820009080b80142071a80c2c019285c44104420400f40d05591000310300c290002e12b403d8403450205414030645030801c0d01050f00e0807450284d106240916030f00d61202d003115101d04007115119a6880c007414000442c0a032061600740400c16a011002912480c11080011090b1481c440c0b581200380050394035031120001610f03001c51584244518400581050601c545000c401da5190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824586681 1250 824585431 824585453
    0x50f0d02130c18150f091205010212070315090e030912030d05070f230714102403020907051306030e0607050c150c0c0a060603060b121203040609 64
    0x224055403144a60b020703460b080b1415903000c0c00c40c40f00c900c41040c140004080904c2e04501e000c010404c501c2140b0610500941042e4054580d03d1b4140c041e0189a0401074041e5002c100f03680784088a4200041d000d91007441204504204010460b0040b490015200d015180c05c100e498254002000394002965a50030b0401105108802440e117500000c0e001c841100c400502031802d22440d9409002d02a510035045071000070407480070008401c0040203203010780034540000303064481c80000160781420000c2c03110704c40e48240d0001c1c41501d00781e202c1c0c040d118140701406104580d00000034001403902840c1c0c2c1398040440d140070343c24000320103d030062040c6590300140100e9528407007068410340500c0031681c40784490400340d10385001c40f40112381d141c0a440310341c070044c2d00c40b50100703004003000403c0b5245031954400301d8500141c6130138004001c0815100460741180303048083c1c4154108101032060310400080030f441105034a005004440e4402881143c001c1d94448e810760001e810801c1c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824587931 1250 824586681 824586709
    0xf01050913050a05010603020703122003011e060504050105160f0204061d010909020625051b01020c03010b06030705070609050607050a020f011a0d05030403080c1c0903020109050f0d02 81
    0x1044030b08048020f542201c9068006008142c010400007010a4100c02c0840c041d00c00c0302d40c0000c0304031002050b080c0902200b041044054400000024802002482035500e03420005d1403426141e074a4005946520803441801e011074020f00c5001410130b101105149814000e98006030100c1c0c43d940007408171741a80d003040303081140c0001d1000859100000741400350489a004000102c516000900c030f0303020707800031200d83c0c000c0180b07a100000e05006031485469884012108041c0380d94a031407c000354611030050061040003480c00e600c0c50140070b501070b60040900305a1440d15a010100c13060741c8100c3c0c081c0c81943c0c5494402001a4042060314440d1600350380c3c468a4954042c40241054070280d900340f40baa0428801030880104500300911540044078142400c00043c5481411800350f035001410504001c102e007040703854003242088100031110395040300708402d810281c070303649114000a40003c000000500440c20f00030f07880f1044050007000400711240341e034000307040e42440f800303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824589181 1250 824587931 824587969
    0xe030109050a200f040b0d050105090f01180f08090a1215060608100905070c0f050d112a150a0e040b0d0f0b0606070c0303080103020901170c0f010509 66
    0x103407101800140c0c940c44083c5658003000c1100907000c0070000e51001103c03020107105941e01c01c4000b40d2580c6090b0701c4502c46a00100a01c124a41820919120800030200058075406c0410382f050041a51074400c040c5580041d1001011140380c48881040c0c00681c0d00c0c9420640b00100814441c0b101d4501100c1240304000c906103041c1000c07a084151461540505c051149400c107202c40c51406000040680e81e0743c4000041d82d503241d003812204112030050140c1086c420100d00d409021000c03c4500c11204070346c80e02c040c9107040e8030900717a4500f291604685145802481d080e2065160f41c800c1940200060a19400c2c1480c20030388140b940c00080d912020401c0180b0318080c50030580501d107a1902b0440705005001c000e034070b400a010b502940000e001680719000540d89a5a5005507641c49802a0038000e0443d143e00e40540114001e01003640b0801400f0000680e1b404031a142010130b04a01b005001c0b82e0019100348103101000c1503c02d810300c00d080c088441603031a13001912410b0a0044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824590431 1250 824589181 824589193
    0x50a11070503031e090d110c120f0601060c03020d030c02100c0206310b06060408011104030b09061003080c0a1203061a03090d21050c03090c01090f150e03010905 71
    0x30010101c0c0144a803a4404e04000c0608010161030045140c511003582800d01549003081e2010079030a1940308a44142c0c041e0104500154205001410b40808072001048844070303601c03140c4c00c0d40c661585050080069102002c0414424401d8000e118118000e00440d0030510003c034000c0b0503104428010801644807070200080523a64982203526801e0031002c100c1440b0790b826580c02c2c58a41c0520181950705904045081d94031040e08450081c003151000704080c005041c8000307031691140c4010759090411002244049501041584c06980006061201e0701d25540d00c59596801c400b41e025110300404400030301007a00600c502401100a6600040359030800e80c6101c041005400d4010700c00d14140304010b08000300180b1408140c9541c1846c01000c0e039046691951540d00d0501d402030309040600303200c0c8107454407001c0c5008482441c199441c803810900112505003051089040141010308100112544412420303050309461800c0c5810800c41d00100e425150865802c44150f8081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824591681 1250 824590431 824590441
    0x1308010f0b09100303120e10060e0f01061e1b060f050612120f0705070306090b04110306040209060f210307020a15020c041e14010513020c030d050a1107050303 70
    0x5200c100d902418402d0081d07902411502c0040c05401d0100d00c0b16060740d030703424014408040801803444264800e02c028800551100010000f0130000d94422802f01d90038000490501e0062043e916803403032210281c0480c0e101000101ca906400040d44000000c85021800c04070b2031500a40c140c1408151000c11107040c880103200b0340e03121581042c0c8081e00a250741e038517080d009108841e5030092252b40c103030312017003103090030340c14500c0551000300214600491081000641e14200e0700c200d00507480511010961418191039100840d00250303c42c00f2034000503403500d0548075020503684007404401c00c203228003049140740d501da9241c0c0540c0703a20109442c130440c80d112904802511403d51503039400c001541c406035a50340184001c0780304980350144031030130100100044030103185042091184065403120b02d41900401c0c01858041d24190754280c0c1151030318003c5540f15840a0001c51600c14110950001040b003d02070b00701481e140c0d110075101c3c9261602410b025401740300615a2070801c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824592931 1250 824591681 824591689
    0x5160602030f101512090503160b070813021f05191106090a0f0f030201200a02120a020703030804050c040908181903023c042403081308010f0b 63
    0x40b80d0010300d80c00f91510380ca01c000b40c1e200385d0078400c441104a0210703040c0307036502c2c2c2182180038103440380c800c4100c400c1030301d0306018200e01218021456511120895210300c8a40b900080b407200000c0e40101002ca12400140000c40c0b45611031216031030040d013000c0c403806480300710900460102000400c00d40920010701c00c203110340341d04001c8a1000b850b010100c1d9a07408440e100a44025208501044581007454002c0d081200c6016540300f44050000c416400b249844d0440461800140319105682030388115007804c42c0e04812803500113002c405e285603811100c490700200112032034095804445055281c0d03010358000035104e140c0d0075450b580c5c015445176601004d00003807071180032489445110001c1e40302c0400309032901a030b007440c010780302c110084080340b40301d5014034241d211600c42c400b0800c910350380d0181040c030125814040e0740192700000401c5c60890803c030003418402c2004100080070440203000c044001c43d21211600d642d04449421507441e0400c02d01c18a807121010645450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824594181 1250 824592931 824592961
    0x3011e1503050a03110c0406121b03050714150c03120f010b09100309020d050c0102010f02190f1103040308070b01051017070908070312030b061905160602030f 70
    0x114025842a000d440d60311402d43d251a112009014040401491900a0428458507024400280042c0555aa190180386d0002d5841d5804d035064040401108881081032003448100c98000c80101425400e2130f0484402c0800f80d44003031791180484540816442404018140010001000c2c6841d81d50b03280364503030301c03410043c0016101204000148a0080260160b50a00400345c4102c400070342020001e0700100403440000e5402003031045200100140000c000018031801c0c2d00900403000d00d5845031060380a40c0914010701c2120340b01c80040907203d03103459015018240741c410b40d0034143c041c03050b0a40c0d21942054804c004001000814403400c800c0d5680142800d803842e2001c0c2450000080c90302807481e2501d01910107020104000380e01c00e801c10303409013940c40d040e80d0303645030380b4585040e250308c102100002090500d0840103207480e06005440e4848114101803110b110b00e40390456440d8403420a00000915034450319000c11550310240d8820945d0504a5506041011035842204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824595431 1250 824594181 824594201
    0x1030c050907090b120a0e06040f0212010b09040f02040920030d08010b030604150801020a02010e06130c1502010f0207030c030801050603060105040509150d0f030f050f030f1503011e 80
    0x3081d9480100513041026080b285950307a401e6603819152544001d01c2c001d4582d1081c200014843c12003400244803019440741c00180c400c541c010244074600300d01500780e810b01008a54001403800004020039100c0f03c48410682c0300800000b00d81c540c0da5a0081401340c1042100c082c4542b481d110000ca040800c0f900b40308000c0c90410541c103625004102c22117100007807046020b1760311412100301810b0300c000305802a2200b0700007991901d2074600028000d03e0a030711015240d20a20300454086020241020925500001c05618075070501c82c0005401d00d44030100f20440d03581b0016050010000d2000c0c01155120b507403640e0303245115050091040350182c118a114040c200b0074884030341c7e049800c031411504192a98401a907904504170801c2150091154200c6100844901002000031080700c5580c4262907864203d0070712541140c0034080d0b00c8181030901d108001040c0c00d0780b809511aa440000b40050704114080e034800f10307094660b00542050102c08448404c20b40c8213140c021140c02e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824596681 1250 824595431 824595437
    0x30f15010c1e050109121706060903070605130f0b12070207150e060706110304051b06031915081c020109050a17120c04050405090606012309040501030c050907 70
    0x18440c0358a610380707220600400a0031082c4800c21071001c0090a4214850362604180302243c0440b5032000606042400e54283c2004030a00c00003407031510345682950104180a8010003401d07040150540b090b501902a850240c0c00548000441c00341440c006400741009100d819150004406008203600c00a441c1000f0740d00410f40c240100d6010b060503c040e02058507001c2680e0700d401001c102944100d080c05008103082119030003c003405040114080c41c072030406c03510f0414481d07002e02441005501c0d074950010040020903c062030b00c90f000801d0003415030000442000d12107444645440e03d0307001801503000891180c0c8000042d00c0c442e032001e034480c0001d1011140e02d949140e12840d660303034003c2c189170462500c80320b8014400706848481905409400540c1040e40341103206070064480d00e440f460030080020f424000101e0345070700880d4180c480807000e43c2940940201c2086d0341500b10034203801031005904030b94940c0581c40c020340c0243d10202501d42001c00303100e50503030014981814 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824597931 1250 824596681 824596697
    0x5071202060411010f05040b03012c01031523160f09060c0611090a090e210d0506040209030a0606050f0906130f060b19091a04120215030f1501 63
    0x42103040701200844482440d0141c0c417070040b154103488a00030303a006100040004400894000c03541a24002c41c961042a07600d070383e558603c40300b140c3c1002400014002100c0102e200044421754016003498840c680d900b01090302c40701c4050560b100101c2e10008c0300c090702c0400301c0c07140390008141c10407440103140c6400d840d42800030141400044110040207981d0300c0d11844500c90310381060300d561900c000d0801260305c0e500c510701800760401410040041c041d0000e40c440030031b9080003896406c0e11f034825040c00c0c88492002480105001070096070055000c01c03e4624980c0d082c48100f24043c0728083c001542414501400498050303007110798014581d43c0c0c240300781c0c1d5950046282e03032111401c4000c114a140f4008140c0580300c298000b80a090000c90b25081c1c0d048c4190101411898130f170340308040556541140e185030050120164145070f01000144082c1c3c2540c0e0423100300c140098010b580c0202400343d0481c290f403044402c1c40400240e5000c0c0f03c000c0004181c40c840c400000d180c003940d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824599181 1250 824597931 824597933
    0x1d0102040b12060609041401080d090f0b0c0a061d15070c0f030e0904200d12030e01140f160302030402030c09060d0b150111073b010303050712020604 66
    0x40301d4800c941203a00400311140000b0036a44e1a82d0440c2c421180c090028001c03c568507603c450300000c00e00450f4103600a4030962801180304d002000c048840d18101c60100c80c2c608100c0454550000350b0705203990184801c140046100c41c05410440c00c0703031b03101c001501003d0302c000b24142100c2440244200c1d840340240a507040c0c5c41441c03075901c207401c0650f20307803545030501e42504c20000c0c10031807a4015403000e01f000280100b01c0300b0500b0104403064418502224101001500a0b010300002c28005000c8507440105101e43d0219801070041000061407000482442081d1312049608803041d40d55141001014101aaa12080300710103090550440c1055400a81c8440004c28880d004645850000d5195604c42c1c8103040b4075600000650a02e0078140032002d41d032020440428041181044825006480000c810040303e44000801c04c0e90300f200051415501d4050680c1050780110001081100410a84c154000c51198135a00e40d504000c0c90281c0c00f10884216000564020b402000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824600431 1250 824599181 824599199
    0x812120703110c07030609021201050702060f090f0102030a0e0c1c02040c0e1201060509011d01030611071703061815010806011101060e0906060307060906110304181d010204 76
    0x16801020608010481903420300c0308000a00903003c1c40c003071600c210345000040c008981e1124410500a4681510314441d01503901e080c0e96040c2c82040040c0c0c440000102103042102c4400d800c06041d50130784140c1c141002c89142a41c00c241d81840d80940c1d08c030500c0100c03400400a034024231505844508180303601034a0b14050035039079036002c0c0c09240c0b00e500a202071340c0f25052000740d501c0020b100c2084004079025803030080110307000300307406406154000f1905d4009410b0803540340c907040a44029981c00c0d6611800508012a07a071070048000384042c1e4002182d20007080c02e401074200c0000c2d1249801001c0202a50701052114030303022401c014404405426035034410840820f0a00301100d49517180100c0b1800e040c802041c03030a510308840441c1103600d160915010318075000485a07103440d04020551121441d00c140000b00703461004c204a0140108100d01820b02e01e102601c0c2000d0750b540801d02ca103800a640414a182e66540f01c3d80a16041e901a81c19085114003c50801d03060110785 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824601681 1250 824600431 824600467
    0x40e010b030a2010121515180302030604080c06010e01151110020c0c01173c0a050a150f0537052b02060a0c1b0812 51
    0x3030081802201c1000b44461400e24612203a280a041341210b007019480081000e6140754400c007460382000b080402604544c5400e40543e05000740b903c2030900190016940c1c520301400b10b0040c860300c03100000160b0350038400244901d0240c03640c1da80c0c58100602c054203000c3c05030800c0e02d12010403801800003c40030200e2031411031690801c1c0071040c1e96100303214a0414032984c035051035400000c00500e020808a00c00b045c000d0203803206102c100f480c00c8000040042280c103174140e000148103641840c40700d0440540c0b80c42551120480840c0111103c01111174221901000c5603128014014006214452821114100d10000340402c0c10058119100d03071140c0710382842501e4000c1d420301e900300e86840e00202c4038603d200c00c141c4000441000d107843c0005103d1076100d54281d0131115a43c1e040c51941440440c05111600b11124071a070801489411910000e410094611024000245401258582c1c0710380c03009003c07106860441c44a241002c150b010051000b824090071291400d6412380d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824602931 1250 824601681 824601683
    0xc0815070302070809090703023a1e020c010504120f02120c1f050105010f080907090207230c03061305060f0601030209100f080c070f020907030612030509040e010b030a 74
    0x56540c00403800c0070704060043e1003e1550081156047c0700480f03416600504010715400b52030591341100d01300035803601820140848804c04106800d0850300ca040d88040c0c50b4640c99449400f15045d02003180e01241c01c003940400a80c1e5496050205201040d1414420201140f07840c481c40c0304042d90094030740e60902011111080007007040c400808050103103105042c01c1180e074100320400d04101002a04007846900c0c080341284550710103a91041c0501413066661500400e159031500300148001d601801c01540d1980302601e91143c240100542c88442416040c02000700500b80420117041c954041c2021174400d9070640c0c080009140404d000e9448402c42c0030040440e5206401038003e80b04a414040c1e1111110401c40121604070342c1e0320540950981c1c0f03895095503280d1000b4010320035134001030702614840c40c440d0014501541202e5102ea064031340840d08a03aa400390341c1020041e44021400302d000850401281d003001c2c8603005000442000030710110000700e002c203482d5001088 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824604181 1250 824602931 824602937
    0x15080307030309020f060705100e06010b22050901090504150b13150801050106050406181202060a030b151b0d0e060304062309010b0a06120b0f0310090c081507 70
    0x781d00030645d55035103100c1d4140e0501400c0907030740e00420300d45a41c6848641040d00c0c401842c1010603501d580c8001002e038140c0d003818001519000101c00303c1c0c210f800d202c44404429800b41c8501159544840044900a00c206933002c0759506091400c01c9608110a800320540e501e84410b2140701e030f48000e07090295000130000000e40640c1405480d03001403030b039040001e01d5800c100001903515071180050080326101d0b0755201c00f0070100c1f80700801021052280980544481c40064094a4403c00400c580229820001020410500441d00d07071201c95907800f00c1144007003514121400c0800c03034440c5443c4818090560440c0700300c1d024112460880c0403034001c01021001500300a011703844044c0d01c0a44480320404442203494912140780100c0f0390541550a20301c0c00d01860501440c0b041c02e59031b952f00c400b6000d040c084480c074020720314043e4090341319038038161405590310103000e42c102d6008115000b24142c821810221a2448150b0001c0c01a5024603410116070900d071030780c030fa0482d503035203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824605431 1250 824604181 824604191
    0x1b08040b070f05010207120206090307080d0506220608010c050f0a0c050a060504050619140c0a030906020408070f0e0c030103061a2707030216020f01050c030a12150803070303 77
    0x4105400b10740c0216000038010341c4000360f44c17800c1c0802425001c00180c25507007180c0b00741d9590050244c0368010500c0050079500b060080841e101d000307401c4540e0000c1e001c1d01c000981d4a590f400300b03074040c2c0312401464659585240c10300614800303010706c042d803000b54280589010111a0100814480c141d6204201b286a403500d82c2000400e024400d88540c2004080c800d17401c081c106a0780f2070b00c0c1582d001500380c1d04030040c503600b40914012024139104030b140e2501e050f901e00b0f4880c503041d484004880101070340c1d0040072000600c3d5101038400340c641c480041c1500c030300301880c0c8041a40290407100f00e0402d81e40800c01000084011281901d42c4424081407260005801a007002c120b0100203910402d4801100d014840520161540c25001d41c2040082c1d03e030b00c2d0007a0120f200300e4050601e0f08140e40c21090242c00d00301c181d40303402e0006140c041d01e0603528110031815504a4600030000440094080d190540386014009a1045e10000000d08500d400440c544e03910a808004003450349807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824606681 1250 824605431 824605433
    0xd0c0506161b1e0506010e060904030215040c080703051b03011107030302090f09130516051809210703112d0a050601060c060f060303020d140f04060f1b08040b07 71
    0x700000c2c03080071060b10400d01d0f640c156490b2203510303104240108401d06250200241c001d107003003194280501e40607009864021703820071802a9442c00200140e070801c80d00c1c41c00186040e4100588402035015402410403104c24a00002c6501240c82c142840790b810001400c01a0003440101d03042154907040050392049240007080c4882c40c0303a8030050b40320080d64100943c0e94944404090400d2141d415070b601d07091804001c4446032514054190003800110001e400a1907180240e40c000f5060012103406240702c0302c8102c460040441041e01c15140416080209504003a00d004034964000107010013410b11003060034002640c5c50703044489043c100700fa4035407500c103120995036140c10a0540f4115a1118009042c10550300c13070855505140c5000328800086500c20382003641d5040d80505070f0305060460813200803c204440c0076903c10304001c034811f0455004001c0000302401d40f141015055944000b4151290380d6805107148450300d00e000c3c1c002140081203c00766440c07295466120603103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824607931 1250 824606681 824606693
    0x90e0708270a080a030539161b060302191d0a08010c12020f09090916120218060a1503020f03040c031b060c020603060409050d0c0506161b 61
    0x1032408003281c5000e0446207400340a800c000525a283d8952000e0100703803100c241c444904401890003041e602d50f4081c5050517603400c0c00ea00c2c5140c03005070410b0790901030400303800c000780314543c102144c200c0941c2003180003022848007050001c00440c1030844c241a030a03d14001f10340c056503000c604000840304103104c2c030300ca1500042c51103013010306411141c45e11002054000c24070fa02604012400e5a11540c401d0341590080703448a80f10306000700d040003690030030300841c00c2000e031814406015040700c0304002e0400c0916100140104c82c02184080c0507130050002604450300300d03404415604c4204038803a124180858100c8a601c800b4511414030040c00310004d00804c0d00d8150002e07400018002401081406c50041da4001c0a10540c0004424005040c2840314450400450f01c01030750600589807a0025507400f070b0015001107a0070b0800e50303540e81005101094400400c0c105140103090100c1003011980c84429460301c17006000c2404805030520350412421100d50950700d42e41d2b010400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824609181 1250 824607931 824607991
    0x405040206070807060501090f200304110306040b0402010e091e0612030a020309041b081306020f0f0c070501020f121c060f15140316110616090e0708 66
    0x1e0040e000f03545a40c81c1e40740c5203018240a00c030701c802240c10112641c66042061044000c2410b40c1c04803849010103942c082801500014000e6481d40303070030381c7d902ea9991002d0100380e10a0344114407100c0b003450a48009449107000c080294002d180740b608000103048203010300781c0026034038084200b030303680e81c140083d030010310b40d40e10340d6114080410380350356064001010388426001100d040c0300e001d0501c015844400016800000092a03810105000c3d2040c20041e0305201d0013000c0252030002c80f90303080d100a5014038015400301800080020385502c2c10b209400c0640001d03c0504041c0840141d80f503500c1010607000d420341c06000485000b0011089a0021400321040d024884140d035661091405100d61048208000010444000e11442403402d0b03501c18885000341410354882051200b8009600c50384030080c480100003200e01400b04020301d500c02c0c0c0c000e074842c00017100c24600c010401c0c502f980c82108001501010300208030f0f000004658403040005444403080d41c0703000703480c62000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824610431 1250 824609181 824609183
    0x2060d1104081b061201060f0306080d08040201030f0501030506061002030424020d02070807030f26091306080c101b0609030e0f030c0f030c042412050705040504020607 74
    0x304000340008140c2d20100720002140b00200e0a2034900400302c003800820312541482c0e19a030f00444d801403080318001c641e10003814405190001c0e04c00c0d22003001070715060a1500240100c1d1201c0f08200456a040c044c1820003001d014090041d94075650325180d50314400340c440c0d4032070700311120341c111a14420426180240380c149104c2e20030340b14540550101044100d86e000c01405480c0e00c1074529400000c801c01112502c000070f003003403403850b100c0c03040b89604154102c0b208018000e00962400c180d4944422420300c50b0003640ea26100389040004a000801c0301c0782010b41840c5007002148004546007407496025100308040d15a81174089034070034114050000fa511105075440d050014641c04840050b00c0f13920b4040b1169240401c001912407807031109076140e80480c07043e01913401c125a100300301090180c215000300c0001000601651680c0d401c03100042c1c0c0100160444529030340c038581c02032000f01100a034449058640d00d8481001d400350900840d00c07100802c045490fa03108860000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824611681 1250 824610431 824610461
    0xb0a080a020901120510081603050607080c0403080d0c0f090e180a02090a0b040b0a180906021c0e0c012c030a1e02031b0d0b09010f020a0909140105090402060d 70
    0x80d2802011906c680310301c80c003c000c450300c0388600040c0c00384400708010090381c2c0c20400600c05039840d640201c50300c070030003441c4045d810401d100000010b1404d5010700900a000000481c0880880000409840320180c04004021008d5002c201c207090850b0b8080c0c02540c02540c6e014180c0b2503001c501d1422003110402900400e01c03000704480d0760300b55404850240304c1201c0c1400107855190070490b800c01503014112481c88244601101c0c03502da03030303c101c00c0703248100405810030b03003004410314000c280c2c0030a024001d40c6460b210041611705001003025041c090820a17080e0795003220060780514908410322181580080380000341d90100180c14000368440340a0240a441100701502c18400c1c02c0101e00a21032100c003042c042003400e030304440b1903070060301c400501c280c503466901645c1c41c09420a2255580e50b544001c030050180010300c6810840d40700c0c0554145030604140c102c44903aa805850b1000d07800c0180190383e5038614050b0007540440d2400e0b1140b00f0480300a004000c50103c0b1265 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824612931 1250 824611681 824611691
    0x50c06070b01030b011202010905010302090102070e0c0405040608072607080717010b0102010e0613060b18100807050619051204150e0a0b1303091a090a0b0a080a02090112 75
    0x2008801101c1506a900c04e1150070121303640d40541041c2d400807000024040380402d182440306510a9003d0880b8007014811a42c11950307070410031640010985101e1100704000900380909d00380f03409650010081d100082000c41c0c41c00c096809081e259405030040403403a02c08034035042c1c9041040714060540402501c0c1119a5460001c410f03990300502040f19500380900d5588540c0117100710f04000c40f80c9405480c044d680c045041c600225007140894605540c0d031038610f039039160300c00d2085e0030041001c5030011034102544249140e10a5a201c0012540820f80c02d00c602e44561054032140036080c101c400082e80180b034151814010132000b4026038213214104814440301c2da0f01442c1101d1510003c000c0c4081c0d00d040a80c946c1301c10740019040c03090303410105021030702030048002a0b50003071908002e00740d12124079440e48420021680c2d01c81102081c20151460320480d944001c100340e009003890301c00d440b04050001c5400402c450342d41c0341e000c103140c040b5900030b0480180c0c7c10441e0204100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824614181 1250 824612931 824612933
    0x1413050d0203031902100b1e0103020906130e1e010b07020603070302161a01080a0f120915030605030d0c15110f0c01240b2b060305010e3007050c0607 66
    0xb40e544083c6c400c1c86501800c00c40035006504190806512141d1942c130007006908082005401a44c081200b46412407410402c070030240d010500f02001400d144c0d41041c91710b0800035169900c401d1024124501c0119020040003144102c008407070156130f040d14410340700e540d0080150001e0185803084240001900d419004101c08030020500d09024064001c51990300d9400c220744c0d84d610ba200c010102c21a09260a02155103031032480504151f034a032450740741b9152030001201080e40b26881003c01e880700c07810701242c035052000311003052561a190f141c20714503132640c0b0045201aa901e00c4415500e5454410001a0004860103003921241c0c9558540c0070710751890091420b200354001401000e5981c0c0d0304003c920840c130045482d008034050500400c24024a549002021030200c01c50302d45002ca80e9410417401188000c5000f9800007550b40e510452071801e010441040c42200041214018004240382c1c80700c00c80410003040c0c89899900c070b880c01524040145045682c840c1c00403c00300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824615431 1250 824614181 824614183
    0xc070b0903070f05031207020705150903070f060c1403030402093402150a020301051012090b0a0911030c0a06030b011803050c10020313050103051e0c0a1413050d0203031902 76
    0x1081100074286c601d076003030b611b540d0200e8644200f4041c242e844524038869000b254201c02c080d1404a6009040c0c82c0220f94a07844100d24102d654800f9000c42d41040142d000d00c8100684800d400341c00070007951862800d41d0001e18084402800380707281c0b109540011602e031404d00c1d046401a035070441c40b80c40d001090400655201c40b030303040803400c03642e0344000100096114000d5034102d80c000b03002e020b00b052919405444034a5003841a40c2c059030b0f1108010042003214800038090200110001003403031325424010741e00b51051000c03074000c0e4005035000c089a1030b500320110460364170340f40c0000d0b01046440101c580c40c0721b0800003c240b142cbd018000c1b06100b40412a00f0412000715003070f52800c1d440203000c0ea240d0003003000c1c044003c07004160420095003c0d0300020f0340203588a0b0300340400a40c00c240301c0750189041c0c4001e010b826010880c0c1d0000f40c5c10903c51201419040d0a281c05c16200000510f40411140520380c05041d00c58030300c1085450402c00c1ea480d14401c80d0b40412170100f010002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824616681 1250 824615431 824615437
    0x50d0e0d020909190327080303060603091f02180409030c081806030c09030114070507030525060c0324051014030a150501080f060915061c140c070b0903070f0503 71
    0x1e51b0003444e035041c81915142009001100316028800038600b59518002040310581000b04040454000c544246d102d14400300d24400814080050042c0c0752914102c05440c01d20008510798011413810307041401280e0000e0065042c0f60380248c6442c2d80c1d03141c0000021580e03908101a9400003008170511001c1d400d03da01401000509800810014000601c03040851038261507241c0400e034108040750120f03203c2c1d0000c003418202d071200907607408100012041c000300d4007030043c1c1d4015a101c860180e810303814010701d11008102929400c450165688410a4660300c0c81a6031252071024139507580240162200302d03110301c0384c07400b2035102d2402041e40c401411130b05002c809500b41301c50011400398020b2109a0086489000c000351aa542806210304004041d190203000e00089010001c140e45980003400c00c0e4034401101096a0246078030241580d0a00b246040b125004104010301c80141c1c1c400e89180c076801c040ca40c482c0380c4840d0505800c1d40300303107400503080042011070142400f07400001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824617931 1250 824616681 824616707
    0x130503090d081909060f12140c030906092a0411072409120305060f031621080306060f0408060a0915061a0c07090c020109050d0e0d0209091903 63
    0x1c07018100d20f83c02c2084503070121502070b04010481040b004140c1d240700721402c0b0381018032520005124000300c0d008000801040740d0404400742c0020410070700e8402070041680144210b4000d10502030700ca01e503215000c514445000900300100806801c6564a030484100003071100540d82e940c03181c50420304420040d407070082c010148401c9002c5241446031003899501a000000c140303c0040d4010210040c12003c0c0074039a00541c590903000765079505201072011a050504280440323441e054503880c4044c0c0c4800340d141c040b010981071201140d410000c4070313032143c0d044817410743d00c240010360040540100c0d00a0413240c41000c040081191150f03000b03802c0c0174051a403240010740106c0d000025204503005d40d21038004110b40380312000400c000030708801c0d0b0110064940c0c10b52588450f80c2240c58441c1c10b100180e4460010380140402030100d0030701111640b40c60042c846800c004107150440d0081d00034000c020b0000000c004007010b2241c100038038442107140e5218115410014101c03020051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824619181 1250 824617931 824617957
    0xe010308070209010b120f0402030a1401061715040311070801110a0311070c0e09190c1d0915070905090703060608010b1e0d0b0a0f1d060306130503090d08 68
    0xf00100720104140240c6080642509840100313546100410040000280041303030035108041003600080d5174400380030030350410300000181543c07401640e110103810401c03c0620070b40061080d600b00031020700015034405e80504260915a0a02c40454904481d942c4080b07411f51a2100810290714050001c00c1aa04280d13414010602c070050740300740710700c40c004006000ca15020710401c0381607900342095501609402c10f55003104040d111003440c16261040803580640103540a1148800c0160042d41390000c0100150329071070008003190fa0756a009030040d00400e0b80e0300004031620710130500140504030140a10703009050216001e80a06140c0c040c004c00b195009d80089200c3c10000152455503020700f50700c100c00214042d002109601c4801d1440340e241d1114055031050712040c90720401080c4100d03649110a00e07040d00d0071101c04da8407001e10b010b11205403d1100175500052000e8004035210301180d04d40d5007600e0f10781d1a510640a80a420400b4014590240910b010103040c000540138 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824620431 1250 824619181 824619199
    0x80c01050703064712010e0403050d1104031401050a1d030703031a2e02030a09060f030603050601090e070905040b010b070f1e02030f0c0a1502070e0103080702 70
    0x2d80940e0041d0107046403400344641001311505004102d1180d5802a007100c02e02080302040b0103940325419180401100e00010b220303038194181646a6005004481c00a03019040a41d0005c0c018402c0e01519842d041e102d410030048130401da800c0310000d50b40301e00984d1000c1c0c0b48200141c0a060201c8803a80400c1c1340c103241151103030b02140ca0501c0810340e800914544180303980d00b50014155515111030441c0b60440c0e00c04581c54081210000300c104900c0f0080c822140c82042d25418812071140085410920042440340c0d0403003c448290303045d904040604006100c1c0c22030050500b07500c041d015116401c000602c0341041d0307011051102d581401d0340d020a440e02c0b0800281c0301d0950740241050701000040102007285030140ca0343d6031244a00d091a4071060319941c0d00e2040123001080d0090f60259840111b213000c000c44418464807001074a500100d1000143c0741c2000307441206100c04002c48140d0001d80300f400101b0103407003d41030341031455849003000025500a5402207000311151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824621681 1250 824620431 824620441
    0x503101a0d0201090b0d0b030d1110060b07030c02010302160c171c140c060103080405040e161e0504090503030105012a02010c021815090705040302010c0219050d080c0105 75
    0x4601072114042c2c0685035440280c1c907102c4018046d034014801d0303064039a6200c2034510259024080c00402d0300c0d9a40c3c0b0304a03400000321426017030020451124902c1c600d44042044600e0b022415911400c3c0c160404040502090006802038400c4000381a1211560007044041018006240e41075034030101d14403004e0742c1d1000005950b914110440c810400b0940c5a000007a40701c0c6101854110404d041541000f00c410740c00ca140990a0f041121071080200d4144843d09080c8a6404130252400082502c05040f07440300b0070040aa0040c108a8190319120140310400c0006a2000f00000307081048400d00c0740c1441620381e00b00f17000700c500058240e04032010800070030828540080f551118016041c8490f03005603030485031458202e8020900320040d040c02a134000031a485085a2501c40c42c5040d2000308202c41d00c5c100400e00c4050001c00d000510250340d1010560300d8059050345c1c820491a00250308046074641d07644502d40c03103200301c0c4c103e1080010400240400d504e5803402400261a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824622931 1250 824621681 824621689
    0x3050d030908030f04050703020a06170a0908031b16060207150209030d0c030201060b0c0a05100513030813051212060d0206030c0d060906080312091908130503101a 72
    0xd0400030b001c520090012408068040408a400a2150048842851350b0b42d0105100403419800100800e06074032015011b4884c407801070780e20020f03806003085422500c0c1e8545415001c0940300780448009800301c03058410700e0604540c40569411000030038010700e40f40c508042d600466085503012401c02500d00180071500a0340c3c01c250000303010340b15203452001c0031a408040c2070015411592900c42c001420440c03c03004203091103c94018000010003418158606914587c0b82c840c0c5902c0d2504120319000d0f004a081c40a6900d8507101400e07440d0740c04143e46c0c450786140058110300401c000145884081e00003040030b121041d01d0040d0176540d000410007800360b41100a500020100b002902041d0301100500d41c0d00c9040e00c000650540b10786510f4203d815a030031064a90b84000744078100c582043d0325003a84901030074020100c00160340502e1148001d0984003d041030408034034403101b20351110707009018100107401c4541c0c00c600d00b0804006002000454a00d05660b0229000a410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824624181 1250 824622931 824622941
    0xc020c06120403110c130e0606031204060302130e091515060a0305070c1205030105180919050709140a0c02010b0f060d320603160302090a020403150603050d03 70
    0x2140c007019021a0b980e07902c081e107803000e12000c0184280100c0141c0006581c0d40100e00d10116202c4000059240300201c0d6a85000b80240019220b41d03c00744a1001c00c4410400306c409445031482e026032240115065007206802907000810464101070400c40400e000140a02c0d010416845e100300707580318001441d0b804001241c10030b41000c001c12005041a000b604a25004202d03807504240c45891511a010268040445c480020390b0003c01000070b1303e0a042d44440c0001ca00c0801507003400c0914203941c0c0c4110000d10301c108280040c5080050280c140f2086000b0110128288502140c50544841d002012171700e000f401c0d450705c00b4010030148144039946038aa0047d18500c401ca00d10400c11142e42c000c12840031a5548030421403542c14803140c51026841180f0a503100c20350265050508003140c0200110701941c03044064848040341d070421001100d4054030301c022961601e0a00f140644500e4001400340c410803844149030411aa0048003142d00400c141c80c0d08007010101101958 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824625431 1250 824624181 824624197
    0x190c120f0216032105270f061b0606010509030601150203071a01061202040b0d0905010f0f1413120c1b03031706030102041413060914090d050307080a020a0c150c020c06 74
    0x4c00007003080302841004046e2800f04100078045a158075002c0c00042c030030341c042514400b80481145405074241d1003089800d030008001d00f006402c154652000c06d60b11481480364800b80307500b810001d85541e0003441207130306036504030150b4004001036202c11404214280b0540340020781012000d980100903200350f07800d82d006451514a4440310a450f00d02401d90000151415503840d0740044c00d01a140c072410402000107580410031340c00d480700385040007000404000d425126140b84034001848502e81c084080f010f0300307041c60142550300b0550581d0002ea201c204500004000200515402548000c00e21421091203080b43e03880e101031509034003441c0b1901c08171102100124801d4078003a1010350306244890800140e580d42c8400130300c05e0360741584003a2030109034501808068401405821080d003880e041140c078504126800134200d24009090a04160b40412412801d9102d410001c4001da0000b03802420555048204d00c0201092107403000948120fa03100704407801c2000036a5196 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824626681 1250 824625431 824625457
    0x50d0e09150906040f02030702101401031109040f0f14100b03060c0903010b04060b130e040503030601050706090b012c0103050705011b17190c120f0216032105 70
    0x1c40180301070181d90741c2c010300501c1e030194440400c283c10340000c0c07014612820442c2c1c014411230100040c10f20840385c640c031010501d808030704014004101c0114038958107032410384802026039200c3c200901d4414180c140141171000d03003405007050011881009060262803c15160341081c9001d811003203030310750030031180c00d03801070000a02c08010312409004540406030010440d501c060b0005401c035034164100651045002c40e00b4a24014220400302c0500300c1e1030700c05050340c2000d0716000c2d07490000405a90411400107a4541003103420741040b00b000d60f0158858045507141c0c20700c41d056001c04044041c6800350882c0740803007120403030b030440c0c100e80d0007401510500b802d0000440c2d4012081c3d40700151565001b11a030700203901d0b80b0206940100c120b906903225107000b4810444004a14081c40c1004200030b0306601144c0c0011650b0000000c0382083c921020400c502039041c02070b04407000c0c00f110200d9000001380b10f0b24040400b222031203200c01d049001c1c0050415245d601074031807003001d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824627931 1250 824626681 824626711
    0x403030b03011b2001060b1b03070f0b0a09060c080403080a11032703040311011b02061605010f0c120c14030a0c1206060201020903150603032506050103050d0e09 71
    0x16490082011000e04c8030808a0240304000030520300c1d0035a800c90b806062a1200064400300b20742c0b9440c145920b555428019516181081d1102006a00b042c94081c010380c586501203080c49407254040c7c0b19441e0701030030601100500020292100b50102c03425404100728030009070600c0f640780304030b12202989141071400d5848030b00900406840c06102c602c01091070042a1803d908100040c000541c804c420380f010401c00080014004649010038402e68580c041c0c58600503500e1400703485050002c0f4001440340c084505101d8090415014103e04c81460800b90510850340005840d4084e042000c043c4500042180101d0303010014105c1c490020400340003140302d11300e141e0092803e450f011300d400c2d280600f640700c994003165429070100015030360011b01005103040c10300c00c0b043c4107400b1281400f960f00e00f600200b030b01c902c11800041300c0350a07480c145500c0442c840307e40b0441d40313030010800c025030360b100e283c00303540c2c0c0d8a26240c40c00400c0c0c14404965240c035101050714403e011020104071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824629181 1250 824627931 824627981
    0x3170f1014040b042c070b0d023a06050904030525051c030c030b0a14031204030506100e040c0320040c0f0e06070f080f040b0703080403030b0301 64
    0x580980069207031540152603107002a46035a49002d00300a40300c114215020442c1e040783c028010107131401900c04180c003c03043c100821041031069894000b02c007400940d40f44201000014401080c000003120f9125060500481c114000c803080d1150b008101e040204640710020013500c2c0b541124001c0004104000070304050407111300d0790034210400f10007207040c54455950242400351502a0480c403640c440090390b160755050241880803941800c4c10015600a10003050307a4a00034003a000c203414600d00c8801d05074400300507024040792811029a200d903202c0c0741160300c8440c146d901a0350380f800501d012841c1c24624102a01407940b20000300c0286c1d01c1d40d510b4001780e004009500c403110300100c01c1000552101d00805800300810b80d286031802c007286501070044085199024007032801400244006860740b8040090aa00820a1a1101d80e12a047d031100d2050382c106d0600c405000c5810010103400501407400389120340c6041c420940c80c18249803c0311200f00d0116805881f55407805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824630431 1250 824629181 824629199
    0xc09090f051b0c0f06090109030306120b0109020a09050a08010f060e010b090d08040b0c0a1b121106070c0306020405130216020f01120c020715030606092102040903170f10 75
    0x420365000f403905131500b00700c1140e462420120121181505d5075181c24034a8101503061080b6030140c46040710350f00384410280c55110002c001406068815580080d0068640d8020320240740280002001c0880483c0c0f0b03000d10a000e4a00c0344022407400f81811404a5030000a4103444d0503149001040303401c003581c0e003040007203c145004040e01c02c500200b10104d0004c80d000000c0c1001c0706040028a145501480c02181200340e80c3d041d08074001041c481440ba03d1000c1c05034038a410380090402101c40c1c030210003d84648120580107090720100000041000783c26009007007160800c680d4254440c0b240000e203c240c3c42a04200c80d084a01006c0c85801450724203202912001c062500030105181c1c02074000c12110b01901004c05a40084010040c211030941002004e2400d45004c0c4030341480d040c40540810418080c0ca080a481107103124480808601c1e0030503042d40044c4184003004c030b43d06015015414ad0240c070304024001ca00040e40ca8140d0351060341c021513030030703811841980c1350280303207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824631681 1250 824630431 824630437
    0xc14150c0d0f090807050d02060c1605070509130501050601020307080f030a06052805060f0301053105060102060601020f101505040203101503060303021f020d0c09090f051b 76
    0x41122a03035607001e80d2600780b9a901c10401c0c80c611030001640e5035140780c1010382c80c1a030304855144c11540b02c03600304800700d61070f001900c0c0050100f0000302a441c1251901034204140c036041160000b46c40020054004000c1070b0320071541b409040200300300d464881c01207850f07101c1c0a0014042600400490005045d07040045070f00504c000b200149490b01e9500141044d0114030b0540341000c0361000c15a03180c920091094001c0c0790442c0d0341460441300780c0080380d80e03000500c40c0600c500b00103081202c140706445111126401400820150071143d4907290b001000d0980d2220300610802d40019010350000440b1a5145440b42c0140104250790b402d50003e000b050021003408500a0000103680d240d07030000d1030244034004141e035151402c010207424050300800098040606206040021903000314426030544800c2e02d4000040043d82051406031241800310b41c005072400f0300c24948194450041020340314881c03428009245408040400e5401c141d0f00b03c1094020a05000c82d044014001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824632931 1250 824631681 824631697
    0x190b030d1d030f010209010e0f090a0e1002070804060f210c020102040f0e0a0b091009020d0e0a0b010501020c010f12020a0207080a03020703061d1b0609100c14150c 72
    0x740d4500c11a6000c41d00300703c1d1524160308169004519400c00d0740c0c2080044815007400e94504a4100c0d00000145040e00c010b0181c105e10766403290b04803d418028051907500c00d8030034800307542c0c2d06641d140c08030944e8032511401d80041d194030104502d42d4461a40304880070b282e1006450b424000161480003084062a00030941d9801c110010349c0d010b2000c2444000c2440e102c030704d109490820784080c2910001c0010501c207007903090420442c0591003603444156503844400607104c2d440461020b00074000620700301080e00c03400420500b040601684541030700d20030390076510342c0010342c0015540080c0a41a07003000c40d20301c60082048580c0e603400b42580e1026481114401ca90f0b805041d4100403c400c825001a00000f00a00c24002c0e01c3c052103500c2c2802d0196200400d1070031800d19290100c001c064088048040001c40d82942d48130300303564000100600d194140d0341d2138480a06100000001103034a400006e84420032001c0105404103800d030f241d00070740c4c11690f4a890003c03a590048403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824634181 1250 824632931 824632967
    0x90c120309040b190f15020d050a080a150306020d0e16121b0e180a1101230c0a0b09152805010e04110306160c0c0914190b030d 56
    0x140b500d1110b003040c0311500c018500003900e4000c180c00c1c920601b045039203800408003958007080701100300a0f8410115121083d840c40d0814a64544107034050142444440003c0e03419040407011060060030390051800c0d507240282003107440000c1703690f240c40c0c0241c3c4c0e042d00e0740800c14090400401c84154400313403150348103a1341460b04581385120003808003801c4d00700307080503027030311082109041400c8010030108200c00010709240f800c56482c2d400800360401524100011038200100c10400c0700e00494076119110710860b100c4a42c840681e80e6008002e9040d52910b0109010585881c0e01140301c49e041d035034802d60b42c41a1340e696001a1718260640b6500c184411044003003444117086403040c4c0e8086c00405000340d8103030400703040c000030500c000c0c01d2140c03280c0c01c00020300c02840e0b070031006920354407140c0c1041d007140390b100e0400004e400d001c1c1c0d210949440c1082c544604518980500d107110300b5600901003060301c2564410800c841c1c0c0c107400c43e50903034026030421038818060f2061510524110fa = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824635431 1250 824634181 824634199
    0x1709040b030a0c050102071a0f0f070f030e0411030408072a060206060f040203070f08060301090b0c0a0306080d02030d0f1b020d091e0b0a020a0b010e090c120309040b 73
    0x401103403601c4001c14050f600c0c62550401400590303418020400180325042912858a40b00d00c000452032181c0300f03107840c0103040094648003c0f4615001d50302d1458000c2040da400600e9410060003510200a031148038034905035080018059030f800340c0e8000d5030086000c1c0c0c01d014003a51402c0f0540c3d0040d180c02d0b060f0501155520700c04c4c01006c5084013401055020b42194213110040c0440740c00ca42d400346102d24018000c11007120744c4414510321a0707145282000140d00c2d04c40100303006101102026110645031010454034956a0f0b0092000900c03d580c204281030b0b33074108160312045400b20104c01a001040301e2000c452060700914047c101040d00040d003034191040c005440e503040d44000c1c000d6084101d001c0b40540d00040e01d00e004005110741b0030080a000340321855401d10500510b140c0840104402d0070340e600c20890b041e41580d01605080c0256100c00c0020403018088600061500c42d001402501b410a05003851078501c1404c011810800d4000410000c2c1110401890308040a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824636681 1250 824635431 824635451
    0xc03020f01140c030406030605040203091504080c0102130e151c110d1a090309030a0b1b0307021b0319030c1103010507110106080c03190602120c0901020d0c170904 72
    0x290b009005420390180215691458044064155545540030910540c410b001300b02d1140400725001c0d1200c02d00d408008026925031500c5501d500492504592540c4041010355002d0700700f00c9014280c40c0700e04c506500c0c6580300c550f04180c0c1d105000000350001900c4a02a0043c072560400407080c3e071141c45608940d400c2c1001244220303618040507200f0440e04042c0030201809150a2a04403915074061351424a48201095807010a01170090581c54400001000d000c0310b54000c41030b040c041d01c1d42c20390703030709140d14000e50b42d12080d030350300040002c1c043c1ca00e149881d0004980c1507410004005000022003a1001da4000da2103e005a50311840680c021149503000c0c8038841c8203030100e490341c078481c035803d61429003101c041c1c1d0400f0016034001140c070345059500140d2058001c15803074070034980d4002032504502038024a44c1903044000e0000c00d0080c0701c1200c10182500b032000fa801c84054400e201d00c2102c207000800700180420f100d80090700c8213a85003c0c010700b04904094004a001004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824637931 1250 824636681 824636717
    0x10503191202100c08010e0f010e060d02010c0203011a3d0e09042003010908070b060109031b090c0513173f0a0f0305040f051015120c03020f01 63
    0x4e60081140010b200d04014400059046407454000480132881d140e0307581400d040c0080c04002801041c410628030804104682c490390301448429400703402444002811150300809900f4202c4092003030039185510000d40c031102140100d28140d110030b020b4540620650640c0605a0308200010899800c1c90f0700183e844840042c0d020382e100d0300c0c45001052600082e80444004500d1440c4280d05208100000c1b070075080941d8081034100145411300d17140e5200588968400354401420000081c4800f000303001d4581145086400190050018120828080b80d04d80b1404510001c0d070101c03480140820090784c03401c004075003400c0c01107030300c0da910580c140b26400204104520303480003c142c0c0c0c010f641840011080040740d450088500301950b0341c50142640303012542c254101a6650001014021941c1481107032613001000c4d40d0341c80c80402c00c0c1101500c41100d01080c07000c540c2d0000101400701e5144561440c0d0000030905895045500300440000720440e41b50402010003804140044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824639181 1250 824637931 824637941
    0xf0903020c01110322151701050f0901230904050102030603060a0203040f23031305030d03092f040e0a12140f0f090a0602030703020f01020405090f06040608030a030c0801050319120210 81
    0x46c81d482d882c400d4112a070850f054814142c02c40c50244152681711001500c5d00416207064400c800c042d50607040001d41c50a9002c03d00551081d40503041c0b0042c1f1060150650055000d0700c001d80035240309640e6003000005074801528010110420710034051301141030110107105140a24400d800d405441c83c80140c590342009841030140c0c2182c179400c2000740350402c405c10b080700e2142030500c10040c071501c406082200242410152040d55040d50380008000c41e900100181c00503c100301015507030045969030701b9003000441d040a0351140442d01d0600a2074240742e001d4802440c68682500f01401d2902900845038405c00b4110038400d802d107583da00b03034140b07020700096801141c84030010700b0024540744c0c08070f11456283c0d00c1040140015200d200c07000d98030060924070480f664450714081001080164000301041c040410b40b6034400703526800c600b03d480040c1e80e0f009003590329001003503114038001d1542800e911301c2d1842e00f0000f50041c4103002411803140103441d5040c110802407030a443e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 824640287 1106 824639181 824639219
    0xe04051207060f02030c0304060515030607030c02030c06040503030417030c181c1b0509060303070b060a08030703020d09060c0c0b13090f0903020c01110322 69
    0x816000307010004410f04085581e85841003401100e6007040d902116401d040001080798105100d40c0c40349010713801401b07003d45031182c2e030040d0005c080016014055000601c071055140000384101c52203140158059a503e181610303003401411071019082501c100b090040c440c039001c900050350139498251414288079524a00061707080c0030200c000007040c3d40f500c001d180c2040140c1c40304400800f00740c2c1c4100840c0d5154400c0000c4004110307070440c5c141c2e1090211001040410500540044019140d880c0c1d486d19503107450b0566200000a03000350780095440e400342a40081c0d400c000700a240392520f050300711680c3da50390b440f5542c030500701880c0011800c00039801140b080d40c0001e25001c40100085030b1061500c60203004240307010350142c0034010f48421503502a031180d20303000313025801643c5019000c5001c0e03448440040a201c03501c261030840420f03441e5944501c42481 = true := by decide +kernel

theorem cover : BRFrame.Cov 824460431 824640287 := by
  have h0 := BRFrame.cov_init 824460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 824460431 ≤ n) (h2 : n < 824640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
