-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0861
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:13:45.393645+00:00
-- url     : https://prove2.me/submissions/9baaa1f5-4d4b-4269-ba67-e526ad017c64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 154676258 ≤ n < 154856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 154677508 1250 154676258 154676273
    0xf0c030903170c0703051c0815101101050705090a080a0f02091905090312060603010b030f0601050f0706050610030e100c02010209060301030507060215010602031e04080f0304031e080403 82
    0x69070941e0b040396103400d51404031140340041c550300480c1c0c1d035401100310207c8000c0d01c8035003118170001c0c2c0c2131010203400c025084804080285600d02e003d054180d078448851842000300c03450b840307052030081145040c40d80005202d0342c020b90385d0741d00800f07110700c0008201000048a009441d08609655400f0006501300800e030207002e0a118881101640e0f41c00807502244039071800341041000441d070324840c50160311042d1800514851081e0307420f01c01085030080780707401c4941c071441e5448000b00c0fa6883c0c0c1c0050f50b0302c1c050001c130b0382c14110011408a08020042d81f200c2e01501c0c040345c1e00c4000051049003241654004052907041c0d070010710042064070781c47e400822600000d800094103080da480e010840d183c200742d00c1a80e041d030011900704100c54041c4400c0007059402d5080ca0000d60402c00c000e50f13248910349560301d091140180036448005070f03038103403000b03400100300340c4400340e440000c42c80da80d8000d8003055502c004855401303140600003103600030340b1941c000651810145162035018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 154678758 1250 154677508 154677533
    0x100617070c0228120210020a1e0203152410050a050c01060504090b070801060302130302010c0c090e0c01120606080c0d15030c03052a13110a09060f0c030903 69
    0x400081c0e500c2d03001590000c0c01e0b0f8212001d00f502d0954183c3c0e0307400a004000d00d50442d083e010f019500007180c00002314041c2d50b00190740a821024040c003644052010a141004190440303515440041c144a0455640000140101c0c034104440303400703001078410030921311890301100300820750400001410034010f101610312800710400004416554002140c2501da029208441d488141e604010300507030071101150140000340380c11030400300035498129000ca414007010781800940383c0604100051180400050941420203101c14280303100701c143d035902021103075404039040e00c0646041484922615044071007940c4c0340d0880f03071030340c0d5911052680482c143e9051151103a03942500703800c64407640002948582111100c0038958180715080c11041044030702421403500ca202031809800d843e0308101103085440050441010100320003c2000c513203040002100070811194468000d13180c00200c481c03a8403807591703001c4580c80c104d44035100051b00501052290a090010600309030105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 154680008 1250 154678758 154678789
    0x10501121203060b030a1e0207060c0f03090b0109020903030d0c0f0905010206040b0406110408011109010906050c061b071b1a0c0601091a0303030a0c0e03010b0604030602130e100617070c02 83
    0x10744800c05440c4142c41a49d211075419102c03280c0b940d660b101e126501102074510040380c0d20f020040d80081d0b9586209100781841511000c68010401c4403050341c0c00d008543e49001c201078108079010245502902d0101c5000001d008070700c140c54001b80c19400800d10a100300c1d40140c050501c1e07aa180d49120082c40c0382c108202e0340c1e01c0c05000204900030309214105800d40a8516070752a40300c0880010042c03180d9411072800c008060101c04505c510009606070050307503807882507074640c2c0c0d00c00c003c802502a0040c080c1c0600c0d0740d500441b00340c1100e41c00001c10340e064a40002201025480c100005126081031980e8070740c40031004001c24055030744640c1000840390030302c0f4400200d10300000c1c60360304143c3d50386105c15640c181580d00b06030403001011004e4030a034000d000d003502c40f00004115005620010f0035183d00040c408036000c40401c100d80c040c10700320500c51103a0074111a40a014600c5000702c0000c82c8031003800c58010311004503108c3c03003080e59907501640c040156081c0404440c02c2d030300130b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 154681258 1250 154680008 154680041
    0x8030606130803030915011a120415140f0f0c0403030c020a0902070303050612070602030901050318010c0c12031404020607021503090d0207140603011a04030203010501121203060b030a 81
    0x102d196481400214000d807481c0e4001c22070b0b140d0080c40081c4241042e0b0029071b4100111008a0060b18003006032121460041a8882c00703582e142800d000a0540601f03603030b43d003403078109619600040000041d0041244031000c0310540d83d10b01d51048000c0b0b055a120ba10b0b40c100380700400c000313840f03401001615403010301400c110a03545c80d650070590b00301000c101c000ca038544040000908141c486882288201c0b40144507440c42e02c00060f4803442038001090400000100040720201070000781152811450000c10038072140c00c0d4020401c030074035003048808070300d2011103610300d610901442207903113620003081000340c90703581c00c1000b65801050100e80184440d04900110300d10800518461580e070000f0f0004c02110580003400d0502a800141c485103070340d10505c00700d440350002c1da03055400d00d810342c10183c41074001400c5e940c019079000a516600f00400866440d55240012540500c1141d8a42c4401c524074070940640759103010306000c201007400000c50500790750700942012070502d80d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 154682508 1250 154681258 154681297
    0xe040609081902011506050f0c010e070905061810051c0b010e0108160e0601270b040302090109050f070e0105070516150f091806051903050c010c08030606 68
    0x4580880d030b000035031190800034865414069050f020300420842030101d038240c010150420038042c1190046880400d072103100401c450426200075448605072500010403076280b10fa440013001e025000c04c45105005030b100310420702c402121409001c1c0121030b441e4900642c14148010f110349003481c002c607000a007126441040105852100050190a0201300903c280d0f0524064518020b081001400a1041408200151f000304031202c0c0d0007002c240ba007040d64109007002d150301c030402c03090742c0d000c82025000005020710013200104100c901c2521743c90300c5030383c1e1176020800720f400865010804c0c801c41c4000a0406205190300942140141000390410a81d9251b144c540032080c1c502c202c0c4c0b04e00300c0c50203001c01450080c0c80130b5180384030300d4075030102c00381e9840040140095101e0030500514030003103e0010720321500b205000d000e000d00080e03810000440e03241300c06003041c4802d44a9001d10202d4451030b5125030191028180c0020f1820310f035403101824007100380d100f00b8840c070050800c0794 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 154683758 1250 154682508 154682513
    0x1409030d09031202070c08070b181c02060c0c1306080a0f020103231806090712051509060709051f0e0604090204170105010905060a0b0a030617070603180c0e040609 72
    0x10242c001e175030150b1840100213041228140c0b070b002c0e00741c104440c03a1070140040d284d828154041041d00c0c00040c0c90b82c0074a40407088190400c19140480290700a50100b880424101c0000d244c00380b1070000c644002004141590280444400d0300881e01d4982041250b400440d00303180b00780388940e10600d800100c028070030443c07041003120425201c280707201c240203100e81c61001d00c21141e940c00c8080c019240d00c1c24801d84403542c8845a1040001c81112600c000e014050203216a5107403006030051401c80d0310700300480c00d440386c03000c40c1c003400424003a51021032142081240340700c520b40d04001c0000c1c80c0082c8841a902141c031b8404c503681c00f0703030104804210120980040c2c0018140c8984116044e030104e541982501c60581286c201c5e0b925080412007603a641105207030468a03c0103160b035a4078900c0100b2005411981c1115802c0e195100c403400d02800006842030455206a4040047c0300b038a0051006607040b505000d0241a210780b8280484c141134100c0e50740140c4180400910071070342e80d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 154685008 1250 154683758 154683761
    0x241b051b07170a020108011a1207140409060e13030f1407020409050a02180405030f0c01020d051602070803130b0a1205010b1c0c0c060218031f1409030d090312 70
    0x10007100b01c1c0d0083c11258085582004925016008104440001141081c90080a801a20340641c03102c03243c08041841180030760301d00800d44141003803003a9500d03116913424003d003041d03214103015490501c00090508520074102200140e1581d0f0380c8923511500102100c0300c02d110354100310552020462480169200c2c895076005030f01c030360040c0800c070036035004003d140840a440c2c8082c0b02c640070304120000d0404400ca80000f440d001c080fa80f5072034442000c6009004034510f110320b071440c00c014056808250400781a6150003a0308850781540ca4001c000c0c0c40e4010150505e0001c01c441c6014020076140c040034041b400d4152a100441d51040c10404040d0b031000e03440700380d02040005031150000014210342e16501d021036420701080b004a40d00810f08010303131a0181c50f280d80410f110604000c01507601103122801802c507141c2442c00c000810500580000358090540343c403c60030f120041074001e540c03142e410310003d1403c100034280140042c0580e03c0b412810091601240b0381c10070300303d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 154686258 1250 154685008 154685039
    0x105190324080d030509120405040c210b031e12030406021201060e1005030f060d1506030b06090907060801120c0b0a170c0f070f0c03241b051b07 64
    0x2c010003030a1544001101a0454070058002040d03600b150203140c6484480c03404550859406039030000d10004004c0e011600209190b07000b8010407844a0103140300201d42d00294090b8404600f40d528000002c00000c684515940504030260056902440c0c4410742d44040c40c0d10030b010349c03000b610741030f441245800810001d0304178101048064040d00030506182c165042d03d40e0113400c0540ca54200a0010340f020f600042c40140f0682108c950803041000384400903440040d8001c051024a07180e240c0702c0099202154218050810300f0300182c0b0f44840050480f08444080e202c03c0a140d08100509a44e1088004142c800c00e02c11000021403804c141e00410001c1d400ea603445445100018140c42c03039540162100010220611210707800c00760f408103e4010984c4000a42c00d80300c0e403442c1a181160301c650000d1711001085188090301c1502c050a030605541540003040320a03158001000000c82840307000001810600c100b81d07a000c40c104080c107101041c0030441340c8941e80c0780f43e0100c540c000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 154687508 1250 154686258 154686269
    0x918020702120f06090d052503030e0102040617060303040605030f070507020a030b0123010905040c03060b0307030915020705030910110f0106081002030103080a0f050418090c050105190324 83
    0x34104505c44a0a00490b000c036a020b2916918144c0844000228003d01c449000c52802840304c4840c1054001d074401214401402c0082d03484503590350380030f4070001d05068204100c0c1114000070b829494048100e4060b00da00f0f13141c032401c64030f0702d40c81b117034600c64014410400c2c00340400c0b8910250f0b82c0d1902a9004504c0350b0020100356041864002c4007101610880a500108108502d5543e07001400001683c0c001e481c00102c0e0b594204040b00607081c194049245200b00000380302000b41c1c10340009444038003400304c40109000f00c2c039210b4100d01c81c40c103014119410a004000c99494503a0381e11180c4d01c224545280c10426400c00a402d000b07070604d0020541c1e5595008000816090000c0910280508400c50440d032541c6c807120414481c100f41030b0100302e029a140150107010f0416907000d880d140a04460f02200c0f83c0c02040100440c2606646524150710002183c0d0321503001c031194000c4c2201e400c1076950f400c2c203007500540b102c0c0341c0c1c280000c02404e1848040012141c4000c000f0300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 154688758 1250 154687508 154687513
    0x8060604090609051605030402031b04090606080627070b030a140a05090d0207030203070e180a08040504061517040203010b041505040c090806040809130603050c0102010c0918020702120f 82
    0x1405c00160440c00891003d2000313022090003000f0140e60080348502a804042c1c0d6000341940042002800070281001c2c000c020354540341000c50428400902180300741007055020181c9585260700e51405c050000e40032196a110350001d0254000310300245400c885048004542c81c007488654a050f0305c0201c410b038800c02c0e50303082000788821041240440008050010b86129400d44d00866101c1045014204503080340c040402c842c0280d24a002d007103201d2000035907035a454145040720300ca07400b912540d0302c111304212022400011140200d00320103e1f60f103d030300318040a101e400044410080c0280e074155032701c1090400613101c602410750300d00c0824001a0341d641c1800200803c54030300700b0032003080240c42402804a50f00c00909107800035003150305036444000410005840c0c080c03403800031030300c603003007100020410200103800300441c0001d030000e100c40030004030111145843c070301c1100813003200114821441c98150340101101800605034030340046065505070324000d0300b0303000e05190b0b5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 154690008 1250 154688758 154688761
    0x140f03090a020a0b09030a2d0309150206060609011b020405010b070b01090b010c0b0a06050a0603020d140402130b0301020d15050109080606060a080c1303060b010306170303070806060409060905 85
    0x5182ca02c45120141c26840140e50130207604c5c6001c00d41d100d141d00c00044c00c13200c0e100000009000c80801c1c0c1000703102c0c500000b100d150b07024500100380d0005407140d110303680c6001c8241400f4500104079507200300f00280045052200a400454126030700414845454159041c80e40160702c66000f914003034003102c0140b99440c806c83c50404c2d03521105038002d0084618001854070640c1c1e02501036000b80390804400d00c02500d802c14402d0040c1115400992b1000c1d07a10400174a242d016005488070301c070400c108000c01c0e00e0803000007a8402040364001d600910740c44180348801c41c03079803050342461000380006080104aa81d4001140c807480386801120a509404014075a0300c582d20b200542400400f60031281801c0011030000e0040f1502c4406022900c2c0010700c002140501341c40780c560502d208242195687d0808000400044d507140e8006401c01c4000300b0390802c03e0b6460041c50312228003d51541d40c910808994103980504003d0344010b0070000026901614002c03d0b0143c65100c2c2d00260a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 154691258 1250 154690008 154690013
    0x140c0306010e03031c111219061203020d20070311040e030708070209040f150903110c0618030a050313060f030b0306060f061b0a050f0304030b07140f03090a 69
    0x14020342c100d209200b58010044242c01e42001c0350a144174100725140440e12002c0700d000b281d031500071000c0003003113002d2010402040703401984e03445480c220401820408a910342d1001d4140c2c0105a80180c00360f801007840411040c41703114100d280c05101c1624903444c05441c9502410b00c0c01542c425128444080300e00b482c00e1925204d0040a109a54001c51400354640e4038641640240180a03114009200000d801e0052140000a0780303075110741080303000700005007190020596100b050300050010011001040300c0004c041510660040030603040200300e4111580005840c0b100703a4144c040e501c00d40e400030342c0400150880700110440042041d0402c003000f4184590340c42c000d020541480e0343e03000306407004a01585c0108041d507822080d15240300104840784281b1440e058a400e900035641400030010400304440740c8aa01603400307903442d40039603551364001c034040075208410801c00301d54480d0060489508004510418600340001405600d0103a0000c56615000350060a160b004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 154692508 1250 154691258 154691267
    0xd06030506041205041206020a18030b0a0b030c0d08070c05090403020f1b010906050c011e0606080604050402030303062b08040e060a03150903050c03070303061701020a0e0105090103140c030601 85
    0x30b400800d844c043d4102841c0003a41c24818502580281ca5241d0003d8804130b40c0384142c5c516200300040d2201450360503039a18000340c10a5048030341203c1c0514000400303a003480c0100304030218220003060352b5142c20f0780340c03a010b085034404101150b18888002000403a6101d54a44501c1540660043c0441c50482007981c1c0c01c01c110b1504100302d06141d2024442580e8003d100c2c0000c2d03403000e24081c1e0300c80d440c27408440d004010318100c1c2480007a0000b40400703c40c03a9a00940c05440c0c2560340c0c0c0c4c400c0c0c5c44036410310040e190242d50095060300306100003039807800d01403403a01d6111501490039010055000701d114010f4006801561303c501d00283c18400303d60340441c0d0980004080d910340052503d19198800310f03154022115140c40d80b038000340028984500b0503200d420b070403981520380d29800c7c3d15014004100a00c1015030300e98030b510042c2074082040c0700fa241d0342c81081d12500c04440c175100044456030f00c0f0302d00240c14140c0d41c0740d52003841d402c1c01c07800320f1003400f80c40c0307284e030362400e00c08000340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 154693758 1250 154692508 154692533
    0x2041b180302060301030b070210060b040513051b031315090303060815010b030903091f17010b0a0e0114030a09020a1e050607020f030f1510050619050d0603050604 72
    0x820310211120410040e152181202d0450341c01500d00341c542e4540700006ca0401e841c00504540d050300700710700400c03e0300c64400100100d8001300c03580da03029414082d03800203032442112680d00422180003032035114100c2034003c60b8400210001ca01c0710110568521001380700001d8540c142c00d5072a01d00e0810981c01d4070a841c0076248210080c0b40380d140c0d41203e00102c0e00140250130010401001103040000b040056842c00c0d180203101482d600d40e84444e07410040e0800c90810005034040780b003c05e2400c41c2c03481d80b605a80a03420503524100c038030b400c107980d0307907800c214000c2c1004480071104841007454000345001e01055131010540c182240100040c0d000f4640151920440b028100c440c1a409148001c08880303054500e691290854000205400c1d12424082d4041c0104240c20005150104503014070341c42091100d601d42c0c5030000a417803030388810b001d550740001d000c00dc014224051402155054211490841d103080030310602002030780e2840e401140c669000c1c009020400c4004810304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 154695008 1250 154693758 154693787
    0x31c050109050a060b09120c180a0b010305070c060207080405061c0e010b0f1c020301020415030c0203090f1306030204180b0903250c03060606080702210a0e060702041b 74
    0x740030321421722a44d80102e00c40c0d5440c1074465044061600c000f00c605010b008082c042c0244640b01106c0c101500c44c902d1f95007280c80300b0240745042100101c030340c024820305012f07038a5a030300c1401180c2582e071200002e44c80b010050303032000300900000031959a40c800400d400c0110385045c011701a40e003142079080e0f0300000364800050741855015101504c0c0c0c8200c200403004100d811105c66841c1c0c1c0303a01c040500344040003a4040d400014086030b007a000103805c1207079001da07543c104403401e2a030390300302d0b124003039541420b40c41040300b402c2c101903140900404510751007882d000126243e61740e0002e02201c80715450f144204804000c1542448800c041c500d500502100c0034601d02000c0c002411030703103100c04414a4800700411801c00a22400e290b030300c0081c0d0750001d0704006154a490000e0070507802103406400500c619070005203e031703000c08685400e10341e206038140d0801d51207a90503030f40c5928404d45180c01820500c8042c0141c4e40e030340220a0000031641840030610402070004000040755140c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 154696258 1250 154695008 154695011
    0x30c170703172508030702160e040803070e1807032409050912030702071701090b06060f0c010f06170604030c06050601032c0616091502031c050109050a 67
    0x20804074200d405003891a540e81605299900842c1070408441c00094844102140040c0f50500401c90144011409200c07103400701c034060780045c6048001c1e0701481c040c00c4440d181e844080740c009041d510103503800ca4294103003c25103003c514003080003040000c0903940d50741d11200c00c0c0300c01550140700c2c1542941c22140142ea2034040c0c1b440d0300703104034800c0c0b00e0b00710304a40d107400040c2c112206100010600c001010b481d0360f030782003009000f99501900c0c000d0700500c13541c00f491032409040511402c0c6040744e0014000b009540c40c1c40070015070b9003003020031a450000400c01c40c0b2441e0002e110749142d401c1e8180380002e02500b01516040d04240c226015001c1c0e41c82070040c000401c2e04850841141a8041004206d541d0f5940040b0040e104188040c140c2a1601d41837517002c0e882110072030810640182103680e240d03944212281d41000c61503060004c03030a4200306200c03c001c042c20403050440c00c0d00480b40340c048040105070100030161800e6021a54030001030040143c103004868014142703410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 154697508 1250 154696258 154696273
    0x1104050a030209040c0e090604050615100c030e0604080319110307110a03080403060b0108060105180105030612031b0c0a050f01081e07020f010e06040b18010f020301030c17 76
    0xc1032040d6110301001e4403c02c106000182004104200c2c0c5024180036840703030030b09080841c107503951004c050342c0c02c4546e1700501c400999546560250210642c134004c1040141d81d40029055898401c144419000c20a20200810107a1a0107001703100a00204000310b0303640b01514880342d00d960b40103682400700071342c02040c3c82d40c1d000000155040107803c400300303911000441c00010007803403282d40003e1216901040020600c035140d4000d000a080c00c1c2c81e1705903159142c2004480c9072003030b100b10200c0840da02081c1c241d0780d4400c0c4042c6920403406000403150917820001c3c6807954020140a000c103680782c25071b010400f48240004071f03008100355103041030385040000281110740c00320044c070304020150380002c66401c000036511000901c0748103001402d0070310080007500c3e042000b88803101503003030010240c270343c1c1c5000445601c119045141c3d03100d2921003002c00c031050301d140d9038020b00b550740382c00221010001a01c0110300852154a60b40e00c2c4500d032604c8981c88285011070740041c1d401441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 154698758 1250 154697508 154697519
    0x3030304030f0504090f06090f140712090b16090815010902030a0b040908030a06080a0b0a0207080d1a0108010902090f0609060c0714040e0a030c0609061b02010501091104 75
    0x192500980d05042891421010704800ca90300c1c00380354030040030a0300f40700900034400f4280e40320707000307542a03141c0a0229091341c0e0517010545600300e188248100c910800103002c4c0e8414078800caa8038206100124050035191205400014155032449491060001f224409038000700c40310010b102030005040c10180780a6400480172051040c07402c000c0e000000030b0222a8541d010100c2c1c220001c0c0104910300503804c04c0b58044d0011900842e10714940000814802000908980d07140e61003a11032034580d407443c030820b01035008180215100542400a0221444139000720710000d1100341d159030700e184035a0001860060306030300a0700868810070605180b62100d0b400108000d00c00d8a0190390303598140f003c165940310308900e105080c06601008a1a151410088030100c03004540501c01c10603441080c54442c500070744000c02241341ca1440074002105c54101488850142c540080c5c24483c1c1c100000110090f80d1507140142d64a0005000031001445503200c1d000c0100105070525080c80d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 154700008 1250 154698758 154698763
    0x50f030d0e040504030c0602070302010e01060b180f010c0512070203010f05041a0601090f0f1406120a0b0303040b0d0b011107061709030c01021306021005060d080702130216020a1403 80
    0x461600035034070b0741c0005017414040d203003203601181d2001c4115615142ca040007802800b20014a400a5080c240000f880050060540d040c1c2c45090340517204040c054020400000940c84105041c40f0340004c00310007042060021082c5d41ca021150a5560744a42c8105421280108000c015891800c000e10012a111500c40e400c18195000100d4664030340d040160740c1c0754540d40c0328030640241d82501155501d499014141180d4a84150015086105041045500030741c0c0440500c4003010b4005405442aa040811842e02c0a02030700d1034582c95081c0070030030f41d100900c1c81800b02d40354029204c19503401440070b900506400d001d42481424000002e104c807240880e112000c80901d030104a101e5428402c403180c04a642c0c008550b1440c2d640d1865111000900ca40b5025010306860111a8805401520301c241c0b401080c0c02e12040042d51002c01c0c50b0846582a80c014054041500307008107148028040400b1071040346945803030790304c10808404082e4000410803819409201c9243c1c600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 154701258 1250 154700008 154700027
    0x80601031a0112092102150f0f100909080a08130b010512101a09010603050105061918240e030303072607050301240f0f020c041401050f030d 62
    0x246004488010348240c501c003d001004c101614102c01c1c0c2064458a10403144d41045a806940135240101e441c0d18a00964100485102c1d80401000001407a0b44800310344e2241c0c82941e150b0041c4070360b921902041c04951720300070100c84c11080025002c0001d0b030071031141640f00031400c0041c82211425562500b038100306214803070090b108800e1000744080140070340200c6400089080120611031400c18001c03621604007607000d102082c001243c41c1e4800d00131981610301c054a400d141001c000701385400c40001d84035076400c200604a0000c204c40311040c01c0801003607150f504940c0501c0d11445403c000c0c01c0c2d416410240020342c8036000c1c040d1004410349902820780d08119500b0080c00460000648000f614040c1d080160000c008860390000081c44c10b880001104c1c03c45c00507958007035001403512140d003e001c50004000c201036107102d05c804241e02c091a00c1550303040304014010900b03440c540081800d10310b080350f0060010341403a0300d420f0841c1c0704c120300070080210413400c003802c203414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 154702508 1250 154701258 154701311
    0x141f0303030209040608011505040c05130b0d091406070f09030c030807050703050304090e1005010e040b1008030a020f010b090103031704050109140c010e0a06021015030f0506040308060103 83
    0x10049012843ca9441d680180020003145009124100348942e513510721001da0300519100c1c030f150110410300f21344110191901e1072190422070311038600f00000c98440350094090f10940544541400c00019038021014858050000080101c0e0501d0100504440014125101040700c14141040032075544400039080713a421040c0c984e030b07503929404e2444c14020240c002520034400041c000a408040e9030194104150400c01e540d4100e10303402c084402d0300c1003071145050f4809000003080100fa0313041c00154101d080d040c0b50030302e46a82c0f940417a0440d0000303e401c00241c2c02031164080310b0203003800f4031449044111150680c943c1159806064840f14522a2113260015000075040000951011070500c0e0803581c1d40d166071181c0841c003591340c11000112400600c484007001d08508041310004c0507035a040cac0103028240c11a00014000307121010310310015840d991070001c0484d03a00c030300ca0310149002e0809400e852805060141c284000682201c0c1010b03e84075109a0181041401e070782940e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 154703758 1250 154702508 154702511
    0x90221040c090606020a030806100c0213091b0608090c010c150915090516080d030903090e040804031a01060e0f031501081e0c0a0e0c120a141f030303 66
    0x200d440c10460715044040c2c000b14aa685401e4003c150541c0018800c2c121501c07035540c50710345030354807428000d60032204170000001c19031060401d00180703814500c40c1400040a030002070b0303000f00c03500c2d104000b40c004062110000494a0300303000959100c032190390300403048001481c90202c03080c002001d514204801034901d5202500041d2600c5054100e41141c0340c0042241030350500c2698000020a078150088980d40b06101482031241010335140702181c1007100a0a00121003000030780192031407107070071010800f00030300c04200755004641941c0204e016900c9651154107500e050b041840d410b030201c10980d080c03c401006069401407401c442550190ba440465002120109103007150111204245041c040000700300e2410000d0481179051521b04001e502030328840084d5250030301c2c8804150003503c000e500f4443c5002c4190b6582d0019040010b051500350b50706062540b0200544042440c00d4452425141d5900340da980c05408c03070903c2d40303d21880d107100c2242d2201a45107110060a05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 154705008 1250 154703758 154703761
    0x903060f060328031110050a06170d020703020f040b0a0b0705010b010c210504080a050c030c0105120c0702010e0303210717040314041508010306060b0309030307080411040f1401090221 81
    0xa00c00e00444404d00c006034001c1c00641000c83d107032802741c5034500545062aa1803041408075000010300502c00c591290041c0888070b0a64090003c040d0088116981050b05c178000041e00b515402010f100030054498115260941403078040d094a000f08001e604000c10040c2c40c20116400d00502100310030700f00c0b0508c0c8030071410402518140179583c00201a400340000400903c2030118034084584021000d90710701041c64001554140107441c0780324064801e500008800b400110018105680141406070f000c4101c0c0000926507404070f5080fa030480c150216181500c40300300035180e04400709042035140c1420096400104000041014040103051a12010070b03072000702c211805880281a00401d8104040e40070748882c4080c8411540c0c14079051001a465101505aa002e044488091803641c0c60705442202c0040c0041c2064421b01c0c14400590740d80e980e02d200700c00c0a40103451001c00c80c40982c00b40d000420300140d1002c60701a00410007001410b80c840c4c40000b11013a4404c0c0303400381d07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 154706258 1250 154705008 154705037
    0x417070503180a0f0e070f0306060f1409030a240501050d03030203060a030b01080d1b0302030403030c03030f021c0e010b1c0c030b04110a0605040e1303050903060f06032803 76
    0x40c0820358841e02c55aa01450041070005405d00c80c240b01ea00103441e140995500c2200803000c444c0144100400242c0c03120a050000e880740ba9400150300d540b81700300b41049241c80c0001d04155a808086178640c012001c1d001c1824510107601104e8080310388108180d40c5803401150008445041c01410541d0000c00128542d4401880c00041d642000803401a9a114245030f0f40c1c8105048468001c504215000f103c1c103190201462043ca034941d02460402d45580e4060300c0b000c550040840074961185850f520015080c4064040c40d011001c0910181c180140c500c1c003140e003401c00140c0380e64107001307100d15151590b110440c020340020031810740035180c60800001142541c1c2000700000660300c14017050001d4401a24224a03049032041010390b540c02c800d64003482644504000042080001074944003840540a00107001c0e0800754a0030b00d1701c40010703007000d1f42100e80c00d20204c003920030701015050810180c601d0f2460504640d035502e1100603004108003039a40c00400b0415a0040444c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 154707508 1250 154706258 154706269
    0xc0b04050f0706030c090f050f010f0212030a0209120a02011d061e0406090503071206020a03020c0d11070b1c0207020f0d0302010905120708030a0902040b0d0506041707050318 77
    0x14000501015140324544903c0000c02801c00030b019000040c0e008000811a407055049032400c0f00c4004000b9500741c0c413020015a8146060386980c01940200030401000c01c8180006600c0703074400c0c1000503902d090441c00c020000c50020381c560480e52243c008000141d8012060307d1060040b8224030b9803514a581c0012054414801c020940340558082407011100500c0604190f6120f03440750300c5031540710b8060503070354031071442958a00e60b910102e01020401c15070003001d401256150143c9000c40d40610a4038109481c08032000040031042c031000c0310203050040c0b1000e002382c1d504082c43d00141030780542e059411460620003455001035000115501c4141070554000e010306074124086842c10080e00802d908942074841c2c3c003034800312000c000004800c50b9440c40c1d00c0a441c50075626481c01708801051500000c0344c00c41e03a60b00610019a4070003428802039845000145130915083c81e08981c82041e00c05444100340307040c400c45c3c00040c0084280c034840d00d400403601c0381e900d090100042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 154708758 1250 154707508 154707523
    0x14010806180313060918020313060b0103090b0405150a0501080a030311130e01080d0c03080103060507020a050f07180605030c012318011d011d060c030a0c0201090801020a0c0b0405 79
    0x48075010043e0300068031030b4100005900b2213034183c4090500c0802060035800741d1004440b641c0342d0b545921115000101140d00c99096650103150005600e00103648988101d181a1790035151584a0000500300d0b02d1580210b80d80070400e01410b2102c0d51405401d25502c140707950005080c141c41d040021809141c07a01a41d10b582d1044000030080b95803000c0300107400400703000344c0c103060007100c00007801c107400744000c64402d035890350343d203001c0ea072858850130010310700600080c085020311240030300458410403401c289071081c00c01400307a061030502c2074110700b071114051901d0141844c0080045550100d60038a04090a0070941d00d85040d1a412622442c8841504030a030b00e000700b01e406050700d000818051144081e01c9a02408038440c1c08a194443c41c1c0700498001034102c04040192011a4078140d0038032400784c4041d0401420195003415034203d00c0348000000c12104e00344040d90b901071209801003146d400210f00d854600344008000340c0110501904a2700a100031600b040070400c90309 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 154710008 1250 154708758 154708777
    0xf11030d020d0b01090b09010c021210050405011d0f0714011b05062e03120e0a090b1810051c1e110f010509040b1c050601060201140108061803 63
    0x4559070340d8140d82100080803d019140d0026400b040085140c604060480d04d50b040c0c16103920005482c594204408842d45800c0c07079806011b4164254120304440c000d16019610480000c10180e80042e016035510b6210303801c10450b43e000701c185071923107803000c40d00320300f23032801e0760407204503042e48000694a101200d0388226803030320a43d803a41e06000340030451070301900c4900288031910443e007480c02c14200071088045154400980100000740d2039800e00e1b161000c150030080200c0c08488009840c0c01c0d015408000f005d5142e0f400440d5a02d044034850310455204440380885080c0b06907034411940c0140a02405000c40c04550018941039495000140c1e83c0710354180030302074010010030408985140201d03551290540d182c1c0152030040d407004040ca0069482d01d06082482c4104005000001d0200f038016213500101c90f100e264000c0380c0f0400a000724000c0c00c42e5494420002d003114603260f02241c03102c41003030050041c0d00c1d012500540004510030326101c0d140c2a1300136581180b107400382c0c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 154711258 1250 154710008 154710011
    0x2060307090f09020906180a0909260f041403030d02070305090405071b02010c1a010609031703040218091204080a0c17070e09210c0c01020a030f11030d 67
    0x401100310392000551058030090301c040c1d4030381039880440d001640900e411580d80507030240420043e4180d041040c01140400400c000180c0e60340e4071200c0d0450f0065407068070140703140c00c08000d00c1c1001c0c10384a1058441880b01c0c17803420840000741c40180c0203501481c002c008212080d01055036042041e102212401881150346194902d00035006034409404e0340e025038100000139404034001c0c40c1402121340c160b1030a40040c400b50740111134102c09604100d400c0100401c4440c10600c103549024041c181a4541d0541d55007541800d42081803100e0100010078020420400161200b040303c6203406018804000d0f41d413980e680440c10681000d8114190f5200490005019400000d807041c807075000c0d54a0311015501c031045540071000c940c41521080e840320104102d42d20000c2c0c50b5640c41608401038440c2c80200041d000c00030400b00c0d905050041b0040340c04203042000b4080d6282902d0b003400100b4035100c544c0c0d00a49201f06403843e010900c512032907107000321310090084540d8040300110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 154712508 1250 154711258 154711261
    0x62b060e0f0a0b030604080406050a050d0e070e0f0c070b2e06110303010b0a050a021c020706090905070e21010e071703040f1208040302211c120513020603 68
    0x540402200301182e550386803500304a81008241804a4030320300850704445c0e1240341c83d09204003607070030f0b82c441c0c2c2c40342c0c007080403c106c04455440c06103c0c03540c15032030394006001024a05012b00c2c40c0000d000d0300c0c82011048240a0100d4550411708403601e40764021100d1201c0c0c1c1d588803a2038690300c0e0140880350880c180549845050380400076000603507100e5151800c61030f02003c405544c0380001d02418807024810070400c03001c0742c0248060681c0c8062881111039545402d40300f407201440411441d0301503482b20300180040ca400100340000780074006c0d01040f0781c0c1741c8242e009102e40100541180504207605030081c0501e01000012080380c0c2140c02400010510142140d840501d4807410300d02c8044110022400d400104c00c51b402c84e1050108903020500b013808003400300c0310780ca40c11140c5040400001005865800502c03900d18007103115614140107c2e03c516040031072a00034000200401582e652826030091444401c2c2904c1480009195650404107000748440d0000658060400300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 154713758 1250 154712508 154712521
    0xa08040c032102061e061507022809021207030c0522030210020609150a0204090e0c0a06090b070b191d0f060708181f0e010b062b060e 59
    0x48030703410050b40c1c0f0303401c40f070590741e9004d0316424043c07480b195520f0415000020514070310700886100c040c1c0c1030f54090540351841660005070b01064080c4680c0310000708401a810344450600310310010450841e00358a0802c0c2c10101e1013440d4070042c5a401815950013007040418410b1080e00c5144a29840101c40d000c4100360f05000100340f8030080b449011280d214804003440828514016010b0500034400c03011482200f45502c0d0000b0301414940b5801e00002411913140e00410055442503009083c1805554041c08039109503a00b080044c0f205008042000c90b40b600300310f5800c1c81c0c0044070f080e01c0e61180c8000144000300c800744001d0b11030901c84410540140c190240c242c0c40c0500d002c841d200440b0810494a03103d0440b40071001c0b62a5a00184811040c8280c1240003282101a81c24807404040c02540d2014000e00c01c0c8000d590715100300c448904240320304801100d045a9541c181542c0b18014200d805145800040420280740350b40601505030300320b103014200d01c600e60f030158034200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 154715008 1250 154713758 154713803
    0x103030908070528030c090f0b0f09070c03050c0316030e01021b13020c060103121704050c04050c0d050f0105030d0504050306130f0f0303150e060915010905060d0504030e060a02030a08040c03 84
    0x800c401e00c42d25280c2761450040e072901ca2032404d807140c030140c44c010f220307655180242c03422680c80400340c050010400c0501301143c018002805580715140c440941c0d0805810028020f40708c00d0310280c159400241071407028132910a05054100084840c0100c442a00d00350b01c010f80526440d0034207900c03842001104110341c41080a00b084400c1d41e5008040d04018082400a02c3c01c1e24098210f402190b481c0e207041c2065048282c1c40b90b501d80d501440e0041c00f120890860f070741146c11400c03501e5002c0c014003c078582441807120f51860b07464250f04150800e00000d4427400e0241410b4415410842080c01304610700000d410415088200400001c00f6418098040e00b031903042121081800348000c0343c420303802403409010b000040e00c05101a078420030000e030b1124522420074140075000c4030019540d42c44c8402010800740400d00400e1905103071030050a442400303807034944606400d10101c000c4560010a640c454049860814480d46170b030b051003130007043c4941010302880d8114101e0050000c06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 154716258 1250 154715008 154715021
    0x40806090c03031204060b1807090303020c040204051f020a050d020a060b090c0d0b03011d0c040e0d140a0302040b0a021e010501050109140a0506120103030908070528030c09 76
    0x201060307800d40c40c140000c0507120700c540f0740f903800c1c0f00d40f001c00850041005540200b2219001400041c0750044e240c900344051002164801c00103100048244101a410310000e0f21140e001e607030960510341131000050344181002e100c01c5840c40e200602c101e02c0f074802c02c0b18100f0550810305032151003c0c1100020f4580d51050000d40740c40703086c407290f000b4030b0801c1100315100709000d09556040100103007114014001c411030b42036043d920f070000140045024100d64613044c8a10700100802c40d0004240300070b5401030802c803061500124142101103070800c102e503041c4000080c072542c0d04c09407c04150003e0245400c095814100820308044a9800056240388091210754502000c1109540a0b0070b946090080c6c0b8000307840c030720040094503000110040c541400400c499002900c41c0b011640580014040c01c900842d4000100141030700121801d0140c00c41502a206075820030011483c03200c04000c10300b480700d0b03085100b2014100d8504460001e183d1201c00d0940081c2c2d80d80154018001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 154717508 1250 154716258 154716271
    0x20904090b071b120c051f0221010311090907031a010810060b1824030f090f061821041d061810031a1603090b0105091b040806 56
    0x883c0c0c19001c0b00c06810480c590380c441c2c0c0301080000301d800005044032003510150f012542031190b840380c40040d101c9555540c805400f043c3d0016180c007420705420b030a0f64408984d62038030120034401480416841e4441480a14003911520015140c00301e9082c504440d903803021703000d0f015032504c040001a10317107800c81c1220300b000210303020f601d0b40300b1000301198030170700c0703a04040d902c20071405545448410804602403030040c4090f00001407589504d010440d0307180200c8244030000104034465441001031500182c0100c0180b20140e20010a00d5803000080c11042010103060808501c0031010456018060f08001005a440c807030448010702c1c41d0068007841c0c054034281208280540d102c822004c2c81030000400541d0401880868400c12000103850035401d080c0307404001c0003085070f01340d109101c60458002d019852421404800c2481c5100c19003504140c02c003400d01020682d840107040c190303001202c2d8003820781c84030254245486043c0070824503404020070002107441010449a104030f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 154718758 1250 154717508 154717517
    0x905030901030b0117010e0a0e03160203010608030c0615041e050402030705180f04051c051309050103021e0307090905060907050105030f010303030f090c0305210f1b01020904090b07 80
    0x4110300660710031200c1800b88407171619081c010800100d900344013541095048800181c0c801c40703664503600b140c0c4003036418003490300744070038640850a00340301d458020066000518249845090ba2a07283c9401520702d0b14080c7d0100000700d460365079680041182058540c68003002503075100036a015080458050b0b12900030701500007818100628034044180400b04648040d98814a041401607009001510300d8840e1a08e60701c15401094615002d02c1c0241d1250341e200d105c0404815a05841500000020381c2008010001600e0b60306814400200b101440406200b10002181c54512694040c2c1102402d20740880c040c450b0108495000d900a0401e45040640307400042d102d500c41990a051402c08140041001c64800d5002009200c0111008161920143c5449040017215082500e154010450078143c29040e00c08404001c20340381c0b4080c0c01e00d5582d250801a900441c15040341610a09040032040700080d4103c2e0114103000304200326404c0f0720304200445034021610741e008039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154720008 1250 154718758 154718771
    0xe0a0c120209181008060717010b120105040b011107120c09050106080c0d0603080f0c06091c0c0512040b031611060703090f12050309070f0315090c0801090503090103 73
    0x400060080751020071003c1c205404642d00303020003000080c0c1c024a41c4100488500c00441c0481060142c0c81c001d003c6a503a10700040c491501e001100881030380030800074042007183c0082c01280b6002541180c070200e50002c0c1113442c80d4010b0b24800d64000e00c040c100c0c041c10700081922455070702c0e00070350f407030003541c4d56007441ea29072003070108580c03013030160f000800c0c603050004031b201e02040c00401000100c003030045407241d920380d2a0905a005103188095219000c2a142c1018200700402644080810010b0920716114181034800b0310083c040d0f0010005655100824440c0403c80000d102c5c0146400070703078542c3c3d41c0c9803d004c40e42040d030350341601c7c03420854014805407241010800072110b400180c00c058407500020781c024040c1d01b10444110455187c000045001200c100280c88034a88800e0b551785025901d480c140072854000c080380b507401e03c0c1e0170320110703150200e0703841c2c2081c22185c005008030782400d08109c00819903012440c55800e06400d0000c211000c005010261070a803414040d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154721258 1250 154720008 154720037
    0x219020d120915090c080318120a0b0705030c1c0903030c1416020a0e09010f0612150c020f16030201021902030a030804030302091003200f03011802040e0a0c 69
    0x554680001c06080100f28107015203001002c0d51148583c50f100b04031080c2031640d9800d049040d504401c25819072510800d0160805017014800c1c0307103107200341ca009050103407210f95504090360390107044c2408201d4003100203940d80c00d900045880c4501951242440d0f005008462406410440c60440002e8203040141c0c0480340603020484030101c10104070340c20082c064642441102c0390500c140d078001116400010703211641800a400303034440400110b0402c0508030110141c0e20958004540890250401c0d008110100b8005002d0710b03404001280d81251100100c0c50003e4440750000540548011206056107503a40541224401e809031143c1d003080d003601915112490601940613040484007600203407154450a030f00c1072013818010f041c0b0003104007140d40340c0b03040112080402c1d030759159100c60300c0356074102804100e00401e52a107800420360880c1010700041c8260204507480035280110340c00960103840240088103941c500318600101141e0140800c03007e12000301c0c03106070b002e484 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154722508 1250 154721258 154721261
    0xb03090708010209060a030e010212040b040203010b03031c1d061602070803040b1c150f0501200703170f031e06030d21020c07032f03060601050a030219020d12 70
    0x4e0100040c1614100582e01c8000c0d00500b07900c09050000d55400c10829090030048440240218043c500c03045141c54680b051500b1640a50034031071281e8070510540d14400780c100859044c5180d00500440d082d2040ca444880090005280202a0064504011a443e20300c0b0f100b5548100c07503400c94008a560f1200141c407403140c6d00440103409401c11600e03014004510f072040c0030300801d1800040300341100ca200150054182c0050307100f400314020404c240c0d80d100c000050003040000f150100c0e601e020001503540d19091000420054106035048000341d88002900e5540e0010440f4594038070b800e034542610000c500070350980c0c030341040c00490281c1c00c000a83d0152403402d600d400308440c5003000c05100442c41c82505080c503d408204a482c218418030221004511403440060030250200400c86400c004104010320700c544400c0a82007a54002206600100203080076562400c80c43d0040740680f0440007040081c0702446c004000280e0b002940c002a020ba41c2c1c0c0b44a520354480803081c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154723758 1250 154722508 154722517
    0x40515010b040603022101030c05041a09040209071101020c061006020607020601030818040218010314040503040e07050d020a0c0b01050a0305100e0f0f01020706110909070c02010909060b030907080102 88
    0x500c62030050100f40701c4a40243d0045c941c081d05010024803903204440c030307042824400d8008441c0c882e2030700020412400c4c5801070110742240243c03501410400e010114403002e01c0203102900c17584115001c80c1c0094001d0100390b00380050301000355a01c500041480c0d03550070044c3c9042d030551110020006a02e4408903642d80540070b96405404580d2958a503803441d600525011086449004000300c0380d40d40b140700800c015290b150f201010060102c001404858104c0d155041c1100040f041000151000c41103800740d0740c08044400c0161180303882120203000707084440c90031710301c00155000d045810503d201130326407058514400b240e0302c440c20311401c041c46110041440d84003510190300010250040d0f5410311361101280e541d4030341c40c20041e203041c7d10842100d801c0d0354001850002e001da14062500342403411070369240342054040209000035001000d90040121082004045a2040d04844001e0000060503c050380d204d00c3c0030045680240c0b2004003030710031a2000100742c40c041c000d43d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154725008 1250 154723758 154723769
    0xb0d0b10090e0a05060f1809060f070c0f03121404020f060a050403061a10110c030a0201080f0a0b06040906140307030203070302100903060507030501052e0309020a050405090604051501 81
    0x802c15500c1d00305484028103005844540d0008112151001c5034541e9200d00101d460481c4184206040040050307090440107480111400920010041c03ca030b0440c0b00a4401603000b20300401044481c14100e882810200d54400e0f03150400c1035402009600b101c04e03900841c0210749800d50f07000514200025889861000400b0a506000030004107070f031507201c1d12100c0801c00324680c0c580e07051000198580caa00340d008000c075417a445040c80d07a01c0c0810210500300011703001000c450000d50000780c80700b00001c02e44042c0348641c000050304506250406a100c22020303101603290340e01c076000003014080c20301910030011004c1741000c05904e00019818110780e009006040301504540030303c00489505800c001c00e0185841c800000100b0750300c140c074480c0740a5178001a06506002c1001800c1c505503814944082205000d07840780e0000b2010288981e005007030000d03c5c6640b40c4081840c0c0d80d41030b40300716030052400f81002a00300e00030445501c1a8854800d544080c8403503401c80558680c00e010744c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154726258 1250 154725008 154725029
    0x30b0a0513020a0504090c050307020f0606010503161b06050613061d0c07080d06140910150e06040f030c0e10030201050a05120411010809070b0d020d060b0d0b1009 72
    0x1c0e8002071685a00038580021507280070351500d5140d4042c50f084c1c2c0e211484030000a0300c000208070710705034140043c680b842884805040c150804a0008246000c043c0c2100c44640803c0c0316403106d10301484054070024580a0b00043e9140503080140080808803016406110881c0b8081403903100c3d40300c1d038400c1d5644100c2c005220540900c192a400a005040c0480d040c82000003201198008000e0301350032500c604042039503410040c541168100b4682c0403400380400206010200f000c800c071850503124501c0300b0219044081d80c3c1203842a00e6100d003d500090001004101d800c0e5041c020400e4a000e004002c0c0015a00c01080a400400729946c1050680c010f806000540c4204000c04c105800e61500c00e0034011400140511000261021604030068180c681503035600000ba403648030302a038018083c128540034051065100301310302081c207143c0c0010020203031003c0740e200c603000d028041354141c1c89001c0304004000401c540381c100340c8030382071180c89500d10034494001311090790322060780e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154727508 1250 154726258 154726279
    0x605030709020703030b0604030b1909021003090804050604030b0f01140109151701080d0e19031b0b04080a030306080d0f120603050303090a03080f010e06060304060608060c0703030b0a05 82
    0x11040003d4000350011400c140d1520300d262042e82d40c2c4800f4002450246907010b038a800c5c264050304052181001c6941d405041807490340260f6960703410004105658240400d1584007490894241d116640010b40c0c040d401007808001c0c4144c03c040207105862240d1204c0c0700e40d80f6580b0f0a0180b80d080001c0c1c50001c0c03007942007031103007120043c40d42012181c942031201d00e00d43c0d6500c0c00c101805091308007401c0d42e4044605080c6103a8441d4044800c0c21061312061100007200c3d8030880e0700001400080d0403c0f620507203200142403500c502000074409a41010f480301e40700e160441e240d801351a4141d00180c10448042030b1700801140d40b090000e1907403110311001c8496041541c401003120200e21503581d50799400800b14005000840c407910141015016900042c903018210090252070310b80b500300080c0061291290544055800000440f00151207035918503224020b01480c2e0051403690103807030309106100e201c5d8400303090b18034802d4070144001c00c480302c20300615400c1d610800d98890651130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154728758 1250 154727508 154727519
    0x20a050915032512020d14070e130e0c09100519061b0311120a030e060408090405180106180c051207031a0d08070b0c040311090a0e0a0309060206060406050307 70
    0x500300300c885450030b0801c80740031204c1183c1d040b138210700c0450340902c0c0c07184450101d0300d40400c5099480540ea0900300080d00035100420303007803801d002d81c0e40005582e59000c1c1c080058100100083c03171500401c0300c0320764581003008458060451081b03030302070f01804402c0800c20381a90201d40c16180c042d03413278034031001d02c11807248488103100760164180404001c2c00380c5164010b0002d0007078001c1d4400a1540e894000318003c04a40c0c2c0460030303501d80d402520902c00050442d200300d81c540001210041002d0301d8030400b4540464107801031138031541c0391a00c00214440103101001000403940e00810a943c0d08200aa030580700d4000c0c0c4c402030051040c0019400340c040d9000700404010060000c48070a1500040b0394900121031041e0780043c4049060010021010310b111352000e0860022402d1520b1030340c8810701082042001813240f1420800510f0744c4400354003400d03500311407500310365000f152403d000d012801980108401030240e000003c0c0181043d005020032540c028009050741460701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154730008 1250 154728758 154728811
    0x2d1e0615080609070f0c1403030a0b120d0804110f03060106020d08060f03210d020a0c0c0f0302060a03092d0b060307080d05030c09091905010608040b0f04060f020a05091503 76
    0x2003038115000f915106400c0307c10b1900304095842646040400249040200f007003004405490b4201c9041d540180880c4803616402100c854000b07900202d00d032920400c0000140e1020f1010640b2078052003100000904264002201000c09a2075258000680c50700c170b0503c0721507404100700c0307601a441001198a0403801c0c903482c01d2890445200c150601c0846810b000503640444940c83c005515400c0d10b0041c8150300403070744001c20030803090003012459640802c4960081420b102c081c903542c1c1d80e40070f0900a904c041503a1050485c019a9564021301a030400708900041054511804080c005000d80c200041c0711001c4e111712900400605440401c200c41581c002840c00c224481c0501400c0c9541c3c4070184a01d00803843c0c401581c1c001020306070f41a0454038140c0c828800c100700f110501011079819000f00b034019406900041c0c1603034480c2070003806064014a40170300d2900c0050000d072410391000150041c00012104038460f511550001a1180800d03550003036a001c1090b110580010364 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154731258 1250 154730008 154730027
    0xb0105191b1b06020c03010504051203130c030f261801020c0a060203091002011b0e040b030d0e100c080306040c180b07062d1e0615080609070f 63
    0x203805000300d149070940c1c1c1d5124102510150206885050340090000a03014422050558420b8008020314501a02c590b0f0742c40c406003859006a800000200e0988032070600d120b2205a00420300c98525035132450800c035403040d27081e003d47d40300403a0800100019800b011400d80300555100d003d0410554030307040341c0040a12441c00d410340c0310302ca548020503200e141401000300241d8014507180e04168041c0110209025646411a49000d100c2c591780e4000a41d1045945514640f050900c8012000714004062180304030b9810311590400c610388550180000c40004000c0d5902c950000c02c11030241c90705401c8100c024030190301800001c0c03041c203050703104003000d81c580e250032028945404803030300c3d400c0713000c1d00003103440c0800090710010b1150034040c031803480c01d801110310f10304040c00445210120501c91162011905d80c161000c41444405000e071140c5840e102c1001016912030003c3d005141c0a081f030b00c045520000000e0031031401070007080c071a001c1505d8a41b0030050184048510200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154732508 1250 154731258 154731287
    0x31403060118090e250303050a0306080f01090c0b16171b030904060f0506090409030923030705041103130c17031b06070c06020306040f020705030301090b010519 71
    0x1d040e190b029500118841c0c40050035501c1000465a084003152800c0c644ea02c110002100c00640c80310003084810380000085a8042c07608540341c40102100724003038041d5030b01c0031704c10b0b110f00203400c44410010340c404d0f2400d51241a0401d03180355074040d000600d0094074640580d4801054000010400361550030170360b11241d000452514000c0320381c400c0c1003803030044000940c1e4030118510116080c1445000c02405007196014070b02850840046c0701442a02100f138000e60300e802c6c008040601450341d9002802c0c1900d12038058000403802d420580f52400c0404d440707031084071400112420301e44181e8014401a5014520f10f03540c10080312122492a002103a900000000004900151030030807545001c4080c0555503502d5100d001007000e140006502d0300035005081070200594001503d2101203074401c80c00340c1c481c0d407042c0010b4014204480c0c260310450000420808100001c00258144e0345d54000c00c206001c00c0000440e068050f107201e03040c08400075424000058000c0810070030705c84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154733758 1250 154732508 154732517
    0x906030203041a10030605090601050f0d060902030609100f0209100513050303040f092003060d030e060a17010e040f0f0203160b0c33040503131d0c070314030601 71
    0x80002d2000da031400e0f00301c5a00300415100442030041100764040d007070700302d92000000d08079541000300164000041c1e0010511981d00076260b1801c1107115080454042e40080c1903030403e20b088003005803a4007105a104074a03a1910044070300303010b070301e1003610540107014100ca640c549103200103548681c09400c405184001c0810700049903a0204002c10141c10012030301e100f06490710340c1d0a0241e5a03441425014400701f0030018070743c0201c200940303510100803203840095007203504041d00d44000710400c0c035402800005000d4004d6802042c46001c000421490303203926a0394031001c0c21130420503580200003035000126503001c00c00d02d40c40e211400740020f055654405c00240711030702528840e80110454400492020350a00c01807204180c590040e404021030401c01c0351007003002918100c4940c80215000001c1810b001080083da040041c24602140510ba264410f00300004a010301e02845100c0190000d0f403007000040c00d507510598180c84038003180580c0141240c0035007000780f41c181001b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154735008 1250 154733758 154733783
    0xb0a0b01022d160b07021c050606060d0608011404021f020a02060706021c150f0605090d08041208030a05131a0702010e121c0212010e0406110315010f02010507090603020304 76
    0x440040e0b000900508136004610382e512070310701c148103038242802400202c41600c1c1d5255800f107000480e11582c8164119003481e40c0d0b06100087d04010411900304070425840c0c802e5601c420030120034124055402100c60140069000041412070441070b0410001600029090360040c1025000303801c00510501001d410240f030032800722064020030880e005055190014501c0306441c1031881c002504042008190075401c10401a04c43d106182802c0d01036940422080140001d0780241c0c2c0181910889070000b1001c42d040086041d0015240407400b14a8000890030141e0f03076111094100c1c0e030003048000303840203242c0c8030b11906078010409400c0d5500e42c4070402005c00300f0b011000c1004200000f030307600e41c111107140c481c204041c0f2a405110500c10484100c84a0304a03460b141142d000c890011155079407890101c020b8000414602e8540301e01005101000e04902d00074500a0002c3c0e0b184141e031a0010b40490a84d102030300c608001c10084c03042449900e00c00e07001550710a00600d861200e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154736258 1250 154735008 154735033
    0xf040e0c12090d0f0807020307080904140112050f0601180b0109081015173328090b01090b030c1206010f2306250b0a0b01022d 56
    0x14030021100192141c002c10300c1c4039512038205004c0b505a90a0345045200303842c03c454042d540380300309600a003201d4008038050031540c2c0c494114035110126001d145100e56500c21030900580001c28080341c0c0d5000316800c100c03058000040003812940d07a00a0000c0c0c020402c80d41000511900001c141040700540b4041207181c010040003e20503008a400140003610381c1c06d28800c054640c1011134182003003024200c6a1000290a1008903400c0c060350051900003102c010b860100d22529881c254440b100b044000032b80e042d81000a5030050289620802e0041d402100702d5003d810014440d4901100510038900d8030351102031145800760031180390720010000200307125110035440e49281d0000005022079942004d90030001e1003540c041030341c040c08044114410708071840140e8012040414802040c4101c410031140404100c0c0141c01c2044013402d00340c285440071603648100d14142180b486107948002981c00305010380300007440407001030607480c61075091260308892603482014440c213203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154737508 1250 154736258 154736287
    0x20613030809010e0118060f200c040507020604021f02010f022802191113020a0206040c0f03081c021207020a050d0804120f020f0313090509030f040e0c 67
    0x6580601c01d16910307204014001800c407071140203030728100507000c1c2d0004541030b505511281500c1c060704241407400b031444404c8a015584200c000c9009401420b20224400c0c0170469291050060780c0a00c801c1d07880440c2070703070b0743c60702645c0094002c54074441410080d521080d0391a5001050f20020500ca207019501388207a82140740c0d00b8410300480c49000d0110f428036115200041d1143c000f40c024881140c0782d80c88052012070002d040301c0e0b03814011030803035500c40c5804c00c4007201c1e440c42151107202501000f591090b013142d0448020064103800716403010090000c00482e5446200b0714940981c2d40d10f8040441074040b10012200e07024000c00202c0c1d1410031000d4801c10140d0300912803c00d032400c03c030345404000e44807070044c44041028000428800d10303003c0203c14041c10403d103101c003030031401c80c50029608044040ea000c003060054801c2940c0b103862080300d4004600b4880340c0c41e0002030325128071402c0d2164401201c100010409108134080c601c0e0300031107155200f410800122150391 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154738758 1250 154737508 154737547
    0xc12030c1509010f0504020102030a050304060605060a0203032a040303230705060f01051008060904140d110106050a0e06010c060b040204060e01020d030b0a050f04060810021308030304020117040206 87
    0x60041d00c01810050414403d00c02c01d0302e05501d0010501c600e01709500081e440b0b02c62044600c0c10000d001000505125544d0403510041001800d5640d542c100441e0007922a0001d4a038a640041340c82408503100350a4080384050110001c00240380c1403540d035041e42d00303180e00014660301034180d4031807458a0490302e0182221a000d8800f4120b03074585603001e941140c0c030507009180710300b190010701442907601c0881198014000e03229014944c94905124400c000322815643c4503204030440c01d80655030203a0001840d4445400a1041648400400000c010980192004504441c2c0000e0080d8800d4120000e0f203070165400048000340900407601340d03442608444042164444240482d507810820f0300c2403030000b841d0401c602e880c400000b810300003403403081511528031064810f5036651a603101e2001400c246040310640c101d41c66561340690401c4484140c80042c120002070310900c003004032413007103038141d4030340b903e4000655082900c0140948181e810440600417946030f0b607a03480c00740 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154740008 1250 154738758 154738783
    0x7150201023103062d06080712080a0e060c0703030801030b010501050c0a020405061c200d03170403110109030815060708180d0f0308060103060906080c12030c 70
    0x5a540d54060a0b00c145400d07510100e00c100b6034196841d0080c00c4070340350b02c2c401984d0780020080381341e03801c101d8a60207884500424a0002c034040080c0c00d5200781c16440744040303e5a40040d034140c03640e00d0b4544448070f003c04402822100c01040022241841182c2c2c824131400010180d909000000140303a00e080e0700c9810031808141e07403100510510a60408c014010042464023a1800e4821000702c0d442e085080c0c0000c0c011521000420342c0d6547c2d02007080003120f10110010300b0b2114a0030f148403070100c0400001c101c06102c4e0012030b90741c00c0042462402d80d415841d203540728845900901c800d51401030066003040440803100300220340038001c90b2050790181c0d031040014181750300c400890b080303030b02c0c2968800d01d0108281310008100609403041c200394400360b1000e036025080842d03a1004074000050442c5180000380c0101900030325540d01400081c3c1c0c0c01c004c480c0c3c40e10491001c598944c018655aa806158101058030703041c000c400801803986c040e2420101c106043c6403420b00411041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154741258 1250 154740008 154740011
    0x112020d080307092c0c04180c0302090414180a1a090c060a0f020609010c021b1206040b0109110301050f061b030d09031106040209011206020f28021c050a0207150201 73
    0xd104003c6641804070380240e800007070340c1c7c0b0301894566011960007030000c4a0710f8298448000c0d0b010345001c3c3d4160341c0900c9000e4000d2004c208a40c5919109900440312080c07500c4508180000c40303040010f04400242e4052201d03003c0d54030a210b070b000013240080100000d44218180c444158a0701c00280250403c540c80d551a0501b0301d0034084d081500c0204a408a80e1600400d105855400103214005040301201440c00c1302c41207001c0fa004a808000c0c1078000e124079000c1c00204030400069904075070f06403108102075001e803045021144000e200303a42d880f80f407102e0180c50b0303880d291000340329001c501c03c0043c3c92003003080e000c01d0442d046418100b000356903680c0760000349a040800d142036100303180c020f4203c03460661300107100c407070040c0903441182d04c08140300010003020364119010580340e40d210686403016413275a4901c112000d40142c4000c1c41102a0080382400040d0054400c00e90318201440d104211004a8881d00820070f90320442c42003031400609159450039199094989500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154742508 1250 154741258 154741319
    0xa030903020d0f021b0a081207121404050105090414070e0a080114070f09032a080c0a050402030c09040509030405150301060507030f052b050112020d08030709 70
    0x8000c0d003820045103071182800541800c0c030024680c04203040c11548000d510383c8441c000c00401003124a04070345c101f840c19110f41c2600380c4440d680000607149035840340001e0f2011013003802045a00c4c60309448803070711809040c0030502c65580948050032000001410000d00b07682030b840c480100c4a0240c451101060046418103164102001510045c0507483c001b401040004410019039450083c400c078204600c00c6c000340749491145c0204001160000025003200d9070040d8210ba80e007038514100b0601c2e0310014400150008041000421400010315070000140340c1001e00000e940010646d00d0801e20800c00f690040c0c0e1984221070203043e5401c015910b5906160510402c00c0500480102981e02440100404c070340c0101203402d40707070749450104124204a0000d40301401038982000240110300880c5000000d4a00c442d00140c080d1041400141d07030724060810b04076040500a5040903c001070140420000030046411049a140c120354151b9141040010411100c11017165a003000b075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154743758 1250 154742508 154742513
    0x4506050901140d020f03070e040309050a0501030c05030406050703290306060301140408130b0a05130506030106020703141903020f010e1617010e07060201020901110d0504050d060207080a0309 84
    0xe00e140c007400e480c141d1185a00d0307150001654841c83c240c0003d20031004e9000100564400340078602c000c15030040c1140c02c6080603d006040444c882c007841d401081054800a000c1d8400d00400300301c00420780f11f0b00d2840d02c450b01c815015000042c062018181c0392088460b50b01090f143d203e07580d20242d00311226640c0c4a004241c06c0c50405020f151103070381801003030916021052505a0003a904c4101e003030740c40c12026014044c03070483c0c0e441804103e03800718544a486801500070420700003616401c0f282e86854800f04081b80c0428004e601c01079110550920006038040450080c150851046560100440001080c0d00003880030440050300700c0445000744560900035103042201100c09000c00c04603941e8030882625107481048200c82030900124401142940038441445c4000d0a4540c061340b1440081d01039444001d81d6400101da43c0342d0152600004600c4440382226a9212442d00707141c0820410395080144003515402ea00b0400c0900040c66000100305585403618041400c10050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154745008 1250 154743758 154743769
    0x5070b0a0329010503040516060e1f0516020604080a030323010311040f090b0f01180e030901050a020f03070c0306060b0c0d12140a050103110a450605 66
    0x8044001040d82c81464600d030b030030010791442412038000c0c64040c1d181d0f601d5041051070016003060411840030880e0010a00c254007050400c1408010360b07148000014004c0940444a00e07220b092002800501031515a5540c0c41052070b445030000708003d00300740c0c490f607a4a043c074040810440c04641c0e18040745d80091504919540c00002170364280609601d59251001c840d050401a2031041c0d59402a0341703040140c0c2e0380035a00040d0040450f6074549043c3c03a0320801340c4400e0054001402c0b80d1149014014003d0045100c0f5921540c0a14140361030000151102d030460400c582c207500807500d084144010400181051790301810b100240c8510314205a41110303110341040d08640b07c10807090110000c000780c078102400407480c1c88003808502c180340c80000d028200b28032005008410a00c01c41d845070340c0040303040c0da0294180e0303560400080d0422400c2192803145c55452041500c9040c0322414408010f140310440343e442d0a2500321101c400d00607030554a0a816210350380e1003081c07186007080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154746258 1250 154745008 154745021
    0x1401060623040501030f0207140604030216031e03091805010501170106051c02090a03030201020d0c020718200f120105010216091a1002033001031103070305070b0a03 73
    0x3030704500001c120444080780c04a21941c01040d040c581c80702000031280e659a0b0480e183d90341c2120fa17914504586480c49030b11220141c03010390052207078029040c00c5030b41d026001002c0705d511016580d00b100300d5000545028070001b0302034041c0094070200107041540d44a04a990125a090006480d8184000505991610341104050000c2180103000082e000002c60f48440c0f8181049903c14064803201400f0b4400e1141407a001700e0511000010550150003900015095100520162881c00030480e0f4130720341841690180203440c840010701721400e61201545a50890348814400d10300703040301c11507a008078080e060009001a400311100c00b404521409007500348050b10740e480801c410404020090b02030051000d98440c4034500b07401c10303040d00d0180d02c40702800328001d00c1d10b00758010f5101d030030100340c40c40440c0f1b100b241002e103254884045042d101c0c148103103a003241d08580720340c088110a81000e54052242c8100030022032000c1217440c0c000d00a03a4203282d601c23102908000c069540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154747508 1250 154746258 154746287
    0xf010b040b03060f0d02060c070603050f060a030b04050109061a13140a0c090e0406140c0a080c0d2307110303090a110612160f02030a020c0405090a14010606 69
    0x201403100740400d8907401c084030340121085600304030395090070000038104404007000075030000e400244a00ca46c02c004c5010012202c26403002c2009a1b0b995125090703420b0201c1c4c2e8a5070206e0343c540c0c1400081c10306c040381c03908240944000030311400284e0f20002141d2049203000e40400b05c23100700c3c1000b4035141d214000c207843d60480c10f00c55280340c11804c08600781c1c003601e540c900c40c3e100c042d0300032400c1c80b84007500c0c01407c4400d18031320742d800c0ca42402402807482d80d410f031405ca800c074400900e11000500c11601c400460703603684c02d900e81d01c800300034055400000e2041c180b182c848000b80c55104d43d54200300030030507980910b003000b030415000161840c5041c1608000c3c54000f80204060004003140501d0281d400c801c0c00c3c0e10001003100021150b100f055404801c4211034000d0103107441a00180f407020703029a88503210007500c01d100581c0c0d2802140c41800041c1d008512030002800c050700650b03080380d030000448240c04030380e41c0d0b6a200d4611002400c08140e540d140e00300110f0f41d000a03a80d03020316 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154748758 1250 154747508 154747529
    0x140103240b0909130507031e0503040f09060b040803070201080a060504050702060703051005131a0907020102130f0b0d0e0309040c050d1a010816020c12010207020411040f03150e030a080f01 83
    0x401c6541760b5440f01518030001e040140f01c05000a2403a502d400340c005540d40c0b01081e0fa41d500d0315441c0144000c0708038021f41121510f00300010400d403441c4130031502903030b40c0d41c801142080501d600458410a0040c440303044103490304400a055280ea0081034060a034a4014080c6450001001812580700500c480d48440c510203040040d03417540d002290600c031040358007080c00c0c004043d0000e00d082509401c50340040e03a881c20410001d130b041d409418840d40c01101e21442c1da030354107400100020b05009042c000042007144601e4040e96620031040200408183d03800c00b0a007200180c1200e27141c00601011400c0029410070381d4903030b881a10800720a04124052748462040002e025440042000d0313020140903102000e818000c01400002c41002000710401c1801c4445450207500440b0f8201d01841c2025007504108040c07500b80c1e0161503a1090605189245450740d000d1404845a2240c101f59100c000700482403050000b020703102e40a4440b0205800c09002c404503408050344503505a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154750008 1250 154748758 154748791
    0x1205010c141c090614042402040b040b09040f020a03020705010f050f040f14070906030b070e01051c1e020a110a0209060f2215050109140103240b0909 66
    0x2142c404441d03540b404040ca000411102501e01400245449a6014480c0d00000300300b008000d020f054100a821260400c071140d41d80c0c0d0207800c4164020380c003e0016550040c0814008903525401504418000a00c00b050f000040c1d000e5000301e91020030031800003170700040ca0700c05014090080b1940389403100010403c52801c3d41d41840c921101600003440d03e0b140268a40600c41108184401640c8130010b4501550b030b00c1c13100000a00c001c2c8030886242c0c0c100c000107540540119942d04412106844d90761a1806018407040364054410030104019a01c4245883c41c8a41950007203403030000d1400103030b0b96511540058032404004844282a80c003450384000145c848400080d0410b10996416800001c5000080c0c3c0d8680301340000005d804c08440032400700c811341d80281c0e541040710445014060340f90b5004440303c02650103403480544105502551a5100794130109440c0f11800c440d8040c86402035450444001940c041002c081c004241210b42d464220704e143d0700020301202d4100030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154751258 1250 154750008 154750027
    0x20a060f0f2d0b0a150c030f0809250806100303080c040f09020d020f0c070311030c090c03070507080406030c09060507050c0108090c0616122c01020102041205010c14 73
    0x5854248035950742c02a141c60440b83d00741c554440301000b5000b101c4001c40164848800107205c42d201c400c0a40009940100136402680150001406095414054a004c002401d0542d100c0e81a483d0005002c01c810311000900f4501800490300030420b0080341c0c2c0d0369510310308004015071405081c0a100c0307441000100950001c0c503940400b2210b030000b001d40c58180342c051090080c0908000c4030703211880060380500b24000828101c0642c4d115481c03130382c8244107041c02c1c155070314142240d4503003000d6108041032032403441d0000b440e441400da00d482803401c10141d48000301a0044e40c02480802e4a46101d00798203908045501d014004e145069070412010b51150303680c80c0000e00c629414007424001090311608107004000c850440540585c0c4e40e01000d02ca0040c100c51080d20540f10300c92004560040c030b911421100410760f80314044c8900b2003071414200c5804450ba9100a810b540d801c100c0014603801c2c002526116501400001603032103070720440070b81030140542c001191058100a214072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154752508 1250 154751258 154751321
    0x60111160f080105281104060c06050c030c09010e120f031908070c0b270a02030106090b0303030609070e0310021909051026091e0a0b0f0601020a060f0f 67
    0xb41c030803001174540d62030200550100040c55145404102e881d0001004a101d6400021302500b01c2c0c81900200700c10342c1c500340600c0e090300056603003420002c001c1061881ca0362082d56649149140100b103105884116050a4985404100140880c1c1c101107150550000b032444801920344280c14020710078902120001c02041d12104000c081e030390aa0007180d4000401400307149005140e401084000c0c80c0403182c540d540c428040d00300e209600349000803880d0496806824403d64024000b1360458881c42d041001d114001408041000210440d0809960b410001d0700d0100403459001030780e905101c2031800701250300a0980041c400780c03150800050b09c4d8460394202104c00b5146c034001001020032120b002d03482c0c0c000d0000007091940c090121510002c140d039031408444055034030101d0ba442000035116080702d480a01034004950010390b100707258440e030703561050b0148181c070001031003581e50704100ca0b203184e8410380e00f5643d030710b961804522500c0340c03818040da00000700c18080c098855001c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154753758 1250 154752508 154752541
    0x60901080c120108010f0b0a0509011a0708070b01050103061e15030e030711030601050a0e010303051602030d02010903020c010908100e070b0307020102130f1d060111160f080105 78
    0x5041000a00c00110034400c400140e5140d202d0b40400d1080030750b900c03594a4040d040f045c044c0c840c143c1c030f8001110880c5c03502100315002c6440281500041740c1c079104400c0f01c2942075810703496082404104500000e0000001841c09511920001041d0750501d000141181c42c85c1d0804180c00c007014403015602c4509141120890710003061701c076108501c0d100c08601824010a540c0b0301071001103922810004404241040e000f025403c0301e183d81c1e40c460411500c50030511400100350020801480407030311810040074080071901d120201c00380d190780828904070310312420b100103035500c203010000c041c0e040c0042000e2843c00d1804106050400c03070160740360f5070340c03603040c0d00410364174140d000d01c90134280500002011001d00d071545034034040c0c1d0b01a000c0c0d40810300c024203080e80c081c804220b500300c035036030310065868801b80344401d90b0811900c45d01000b0041d15041c10f00008002d07448540c6010450787d400005100f07a0400000e280450b05008114207030801c11059040000700702c4660800c3d42c841c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154755008 1250 154753758 154753777
    0x16020303040b06030c12010603150506010c060902040b06030a0f06051e0f131e0c03020f03041b0b031e100e130305040305150610031509020d060503010c0f110a0206 72
    0xb80441d440d0500080d00e0100060100d0b6003280840240d5030750280b044d4040310459005081e44040c1842221000c401c9840c112501030100d00f8507030030310f4040f8603550300c1582600e2001c2e20005031102c27020000307195500b08907404450f564460440241c0c9891900609004050544d5605081411401e91310003402001744047d008114099101000707980d00c0607041103a55009004020305520b0007074204805003c4041071600e00d0401c1d40850400e44648211000102c80e01106411030b1215501c403007804884212a21810700002004122401d8050003540a136554201800c20740e404c081503184d000700000d02c00b0039078141400003040030b00030407625203900112281d11814181643e00c8e041d5014003540d000501144213801c0400002d00b48152101d005c0c3e01d040b581c20740207a41c8220b04909a131694a20070804c0c0c0342c280303010008680c81e034000d88107450324410b0109510341c461002c01c0c211124644d0000c001a1900d5095491503001540d2100e0800030303002400108803c0d401141451083c109170 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154756258 1250 154755008 154755023
    0x50d02010c0e0f03071a0301060f08010b0301140d02040f02130608060307050f011202071101172401020f03070b180a080f072102070510090812130302060403030c06051602030304 78
    0xf0f10160340038804c00000e071401d500740c0c0700101c00c250300f45180c3d40c00c240242c8000c1100d60441c2e10606005d07116540c122541c01c04075074a140e0810106440402d10109020b4100b20074040710300059882d801000003204501900684801c030001d418414a141076100c07009001d040001d01c00540c038007150103410703194150350160304c5419410048551415420f110480b071840490000c013000307600c0c00800086842641c401020700701010205a4494041e1208004011850b0000c4601c008024010764030b42d10500540308138001c03d41e507190642d4080e003c1140e1460440c001c001050000328206100c49032003200030070f044003146c1e03203c0e800c030304c00c2e40000ea40a100c04038018040007101c4035401145984101010780c1c5600c00000a5512040e41c01000d11a40728085202c040f01e10a800500407900b1040041c421244600d00c6603460317511009002480d42c13041400840941c4620004100139442070781c0b201e030449954103019080316400b0b0b040b03448400c8800518901568000280c0c0d81058100d00b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154757508 1250 154756258 154756279
    0x21070515090c06040e01180c120e0f0708030d0e070806040602030606130b0a121b050702280303030f02030f010605090307080f0c180601021e1005040c03050d02010c0e 73
    0x146070700d420308401c0266445100002c020424842042c030041c12547c0d0503242070054803068002e101035610380001c4100241c000381403070105001e950401c1c00b0281d058400c1d1040c802e6036403a101d060918940000982c0d60000030310349015034440c4520070503200c05102420340c2c4d038242105140c40d500040c0001c0c01ea245c0100224895664400884a544005500390514551383e190340d2050384c1c220f43d80f00300c00308121113020950b4603004d004e01e103080c009100f40c2c2d52810503101803d031143d40100100785c1e00f12400c40300407154407107294128004400030400f0341580c02e1652500400b5100240f1100130760302c4c014418041c014840f11205410340e0070905289440e680e034040440c2c42d14006600a80f140c1c440c40415204601012070f4080350300509461111400c549501d20380355542d4140d600038010780c08000f4400907c5084500d0100e030100c824240c80c101c1d000d00040000b520300a403000c1c0d0b0885206107080003003100c10409004400307400d0000b4090008182c4011388078642490344980600c83c01074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154758758 1250 154757508 154757521
    0xa0503060c1e0409090f0b061503060418050a050a0210030c0e040b0310050c04060e0609060a0e060403050a11100810050f011110060323100b04090206070521070515 72
    0x1954013804c140c0e10100039075829070820004000300f001c01602c21030240c0002c075041d0305250208414034000460802e00c2c64481c90140b000600c45003001502d0107801265800c000340c010710182e41c0f4207015100418064a060040100644028040f002490f144c40244440e1a8202c042060b030038404447c0040c40b94907002c0443e00b13014a00170550303802d503e008100040b44204401034402d482c2e03140c4e1400f81c0341d0b00c200180851b074440c24508035403160b4240326408a44d88149000720740c803440075007014142550390350790b185031011000c002c8a03039030b0400c40ea0041a0074411003d0162512510300000e0b94240700b042070196079524000c56028400089041c60700786d002c0d181d03400c2183e0f004800c8900494004c114500100014003003250270703202c00091a04002c5201d0001c0071300b0741080c40981143c1160008550043c52190015908151100c0e00100581d494201800d12940554080c2041c090310700c5100c1c015039100b20403121046014402c0700007080c4000b6070301941d842c00380305540c0d43d52110b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154760008 1250 154758758 154758817
    0x1a060304030c02270f0109060807050109030b18100501030308150906010e0102251a07020a210804080102130e010f05012003031603110702150901091809020a0503060c 73
    0x10305000240c0d696209000c40207a0b4000014100c2d1f68010007000130350346074191f450310381d40d00344101070008142e90030502c00b18100b102c1e09500300c1c101151860207510710101c2c080c01c1001001d0001c03039182d90341d0010818103410400c00b992018254242814800c1400d0004240f032401404150421600154111069001b0440c0350742414040d86510201c07030003c40300d8031150800c0c0c0900200400410040308040180c6420345d06119801044d000e0443c0c20027940144003c0e40d00b0005000c04400040351000c00c040c0d030004e001505500300013580c0c0b00104451444080d2442d40041201485800100981c814240b00c5000385c54092924a61241e180784407401c2e520200c0290b51458000081408411003101f240e03210f04003529242808164207074900505540113a01d030180d04820305d04c3c03e88030310411850041c949400c050500040f020745a8403542c0b40c0391605030301a04580e0b40e585d010029868603030b011000a15048000388070070720313105a0703103091070158044440c000c002801c3d0841010115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154761258 1250 154760008 154760059
    0x120308040303111602031002030903041a0405040204090906051003020303160303020d110a110708060117030c012c060c0f03060a17070e060d050d05030606090a091a060304030c02 78
    0x407046440700880c45510303903040204c1004a01c42d2280b120544440d10640c000d480c4550b0100010b1400c09103460040c201c1c1444842200401d0802003002140690fa5132003d03002414841000240007021031511104031900a05200d281001c00042007006076000004c4070300c030b515840e14a41211040c1c0ca02a0064041e0903007044607982445000c03001402004050410417001da80d03600765102d009440540c46414a002d401180c0d000080140002c0040c5c1c00405541400101100d151240c00c203841404c692420904103022031031901c2500c01000d44005000b083d0070315074082d003210300700398018150303610900c02c4003044d410b0702100140e11aa50034402000820b0001d000c0202c2000034802280c550445000e11a8007841440121303140f0f003041c000c900c80043d4070000801450080368001c2d20284c0000340084d034080c0040050750215118140940001d14481c5008151600c484251030903403510640410f0113200305104210110b41c1c40100390002c5038041d43e10100f80035005140380c030104603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154762508 1250 154761258 154761281
    0x10504181e0213231e130501020c0f0c03030f0d050901060e0c070b0703050408070201180b0a02031206040c0c1506090222052d0d0f03020a03030c09120308040303 71
    0x4145101c4070f01d0000c55000344148003c20300e05204c84d000f0307000f40000c03d0a019a0822800c3d00782601484450b08420881c581041d03206030032514940c2c0701da68aa0981e0300c00120200541c1020b0342c1003255030f0702006088140c0004034091403c4c86e251082968050160b80312031001207880300c002c00c0c21117400b90b0041020304150100c0d00854038241b9030603480356006d1001260154417001c000b44440d4805c0c421640100d5001c07005074030f80b0701503400445031403080381a00e01c40161700780340004001da09200208a141215005551218140d510a149400c40103000d98081d900f840c0000314610f40c0800302c2008181d1080c81602000403a004081c01441c050b008028040d2002a88600102030307600983d5041c002040070803445611541445141202040800a0100444c04611000c40c03c9000090144400340c24100c1c080d4054a40f40c2c245448070034240d026810030314801d424036500d4016050307803440c1030402080ca40d25003c14102544421400030b410003540328003041c02c1501c203412503101c0341c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154763758 1250 154762508 154762519
    0x411090709060e0a05090601080405011b0905030f010e030403140109080f03060910060f0309020d0b070c150b130b010e040915230402010e130509030d05010504181e02 73
    0x9080c00020303041c10340900807000424803d50030440b25152110251068400180c03680020b506c8010065940700c8000c1d104442654841c1000b54030040140d1811019880941d11601e429162100f414207044800201300704a90600300c155101d0031000040311304581d4806401e6000200782a255401061202d100070411400040c12a444900800c051400396a00b2a4400125111000d0704c1d0398442a600c142c1e004540ca0703602c608840c0d802607028249090014280140307280d0250f4aa10303d24100303c1d0400c0204d0a1001c281090104c0c0840210300d032031140c5010465134400c030000464411248401c210560f0b281d84040d0083d0f44544914481707808081e0080c00b001a00c1c3c03810b42c800610701740d410107540d4a450000700b04040e0460803182c41c0c00880200e03010941745e5800445061880b00c00507a000240480d00e100305500305e103d1300c0e104078103100145440755003403180d8000780c91040c1d00c0340b0711441c24036038403551003290200c00b130a24035030100750103560281c8040d018461101b03000e8041d5204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154765008 1250 154763758 154763761
    0x1a06060c0607020c01030b01020105070804060e1501150f1704080d0222030203010b03010209010c17041805060102060f061305070e031501030507050a0e070c02030118060b13061d041109 81
    0x583d0005000e624040091b00c0511a2000c0c40c0c004900b03e403000c84184000a105001150102d110b41c0e0248050011100903208503480d0140c283c14a18400c1c0d01c4035441ca0310680c1c5102c00103034040640b035401e9401e4541021212034511b49001041d0b0068009030840d8000100f00e40201500c0e412030303026006000801c0300d511006010301d03d450001e480103902139420045034041500c0d06108807084642c0c141c5400050030b52a0700e035420f00140301110018002001c000214500b446240d9013407445008202c085001d142242c002424118003401da0070104404c2d006102940d5203030a103040000c0c121040001e201d55076804110340c0d94404e01c88054050003050707013172111807450548490503640940c0440d0411a9960b051203141d9035507100e090b03a8050301502290f0700e6071140809000302c1c0e00050001c51000c0302e501810072800004003049400d26a540b06910f45818641709400c0c0d0054000e00402c003903807400104001d440c4001126440294807880001c08003c0c0350704140c0b8650b58090301e20300c080e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154766258 1250 154765008 154765021
    0x3060302090c0c010c090602101104030f200a0b12070215011e2c04060209090a0614031507140c01050a02280509040c03090209040602090f01020a1a06060c06 69
    0x30b40c443e9055001d554240800c1c003800a0060400e0b40c100c1d40340b9401803007103a8225005500600101081307540001c001c0100001040e80c040000340b516000f42500c0d5039540b208040c500c2180300301e207c1e013409000002d00c10414400c03d0300070b440c00300300c00d0205d01115660b0300608900b450b034481c0840c0f110030080740000c00c0365494280c450003071184510b020483c058946035482d11400340c40000c90b1640c541d0150070802404841c0c401e58000d44a408054104070f03550002500a40c001c8031803c0c0030594074030701009109481b04004002d648190301804084a1410840321080700003008081404000c1d1190034841640d1011140d144003100c00810960810600600295126940540381607050085000c8076004002c2025400a0281c440601d4220706c502030001422445110303805165490328210051b031501804907200741e11441005903a4410042006410004481650b0443d8013441d07921001079640702e02107140391481034400ca8903035540030004100c1e202e51045140103000383d0b018040e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154767508 1250 154766258 154766281
    0xb0c0a0609050c0a1a030115120c0215070c0c0e1e0f070201050108030c0703030e01120c0905210307060e1f14131101080403050d0603051f02090102070e070306030209 73
    0x20900f5044440744802030740e0322403180041101c064a0b00c03500e601040100080c5032100d004207a00c07551400d1084201d01c11032000011648500000400340c1c010584d2003401d13014a00819600175042d04011401c0642911405003641843c00381c1c810441000012074014074004000045444102d42d240c0704510384001c0000b000c00080d640e080241d828080049085000801600c060540b0170b0000c0c4409495901e003196030710000824a814001020118951454540a0100d180a0076141d41c20010b1506040c0300340c070803c020400740f51445100d100401341c1004001c803940160040c2000c105500100e1100341403240d100a509552880c04a08408448581d0001a0b4030105402d1101056070b80314010707a83d002030a00024200000c00008000640c00f44820a40003402490308034103000041e14100c044843c00d80041e500c99205508408611440850709809502e01c2503007507003015950030010350f941f6568050051000004000100c6840c42903000d00019600205000300c0341c01d05049841 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154768758 1250 154767508 154767523
    0x2100f0f090c1403010207050a030c1b030f300e0402040e010e01150302030403051213061e050903090d0314090301021c0c09080d0507020d050d0503061e010503010b0c0a060905 77
    0x342100400c3d110540b4502c0d0600c04c1e00d0b50309401001404049a242c1d0742108d18101a440c2199100301600041c200200414a0900551710407024031500314085d0070414641e00b5a011000009444903a280350310f0348503400300c50b17209072a50030500000d8a0740030002c2c0c0a402150407155600504100001e00f5074445041e0604a4008560a2a9804030610102e0030781c44101d5028010030801c00601c0e10108524400c21703070108094007001060f4201c1d41d11103080e6813214407010034060165050f05544401441920381195045000358545500140480c0b58940001c030050280071007081c590a554458004a800e5039100500840da10007440c92a0a0303810080f0400a04039450304046903044c43c0541c00b039800365800800101640300b18510221140d0740600301c12a00b120b0440c0448000070800c00c803410340d070022522026202d1400d00244025140b2034540d80410fa82c0100d004807080c0d800c00304581c15602c40700c40d0507a41d90340d032080680c64021400c2c00102064684410102845030104501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154770008 1250 154768758 154768769
    0x91003020927060d0609021302091203030103052508100218040b031e030f031005010f0c031b080405030609060703050109090c051002010e070b0d140702100f0f090c 72
    0x90301d040c002d441500988000c02c40404808424880100742c803071400d50080e581c81449008041030002d010360206040038500360b4540c8040381c020400001916000720a0070400116070015030856256440d0303203685000c0c080c2000c1c210350807145036010a20074040c0b0328001d0309008003107540115801c03001070b000f54442c0d410154480b03040321003a01c49113041c0c0142280418000c1c024109960120701d603065880b6034024100f0180303c00c21141c0d4542d025500614030940c071944460400c54a4440090300c16005142c080d402c008207250300000280e040b11030b13030804010580c0c1c034032101000c80c5000209845150030290b030510907441001924003000410074442c420542d000d001c20303641d034200c0304161044128028407491000006010509100c0425003094100d80300104c0d1042c582e00c405401e0401d40d811040b0714140020303960310107c4541c0100b401c030a5028800000c54a41444000e4030f0705c0140019009140e00c52003161b03440c0301c45800c85408411060350411502d030403450034106461107403054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154771258 1250 154770008 154770019
    0x902100215060616060b041824050705040608091504060f0b030705030705041119080106031a01081501030f020c030a2a0b090102130b030f0a0603030f050706020910030209 75
    0x240b40390500344107498001c2d60091a40051940360b030343e150f01030904214402d030442d40e41c00c8000f4002c04425011665103000700b598001c22162107010600149040e5100c5074124200003d0002e0304e0b40c020116811200c45140c00c0c0c2560301c80c0004c8605140240002e034122002910034002030040755484203001d403010300f90410591030300205058903440203104190b40740d007100384100454209504121002e003540340300240350000c3c40088039a0300b020401800c00007101e84005200d600c0d054803c43c0725555410140c81d80707001e0240002012610b000703100000300145c504844e005039010307800003c964a6160002d5480ba80c2c0354070020760329040005400c0010721204030f80f81400402d410780700581a40d1106400f04030300c40d9141c1e502e4050005d02400d1a66608008040080350b016122a0251030721030502a070b64100f800d9080d0408101070090800140380c0041080000d811a542c50f40e40c00c29420074640700c46c400d00707184000740505038159801000f50030310302070303031036810740c0140001031044a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154772508 1250 154771258 154771261
    0x70f1208070837020d030b0d0203010c2102070503030a020f0c0a14070e01080d03020304050a080307031505060a081602071a0a0807080903070609080f07140f0312041202010902100215 80
    0x442c0403d583e40b15544000b40c1c00ca001001d0304039229801c080316500300a0f00c013151080d41039000c00e003140d04501c80781001889000031504264800030402081e070f072201c50305501b000b0480c4c44003a26840090151140d06078001100114000680f058599145807601650003211890500030a121001d009551090146002c04a24505a90301e0a4189c40040340204803808a41c4c0065000398400751080c0d8040c46050051000070719000015072298050342e6011900e04401c15110014208642000b40314a806200d4110703410f901140c0168040c1508400d11040348109006038140450b0fa0810f45030305600c01d007402c0c01458000010419070146a580c011036035200481100d04000c107a40119158004101c10380c0410107030740040d00413501403214140741032582000c49030290300c05007040390301e04901c401c1e800b00c02d10140280d0f084900400051450301a11541c0200642d80c024402410508654a20500e1900c00d510034402c065010f0403481404124a201958541c800981004554503000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154773758 1250 154772508 154772587
    0x191a0f1002060f1509010801060e070e030d2001020414090a0603030206010e04170d0c02010c0302041401080a0902030102040b0d06080d1e030b09010f1403070f12080708 74
    0xd15040210035070180c020758580c0b00401d812000058a800d000090b0a50560341a580704084640200300030300c000600a8540703013900501d807600500c41801c1c4068110755104035240403822200c125405d20b0b0444002c0c880c2130394010110b9a040908000351f01c0440c01180e0043c1e1542007d450060444001c0c0c856560089030350140c54040c0002801030304250010080306400290980c0c205102c1d940c05510095003100b95031039900100e8080210781d031940d0741c00d01d00903020f20840220118034942540391034142400300601c0302c12a10514100444900000c0d030700021681302c00e0303d00385d0040003503681da82d07034550b46000340d00310316259800503241ca440000c1c64500014075420342030541d180c0800c0340c40409542600142102071140500d0745030403040d02284d956860803400b1307000b1a07803180c1d4882d080000707c81e541c001d5840f8081c02540039000c02d000c00140c0c960319a00f01d550f02a410302c0901642c0c94180c040e0b0240c1c003c020204a40400c840c161a403049400c4401c4031001030a406c0c1060014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154775008 1250 154773758 154773769
    0x13020a27140d050a0308070c051617061b0d0b04020f0702090f0906010323010e030a0f0207050a03020d02220203010e09010207020f01030509010612050604050706090f050405191a0f 79
    0xb00d000900719030202c1c49840001c0c0c040c240655008840d4108071410340304c00c3d01c2d40703070602440850840d00c843d803405061281040a583c4103035122035800051a03586052480c0b6919010300c03100c520654100071a01c040d0303540703443d0070000d140a8060706c150f4540c0c080402d144215002903104030b12a200160000303ca940d085d00d00d01c1c2c454004030005210a900e56107905071031141d880c0c15903512a1411a105900300401d029070181011664010359a400000300010549101d0040d106d085400090041103180d0726000c0034010341e038044501d40800c80b80d5100040d0001d413084041000321b20b4241c8411402e610541c0514100c03400c00c0034290704c0750f80e00c1c0c40d0035080380b05000c0b000b54045400c00000105502c070723170311241c1d02008000002800a86401e501c28550b248000121541c0e80f01c04204070800c171051002c18001c10b8a401d014100078108141d0020751950703802101d00555552000542010241044100d03004030140100401e00c04000032070704d0103140c084194041c3c03016014034092401d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154776258 1250 154775008 154775029
    0xc0601060f0f020703021003020403051911010c0f0b1e07020705040605060319150b07050102071104110a05070503120106020f1b130209040e1c080f040213020a2714 72
    0x141e6004c0e00c80242907a0800403c508a90301407010160f0a20003c40094010064510005420209015180517070310701500000000728a45041200391040c0f607000440303003030343da1803a5035200b904058140d44070586100d542e40041340e280c0310401c541c401d1089c0c4680204100080c0c1c0c205031400e110507615001132203294071040d62202e10300306803031407005005442680503111030317540e44d046002090340c1c424042c031181e04003d00c10b80b6103940c0011340c8010400451410740d0800c2c0c054406001403c0001d031440c0483c041c250000060000c005130120402c00103100720b40740041001030f032034800e523156240250340300d2907074202c8800c1c0c1c8513507c60f17140d58042c40060b41a4170100207001c542482d46089410b000fa401020a4940050303c5004c400414082444000480003000d039203840c04054150006001038800b401c50900e0410715407d01c005611a00300c5101500c098140141e55107081000817514960384d08002445070001c2c2b880501c0c0700079406004011602c07400f80f40f400409045007000241100c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154777508 1250 154776258 154776287
    0x3130b1f0f060909050402130618200901050313020d11030d02010b060a0e03070b030a05040203060a11310b030a1401080c0d1704080a0b0721051b0c0601060f 69
    0x43d24800c010403e2181c014950052002d0180707070b10810b0b11102c4038140ea980d40c0203015054642c1442c91606496407003a8080060025902100c0c903124007101c10103441405040e9041020000c00130b6100741058401c90021903029043c0c81c400e1025050048045480b040103030b10a00600440c014107034814041c5071030313007000200b01524088000c0010344000d000c000b0380c40d415008a140015030203422801847c420030404101140600e0948101400c1100091062072003030726000c00b0307011020340031055a18864000010300c01402c00c02c80d03000c00c0034103100c00c5403000d60340c0101c020508e00703007020142d400307800c5003901440f442082403041c04100ba0b0902400c1255881908480350350b14100b102d0702c0b01e170b074005c4110140e180952030100c0c01030b80c05604999441d5110707541020030021520381095001d006440c0042c4011503002440000c1c2d48200c180310300d860b40b1000442c4110904004000c13101640410495917108605995a2144024071902010490880c0e04100031070045825030176694 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154778758 1250 154777508 154777517
    0x20030a020a05010e0114130f05030313090207060b04020307110f0d05070f060e1236040504020f040e0c04050606030106050f0d110c0c100e060d0203130b1f0f06 70
    0xb0b0070600116000c2402007601410401003991507031080c02400c0c0107000340050b09082e13100403828114100c40750750040c0c1c0040d010380c3c000c001c440038074044480c45100307846500d000940c0ea5000360a01c5c1c2c001c3e00c4800c40840d8840c0c80041840301c42030f003015007502e001d1032a40c292a00001c2419216403100f00000e8281c02285007002400005400095100401442198000ba9901d0060800c0d482c203001c504010f04420b20000e510100d120240c0d03c1c04050720300321401d06400f45651061144d4038000002054011a00c1e030010804555035200e04229010003d0030070840719a100e100542d1395000e00c20124082e40c40d100115110b130904100700d034140d0b0304e00d4449610300303070700c400f402c010580c44002000c65055654054030042c5115500802009030714000405440c850041000107171110700469a090100e14125007155407900002d032640c46020090042c1c80303503a1011958010641c030340004000c200040d003080380205892804203c121414040c1c0e0102c581c44110fa0010000140103210216 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154780008 1250 154778758 154778779
    0x220e090309040e030c12041a03010b09100c020301020d0f0b2b0c031703092512050109082b0e0604060c05070c03060b0102010f14010e07090305070320030a02 69
    0x34240741d000f80c0d802d40100320403203203482401c440701d030700b000d1b00f083c0c11030940b400010b01000700c0040c14410130503d03402c030003c151841d4503002ca5400a440b814024901411507542a1b915141c042c031900c414141e0003800030b668800600b6118001002c0c411032003070719a0314090740104d0b107007002c820391303190907030000155091403030070025040004d1203414040b5500184e004e8044001108103030002e07500d540e003502c0d1644030300703143c007440d81030610303000b4000844080303041c0e41d60381590341074523050480c1c818403401071036000c0c0760a0440c058441c00c500134144140002c2e400050200e400d000d0f201c000c8038044006000101220104266102c111540d6204e80c090b01c042004604503510010002e1820308101e49001526a1580358205a55105940e01580c0e00d440f001556020b0117004403003200c864080000d00d4001a68044041040c013070b044500e80c007180000c825a0081c08400c1c0a035400204881c0150350301e241c00c10580805044d03030504038090203900320090800140c60321080d0707401441800302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154781258 1250 154780008 154780027
    0xa0f051608101a0f1903050a050303040c080c03070315060f080a06060509070509040c030912080109050705070507030b0603010b0303040305160e1e0c09060c0618120a030e070902220e0903 82
    0x245d0842c0c41c0721071201180040f0000000e00200140169030f4815805141c4a207080d08010520070100e80c0711040c40d030844080401181d074040340e03100a90b40e006002c002402d0b80110000000c0c10f031034100c10f55117451108042081440000c105011314031608040c0000c50b202c03021b01503510010748a20000c10320034004400d0324685074200301d05107900c0e8078000840b402e25031290f00040091201020105400800520914980780221075101c851424050314040e1507640707080d51030040f807202905107244000030903803554003034000c0c07c110000281200e803160340381d0074a6500c881210700320381003130440305100041107070310901d04a2080f8050098000c180408841c090200500100b030302600c081c3c200008640359503040d0103840300504240082449162945110119604440d001980c6903c015100c809012101049529400c10f0340342c08108103691103481c619003c09904041d111130300201e407003149040d0142d41c0d8241d1010520003c0081550b902080b00c1b118000c0d0b91114007a082002401c42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154782508 1250 154781258 154781269
    0x90d14010c021903030c051204060f0c0f200f070807090b011d010e0d02041b08060910051c0c06052a03030105010c1406070519030b01020a0f051608101a0f 68
    0x11225650b0030468a0300c40750181018003023030200d07004c42e122039540d40c1c5030002e0081c0e80304003c0d442c081414828004103684202400700394003400305030910711020034010b484580030301c083c10811888030100d4480a407541061074642c4000d010341408249020b8480403076602c200e0f24006440f00d2030049003030715804200111101a161400d55800c03940d09810b520060300c03284030f0b240884c04044082c11141c7c2540c00000e00c0c81c50b016190070f00c208800b41c14004480f80b2200e102049410031581c2010742c145009018011018a40001d0402500c1c1580040c442d50400000c0c05111001c0c00c0100031002e480c5030103c44100184410201039100703100500a41d4007034185072141e580204214103404075088071583c030b4030304111090360000301c01143c1d50120504030128000150b0a504041c001040c1c0e070340000f560356030320600203030041d0048810401405401c1c03044040b070580040c020881d072a110011155940c010403c80e002c1c072860041d0000c504070b5001050140380c2402010900302450b02c004000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154783758 1250 154782508 154782521
    0xe1306050a06031d0f0d030605180a051003050303040b0703050105030f061b04080709060e0121060b0607060c0f080a0603080f07031b030f12060810090305090d14010c02190303 77
    0x102c0c0110b4800c51449082081044c0820005c0190080560030f8000c0c038003c00b170b5901c0c0e5000a00452070b50072604041c200402d030b6594000c154130800a42503035002c0608101105640c005000ca020000c00d000c140001018014410010b54400b8005641d0b580181642c43c21046040394440e00101c000c140c19004400d0302d01d0541d0003026203941001d0f00e80300084e0602c100c2e580503070002039440804100742229050100d00512101d4070100c2100314030204003100454010f00200b040d0b5030341071481e103140d81310000d0f10407171600300c1000c00039440202d4014040e1415a10004042100440094001006401140f0589501180e01c0341840c1e508801d505543e044403408409020106091000388140e511561031018025035901b0380b2607404540107008048840720314a146410701405000100d030004001455034034070300e00000c0c0030100381400c8540d0302484211582c0400d200f01401d00388201100b800001802c580000c0108140401d026a035944a4400104101c0c3c2c03d6065800840c0c080d03071004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154785008 1250 154783758 154783781
    0x10b04211109090c150d06060f0210180b010e040203070503121204080d02030f150607020a0b031003050105090d18060225030b010e04030e01020606011b02060909070e1306050a0603 79
    0x40d0b10008a03480045c03038407050402038603004c0c41c021819929407004c030f0250310000d148038101000c0803e03644e08001d407034010551020840903100d0b4001243c4043d480104190203400c40c2141900f945c4619080c04210b200355400e83c03182c46405000715140c0f81c00701d032008070901c00d07010f45803070310203a01d14944100c04020416159501e003804194a550b0842c001075215504c400c500842c5c901d050031050110070041101207000c0d001c00e02080005031121464a02506c00c4114001d07166600c0110300300749008603820041c05035090005004192000281c49407040050340c54898210611410420398070000d41308400050b0f0020000b000c1c80580e0010244c0000d0a40504605040d06c2ea00d0b40001040d01381e00c9050042c0f00c0000300001d147d40702411800c0c0c071b0f40903c0a01058206040000d000f11314508454003483d200e10300c0d002c05c540ea004115007202501a054202e40c3c40c00d801c018101c2c008141c1c0981c010081e244030350800407454490802500d0004050143d81814007804034000c02900240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154786258 1250 154785008 154785013
    0x6120b0a080a120915230903070b03060102011118010302030714070c03121707030b060c10020706112803020d14010312090e1b12010b0421110909 64
    0x890480310520500c80640c3c0034181d6105404a2190000d00b40800c642c0400850881120ba01101c01d1340b01c0d40c2e20220320010140722401c041940c078608214031032041c07116454030509070002560804007010758401c9000740c0080100915105445145100b51485006401d00d40c00072410f40c4d40c02540030b96000b890328608411241100c80d034502850740000b00944410b070701402d08101300718510508020b056424603100c02c94002d03680c450900d601000c0c0507941850340301d480c0940c0d145c55a50a45413901c0ca0041201c00d42003c1d0792503080251311000e410341e80f507030078103c0b04641201004115024544803800c1c041d40e4140d00040c000b00d00e0704001880d82015000c010a540d800654010840341d04c1c04600c40710015455403034240d0004451180c200b060102401d420801100760340c047d0760340450407110b610700b800c0015008411622500048241002c0200c001207089403102010b841a24034074140058549a109030002020b0b81c002002004038407461800310322401e2040c00d06800240301402c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154787508 1250 154786258 154786279
    0x1208060a141302040e0c07050c010c02030c0d03230c06060402090907050307050d020403230c010212090303041a0304151401140406090f151a03060603040c1a04080609060106120b 78
    0x5e54001d07140058416228440001c56181d0510105020310700002d04242081142c010156000c03903201d400c080e510b24410b00c0b1088070f403400c3c1400f588482d4400070685c909440c41d00082d80c000b1010380c1180f403c00700f0307a11982001071260304242c8200d445110000f00480d1003580d50507000c80d56a80010b112408010060101d400319030828005171011703621400100c50f040c0c0c628030070f4255040c19180440324650080c070b1280d00c0c998001c40c0d042d40410b0308038040c80e6140c0060020900c1d5109a50040c00c01c2d00286900e44600e108180185020b24401c000c40c05500c03030782c501c41c40150382c010541e448481c50741c48010450400e4981f410440e07014045c002161190341c1e1a00301d01101c0300014000c40040c0c4541c24107601e00401148240a089400f40c0c040c940b09a0342101c40c402d00000b000b0314041c0400102181c18885401d1801000b030461a004230900301c1d11214110b81500700344203021a6225107404910001c0d00030070b945050394201da03900812b00c80c2c16085c00e8050f040028056030010203216 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154788758 1250 154787508 154787519
    0x16020a0b13060606030203040302010f110a120207080408011b1d040506180403030605010e031c0c020307080a030210060e09060601051c050c1306050c0d05070201090b071208060a14130204 82
    0xca40c02000c645d10010703264649810081d0030340e1503400c110440d4074030f84840070081004240c2a203c1d1340740300c0d1404802d501c16014880000384107060024181420218000800c038074150001d502089a6000300300c640480c0c050251103200010030400e0f00390305094009405418181e10103980850000d09505600c1c00c2495180d11070b001c00d46040d40082d481d218140101c0d608450840b19100c020b400900c1c012801c030740e002500348402082d240401c11100314a0f070a5507810030010019199034030584001060900d40030350f44150010700300e008582031540010b00d16107422203081c03040700542d01500c030641c1d64030b0044a03158449114010068440f10700c548402000c0e22540384a61180800607507200c224a8018440b1340c22548524208242004440c4040f103002c54001c0d91840c07241801c640f508403a1005980d100320580000030708150206d07005042c400d42505403c81100310b901c400322103403281d17414400041c2d50b40c020200982c008414074a0395041403200b01c00261207524006081c1a100d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154790008 1250 154788758 154788761
    0x2010e0f0c010c0309320f0a090f09080409090b061c0209060a21020a0b0702011209061407080601170105010903032a0f0b0a0203060a140a090c020304030b16020a0b1306 74
    0x110764900142c43e021030f040c0e4000c40f007a00319190106c1c0403200301d001800000300045003c0c80c5402071040090700c0700b20306002502140c002c40c240f41c1c0c0c88000c00d0303111a01c0d004088014840d89000790340c0d242da0000400c1c100d04140c0c09078400c66074140195080c80f1560340074484003c2d4080c14141d0010901140055507541240b600f0b280d00240d5081f84045203841d0040004c2c000c40782c1c01c8194524400c2222000617a006214051114800500072404081c9400d0150080c440b100482210561100411003500c1d40540c5052003201d0036290f006c10b035003e8502400d81c90209014846c041080d081d03060011074003c02411901e098a08140740d240d0000071407413803010b001d5407002c0f60740380c07841c2c4100020401074500300c660040c0a0340c0c0460640c40c0c19800500840020320805101403991052080740303032201c14952015003039040c401d00c15001c1c0034a009607268418481a220014090041010a600c880c1740191412003a4004c4c080c3c240182c82e15008014050503112a1100c0d0030002000101c86 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154791258 1250 154790008 154790039
    0x1d0616060e010e070503070e0f0a02040306060b0d0f0603020310020f070c0803030603070801050f0403031d010627050408070318080f0304030317090d03050c0708070f0302010e0f0c010c0309 83
    0xd0300c00810101c4243c41c8151416480d03802251080d0441002489110b0725001050382c01400c0000107074041c0c8034843c81c41c00901c901e1308080c144508028021034803486900040403405203218040103d8900390100780d044132160300001350b05400c095141d5402d0050354018100c80840038104501c2e09085a07519201094550b0006640350030100070403c0740d00d801e2102d90000c0c10510028000c40c5081001c01003074440c000d0000301415942c9200a030140d01410f50000d50420541c0200b0049e0380b11480c1c606500d0103141240d0b01150071054451182070540541405985d00101940c00c01409590a0750754110a0a1942c8280307a11240040c44904c200624200305241e2009160344a0441c01e0003480b050040380500044452842802048800014400d880165902d00041d994a5401050705207118801c8050403940f40440c69030103000702d000c42500050300c01d40080041c00300c1e032409030342c85030b016050404a5422000412405500400c2480c00007840391030b0602c011a00c81da14402c90995 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154792508 1250 154791258 154791281
    0x90207060509060c0412020603180d110c0102010e07090e012007030905010c0503030f07020f01020a020318030d08180703080d0212010609080703080d02040b040608161d061606 77
    0x2203901c00d00180d1882440569040380b103005541d85410308004c0d1a80010b9450f030802030107924000b0010301c030382d0302d1040c518154440c107070706031020341034424801044600b10880901043c082c408036030210750b00512442008585c14000b5020341440e00b09428010110301506101ca5500c2d160311490703031040740a410b801c00118000543c4c6621710780c100100805050741050781484101c40c01c034800300d40004140c0c1d501c601c0341d000380b20096440240407401d14000428240507980040394058110350040003901d1442a400a035020080b8000f04040d5140240c3c080300c00400c018801190105840007402121090403030100c3d03160540d20340c3c5450503a4400034039151055800705032954008080c0c0381c12401000189842141c09040c4580b00e41c441d202c07480b0090507103500007543e00c084000d5805a500a000c00700c1460b44a036038a44c4040c1012030308031a42c85c14043d00703112100d0500e01464038001e20f803440708171981001c0040310074000d05601c514142042a14a14007100001c0c20301e00480d042c003003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154793758 1250 154792508 154792511
    0x210020307030801080304030b0612010b041b031104050d151103070c060f0504050c060a0309020a0609060801060c0510050c2206030c080603062806090b120102070b06091009020706 79
    0x50303882c10010049081070300149055002000100041034110640d01e41106040b2181a60415065020f81c010306000c2c0504e0381080c2042e4000f41072103800719882c80f100c003250302c05001c103004c84046041d0912940c014180c1c844020500310700421445581d05030340c58405c2c040002d09c01c14030325081645070004c4a000b00001d09c60040603081000034000c0b541c0b00d502d106020700440c142581c505451311940c03c0041c2c002c001c0400c01c4091188a90089804903801070300000c890358030350100402c4207145001d6640401c409000010380706104e4040c0c900c6040d000005032210304545600c81c00038240207840e810714013000b84240030108072100c40003207150660362250000f6920700540681901d03002c124200038460020104180c0b6140480c25503400100e403d12200d0385104414040315000b04401260701c1e0314a404004a103001c0c1c50390080200348000c0312080c10218190450034241d02c22a00010080e03080c05011585a0410000c0203810002c42420980029180e40c840ea00300d800010090342c109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154795008 1250 154793758 154793767
    0x105100512060601080c180d050c281503061509031103010903080105090c0f2d0403022808030705060609060627010201022511100e0f04020702100203 66
    0x385410728441e03400c880003202411039898120000380004900030101801b0b0000051520b040207980301441d041d03408001c0551000307015604110b551900c0d00113046003e00024405520351403c2c1c003006101085403940c0d0383c802d0a0406240500254800001d0418140c6800002c60160343c02a20321045410656600005910b1400c25903401207444107050b0183e4503010107000841c3c0e00c60012810340d5030540798201c0d0741e107645541d40030070f00c5180e0794072817025404104842c0400d1540051603076101c08186c4018990100c0300b03001c459100f0345c44025805504090005c0e0320041600402c020b0301107560514440680e1a08568110380c4850300840701908401b040003030038a04204000d8125800f50742c038a061094460320085041164054052984201d2041270402c0c0c0c400d40407900c42e00c60ba020b0080c95001c1c1c0580c030b030f500c0700f00c2e0240031031f0411a01c0360341000364100120340030846c01295940000e0105030406000303401c10150b60568119800b04070039005a2104117030111301030f21032342c02169038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154796258 1250 154795008 154795019
    0x3020a02130501120305070206042606010501051204020d14060c0d0e0f28021804020108130201020d0e03070909050c090a0c12051812180d0f0f020d05010510 69
    0x2181c000c0710490300c0462a282c018840c82407240d5001da0842c0d81410b1042e80d90401d40006552806554041e03210190729502080d903100740310b4500008102c0b190304544003030342c07144010b5580d4010300c4c0a4181441d100d07030000700236242c039a98400e041801101c0680e03031121070785007403401d1480031103040e41c010710005010000c00b0041d2107a079481c080402c0203802c59100074030085854034802c15102d582c0b410280c00000881b006910381484990f0300400c444842c28016540040d442c40403a0b007640880c29410001d440312070441881d4010941c143d01810091100d0b48058403c0414189144d82610420101140000c141e1080006a41c0034030024406a0501020411081001844524424105405000c82d66000801760780d96402d4480c001c615540e645c800c400f4840000480602c0c28818034088071100301846008024209244030210068500303802444803060500c41c00400e07802e1b0160b2100c0c0400e6200215860f1144010800300783d4000030f8880700d0941c0c1040c1c441707194a801c900000c01c41d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154797508 1250 154796258 154796269
    0x120607021c030501050f0103050c1b010c08060306100b0d0e060a0b040509070e1b0c0d0c06180f06021e0304120f030912120204090207321f020d0903020a02 68
    0x20185498502441558100004a0351b46aa103403007040c14151105e02084030340c01d01c0802e40e030190712450b5003421b24040701481036019006c00b050311004a441034002c503c8a08002c01d00c035104405400543d52128a800904c1107d507000d01c240f2801c13181e035110761450848007442218059164004082504041c0c00108001c849025181030490361003028200400f81c07040c1c542c03680c42010501c0c2c800d10803041010b0141544581c00c08400b445c01001c1d481504140c200b10182001c6010300c030208008501c4a510f102c2d10a80801b02074500f000110145000a0340364004140c0c11070b8500512840d02154908510f85400540d41110700403200c3c054410700342c0d4000001030300010035150920a00b0030646803030034520441807810723007001882c000346080900d5580450740281080d010455444525040c070492480074207510180d030080300c80c4081c94000d68031180e40c0844840c10040c066402024144171500003420307001d4503495400f40410101340d0b056100340400140290040d1543c60761a104020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154798758 1250 154797508 154797553
    0x105040203070f030b2e0206150f0f0420120901090c050f0a0f0803041a090303040b07110a030b09150f060d0f050708160603050c0706020912060702 65
    0x1401680306004000e00c260340a6224825200c2505000a422055001241c2517581c07004443c3c2607046001c003131131320060b0703d0640030074000001d6007502c000d900d40d0208a0b01c0b0b008404101d592212207447c900f4130928090664881c8160010700004400c1145a114400da200843c0070003200b40c40030901039400d4180c1244c00e648040740f54000c0080c0c02440e61000e002c011b5a0150074014803081016040c181c45507225503000d0300d040820700f51325998400010703a480d48140105018000da0701d03a0048824447c6054a40d4410010302540c00d040c01c4c11801c018542117420142c130032541c100903482c3c0b01c0c0c540854001c05180241034001080c581413400c2440c140070b0815050480001d4010040c044003807222564101c10100c0348000c0c0c1d5146400c201d40c0040f5240790140186c00307017400c0092102c500041c45812011800c805181c3c4036580c40c001c0d011600212985000c841c0c0800c02040010000d41c000c2c40f00200003003032001000c003110034492030540300f00e40b2400035034045641c0c204000a04080c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154800008 1250 154798758 154798769
    0x7030c0605071e020105070213020306010306140d111507051005010506070b04030e0303070c0807030b0601050301030309091e1514040e0a02060a0516120f0f0818030f0412050601 78
    0x285440450703074405901d0f20902e506100c906403024074010440e84250100e5403807075002025500c07103810300c1c41140025441643c0c083d011a00c0c0c03e60020700c5100c00c10103c0e00329240101480103911042d100e906003200c01c080e0310b40d8008440c04880c2c03648410390011700780060240000b0242000d0111040c022254180c024038440c40c014840500010443c00c24140d025038545442d03581014a000801c1c40c0d40035408008080210800c00407401450014114045a0080c05d01c5520303138840c84c00540d8288400c3c003014001600501c02440300880075017045d098040d074030240c0a102c6400781c814800302c600350429000c1c0302c0c1c0380310300c01c011421003a80c01140582e401c990801c140c00405825aa6031800003200a0007020301042c5120030a00420607a603450420506640d040952441c08143c24004400c0703450208001c6500701054610400001440c8815600e039040545c40e00f800c0300002180400b107410551204106001d008290301c40504001c0a44011404030b4140e070345081420320720145c111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154801258 1250 154800008 154800017
    0x406030f0908090d0813090509120f07060e070e0702010b040e010605030c010e0d0b0c07061401060903150e0709060f1403070b16020301060e07080a06030c0603020a030b090907030c06 80
    0x1d011401001c1181c00c0c0780801c64880c61010b0329864000b1107805652048204101d040c000054041400c0d00a40d206101200580d0b0400c21b01e0840d108817809162000102c040c2c0078001c05001078840d50150640d098084212044150b45281403c0c862130102c2d8400c00503512014100c1c2d00341428065a1a2100f10400a0103500e0074000400e40c5c95000180442c1080350204003110103803140f400f0030040940011640342d00b4903041c40b040c0320031341c444403040394a98a444502c4ca03031403461340c2c80a8140e400540c2d0f2006458a185c5400401d0012084080c249603641c8040190203141000100001c0130182000302e50f00340340000c0c1e41006181644200d554802c06201040340c0d80c1d011510300203844405c6806500c940003c0320440041c1582200250150710b03090f0007140b070f5180e45912510488055030f884102ea0b5498403044203580c07180c40004d1503400700304c1e002e10280e400381d005410443c0310742c5000281c030b6413000001b8071200c60507502c0c03a801d608484014000c1c011452008c40160415040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154802508 1250 154801258 154801271
    0x504031109040b0c0a14070507080607030e0c062a1f0e0303010b0304051c0210050108150c030a02070c12021f0822020607150e0a02010215040215030c0406030f 70
    0x4503000003c000a10900441078001010f9650501641e0403101d0301c6400300c145511204145400355540456006804062190b00005680203220740907034412042c0070300c003405040b482d941c01d0046e01e41082030351441d40c50343e200d111544140e9880c1c110019152150081070004006101701c3c10081c400c800f000c0a07075060609445100c00e001045904540c90140550f54a56550a1090918414221005105203041c0d000000207600048800d2684007142d0100010f990b02c500c125a03500794248201001001c4a000840d15402100519802005414094600302103962400d035110304942240352100c03070034001b200a60038100881c02c607a000c48041c29a5005940c4006494203500400300180d00307000040c00c41c080340141241400c0d1a03406014141c0790186441c0c0711000c0000c40001c101c48620f031105002e00030b03a001032010542c0760182c010f40a02c0100140d902c006050081c400e9810000201e000c0d550445d811000354401d905000e00301e0745503414540c0003000e4036045058018007506100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154803758 1250 154802508 154802513
    0x605040c090e07020f03030708010807051c0209221406090a030918020409140612030301060c0206030c13030b0403110607080109022a0c09010503031303080d02040b0a050403110904 79
    0xc503a0140c9030140d80d00c1c91940c3d42c41400304d10300000b800304c1c44086e000c0881400b000c203030088055410380329084141c81449841d03005200380031803040d0228443ca6000c0d1108405414403a080707a41065222070494030b5500591070002d46000c44c4041103840d0313100705040a81200043c40525044028007019000d9000a80c400a204503564080e80102c8460076074034145c4116240d044400501400006214015140d0f8440707034000400c86815010382080d2a03e040c0540010084905850750764880d03010141d842e0b0248001c0b03400080041034400c0041110b03c80c03483c4030140d031400131031152040c0040707441c0c0b03498001c6c44030140600307599030744d030180301442900c581003819641582c80c400001030b01e91a180389140044109621840c440d6801111107600726200424014030100080e23801c2000d99999030141603580c45000c40e4038408210860b000e000054003074000b4203203080015805810a511400f00600e035900c0783d034850307000c5003000404004002c5400418551403104171224000c44c5060b8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154805008 1250 154803758 154803767
    0x7030b1e0411121b09031b1206070f0e032b170c030103020f010302160b0603010e07080c060f040819020f10021c030e03030108010c0806090910050604060b16060605040c 74
    0x290202014604007030f104e041c0d07040b103034058801c0e80400a0403585502d1307691030707020380780340341c0104a0340604800e500415403684000740050243e10959101c50000800718411225400100c0070540d06002e800805290281c0010807011002c241019030410040b007204042d290000d40e80720300c2d0b071840c1c3d0b0741c0801c41c10300b502009803411682c0503502603400c3c190600049000744100404922886030b42c045003014814110030040c458007050340200040060740a0030b070341c0d400c01442002c03031590041d4612030090500c07801801d88030844185e9141070076210a4420309101001c00c802203130000c14507448080d03161942d00300c0450102900c0410304041292402501c03444400003002c40d2001c488a01e411184c0300740c0c02010030b4002c00098a031256140c05030503010f044182109030004102c80e0100300c8030b03d444c0007881c0c003c000c100020400f800142140d42c02426009184030f500036945c90000405e0b0341c40400905d114202120034650301034452810004030740e016002180514548a4000c6034950070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154806258 1250 154805008 154805011
    0x7060e090604020c01090b04020102060a15050f0103090c080a02100e01080402010804021f05121501081906050406030501090b0901060b0702040b0f15030a06060f0807050307030b1e041112 82
    0xa4910500c25515800490068810051000d14640c80d0400c1e00d800e105100700507c0c0124801d1342610713105d44507100ea074800c2c3c403a425507015815025000c100076501d041c0c1100c1c0d1610700103060101e000c94942e01c03281c4c003e0200d544840040c0c0c00c0032000d6411450301c807454002c803803a182807888210300510300017004513400400003418004907402007410f560b161070040119201c1c02c26000c1805000000080c541c1e00001308401e11507010b80003090446480302182c0140910682d00d0446c02d03680c1d4544c00c080340301100c041507a0103a031144007042e103850324003a09019601510000c10b200c5118500343c40000d800030703e0155107901d0140c00b0f104a8050008541d100394040b10003041504141c0005016200342d030504907071258032202140814a0322101035072188004800401045903071b40000e03030b00d95200c094440c0001d01804001002680250040c60f0020014600040c0c41e4000c000850340024403c000344004034003800008000b0b15045c001e8104420030400751900301a0385c150f81c042c103001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154807508 1250 154806258 154806287
    0x10e041205090a03120909050a0b0319060e0706050405010216050f010f0e03150f0f010513051317131a0706240905220f060b060d06080601170706 64
    0x81c0040c110105980704481c04000e03580100e08038034851000c800c094012070683c13041e03c0c20760b814000050101c80b003610a003d1107a4020f00a054602c80002c0001801310910b20100c3c1c806a0304e040645603c241003000002608854942d10f80d90b600700800a854010001000001c80c0900c503003d101c241c440951000d0b031a030342820301d40701c0d0301140b96064a1b81e1801740f41c00b50f010f1085440140304001100366290155244100598540d1101e681c0d070301c040c0ea024020583c1140721915803c1c0d104401c1d07406243d01c030b4429000d0780c04c0301d280c0c2d03a6003114040200d4203000c951000411100203414a17134001c2401003451840070f4280121884800b10503005000340900941c2d43d07061609500c100440e14080000b05500342001e00e20744405440c8000c1406a8130100b424802610168070810300c003020008242d0090503550000a095803044042d00c1d80e01e210781e030882c10600840c90001050b02800740500462400f0300080d40c14142d94010540c40790481a0055005500070002e03681c10003001c0f0142c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154808758 1250 154807508 154807517
    0x50f040509210d1103040c060c0503090d11040e06040606080d020c060c03040b0d06030308060103060b09092806090b0306040f060b01230702040c050f040e090f06071106010e0412 78
    0x5440c50424003540c01410098103595090032013500c0302c1c0c0104002540304034440e0b94107001c110707121581160ba130a5200c4004007158410800b4034020f2402c01f000d039003654440c80520150b901141c01040907198610090142070380032505000411030503004107000b070100040107101038a107100700250384140305802030b8084e51002030f14403004442803088602800f010340000b40c2d5403220404080080007584001c2e00081c11080103e8001e6110b809aa4103c451341c5d404d0703078144035440041220000002d029a01050f071068076850f680c1d011500c0740460310021085c0054968a050640750a45055100e6548682c0200041100081390b14003800c1c5103d80101c1c00280d4104500016207101c40d48046001c01061403030f03c4141c0c0d04c50164010200a4801d4a0602407408036603c01e417114099102d03440704548082c032041c07044003450310a03103600100300803c45924046034240740341050410340794440050801c48503440b42c5001040514014207081c034001c0305a1910340c4900c1c02d03641e07011a01c5800c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154810008 1250 154808758 154808803
    0x2070503040f08030d0e1b1324050a0503010902010507150b030a150f1e09060209041103010e090c010f1d090f06010e060408030d020a0c060e0106050f040509 69
    0x1000c10039600500b00380031110200035228610a83d481d0010702405204a0030854600c0400c480803501800c001d80000680407506000740c104645501454542501c2503960f10f5100c14009102d404041d02c1103040252030f850600701000d0100c54030840d0491402681003006620050f6800001c460800d81c20038030545424402c50f085d1400b5100e0a20440e91620a0611800c04d1000464140c43c00e4035814404000f0b0707103002845c8000303440c904850600c0406250142c51302c417140d0381d00141c5440d4815540103150042103000078040b034400309504841070780040014400c0c4072a4000241c0c000701c03840001e164281c910f00000307100ca03035070700349900401411b1502c642d51011003000c41e00b07031000000c1c040b0410b4a40f1820308400c4003000c0b01c00c0c13030000342c1580b0580d810f070800301c04840030307940040007540c509145010001c02030342c4114200307810007400c2207821010a0700c41c403510890a190600203c1e2942c034080810610402d0310206034440c0d40f40000f80800c030303500000c10a4542d26000c00071001e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154811258 1250 154810008 154810013
    0x61d1c0215070303050f07020c030a03032313110904151a040f0902031605011e021e060603070506120a050a0e03040603150e01080d03020c0712050309090c18040207 72
    0x71420401c07810340d000c12022540d042015055045903100d0310346071072415890303614480c089942e130844400b500c1d0550406600308002ca0322903044803c5e001900d260384c4140308840348a21010240c1200d00307418a200f18a1214204030140610800f820800c551288a5084c00e80700c12040c100401f240b154030300c0c3d4510f2a213000511030030349038510101c02841002000e01c50382410002d0310391007008074482e028a0003038141e400c0101c840390040e60301c1070b500c02e01ca081d46074005131940d00035928500c00794810340c00d4000d140112101d0201c608400c904c003801035410300a0a041c98014030790031591080d2001e00584514100070841580e21840f1158046616210b100f0300d5401407a180d000c40c0340d203020006000c1070f440c1e0540c022261a0440c1e03050504d441d0b0b035a51400801080c2805a5086500100c0d00c060f03009110b40c0152200358000360a840101d9981c0616486043d6030701c40c00c6545400c00701e03030741d14180b802c044201d07030180c40340e51050329020301e080c41e500e52001d050500d00d208c0c5502040602c00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154812508 1250 154811258 154811269
    0xa0e12041e1a031537030219060305061f0522090c0e0910033801060e040606021f0b090c0c061e0103020f120601060504061d1c02 57
    0x20b1141c03180502d034800e80d20305080c60aa008136004649101c0e001549207041c03c1500c1c40103480c403030744600c030f4443c80300420205170320725150a458105003001a00c00310169481c0004581c1c881c00c0d60301c904a03558900040a01074034401001203211381d6941d000030302120218a1032107295421850055980e0140503c500d42009851905000280302001c0100d45c0342e441e80d02901c1c10207010b03143c04601c01d107000c0410100c0007040705d180c1220785c1c8504d420000100c1e88590003800e0748000c3d20031034000a010810740c00c800c1f807440550704c80b8958100100252500440031400700c007000d032800d10031281017180196031801840f810b80085011a02e0510325158564820000b0700401081803c06040c0214004243d07040800300f54246d0007188040341c00040224040071840001c201c094007141e00e95000c12541c030b00c11112440d040307200d0070491041d506042c04028003030401911440d4845041980041003108141c2084425003050f4510481c16a1001080c0c501c4407102e102e140030120304c0d0b101040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154813758 1250 154812508 154812569
    0x1011070f1b03030f1b020609091315090210050a020a1101111009110108010f03031b0203030c01060816350304080601090f0902010806090403020c10080a0e1204 70
    0x280307140014012040560003210424851070700e6a500c140680d040b8000400c001c6039050082d0300c40310030000c141c81760070710300c3e0401d5001c0c18019130454888010748505807404000c000d07100381607503240c000c08110304e0f0600e2004014102413501e43e04219202d5030107943e81c1c1c0c0d99040a8601c50840c95926140d84c45000891600c418130026940780e60400b50365100a84041141241ca020313190008100a52203204c841d4122113080c0c001081d45459920162440400d04c00300010394055182180c0150b1800c20051481c41040c10000074498074020405050441d40e682a050880e1700d000304000345030394008a600719400041c20402c0100707502301005441040400d114a2902000c1000900100041074103412102c0c2c0040600c03c4c1d24a180080086620685009021451200120b122824011180340d4001c1c400c0c012100014070f81000151210408201030000a04907401c10042403440c2c040d031080c0c0f0b000c000081c44c403d452106030070f801e0300541c010514000401d50044040400000484 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154815008 1250 154813758 154813793
    0x120309060c091e1207170c100c0f052b12050907230301050f090c010201021608070c050604080102070501140405070e0403020102130902030402041a090601030b030f01060602030c1011070f 82
    0x49000c00d43e580070f041d00c4000c46c1d556a03041c40c0280c88450056041003081141461100d640d85540d11010703680b003e6003914000c0f402d580c6803041030f061060003c241041c1c0740c1c141c001c3c034201d040583c6445c400200482c04a0031049450350402003400030811000400310709417600040250704825080c03106500361601e035040c00368550300345800d000c0e9900c0a40642c0e80070340340c0c48082e5804180c03242c0041e4244e05c50181d08041d51451701c4c5162011812020144c4440d91256201e00400c5a0390400503c264004e50401401a50b0000324401080000d01c1114041d0402e50324801184c03400762245074881e202c62085514071114000000d0030913200790f048550130303d0f501a03640d0300706445030305420007908111003ca01135443e2001000405c1d00107400c0c8004003000030701d400c1860380c90703200440150440d14400c1d50540708084507515040f40030300540f0007400d40c0398001d544441c6001805480c0c1788108011565440c0b0340b0410484c2300081208890322603030800506000b01d820381c07400b58080354440100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154816258 1250 154815008 154815013
    0x11180111010f0c0f020706050d0b0402090a0803041d100909050a06050708100b030f06010f02102412080a0c0c0e1003050d030608031801090503120309060c091e12 71
    0x9054555826900420290120b44c0e10920546040705050360354080502400c03003c5002441740c25800c044a401090190300c01401c00760509280d0004505980403507080220290000f0034240b0003c19904603d00042c0c0507452194040c0c14113000c11000302505011f102c0300702d600c400000092000800c0f010b802c143d032000d8200114689101c8c0242011010784842100300140f0600165006040d01940e001e05400107032580caa8458800541e4101e00d109420b81c1036001e0040802c0403200380c0d2140460004241c40501001c41c83c1001744010201d141e0841d181c2d0420380e844001c0401e10b500b0a8400166950a03d138a00c102c803418012140509540403201c0060032908000712040410981002c6a10030003c8844081c52000d094065540b40d0141048541c03003840481044401080d594021013410304040e01e5036500e85000c41c0c102084071000d80244200003041c011010010461250321803804264503042104500000c0d401800755580461054120020a420760303460a0220484544d00c408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154817508 1250 154816258 154816271
    0x40b0d0c0503060612060a0b1201060306141803161b060e09060a12020f0607050102040f15080103030f08100906140301060e01030305160309080a03170a1118011101 72
    0x181203000110341d01689000f0b0003040007203981030414443c2e4281c000740c80405490a5510440c4840083c45400b204650040c60442c489070314110a100e004065801080042900105165620076444000e080c0e001c0840300101d1143d8140408416a090f40e84021004c4a12680b01d00344014500020f15001280340c484000009200f90010040c50b290442901c060b041581c60380b0400841d10000e00c548402c05803510203a800510b0b00c05d80395142410010300c12403c041950f2950384c2246c0041e000300c0b1a94020a40601c048218492542c07650005468014000e42c11694010004c0080408070340520400304003094200c060b1403001c1c0064a0310300760030418075540d82d44880840c2c94443d0500e009520b0104045030380c03a880a00307103041e00c0d055103d02c4e05e0300400c888440000701c5030f150180c0c02c1096018020640240a01155070100c4c060f642c0c0c400e030314802d12001001ca2201a200004a03440c004200c42034104640c180c40d00d403c840402144003500b00c60050b125080004d544a826528049 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154818758 1250 154817508 154817513
    0x1c0311031e0a031d0705060715150501020f010c020304090504020d02130506011202120105010c0201050d05040f12050c0705060a0224090606270601140c0f0f01020708040311040b0d 79
    0x1c0140c0304000b07565800740000040040c203642202c6401c160020290403070b0f101803102c0d00300940200000c910603c65106640305101310f036021075802000600c50340301c40c01d80800456030304200d00ca8582d145007000f002018001c03040a540d82c42103100740c101c1c05071901e002505542d07a0700a10284a50041e200c0c620410a05440200421080300c0142c04201c004030780002c90b25041c400e0300c022001a288004445c0d0800340103440340158504200d040080800041c00f00030220b00905008611500d00a19040120b01e41155880c400324004801c014082c0b0080b0008100082c0103002c4035819105191b4a011020f000ca01341142045e40c0d540d41c0c04010000001340a100c21150303c40c0c190b11050b030314140c4540d4100012802024138501e8904149180b502902c2e2034507007c942c02100504001e04014030b41d403440c1e00660040b20b00c90409410071ba6245906444c2070001281040c4100000c600c0c2003883d5941200f10701560102a003501100c4400b04815155903106210342000100311200781307a490b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154820008 1250 154818758 154818817
    0x8030a080906070e0109030807060920130212060918010c05030604060b030403080f0c1306051b0c03101104050604080723011b0606090213030506061c031103 69
    0x251206011407182d4400501d0300c6128144110921805a40780e0004510b1619840c0300f94110314010f540c00c40e46e44020000264005089080044030940084004610b24080102000b140c10b0340100c903500401241004004504c900c95000b08101c60030402d41d228020000c4080f1014001c0d29100d6281c2102e0000940d00400510301c80d41d0308440c2802666142c002c1112103010076280200481d01e6034022604c0303401e029007800c1d88481c400c21118204070241200e1001c03e4400e130701c9a808110002018100003080b040c1380820300d25110001c0c04c80e80141c1005c6940c450706500760001569882c911081c1e91030f038150840300103207002032425884075140d075081e948038405403003410038190040d0034004140500d111020f8829005841b2100100035014519940c1c6602280c00c4605690303903540441c2604251020f4000040c111094018280c02e500d441d620301030002d050540705650119415441d0321142d2034813003241c0d038185081405060040390480c95800303814a40031000301002c03098980c030000d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 154821258 1250 154820008 154820011
    0x18030a09050f040903090e0a0e0a03030b01030506030a11040e102a030c050d0e0c04050a0b040b060f1b1207050102030f15100f0504050d0c0e07170703051008030a08 72
    0xb01c0382e0003466980c0c441080b045440920004011414004082100d080300740902035200c0140180855841c1c02c4980e11740c00c00c44a007030304401080c2c3da02c180c118070356070600c0382645c8400190010443c59a180d281d03403601110303906407140b1644d160014004115005d02c003503520b0050307812042c018a00b6082e48804038100d29006035003151911461160603902c28015000d030071215440f1540b400f046003040101800c0d84003c103032020310401d0200992501d80d40306061041001c440005044010402000b044c0c8502c4200a031054500340034403802c002c10b0808480b4125801c1c01c0081d040d190540d002420304980c840316005445003c980b40c070a01c481900114850780b235034841c848030f5664880907071001e040c22005403504070014a90f6540c00e1400b918210729000e80c2414100d092540e2800080c0580c4044482103542c4a5400403c1104030030b00d02d1642d801080c5c6041002d145010070b8607652110303e000b001d0008043c0c40d8030105811844511801c4082d0151030181d030350f5040e0340740d80035145400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 154822508 1250 154821258 154821269
    0x602131a0703080f1006080a14070e0301110c1002160c14031c0219140708010b0406080307020105031303030b040c03020c060601050f0d020906190903030e01080f060918030a09 77
    0x2c15000150202d214000e21392140c40505a440e1001c0c1c106402101c0128000b03002914555490324642c001c00c4500003005c3c8104c5207070360740d21003141d070080a2609607a80c8517255403000a040c000c041000c40003080c69248800c01400040e101c00440110850204094001804800c0411004121458801c2039141a02e200b50100d07007940724036001058100000740c01580050b000f0304a126540004400b25009141c00b41158001c2510364035800c50510041d58460001d5a54960000a440c141401241700030440c0c00f02440c240b01445c5c001130282d2100810300788140c441c0c900103100b014082e62040d56400c80c0a80100440c0d41581c0d0301500a41c400140c9007002c0c420b160000390258071510490f04260f0003402881e0900204510080281d008500500e074048402d00515600c80305101603181c200000b81d5a0b45125031039420302800d0810003440f9641000505020096143c82100c1c1007508a2802e440306245603548092486002c041584001124000014a940b00982c4621100160380 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 154823758 1250 154822508 154822517
    0x30209040804032006030c0901090317090109150e060c0a08030f040b090d210b0d0b010609150f080702101103070f0c0519031101020d0617010e06040602131a0703 71
    0x20f0301c6042405002038540c05140e12405c1000000d1012441001601e6816010704000c60066101d90340c4400152400404158101c00400d040c442581e00c4a000f9000f40038249a64a0000300120002e01c0411118405e0b030061200066805980c04200f105040d8030381c1260065440c0c2c02e002240d406e11030b100341c03025034038001c03c8004104540740c080f80b81e8a07458440e8648914101030208150341d151243c024a560407580c6000548040c1c8810000a04281c410355a000856041c420040c1070005541c2201051001d01c4400004003604242090030705451030500b0311550755951022482c002c005020705085a041182e140380c00101400550300a0509441d02e00205d2180e8a04a8030a40c581c2805401e5901ca07240710504c8030022441c07400b105009242010b00724000c40b45050990f40200d9240406581d140d9003080040420340c0000e0021030b03200c00038440d4000c02d5140c26500c900160000e80155800105654030294901e2804010240c00050034241440da1003010805e0b08031100641c00f14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 154825008 1250 154823758 154823783
    0x50d0c080c03030f071709060105010305090c03060a02030a141303050d0216030e090105030a0b060d02010207030212060405010b0906031f0615021005150a06050d02160b1608010f06031503020904080403 88
    0x86e00c000040d80d00c9900d14500805080e86804011800340c44041c01d981d0043c0100d00405156840500407544181c01a0b000580c0c1d03810202203100031100b0000701858448141010720904056094040030266010b240803910b46079944e10310360081c4200d18041c07180300076120868003010380043c081c644441048030001420b030307a0351080c9a140c0340b41c1da000801a0380340c0d80005015107001650b001003113006104646509840f540480d01d903114030360110315264081000c020401c80c003401402800401a940c4d00803505120340030994401c6400d90442001c4490000c00100c4040c81d84070000610b0381c1040300c030201290788006516100e20181d500d100905100002e00009400c891072081c041003c0e0103010b24038601001110290048030b200f40c80d03150200100421030080c00b10394002c09028681402d02c1d81808181d410880742c2041401050012040041200d000d0507079034541101c05500300800d1444070745400d07186140098000a620141d00000d100c203020a040240c01070760b00c907082c1d20b440d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 154826258 1250 154825008 154825037
    0x60108070201020307091710061706070c03080f04060b090a09030825110705040501030606080607030c02061f150f110316030f030b030d0503061309050d0c080c03030f07 74
    0xf41d00c0201c1d000008103900003400c0001c071302202101d01c003901880c0141d8050030084400030060305d03903950240c0e084540c00d0b520781c0c11700d86042c040550000003904000c141c041c22507402510300c0100506d000f2091406c07000180074080316410039002010000c20808040ca42403100b10018032540600303030300050007100011042c0103441180c40c4111541c204140360844420b80884406248144400300b5029103040040c45481d28022640614030405c800700c0c0103414609014a4210010720102c2018240740f00f141c40c082d00031400d02e81001c01c940041c070943d900490181800ca189078012995800d0101c20546c009a0100000d08818030079600c1d14681800b8000042c0d50340612202c80d19070f00040102d0b080001e000380c502d9103040090381004110f8a1304a00068104202d8580d42d00100d000082000b00515001003200350300c041100003001411140d4030340030741d0741d04c0c144101004d1040c0d5290f602d041c403100c441980c4940c04142c0840b80d0300e00d01000395a01348002034410307030041420381202006 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 154827508 1250 154826258 154826261
    0x210f0717090601030602071401060315050f040b04080a0203160804060306080d140d06031509020a06030905070b090f030d020c0a09020c060601180506040f03021305060d030c1a0f060108070201 84
    0x100401d0005203800e900355150400254460001203503001204c1048442442d802c0c0078420007140a0459245205010308041098900040003550320f180440f00700800509440d80d41a040780d004848661100500c0354143c0c034510860900c1c211080103442d54408206246000300165080381e50b050000c00d58801c485640c80741461140c0021403030404040044041c09405010711880c1c00001094003540c90301d50510080c0300345164414281c031650b4031019030400c030060000900b220300e07003003011300c03415101c02c0c2c0c992201e0b0081c442d103120000b41d00000e903903512503920052a0000c0a440a500113182d0180d61510103000c440d000350308022002a0302c40c1107100352580000e101026204664940e00112035540584401d420110382c1104046115221500684041c20081100d1803d06065004004c10784d90f05017201e000e0642440c00b080400d40703c01d88010355090b4076080c07510021308186800c0c2c044407029080682148039440400030341140100d13040b40500c00a0300c807000c068176001d01c100d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 154828758 1250 154827508 154827511
    0x20405040608120f03060103180302030c0d0207080a02010e0312040b030406050112080a11120a120b040204061403180d05040905060d0b0106111606020a0c0605040e01030206210f0717 80
    0x2002075506104811200c0341460003175510220500d0000b03160001e91007540c02416280d42c0580041c0e2021440f5408001c0410000c0c0b45190a030005200d081d2500d00c0349560b5000d402c20007030404c0181d84c030b038a24544081010860941c00d03805141c0e11561900c0c4501226007007100c0680f2543e0624000103154070b540c442c500d05003a0032080b014030340081c070101624811701e1002503c0a92240e400703c041d081c0140300185c8814105031381c4500340d002c1031000d610151550900076902c10303481080200841d9810a0310803200c0000d242c103803616607540c442003940a10a41d41901514007901c103001a40303d0707000b030061043c0c1e00407a2040084e0748550052046a10b071000d8000e0100e000b100050240a00030032001d030b2801d8180d0300716944841d4038204807024441c294440005030b80031181c01c0082210300c0c01128090a030924129040918089621112010620019015290026401420043c5e0b802d4011488185500da640f8605001c5100000c042e422074014002903030a285a0200429035015103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 154830008 1250 154828758 154828783
    0x1209050f060a0c0b0903031006020601121b030c0905070801090b1003050606070204180308091b01030b0d0b04030e011d0d061d1e0105010b030c0a0309170d020405040608 74
    0x144060600c0300288081c036030004080304140b00780da0410000003014140201e01c1403540e58091071b2a03017040c03040f03001404065041039041d5008540180b00b0059403480c0710082c5604030940c183c035007220140000101a0f41d4001903c9000240f401241c001c913640c02030b900926555554078016030307030f81310b0b0f04017110b0502030140d6100c4084801010b0032840394014580211009142c0c030300d04410340e0700203802c454610303610084026642c1d00345828560003403115648207050341c02805904001c0c03110140041100280305051650b2505440140d0315180c5580710020f49c4688800d4003424035050103480c96819502250005036951a200e8101404055020b040c21010f4402e2020b0172040d900c1c1e00191101c02c00b24000400720305030910815108000303042e0400b18000740d440e403114040b445d4500b541c10580250002c1c1c2020014441030700000c0b422200b10450f1807400107080300d50352a00c02d0502c001134103000450140407460803007a82042d0700070001c45500312003c010385942c4000e0203407641800c0c9960b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 154831258 1250 154830008 154830019
    0x30b04050d0f0f1d031204080106080d030b0d060c090302130203060a06030b060d0504080c0a120210020315010f12020f09010306050f0a051c020312030711010509120d0e0316120905 79
    0x10788060300d506800e44e4488100400b62010400510708080854009a020502c941e440350b0023000b4201c020310a000c488900703842e0500c024850703030020039002c543c418001480199500d144e5400305104030700c0c1c50302642d8000c1440961541c0001140065001650b0482c419040d2140001748240a84a50021900040e05160901c4000c4260b0303401400000d02c1690740c200c080044034501c0ea404d0101b07031815442011030f003001d28001d0030001d2410b0544c40d09180303d24410410702c03400e4000260000c108078424a0301c80340c18220000c04441e0101c0c280c261080703890001c00c00d02002007800700500048082070340d080240568075001c100120200c1700c4001d4021140400500442c101421440e114000d8041d4152408e111a03020030324020300009501c012080110a03c1142a4400d88100000801c1c5000340114203110b9403550b11420710b241c0d00c524200300041d142600c925250012034280c4448815241c4030144500d201c10b4a8802103000c803182c400940b103582c1d4080c0544000303815258054034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 154832508 1250 154831258 154831277
    0x1140406060312020a05070b13031203051603050103020d0b0910050934050409170a030524090f060d020409120f170c0a210905060a020408060a05060a030b04050d0f0f 73
    0x103542a542703e040c038000d81070102d01011010418079a0100c024007010f0360002003501d4034400504c86030880c20400020142000d0040026940304080e00c414180c109480121030380703400b002a454010441c0e140c1e01c00c3c0e410703c0c0412136201e8001c99034200c0d403281c40c0c031030300d0a18504040c0300c06001e40307058810b1a2980120003d024509040c1c0c0b142d04190701c00d4200c00006003003034001c03400c16001040b03004000b079110010031080100220b0454259060082d880203c0003015000984e2442c5c020021000c224a0600195455942d000047d080c11380252041140c2c5c0c0060a0100d05480847c151401080328840c095109a108114240b00000c00740c86865981e05d5121300d00c921a80090804000c00109640002c0c00203405048810024001340307000400c8005843e02904100000300114085032051104202640b00858030f19800149400c00164540c0d0702c0002036010103080e0000342071440315001f00010400006056075030350302c0e80d4a907501c0d90401c28404880a001291880000565429 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 154833758 1250 154832508 154832519
    0xc02120f120408090a0b090114040e040204110409020d0f0b030d0801060c03050712020607030f020c030d05041e12020f0a080d0c120c0f030e0105010b030c0c01140406060312020a0507 80
    0x42150b0060300c26200c040ca072810782000114112980d401c00340301c00d0400182d00185681010030310f008400004519401c1601d4649400d5000c00018030190007541c4441c2c000c01d901100500700e03409846c0d0000c0c119182c006a00106000782581c0321384d03400c100c3c60f051203078840b031500158048410b4800d55884001d82e0a200d000c840d6211001070413010300c88203110361000035a82b202c001d250115136074014209071900302c00040950b9400810340c2220b601c100074142c2090004400c6030183c10480340045031607204d03842c240014195a0620012a84036402c080702040342e65101e80845400f10790840e074428415021480d00c4020401005060900c10003010706400c03040c0c0c226115800c06030400c44c0c1c024034113000c001c0698040800490004090008164440d9010303c560801f010b07145008021944c107205d110010f0348000382c084c100c0340074041801c2840a400750020340ca0b9101c4811654400c0c207080c640319024007141d01088800904c030300d00c5020b00c00d01c009010911103400400901c0c1141c85c16 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 154835008 1250 154833758 154833787
    0x5060103080c12030403030b030c040c021216050d0f08090105090304060f2606031e0309010c14070b190c0b160201200c010c020f07090507210c02120f 66
    0x74102e0518011144200e0019101d80041c40c49940a82c401103182000700c1c0800d410034882510f03141c452890100800802940090b540020b800070a03426581c4290050502442c2603000c0700c014803600c25580801641c56121400c0141c3c446152582c440c40d44440c0c400c1030903a80304640e42d5a003980140410080325205284100100c11141024841c1c01e2903840440641c02c00396506504e451034032420300c030090404011100600300c02c00a0000541624003a440e04c9100340000d650402c58244d070074405210601e1353b18201460040e04503080503580c1e43c921181078202161201109001c5040e00b003219001c0c03072001c2903080c0e004080205655411040000054999003003030110765840d1046007030300395a000034280408082c04600e8440304410304035800c4d184101102c0085400560381c0707412400000404000f40c480444012034151f94040041300e014512a03441700400450a121a4581040794401d1400c4e02055090380c0c040350f41a02402058480c8143e12244c503881040750168074141c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 154836258 1250 154835008 154835017
    0xa05032d0a02120f07080703021c0c031403040302120d0905010606092603130b03090d111903030b04290a06050909090304080d021b090712051f0b0408100204030506010308 75
    0xc03002a517080000913103d0302c00c40e4110070381c103c000d13034404001817105425000108105208510701010040c80554000b0200080368a1034006641c020021a003010300a126032041c0c1c48140b444252140380041c40b0801a01c2c400c00c043e6581d5282080c04103403030b0710071004442941c010808070900000512000140140c04000b000c0300c80c0814025800c800400d502d0360002468030382601501c3e070600034500c1c0c0c00e02d407070f6005007428881c06089458280381c5c00300b500c5103019403030403605026410500b400c1e40901111040781d94413520705003c6080d100341e00c80c8075400240090b01d814281222030300a000d902c1a1501514002c84c9090100c1c954501d0000119a88400c0e130700141c0e818190b80700c40301c80c40c0115500404000d6042249071092a40404861614080b0112501c42103820084005000ca0403140801c040b05526030002403400d40c2401044080440d001c141039500954551501049801c00d00807642d03e0b0042c078603003c1040e01d1170f009540c01d503900200901116480c5030f0b10004503510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 154837508 1250 154836258 154836277
    0x1a01051009050f0d060c030f0b0604140904050a0501110a03150b0f0a09030c0b19020718020d0b0307090204090e0c1f1224090213060e01020a05032d0a0212 68
    0x410404c0000010100c2c0a24442ca0300162804516100724194040959080c1e0300c03024000c200c1440100220402500703140404581030751104055101c0e4282a42404c5801c5000b1746158240002c004699040100801c50320b19182d400700000d060754002c0c40300700e18a9100390b80c042c2034180000c0d81c00e044450f00612042a550401c503030702d80c3c2d50390340c1d55a0401240d40500c49401c004500c0c44030f040e810b400c10548480807840505403071800c2003890240480c80414000c000c030b40c04520204041c102c0c1c0e00907920090300070101c6103c2a03032070907108042d5002d8000c1e40c80080c01c1c1440004d48070000500194070f018002d081002d448615012440c0d902c1d240c5c0809001c005040900c00565003251081800c80d4800442104064411032a00309010070f8a500000b00244100003a1001c030582d4041c0e00140c1d080d9140540b00000780b07000403450070040d076201900c180800615180782d80c03004804c0347c1141a11a2802040f40f094508617000c0f40100c4c0e0400c409a0040d160701d001106842c00280b68800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 154838758 1250 154837508 154837519
    0x40f08030702150901060305010b1203041e12060504030e01020c01020c0927160f06050d0c020709021206090105010905150a050712080901060b16020d1505041a01051009050f 76
    0x1000020039110f501c0d007518406582c1e55690070a1080c01000c2c02034441c152405d03941e000c4943c1d2215015540c0e44214403a00300800f00c0d28880450709461805a04000d2014485180351260981881001810f00f0b40301200400c4084d4000c4200d94004204000703401b005030041c00c05125450140080b5490042464000741e054030300809000660302c010390b411814031030050101d6914485010b031212140d40180142001c080c108104441d40141142c05020000001080f070304500d0a05a141075499000350082c0d0380041007800b084c1c00c1c4142864400c102c03c03600200e050740e80c0d07001514071481c1809103a07000086180c000c80c4100105008145842c2170f49806864074006440c2c003034070715040e5113050002610090074000704210901800028103032241946242410f12011441095a8540024014451414644c0034001000c001846a51004d01d082c030552500348ad000b0140d8640c0303801c0d695580032110000c01c0030300741104030340340182c000d440b48501c0a007403030b00700310307a0f03104480b18158050f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 154840008 1250 154838758 154838773
    0x60d061e05010305070801060803030c071e05061812030601080601080709120309090b0405090304061101021b150702030c0a02040b030f0d05030709091505040209060c0a0f0204050708040f08030702 86
    0x504980c4103560085004d840500512802c01405d81e00350b40765a8803001c4c40794420b009109030440c4640448150300c0e804168010a440802d42c074055042290102604602910301000f0401a251103050044210541a50a06013a8190505072804217a9419000442d2500050301c0355000d0301c03050390006100e00f0143c4000d41d030340401003c107090014046000508052003005403805500a403040103204a40900c01480c240c440c1da940ca000b030388078000402504c2050540460029811108141d50032400c420b1100c0342c440880e0390310590b040714890790290740e5000030103281c8007000350b88610304028040d20f0b02c000b068082001804840c0441681800348075402c1c800084100000c43d1480d80c5610f030f1603241d180054015010503426400301001313a0924001c16400b2450351983c50540d03504550041e262050790340860801e0180c4d0750040a644510aa40424090b120b5407010b803c0c0c0c4210b40501030f681e58014215501c12099600034440c542072603002e000150740c20f0195174480010706c11100c0c02d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 154841258 1250 154840008 154840061
    0xf031005040f02010305090a15050a0b060c0102041706040804050904080c1506040b0109050d0b070c1e060c05040e04032007091401050303030915070309060e15090105060d06 76
    0x4440003940c08561a00030511030b081156054014994000480c0001c0c0000800c40e03103c004012000c0c103900384d500350f901d50020320030304100d91000d0790062001d84216150703294800014001d5100703002e030503024030b4030503100209004001140d500ca103a0001d80c1908103480e0006102d2a030b90090001c40b00b41d40240311240140300e08000780c0600007000c0703203240c046017042001e0200300c90440d030040b8100505a001842a82c03521100080310503030000c084c038007982e01c542040f40c000c0c02074480208016459403140d0b000d005004510b0b0041c0340a44d5080100114105061307405226901c260f16201c00d146d000980400d01074024440a000116807400200c4402061a03041010035000403010319079034a100c4142c02841c0d05900c0c0981003d500541c41c50400159151795100e404032a030580000510019400d20301c80d030007190489a20030740074040220703849092604c54079244e2051f800410628001204d018050003094000c14000d003003042e4040c0992265000780c800c400300210300d0611711384070100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 154842508 1250 154841258 154841261
    0x80a0203090621070206090a0305130302030607111006210c03140703030201060b0a05030f07090e0a0c1211030604020706090b0403270302090f130c060302091005030f01050f0310 78
    0x1c0a01058192281001c500f5842e040c58031000e001c400c11540107034100084140300258500754647c140c1850303500c0343c814403041c011701a851341000390940207840500c81403c0c0c10a40800226030003130b00369000034500c011201d04840281c4a4005442c8012a41c940821001d111850000f030007442c8440740242c9a45802c04412003442c0098443d90150b003041043c140d0a2007038101400c40c58407820301c0d1610002000305240005082c04c030810b0500c1d0003080e100ca010b100f0000040c840030f0100c2c1500d00d007040c01c1e000108040a030500114840c1150700803140010700c507050140d01c0c8503c1c2c3c18207640303448050100030b4004000c00c0b40c1550780c0b80c0d42540401c040ea044148624400c2d581c0030b0a460031100c4503008081e811007009109120020244016035440050a13400001240701d80d8296860031100c151004203042d014000003603502011035010fa06400400b05844240c904605c50860704a041b149480115503001114a0590041c000d0b85080030890310f51600c018120760300610400c40d21760 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 154843758 1250 154842508 154842517
    0x72717010e01110c0d0e090606030907091104060806090601120e01091b0501021e031c02072a170c0f030102120a0204050406050603040b0a0c121508010608010513080a02030906 77
    0x100f80801081c0f070180c014040040d401601d241d8604041803800e208086004010040d003001d2040c4008400541c00d450104031900083c20010001d010303040040c81c51040580c041d004100020b400c000006040303003018580c1500551701a500d441d205a031004055005003042d10304003807195210148400429238a200f0341408241e00e003208902d02e450310700060301c2e0420300c1c5052401c42441c1d4824a25102000c33003524900400c00800c3d000214144130400003e03c100c1d90000d05880b00d228202c051a041c0c00320440d00105100d03000740140d515032150151190201403031800c1075016030442110307405c20325501301e000305018002600340a00d44030742410320780701120b2282c640c0390301050802c12440c02d4001c1800400e402d84201e891402c0903192840400c0e4000e0a442e031007921102d1a4125501c1610b0a03818401a6101040442e001175181c5a0b140003510031100d0325030a010300424400810f205142c042d04014880c1c0070b00c54055a110043e680105040d403081d40000e100c914038a4031071000a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 154845008 1250 154843758 154843781
    0x120b0409080a081609050607060504320f0610060e0310020c010c0201060e060319080403020612090709020a080c1e030c0702090a020c0c01121104120318080c010c0809030d0503072717010e01 83
    0x1500c40e0400116433500d042c0c07010340361600645c40f4400384034481403211004c0040c2e6045142090035054000d01191803c0f5881802517003940c4001440004803c066100052000007640244103980da21011000301050943c0c00e0341d415040080c0c03aa030318440407110f80c0819071103441a04e04041c0d40380c0000c1c850350082d4520000300240c002c20003080c0c0c0810701c00c0340c0241010765000c608000c44058020440c40c4e004102c2800300308009100074520341961004640d4210055a00e41da901d0302d504030314050741080340200d0181c01c001007c40d100802030b000342d401880304140104a000306102c01160030041505d07a00c501548c0c1ca181c4c4101c00b05c0c0b03110080c0060900c5950305120362815150082420032081490399918500319410b0040c480046a01c2200d00c0b000d2030002c040c0c203864142900300384200001d2544c0b44c840c11000c003114680010146108148580382c0c1c11144034010000c01035400340000702c149910305046d092003e505610b81000035a5941000041c80344402001c40d0308482078694036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 154846258 1250 154845008 154845083
    0x50f04020a0b030103080301060305090c040e0304050f0409050d0804210c0209070302030415110909040b06010810060801090f0e0d020c120d120b0409080a081609050607060504 77
    0x200000d5040c114065001481d59040961a40d85136844007034007400180141e4040507203070030110704140001c1201c6207230000001d00410070201e1140c1d060f40e4a034020b114150041802d00d0b07100220346458460310f030005030002c0280c61381c032094042c111203204c402001100c030000950f56010100d0341a03207401c0402416619110500700050040048030003009040a0415004008020018182d9006151981e150380070104689501c0a0b05140ca409144502600001150308003c10300106e80001030141400b81c0b00c0b000e143c0c5400940c5030f42e4400900403c00422100401004103c0700c81c1d12030900c002c1c140400140e80d1071603410031030a02d002400700c035006070b00840745200c10b80780a5000400c2d1078000c1c0c000780725100c3c0c0d112000d08122071a81541e11800c2c2c2d5021400740d207846503003081268941c081401a49c50480c003170090b060140c10f8820406501301c16443c880410700649904080d503900030440c2d810500c07151b1705e02c0090100280203c1b003003d0a14001403d81e2200e4212a40c00c0358030900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 154847508 1250 154846258 154846261
    0x5060d0c03110d150b07080d0b210303010f06030605090c0306060405040207120f02010e070b090a080316031101180803090a02151b0703170a050c060a062d090209040f050f 75
    0x100d144e8010000d0301301405a200820a110000f1901000c481c58040200d0022a0001c030b030000203a8140301148550104043c2015062030b0107030f02000a40c1a24100300d000309800c0d031039810440440b5194011a034100d640781010620300410040a19880100107114034682030721140490700741d0700b14030811182c156801d90700b5890349030000f1348490310031580c3c0b00801c103000440004a90300c4820f40b107021459400000c00382030035152080703c00050500c0700222550b89011442d01121041501415400036003105140725440006001e1010b41410340c00624003500c0310360719a40c84680c00079005503403510540306206e0040c0c0350301115510780c98106014680707c10100c00300d80980401f401e1800364542002800f4000036500c00c035044050b91400c1007598480ba080300c000e07143d038815035420301d40c07a116140402c21490840e0b04000107a0398405d51401200c6603840c00015100aa0400e0707640a0b1940f45042c041079400303901400b001e0b44000d01c0428118045410081200c0040d12119500d010000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 154848758 1250 154847508 154847531
    0x203120304060b0d020f0409050a0218090706080907150c060c0815190b1c090c23090115020106030b010323070e0705130302090a06030312020405060d0c03110d 70
    0xc00d406039020240c0b13801c0e042103840d50020b03812100f00c4075241c1c0300725601d0901100b4010204100c101541d4003030101034604146d0002010200300c01c0782d0054180c860103102242d014440c0120b10b014900040080031031034202948143d03003203400319203641000761400600000c102180101c640322001515001090b04210b105560480c001240603809080707c0300746049904d05089040048590b403042131615440c00d07403d00e55018800d0640525101e0400101c602817140781d01b6003c00b02ca050a5038401c61101604020f82601c6900703041d182d00c040b0360320040100e0f00f021500a1303141035880c030000038210345a41d00c400105200703030000e4a65601c083c14004c200840c040d61142c0c80c0a00000600c4a2403804100d00c05455004040a007041070201d039002e9031440601c50309002e554024032407409450300544180080070240301c2030380007503001c00c0301030300000440c8221010365a028009618200c5da0040640c0a850614016000c0503500ca404115041102c00501090401f2003008203480380c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 154850008 1250 154848758 154848761
    0x602010c0903020108151206010312030b2709031b0f0d111e070510030b0108060f01050a0c23030a11030f040306051e09071d010e010608090307020312030406 69
    0xd10320141030055140c0244050303170300320050350380c070041400046600f41d082e04049104080000ca8034801442107d001108001c2888080050071001c2da4042124052407130800000d2000c1ca900a01c1801d104e524a02035074000d5554a64031001f01c03c02c40e450814000c0036400c3c3e200004840e41038581011101641001701404060642551450300c8009542d180303a006486900b404550710650340070f03076501e40c030200d07013445600d0003810001c11204074030300070400113030152807900321083c0041d0380131000803243e25140300010070790b84042e0b442c1e40c107210312140c040c3d9080c0600d41054035500301c034000004c2c1001d10560b04180b1401918095510750003e6040a001140e0280c09451141c0003803003030300340303c10310758042e1030459400090200e420b8642e1105140540c2428220102c0c02e840401088400e000003d03810007180d850a0b450308005562a00040084000f07000c0e080d0714507a01401002418450800b05810290050559203003100545c0003a28110316241000c80c0800088100b0007880310390b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 154851258 1250 154850008 154850021
    0x210f0609160b0403080301050d03120626070303091e031e0309060305010e13030c05010f02090307050402041a0901090e24030307110103230a020714030c070e040312090b01060201 78
    0xc00e600d0f0306060460340c80300d03020300050003110700404000078000c0500d03129940c1401e03010714845e02040038a440d01b401101c42c2019030346520310a251840703100b6001c140098408112601a40d07403a80041c04c3c94080f508003140804040c0ca021003540000c4041004410b0700c030f01c43c010081c1c80803030f003880c80c0ca0050a0b0b90b61a0307000720281840c040c01089a03d08040c1e0040d400300403c1c24003969100a49403d4403c0301d10034002511540ca008080303240c900c6654010424204104c007143c00031682c2e0010001607102e980075a0040001c040700c00c649208500000d8502490141001c410390f5031140c02031700203210f00311500220400c1185504414420400d6124103502d003c2d00950f25240d0551039200c40c200c50181300c1410599100204080d045000542c0000450709290109450414580400c003941140b042036803d412002d40040c1d640c00000101c4000002004c081c0000134600400072081400c01071041c2d0a00403441d1051400302c0840c8525582c031351080d4990442035041a000a00f124032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 154852508 1250 154851258 154851269
    0xb1612020607300212060f040b0a050603090109021201140703050c03040f05010e070602031b0a0f06050c0403080a11010b0603280b03010c051e0306210f060916 70
    0x12080c014450342c040c084481e550f54401515145950603002185403100e88507261012902c041071146044e211a20602d016203800c1301c4201c1444290420030040710145404240d1218130030030104154180040915404190170000144990050f008240035845405042e49265035032488401c191403010402c0d60003c0151030204846d180c200c20b003050902c400742010380f00101da48184000c11001350406c15801c801401510b90a507500c1c0340113541c0b0341005a034020010281c16568a000000003050040b958010166200388541740e101c0c08011311000d000c0c4200c5c610100400b0010410030002005131152070303035610400480344c803501400c4031001e1608500c6150108284031103042e1208481d1000d00b06014991604000d202030480108241d0103a16015400c042c01c00a0702500500a468a14100c4244603407a14006050807854401160300e59840500ca1041043e0316615681d42c81174101d010007104c1c0d0451110254034a041001c6507550b109034024820f5040031045c54414500810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 154853758 1250 154852508 154852513
    0xa0608040606090903050405190f0f030b0c0901090612021e0903011a0924030a0c0e010906081507180b18010302070b0103110a030b010609050901050f0d0314040b161202 74
    0x5115680041c80d0340315908c1624884c1e01000b008800c0301c2c0460403c0c0000707040200008001365034a1801fa00d0a403600d04c8142e52400f0250b00045001c40c0120032100d1b5540142e4450301100c0c00c0900c1650b01d1741d0008040c038481c1c0e0303081c03200c00c090703110b5001e2441070103810107003080d22010100c0405080d11002070201c00c0011202d08009070130348400e6010303600210452003200b62400c3c0800d4820800d100300a41c0b607814440c3e202004140124042d00e0340507685000d0311110300d80e882c0d89584040d40e00c02d10841c40d03160310564416540a616960180d040320b020f16280c0040e1469040c0c101c012000d0f81c1000c9140030700001c1022000070401031904080d8400e00b0700f5820042d180d1910003074080c0c148005403400184031303403042c020768580710100d01640c2d00200150ba40e5848040040403000c0303a0062038041c0c1d11100c00860240b03031907440c100e064540103041e03503856800d5560480f6000d00c10100306180920500010800c880e00c00042c0c2545402894040241d0703545003865803806405051940954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 154855008 1250 154853758 154853771
    0x6080d020d050f090307030803041a0405061303090b0309010c0206060d02130e1e06010305010c0503042015160c060e0303043605060f010327050102090a060804060609 73
    0x1900072448509141c4541802e503100d840c084141c4125105a0000c15030500400201008200070707170001e140514011020700d00752541d04105102c410340180c4000e043c0c0d80c001c134000707a00c042010742c40d0301d0700521a03c1c03c2103c9659030007403081240c00654450005035184e0302e0300c81500741d042100c281e026100701d51241170a45590041008540401000c400803900d0301d11100903641c0800c480302c0f4101c5999802c0c4048581c200d54141c07250bc0a0104031219420064100e034000e200d10152805650003c4251580040283e030744071f40c000074682640d4001c10b10a0741c90f8041e5244c80040d0100700b100c842c5444488486203450300342c42225402007410f118826110600545001040d60147e41402d0f80c00310048507000202c1c403e420039035440e40c0b95408c445207a030030450703400c1d08610700449007520b1181301520310000660a58010190308248200034a6400f00c3c07960702410143ca02500a000042c9800303968400b0440c440220742000020949184c1803204210649c81640010001c100041000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 154856115 1107 154855008 154855033
    0x40e040b0414070b1209070806010909050105010e01060c0b0c0403170a030c02060c090d11030607030506010f090305030403020603060619020c2106131b0e0a0608 71
    0x300041c0e4505812400c0c0c0b001903210f09a03203100e074001e400c0071500303444c0d58441d5100a09154982c85120800640c030501400702c1800b070300d11042d020504020605009007510310690100003803240810040180d150b000c1d22009070f26a019140300a180ca88112012a40c0141c0d00007400d00350340101c0030002415500c000b040aa4081e4500788100481e00340300340e07101c1d1021503800498017000c114280303451400041c4c400c17000e0b01c144062084480c0e1340c00824900901103e045000c603644000780000d6680240c0f15000e1003400b80342014645003560303503942d00c901803484000c0c0960f801001143c01595030100b5148034401400c00003120380d01c0b000d0300940c0e62800039840e6020ba80c9580c10500d01b21550041c003088e080e88103008000303540b954400c0c000c092409900030303100c1000b00155011501d500983c00c6000707000140c054000d504001080030102ca8056020020070f91080404048 = true := by decide +kernel

theorem cover : BRFrame.Cov 154676258 154856115 := by
  have h0 := BRFrame.cov_init 154676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 154676258 ≤ n) (h2 : n < 154856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
