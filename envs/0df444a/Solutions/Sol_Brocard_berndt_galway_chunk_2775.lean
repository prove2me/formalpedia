-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2775
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:27.016281+00:00
-- url     : https://prove2.me/submissions/5d4bec38-aa7d-426d-bde0-4547c2b8a1e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498920863 ≤ n < 499100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498922113 1250 498920863 498920869
    0x150b01030f0606050f0f1c0222060e091504090b060f09010501140a020c060a03021207050313020609121c020c0402130905041a0702031e040501050301063905060a0e0309 74
    0x40c02074441d42d440340c0380c1411003901c2c807c000c0501c545003003403855600241d44046c0c0160001481800780841c10103480040c240030028041c03111003c503561180d100c10700018a035449c140e04006401c0c101038130070301003c0700c00e24100d8040c000903100d0700d100c1c64040790200414105454050b040302c805079146210610380840410303aa40c4945c0c11801103015a58420328544c44000007801100c04c1c550b07005030380c1c58108c0902c00004002400407030801c03004105004130244440c031840d000b103404803a220380d146120800159a80c42d8460054118090002c800348090b0010595202003240b40e020b803040407441c2c404110403485004084410a038869400f409803203085e40c00319600900c00c00f0101d18070901c40a42d402075807030807118200103900000302041c0d0300c005031703032040b00c01840c10100750704250415001070a580014041c9204003d0410300b880c0f040051a8081c0c1754078440301600845022950f07604090411780c044055400b48110700201c0c2501d400340c454503088100d807001540c1012900420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498923363 1250 498922113 498922117
    0x111090111010902030307200d05031b07090504060212070503040b070309050c030703060b0a0906050a0506030c041a1b1603030f170f01061709120d0603150b01030f0606050f 76
    0x2400c001d540d6501c9460005032001c0009010707590080ca41e0b00034000300740c400c408404022000d03081c003410040800c2c10000d0300000070f99491420629110000c0c824500e00207103030841d941d02c0021030303509040038802440025801403101024542c801c0710181e8422000352000d01c0192001000043c54000103140c0910a0b406501442d2090041daa40410181c0020b450708585030000e44d482943e5850708e610740d11341750140e4002041b58860a00841e8030b801f0000c3c64100c6144150760040e41c0000020300c0c0c961811044402502c0000185c2642200310507500301c2c47e0300034056407880b1243d00b1846240311203000413580c00000a40d800452424103580d800c0b1940c1074050f0a410600c0944130010382034000c004401480b4030482d00425005e90300d4000300501d100450740d68440907003a503006118200b10045405000c08004001c800d0f500c1c5c225210180c010a8076610160203d2000c60035040d03802d40a8107c3c02103508242d0b02803005420201b00802102d045100d2a000700b041005002c01e04442500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498924613 1250 498923363 498923387
    0xa2a330921050312150f0904140c0a0305010204050405060f06030612030d02160c06030c020316021c0b0a05010e160e040213080a2616050f0706180801110901 69
    0xa090381d1240d0250362080c2c41c5402900b41540d4421111003044002000b00c0c051403481c24080310105284540740d40800c4840d240540301a105031281d0320306a0711003c08010901c1100c00103403040c8041d40d541c6c100a4000c0d00b03e8054103114504090200e00d0520b08802e2002c09a10000c040501e0b5468036810884070100c98101c40119000a01c0510030301d95452015002d2448840e880074403070483c0707140010851944e600b02009052410210110450b40007080e03d244241c048040b20308408180001a010308500545001104012019100300000c00d44087d0086412801c1400943d80b219a01c00000108658000510100f00f40b81102d40740700d10350542c071012003c0c10052030b200881d200044010b4a81e000044150f05c24001c00d010450540e65109141709000d49070200e8040800c00304045101d0215440d1221481300e0455013401030910081c00d075551640100c0e0175035591a40301a0a0f00728411075402101c0c01c00038001002d29060052000003181000130500d058030010054981c11a030403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498925863 1250 498924613 498924659
    0x150906010510080619080c03010e16030b070c06050106030c0206100302030c01030209040b03070803041503061d0601030e0f160b0301030c3305070b09010c020a2a3309 73
    0x41c000b10000941a40721700140c06800050a611a0440149400d60301455841c8011360b0011891381c180883c2004020140d80d400900e0b8100342d210300d4811074001021201c05031280d4604400020a070307416600144c0031803603c1e0241d8080e43c1c0c0e41344048044062510002e50107810100c0f10340302a44c03003a4010101440e00900006464403d040424900300003600220179a071710000f0306210413499800c2011301080301d46003c2c442ea034100b42141e4031004501c03011080d2003104501068071603020350090030310b01e0400380455003841405c45400b60303960501140b801c150a0100e10110380031181b030084a050b65001901400440c0c41d0805a900107142c040031301444003441101e850420b03840c03400c0f515005003c3d80c0e8140e02c80401d030902c1c14a820005d070052100741e14000401188580204201d541030f034100c103111049241c6510203402c20420301403c4d0961041540010a4030815001044241c1e03681d500c90180300400074280c0d8000148000140c80403801100301041060036000100340c8141043c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498927113 1250 498925863 498925879
    0x5070c0b0f16050c070b073c02090c0706050f04020901151e0201060b03150103110405030a020f04200c060108060705070f0309030c0b030612060714031e01081509060105100806 77
    0x610b00c1c00e07405410205048500d525023001c070308040000304480054400c030701d00d881c00090190180000ca50000603e00078060300702840041c200c0400407040c1c2c1e10b1650404c0051200b4075080066207840ca5080f5001ca210380c0900d00007040c010103007031a40c0d000881e01d4842d048446014095582d80e1482c00b100c007000c6649800e000300d1503400300000b850003030a08810b492840403071403001409680604080490483c411b02080000740d40001e045464560140c40510b0f04045000c049000b81103041444100344405118210011422070000c0c862818181d05840c0b9603601d0740b0303546483d41c409440000000c1c0d401d11580b00810400301003901210320905007551256034a9030340d800052003550007a80711150100070400300c0d0504081281d085003080700907200d03d2030207103000b900c9107407088034080c0c81040c00f0000405c800107643c480c55a80d00c81c0098507940c0e44e034a080042c0d451810881c020140d20019021940ea07045c00210a03043e2a0005d1610485030f0030359104803038602000f4070041c1c1c80164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498928363 1250 498927113 498927119
    0x60a120f020415091b1e09080f0307110f1012150b0307031a150705070b0c0d020f0a2f15090109080a0b040204020703021005070c0b0f16050c07 63
    0x69200e0200388662680c584640103103050607180071030348850b000700043e0b40c5c0d20681e102100c0e88540c2d20906144a1603a1108906008108448a500729001480903204240005444002c00406170034220310a9000700058540303d0180042c048418040c3c581064013078a021000c81e0007110b00a2104802d40360000351901813410704200c07a0256489414601d07000001d10034025858054122402840900400c1e424240c202060740117100300004103182d4004522141004414880c3c500100300420b006900c3e11200c1d04100e84545005d01d0b21805841186a503403200d080c0410f001c0b00742600300c0c0d034401b41d0b2003411880307101c1c502001d911140c448036466000d10041d0f031001048021008142000350b2105030240c00034046038400e0700050700340d0340003ca0080c00640c5a165855220742e042c3c1d005070b01e4456910f000d031714000c9840d401c0007905040c40c00708001e00d41d21180c4914824000d600c010700341c1d1140c0002d83d07601d00082c3c515904030080c0350003102c0c0d035501420003403590700c0d011021101041c3d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498929613 1250 498928363 498928369
    0xd150501030609120c17090f040e0105060f220c1b1406100b0403060e070b0319051005060d0e0f0a050102030f01090501060f1b02060d0207060c08060a120f02 69
    0x1d0700111200c90380c072030312101070201c044401c004080b00c0c0c1c10501001d10180e02d0b01401c004810340888684400020134003040c0e1070301e50440042e0040540b00744000b50b002c401e540d0103410100d80050041240d10381c1c0c50614980300e204412030a8100650051425150941c50080d001c551200018070007800c541550000050200014560080840040800c85141314508241010702039601700007800d0303024819080207008030f6040b00ea100e40c002416082261806041c64203692000d40013034004410403644004081c071680c19a0303c441c20800055661800750521040c090003010381024040c020700b2a01d0409a21035100344200004407070019040c02103d61070414000e20444e034994002c020300c03214804035500c5030b001d002d030600140403940c18180c0090200b030b00b407008402003000c090f0607a024850780341e40100e4055005408181d030307280c04004e1400a9880030104460045c0b805010001041c03107001800e000c1c0400500d120344c41460903e80c2022184040d6042c2c0e0755084080031400107075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498930863 1250 498929613 498929621
    0x309180a02070b010602011b020601151211041203021002030c03130c0302030d030e010b040b0d0f0c091515090e13031b030207210c0e130c030606080c01030207110d15 73
    0x225030b56001007088ca40805101c034406c0c032017038211025540500d00620004000c00041d2180350a246040341d603001c1d034260303140068507002604030422140082c003c1356102c02d104001c4801402602250840c2e1218a5403208922040312014040901030001c2100e02c6c8807a01c009200e6400f42030404404d640b00d4000908180780781c0d01c0c80002c65583c840f80c000c80107080c01480700f412012241001485030440c003080700074010705001482c04c49500100070030010240380c000d000d807944000800036007902c01014500d030400b44c000d0002034144411701495052190320010191200342d8246074503600e60004040d501c45000d1412028840098031004143c11803107216000940641c1c02841040d240502c8200081403c0c4640015840c4682000010440f0b400030301c2e003121800144c0f80d0031035451405440e152203e01b40010080e110041000081c071203160000020394455100f56031581d60107100540c201d125481e070040002c0c040b00d02c0c3d1490351525500294441f030182001c00581c0400c400c0f0f0390116 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498932113 1250 498930863 498930869
    0x30c0301051e04061811070c122307031a090706120e060c0301030b1006020c091012230703030e04020903030702060412050c0103020306030c04091718040c020309180a02070b01 77
    0x1024031181c5d14080c940904070800c0703503440a0340c0c034162241d04d5403c10301d20580543c002c0d403410564564100500541c46402215003150a4016805600302c21600d440f050b2009031079850a140c0c940c00c07080041d0607018042e50b2501c0081030101c1c50250152481b45480e41095800b5994480c60017134020b051004c0e034490010080c031a66a581186010840400007401005038603281500034040d003500001c1011b840d00c82103810902554491505c103008040d5130300100226020001e00e0001c029031040070448003402d0000100d0101035035200c042c0d0b122802c0c130024001503a62501c420150a05900800d15014050240c91400001c0c1e00407500952003075110280820304d140300e883c248617060014140e00e001c24a01580f031410035600080d0381c0c1000b0020310384207030b40d184048010000382042c800500301484c5001c58540240c4802c1001882074803061602460600607c032142603c0881110008003000384998190f011120910140482c01000115a10f90821042c00401c0c2480ba1031402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498933363 1250 498932113 498932129
    0xb09012004030c060306120b062707030c030b0607140114040c0305060603010c1d01030e0d020d020601050a050102150c0c01020f03061305010b0d090f23060903030c0301051e0406 78
    0x341d5451494140302c4099154458010035141440601c50a0042c034104004541c02840e070040e507032540c60004d0f205111910100c0903070301d100180c86020142c00f18586100d145103440810050f0b40600d001d03000c0d00d11684010b035201c03800708030a2000074103440450906c1c1c0100d0000048240c5030784a60004080161001d03907551100c00005c004102c0200403055002c40245c0080c8641003080d5405040b9208903c941e24136984d01d130180d588281d210b58850880c541034541160350b4541e100d04043e4079004001107280050151200109003420940c013000101c80040c2c1c010000c0d481984092441140064042200c2103810800d0844030002400134010060510710400da50341010001c00c8121b001c04030540b1f4416052034010019441d00d08151002803003000004150140203240c00c2000c1c0d28808002801204400d034020140782800d220450340422040071074400342c0341e50340f040c2e980f80012903201d500d5000c200014042070820044883d90b502c08507444c52021700030000041c00381c500f0f6411100c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498934613 1250 498933363 498933367
    0xc0d0c03170919050c0d08041a09100507020409240e071d091222080616081b030109090c060c081e0d1b020d11060a0911060c06041704060c0b090120 65
    0x314282c0200c0c527484d500039507035582030b103042030140c045042428490007500034400041400801e54030359412075003040340d0000e0600283c0200b4001612541c5e1a00c0141950710701c2d010016400c420001045404d0741c000c00e070445603003010241c45000002000f02031303071142c5c00354020104641d06010042c001c00c1c450020303010040344a018040310101000c2c1e004c0e820903405107041c00f15074401000c0070f41c410002403a054082d562043c0d2040704220485803c1d08210074008000101d0380007640c88000320a00c01c1e840c02d95600e40e581d00440e00035181100140000c83c080099803079100c04050300c1403d8030b0040d6800c9050005280380b05044440704465191000c9140b0810102550705200c002d0302c85000f070400800030106034074000c0e62050000d22a00100741d55110040034001620414051070100a00495031000b910400c10f032503050a490442d010040c03d4041c1e000f0740e10020548003a20380940c3d40d0540e40f440341c2c5601d0215070004d03142c840e0300d540c2c070401152040c0c0c80740c200c1d000c984c0134080025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498935863 1250 498934613 498934619
    0x1431021314012705040209070c0302010b1c0b090c130209011e0509042d020f07020307080d0216050d03051806221e1203050c0d0c03170919050c0d0804 66
    0x1c600d83e0a603201c401411490b0004220040e03031100b00c10f1f130300401d4501d0030901841407031030103900410420395803660055150040030700c0682c03500c02035200d651081c01561140c2d1150135900c0c8d65170886a551a900104500640b8042d40304c41c4d0123861002c2051410b404041001011440032240c610000741c001580000c22a0072400e0a001e078100d08c4c040c04000305140d9914560299000786140390040005400088134883e400b805026110303115001000e41d0b800503a60703455150380d2440c0955800140c05000780c40c80c81c1504d402e02c0c41003201c00c042c1c140f14000035150b9045a0a90050081ca040d980c83c404082c4001d44501000e0124041c02400c0e00180082803505020f50105680c480d6080280c83d1041011520464544800303c4079011249900c17680f4900e000d591501441c03903c41c01501c54032040350202a030000c01008510f0082d2140014420030000202c59030308102d0ba00b2000d980003502040540300d01e44c0096100a004a050b10300e41046500095019040343d001580c098101003014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498937113 1250 498935863 498935909
    0x5040f02092406070f14060106080702010509071406070f0605151f14041a0a11010c271703040303020c0d0b0105010c15143102131401 59
    0x240d001580900100e02d07400341c0c07500c040c00168540030468025031010030b0740020000c1444400e0015540807843d1b17111070406044c2c2c0340d135440b004d225060000c1c07411008030751250f0041c401c2c50300404094000d040002d0404142000720b03040c4180340b0780c200c03c0c2008078001068900004110807807152078089401d007880003000c00b00b0303170f020710a55204400c00324417502d21a0034509a410381000c00e0500d2041c240e10741d0000f0f10b95003e6070b8400021600601da018a062400780020890303000241c40300d4051000d40701072507080360b0049401002007001002c840381c02120740c42d0f080c00003080c03081ca01142c064603000300b4146012144000c0445500101d020310400d9014440d0880943c0700359103c61011030b054030340b2a10038106100f0725051024200030031043c491104440154411041014000700718250003044c0004000c0350111250609071703074034604032116008510380315034621645004554203a003c0107001080c80c501c0c1070302c082e42ca00da940e1080319030f440517a00806104041100007030ba01e450b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498938363 1250 498937113 498937129
    0x102030a0603060c020c0105030609090309060a03050601030c09031a060a0824060103020316050307020a020904050609301b07030c0e0907030f0b0601030b090c0405150a09051e0405040f02 82
    0x4040b06640101d186c43d04641d0748071040d00d80c0404200c03501c034500e840d0481e595085118041c401500610f0020f030000c4c549806030840c2e03000301002e80c3c00704113604054504640720b5a080c04010306017541d88182141d00340364a45116005080200b0b120180d659482100d4640110171442c03d192600c0707014018241c03846031001c6a030140c1c0a0a0951551424030b08510b0140c03034004041d0240407002c404200101d200304420000240d0107802043c5904041c2003180d13503040c08541e40d948501c50703c00c803d90360b003041c160000036050b001480300442805036260403281d40c010704501e81e90b005004080000c03203c02004900001e40c02800c3ca030300c0c1107040840e10034507560020300b00c3c001640401403c00025980039034101039207400031545030740c45c0c5a250040f00900a9548980da2149601c8244004e00f40c0346401001140e504a80d5588094402d6039043c81900900c407040000c1074440400b0059820903504040b0030026040040c0d1860700d1000003d021104262002c0d2129030710103180038214244901 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498939613 1250 498938363 498938381
    0x2106050115021504050307020406031a130b01121103060708070807021f0b04090606090f1d0c01080403110102030907090c020f0a140c18160c1203021b0102030a060306 73
    0x300303206801c4000103561031900024218a16407500002070510405006459a141d8010000c0c02110398034100f4004620005405240c4601e0600c08551254914601e40120300e912601a183c0780c0c0ca400f0b20320345031440310401580c0c0b418800517480c8460342d00380b01c0c0c1132003100e04d42c54400c41420241c2d1300900080d0700070b00c3d05055503c2703420703249400bd000b41001d400c2041c4540e0701003250080310340405d01600034104000c00781801c00c0b20103c1c0c652100d8000c0d210f1080c0303c00c01000032002c60b4440c00202146007410315096003006850003065441252150352160003030425201d502c0708140341034220b80c0100c9020007107070448a014000c242c07960007086030500c00b5100815000e180e081400703484000c3e540000713140b40071242000000e54800d10136010168401040344544502500c0b0440458804440c1c8141c45135407038a1400341103004e40d010300c1100d6000782e03142e1204070401030300f500254030543d507909188440c01c103d981044424001103109103400200440c21034907510f0400180d0707010351 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498940863 1250 498939613 498939629
    0x80108030a02070902090d080a0e01080a0618181e0b0601030c050a0c0201111902120102030c0f09130c0c02011e02100b0a0806070903051506012721060501 68
    0x1e034840c031641c005507000030b075218a040165130751051400200e010a006c1e0009241141c04144005403d411071041711640301c0a8a4407441176a5000e04041108c0d51401400c24124a0000d0030002015592145c1202c170703903e041030341d9120220b031a00903d29621074444007448042802c010b04203c0c0603403065030800000e007014400c2c2d29402e0000b608c1401001c50240800862481d0201568414406c0544042c605020f9608500c0c002d40c580d03070700b845030010a900401d640050340303030f1004052084074480c101d031982041c2040b00a000c1400c40d9031040010350b60000c4400c0c100d223114240b600c0788500d080c460b511000340c00311051001500302003ea8110030702d941790b0a41030709035258000c181112640515030001860f5107100000407501d00d02130704041d41c144200c1080000d140d07045003c0310141d030700980403141045d110120848042100b21801030000c0d0078000010042c400d280803407150914401c020701015a01c03001001c0d03051010003440c08088184400395400e10069104881c0544120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498942113 1250 498940863 498940867
    0xb06032503020a08160e04050106020115080c030a030f050702031c03050a060311190305011b110c06040b0c03090904061a150f072109061d0f06130b03090a0308010803 73
    0x202d4000b50140100500142c90000179421a4080d180319009860300460014410803e03540c4642000703008020045401c201001446c50100720a40009811011004024002d043d0410070b80e03003c4803e085841000d10601200744400c5005030b030140584004d180712200c9400030f506005100509031103001e049681a54601039040c0040380c08a01c1440e0342501c01d613501c4030400e04100300720040c0e444540c80039209503c0c02c09161101d010442a00d0015a01079503944052208950303040e4552000401c00b9904c084100700c1000321588410140085801040990307041101200c04624015800c88048504641c1c944440440d80039039110640c80c1305054075001008207030800803c51506c203690346200009004162101003081242c0b60024000e0080d070400691b0011f09005840306415000302c2011904410441501082c28400c201040800500c0495201c0e640704c01e220690303101411000c0402c155007008aa12042c06c0c005500036424600141840c55660070000c1410304d040c0c11540071070f041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498943363 1250 498942113 498942127
    0x309010f1704080a05070f050106140a1809110915041b08061e0a0303121409061902040b07150b0105040518150913110a05031f0b0603250302 62
    0x106600c041d034003681c0603e1240c1d031001c00c14001d0b506401007130002017110204500b010100700e01900000d00700ca007094001c0c8050309401c0d0402810071400e01a0260a03c40301044407240303000b039040014118050321b030905105400c03d001c0b40310710ba0101c40106480c1501e204043c11420b15108a10801c880103200b500c1007041c4007001800f000c0090300e554130400c1c00300d80070301700f568140d8103800d043c41c001030070388503510781d40d280c09030120b000d510903c4503841c600900a201125042a030910031909003020304100d03a900c0441c22001c94100000c0c816496003440b0100718044070f5001004668013070000c6030f0844507140220000d440341c6614441c10005d00340b00070403154840c001c2e012801f000000c0a98059524107000c1101c1140090703007236a000c40803405210b4249803005895804034080c4030b4040c0006500c0c804e1004c1100700740b060907095842014109002d00112940e050310540c4c165021580310120000200700340c03c1520000034030001a200844040c0040d00510b00b280a181829810140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498944613 1250 498943363 498943397
    0xc02130c181409100e10031a040f030f120623030a080301030807151d100c08280507030e1b01080402040e010b1305150312030a0c02031b0309010f 64
    0x92410802c41c003031404503011403464040d90030003002402c01680300408520304082c102100c80c409201c2565420003000e1030190309180342d0401445035803c800a02c00342c10040e94111910320401d42d142e020091078202801c42c80d42d190040e0b1000f0030000307102201028050039406900d10b0000c605034440e1344081c6000700016441810b40b4110381c0c110800d01d46038203c80c207042c007520003005800900c941c54152040c1400305000540c10083d0a030100710340720f0700b80a0b890681110300d45c074000400b0411406c0014a0070141d01d5005200744103101484810100b000d00d540c1c142c890039100600800d880e0301511110300410080c1e0018034280503d03c805100401d000a414070343c010304040d00458079801c913016102c0c400d4000110411014120000e200c040744003a400814003900e105440c482c0d40d082611952500180000744a0640f0302c80914544510f00040c009041c030702026070940c00180880c0b01240040f00c03200030f500306210040e643d0750a20400040c48551910b0018080c45070441d6400e003420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498945863 1250 498944613 498944639
    0x3230f0c12030403060513060f050402030a120302040e0c041a0414190b0a0c0c080f03090f0a08031c0606110a0b07020102220e010b0702130c0c02130c18 67
    0x44425580041c01c00c0d0000c0c1000d05500c100e40001d00302a05100600c11045482d000034500d681c06800c0800c4204050720154090703c01c1954040e6043d480451444040b8400b03404040c1400c05130704006141c1a03030740d40a41e4003140101c034920403542d00030038100082503803451280078000003942e00c207141609004d44098a00780020115004094a640d40c44100c001c04071242c02030b21401c20099150051802c004081c8200c600b01211541540900051206000110203813000c4128010710b0400040c8070a000000110b604000d0b40118240c030001603842e020b000402e07820a1148560107900d80740c1200e2001d0380c0565201c03104001c01c0440140c21900d021036100c81550348070814100b03039200c101049000e40542a1410640c403408003010487d84a81110602200c0c005071524103075a80c1c4a0306840310380a00c80f406500883c0142d030a103044090350b40040807511301402c1c034403010076407600840d2000d40c03000d180015190303072180444580703500704c0c450855100c1ca100a1000b05802d14844014070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498947113 1250 498945863 498945883
    0xc060b2704050c010f1706150309011514010207050103230f311b0e01090b01080108070f050d06060b03130b060906012a140703020a0909170c100603230f 67
    0x2580040004c80c40659070103d00e02d401041010b0009d0b16814503112a60080c98034002414440340301c00c00010f00030182203c2521450705c16005405210b1802c00194040c0070800c0710a0700c24a002070000d031241041d030b40207501402404601c81d03040e00d01115404081031002c001d0745400b800d180c01ca0540400c0030380c0940d10f55030b84000c27412586c0281e0301840403c0c07030030b5030000d1080c00c58040001c503580c01c0603804204000802d0361400e110380d0361081f44a48a0a090140c411000d410000c18802800c10070741c030414003840b4034400500310742e41d0640d42d941c0c0d8000380c800f0f20b12400e07982c0d1003500b4002041c6580c2c1d04410200e6080c1411306080d80084c20710700c0b86040b11515000c2640700c441450729100414200a038008008501c0680001038144e2501e018bc0800ca03c0750801e2080821201c00c10300c1228500d5a00c481000c507040c28007420301c60140c02184444800c0e115480c00e0030950406401018000c0d13104191194401010100641025140400340340030707607004207030340040e0f42d00020f0300c2980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498948363 1250 498947113 498947147
    0xb030a0b01111513030203091e010201150b0406050913140115021c0f0c0209040506181b1507060906051504021201090e1509030307030b040204060c060b2704050c010f 73
    0x10361401172174260700f9401510710300c0da403000c0c084038240000b038240321500880c1c2009034001c100021801c40001400da407a4000c0c00780d40d580a03c014405140035030005e0040e030038014003440e650701c20003440400b030340d03302d04440106101180040186e00c0840e400c0039400c0810703001424001462030300a0300100c01c025620ba0400032140c0030300c0d0090f0b0050382c0c2c4c450810b801410458184c1b0b010705140f07980303600a60345c101502c000c030341001160b1040818005800e01d81c1c1c18a0034044101d40702001003101e01d80400329030310b007010022140059158071a03014807912507280844c07103140001260700d800300c9540003980524010401f9001d4046d000b45000c2c15510b0007000081c14106074202c0074504412100c05600b030043e030409000398210000041c501c02c1c5031340c0d5000d10210201c982804103074001e51240b100410328040180c80056050741000e03e00801c0a00410041801004512019081108031100c00d041c200240014040e052200082130542803c00c0017440c1220701004103402440140104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498949613 1250 498948363 498948391
    0xf0e03030f1b04060c0507080d211401180c0203040b0f0c0709050c03101a070b31060605090c04151107031101020d030c0207090209030102040b030a0b011115 69
    0x107502da003502c12107501038004285292900d4a0360707409401580c5008003036410f8030400da00001c070303980001900035a2004035030325060f4441c165080c4c40c2540904a0042c101151190031520a2401e490035540c02401442141110554250003280448981010407030840d00304020512510030307002c1c21100880040010199221340f1441c1c050b0400000343c0089441034140002d2140c62401d000265004424100c0e0300c240c207543d0f5901005c658120010a0f020004052007803030041403481556542c0018481400480d200007406880b461080c40d15040a01800c04000f0308280540c070320a11000d400155184105e074200301d0340c100450301440c400e0302c1d5241c400f00318043c40a40324071461091348501c113044800b03a580b20301c4e11a00240302c03050320321f0051044003020200340b4481d01800c2c1c098061f5070040c160729410310103082c010350305c682d1420390159000c00000812503e000021481100f200c0e000180d484a154001000e038038282400c80b017035600411200304641d05260309070b9004012007d2002e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498950863 1250 498949613 498949621
    0x510050306180a0c0f0e07090e0708090f0a060507120b03030d0903090f08030909070f17070203160c09061203080f0a380a1a030c07080a0c05010f0e03030f 68
    0x20700c0c0220b5804001d10307600201c44e0005000c0184c418001c05d40d2046050442d8551720300c0c50450b161652807098802e8600104040750901e0702a8941581026428065a0103031000304c201e603150004110b0200c482c50b9403081007101181d8415040b0064080c481402d0007100d0071540000e0740d038001c10410001a9590305900000c06000e024007000524950650380642035940e21007030389039042800f5041c002c0c5c02039400101c01500c43c012611180c94191034600c051004005101340c45070000348a2002e52004221812030f02d0109010821040c2c8108041c200c10350600c222181581d00e0341e030080e00313603c0d400c50121001030781140c0700382e9005040341042644c3e6610a1034040c06088801096184400170b4803000e0501d4890400b010120054003640c1008088050113101d202000341c071a0f805075081040071082c070f900445c402190096000381712641051f0040c0c9801086034480408070022914805401c81044000e000d03c00014101c0401000410401400c0545902c00100407000b5084860005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498952113 1250 498950863 498950911
    0x71802130e04050705030111122a0711040c020f0d0e150c030901030506012102030405010e06090619020a05030105090601120213240219050a020301110702040510050306 74
    0x32001045607200312041801c01e401c10725100c07502c50141d1406542041000081010800c0499000442e22860300403c4e954182e1205039805a81848001d00014081003c3c0051303441c6000e0141c00c2d02440201d00700000c410f080004907544c551000c8295000400d00e80c0c200c010205410094400e10b0070005204104032000400c016482d0410f03048220b4081420528402d0010182911001c00c2c1c0b420800e40d00d0f0f00e001520390f10f0001d02c004d143e1600288a069070021180c014541141c4914004210f0b055019041410204110303000b40b02580450f00701b000440d000e41b0b4182000110714411850003017075036001032051105016440c0a40d880501013182a40300c1c034216540c15040391400c54890f21029040c07200d0700c0c0d061060001e82c000038014001c1c910406100d03a002c00000c2c4d0010074040c026100c074440b08803030042098909014003102c0d080580c600303000302c0c001c5240c0404207075604d4045104010403181c2c05801c2c1741c0c2030360360a941440151400102290844010f044d0000c2a0701c4c00301c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498953363 1250 498952113 498952147
    0x1030209161407080c010e0c0303042c1f090e060609041a0c0915180d150c1707111b060408030d0609180f08030402060702120a020909071802 62
    0x8102d801d030000050280038070000001030800c0b4140c0714000d102c00d40c040800e441d40c64040c000041d6150304100402c01402c00b50038507503680d01d1b0403c0340d0703121414500d010080010500b10745007150300c140c080780c0151813402074009101070450500e08001146100000554030b8800900d0140589590700104040c4010541c400010044c14005500710345007170101c03c00c3d550400c6000c2401042c895a80e0442c0110220a881c000480c04540695080d4030604000303140301d2410042c1c03034000003201d0b01c40e03003d000c42c0920801003483c1d407144082c4004100751030071603400081040c010803004140404100074003050a2100803034160356002141c00b40800100380b88515400410340780710000d142d0900d61507a0308000300b01c440006c001c001285449a03565500100392000900c0d260801803020001010103024680103400580194180240d40d4082200c54036580c0140206521030401c060441c640940042e901100310001b806190340b0344180d401401526205001d903460300801e8401506ca100c0d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498954613 1250 498953363 498953387
    0x70804030f1110032c031225020d091a0306010e010210090b180f0303010605070302120d05060a1a09130b042a0302090f0d0303060801020406110c090103020916 70
    0x10440c840e0401c80c03c40a0000d1243d040350603040c40300380f088000100031a00c1c0b191070300d0030040055460803100c035a5130100a44010400750700e1851611001e1000341e2900300100c48040310782c000b040324003880344019100c00c0b150390003001c00751814031100c00d03003800041c00d50750802c41c01c6c01c0c071200c2050b41100503410302d07a020034040c80301c9281051200c184440003040600591021114088029015070359a4803040c000903004c002d076000308010880c040c4240001c21840b40a072040c0c0d008200040d09001c0710358007210700c040c003064075a41440014500711059200405010000280c0300a02c2c0b5912242d6024884c102c511500c8c8890b032a0f2107104540c1c10081400070018070800803c882038011907025001c98918041d1200038694041625010344211a00b03404003c10301e62848012504009003100f00500c100c0400d5182c0d180007c282c9001d0010304040c20b20394680d00010300a520300c6903c0d00500801803031142061100410260311020003054220044100e0110403030300d460020396121030250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498955863 1250 498954613 498954619
    0x91212040c0308131a13030b070908100c08092a0409020a030f05120313240f050916030c0b16050706030207060f140a1d1002041703070804030f11 64
    0x140001c9040101c070110015138201005e03040540d0824031580d0301c3ca002e840d08003072105884010134404200c0c0f0307034071490788903e180c540055055120b1895506001f2000380118556840380780007191150043c41460344a5032104c02014a1116054803000f42c0001c540042c139040d030000c4070a000390300e03250006040c40b500079143d601c80903581e01d05a09030034847d80c4240d8150003581610f0203085140421280500318455268030304104940380d41520030700a2116200c04465507807912901086070003004400301c03044000040d18030340036800030b043c00701c80b114400e00005000300a0000408065104090b5038841600780c0d15134010140d41c0359441c03c4803802400d903203e880d80c0040c9a0f5031540040aa0a109110a00c0310641001c41c0d00180d8035240034003500d295640700001c46000440e03110084540480032845286107075942e81a013046611401e02500c19000142801964140e00391031241751ba000c2c00642c541181034681c01d190303005034080100100055002e040a001da8080b2050b500c2c4401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498957113 1250 498955863 498955867
    0x10b030a050307120c080d0c0c120e030d050f030c070809060c060709090c0c030c0201051e1908160f12020406080f0c0c031b070e07080f091212040c0308 67
    0xd41055503803500050700850b601542c0c140c3c0034101d10b1264865101e4203a0020180c0c0c00d0181199041028041d92032461042140c0321441201094140761650701003c62910b981000800c50310501d030429844510440c00e12404020746d00c000c005140440e98003040100b20561101c103145052a814030450540503440134022072070201e22040490344030700031010741d1601402c0d95901c0c80541e09550851240d01d0200d5034040c01c1002090003840c02c0c0d80c0341d901c145056480c1c950f4003900711806800212142030300c1e0f080400d20171043c0124000320302d010003c505082c1102c6c03401600b818240c5403540304520400206000e000681800391007040080c560b03d0409544a81e00c0d620020f180d50400c5441d44c210803400404143c88445440c1140c040107003c3c0041d5107010400c01e142e100d0301500c0319510105205002e4005603001c100781714103015447c2030b60303034405504004da0128000000500403140d5500288400c10340c40c41c038242100c0c8480b409100b07241e410394550801007400010381d48090302036040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498958363 1250 498957113 498957133
    0xf06040b0c1006050103060e16090f1202010e1e01110a120c021c020f01030e03070605090c1008061f030b030d0201021e0405130e03071a1008210903010b03 68
    0x1055604119103110b504028007075031940118280c41c054411460882440c0d40807800c20f445404a04c030070814a82450a4050740e1200842d684003450f9104030b00000c6008806001c543c0d01c01007401e0552000c85100000e4000c0c050b0f2840200d01c0f44102c0c6050140302600c24040c810240402c0206076003004e0200340291040401030248040c0d104101d2150749623018011080c01c88168015180790003500c00b1141a0f4075400541c003d08040629034160311007840a503002071340d28099a40b2401242001d4884230b810001400400d000d1104e84c4004c0c002c0c200200009500c0f440780142a0a144442000645450010a13001007104c40720840d054040c070101c2d40c658030b40540003001c0001a00b130350743c041003c64060b0040b41d801980070705a440709807110a8681944503401002070703001c442c0e069a1400413265110842c90451242850100e0f15075000c10072700310342c0f43c050f110007441402d000e00003040880c02e8880c2d40900c40010b10040c1100482c890100d61400d6212210b0450042c04903612550f17 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498959613 1250 498958363 498958387
    0x70b0a050405240114060c06153606060307140708040e07020705010906112a060d0b0315090c0103090521030a0612020a060305070c08210108030f07020f06040b 70
    0x1402d004814807580d6001003c0403a0801c002101d0f04001120080e050b41c0e00d601040007100100c20700c040743c1c41126440ad207030705525011010404107100402800074805068030103401400014510f0f48121810b0080120060700003200c007070a039101d03e803125945d90180c0742c8522207020319000000e003503000c4000c21016503000902c00c1c00b501c1d0f090301c9201085a072060111644c03140c2502071640e940100034001102e89d00405000c4507034801180d4401030380a01408543c0d160000a4640c1d945034a811a4034a1400c00b4010481960500390100704a0f141c45001c9a0783e4ac28010026410503a5551040b028000d00b80203400d040c040c810316013524068001d40606103500f051300e50020703076440e01a0004441030100c030384943c0c4a5014050400f0545051420740c010b0034000d22910500481628820010324070000500400310b902220b00d1007224000c8d00b4025910b016000500c40354010800798005484520a4442465044400011921881020440c3c5020301d81c4180050311021481e03001001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498960863 1250 498959613 498959683
    0x408040e07081f06020c0603040501110c030a0e0a0e04081c02041203030e070302031e0c06030103080c061b0f072a0302150703080403141b0f010c0302070b0a050405 72
    0x10503080070404000101030580462030f2072442040c000d644045007030007684c01d0543c0559441030241c0000500c0c040c140c016040140e0188440310002c0d08002900080d0a410154054501405540c04c1e07141600b4041d5000401d83e0181010780341e04004102c0c4940300f00c4103241540d401c1d0b01c00d04107540f215a06d6150718054882088202c0200b41003e0349440248000145030007107a400800402c0e039000b86429440b04031044821440c0700f4064840418140c1c0c403401c3c0154001c5101d18107140c0d850074418405801c0c00006480c0b110b035140032203116008940c4c0d034000e0350320a058100540c0d40c0c654003441c2c03860403070102034140121498072804010030300c4070050005041700d00a8803841801c00d021842c000c080d109038403000b0701007000e410104000c40c2c410a012400403170502110f5240c91400c1304800d180d1200c00d01c100465a100d4030a03044408402e00828485800a06095041c48030541c6c1e0301070003400003040c2201d00d90f81c0c2c1d4001001d0040400001c1c0050aaa00382445061102c1c81018805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498962113 1250 498960863 498960871
    0x160e03211806120402010c05100c0203211005060f0c070e0406050c12070503060d150e0d0e0102070b09041503060203061e0d060b150f03010503010501050406080304030b0408040e0708 80
    0x1074144a8400019030038028100d808420100b01c00007184d41d1035500558140703541074403c0d1180d12805460015030100c4d442131080501c000e800441d1501070501e055986034000329444907442e20b041b400e00910210016055054035402ca464a8640710300c11040103242c040c603034400c0d0091180301000244203441e0800c00740501c2c040c880501080d6141d40c640031541c81405034a584004480000521041c8220040d40d0000801021100c00c040c8a880d4002800c06c0d0120300d2407101e039211a000e1950004106800704120582001140d02c501d48001030749840d1031b0b1040d07640994000805d840c09035180d138489010a280c3c85940140c2540b00c4c11710380e009400c1194180d0003a0440c10807564005003410004060080080900700101c4840d071f0344001400309203c0807038002c00144d0120840205820117440d06000000c1c03019165071402d0205400d545045c2d00c400d01403031030020705100204000c82201d060f01e800c00071044142d01e5524202c03c0d2440749030300120b0358041040a001445911880300d90003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498963363 1250 498962113 498962137
    0x1b0c010609051504060308071b051818070f0303111606020a050f0102032401030b03061905180604141f09020301150f050409080d150e0708160e0321 65
    0x121003801c1c10300003100d4160001505d0760070148014070001c0d00840501c54424640c071f40142750035075900c01060300069028201d40171a91030004200b0040c09501c4030b102e03030500b91030060186500c0d01c0300c2203820b4032003800041e0412500d01000d4403007030020002d1901c071012401d000e041195031950001d4445070000c104032090302949005800500c8140283e80c0664044590900300100c0c16a0414401812030b0b0101e051680b00e82200c841036405000d428030902c1008911030040f024101e416040b645d006001e03d0481c2d03170307680112518080c0018031562040e48100d0302c507009101e442d14036283c40182c0018040320104598225607598443d040038200500c2079000348198218030f200000550428082c0c50703c101000101000545010781000b10a14042d070103807032800804030155800d03500c02c4401c100006103035034000c200c220501c034089a0700c0112850440c129090400c542143d0603c4190b90000304200d04c1003144142d6024082140c400c50341044180c03105000b480f0101c2ca58001c0644221 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498964613 1250 498963363 498963391
    0x2070e010905060114160b04030504090c03091a070c0b07021e010902030a0809010e090a090c0e041a0c0d02180306010902071703180a050304031101171b0c01060905 72
    0x5034aa0903000b82030160794140c45103100611000c142c3e01d001d402880b000c031007480b07007040044041500f841d02030380564025614241c0d2a420a62550300b034501ca03041103000c0600c5d000390380c0301042c141c1d02c0c000908540d0010600d800d4580c40811a0280380d83c2e40c014001e14600018009042c0d00008d0380c07441c1c035214a090412030040036511508072488514040c2d0150401c085450000301680700412012130141400e0740740360740d0b000100304511812034200391380542d101080c000380009129210001c000c5c1700c801201516065480118641700714140064090007400418141020715068070300325a500c200c1151289450041c002911041144403400390103403400210314a24903000b10b610761038109041500301c5503089100c00040c0d100501100c22628980e0708084041003c0c42007414042c06403000350707211815424002c24490140b2030b25414007018907844001061410300107548a00d450b682d0040c138030501e112150661040181c1035002d5440c0c01d41c081408441c69000c0e070b019580404c6185 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498965863 1250 498964613 498964619
    0xe0306010501110a0201210905010b090901020301030206070602070302190f030f0206090307140703061503061118061e2704090822030503030106090501170c04090c050702030a0302070e01 82
    0x92101010300f5980703040d641000302c03500c1c00b550007031400c194500ea907461040c0b0505141500740303089411441040b00c940c0d44902c40b500591910b100e189401103039400086141d9451580090318a04c20100c1c024022500420603000f40360003400325540101880788000d0410b401460500c4105050b043e0880c0482c41081c02800c0c0c0e2031001035100c0c40340d0b0100b80294078000503030311129010301c1c00200303000040c8591036021002030901e0056528991207504400c0403517003149001001d64105a1103601c1140081c85809080700b000c000e0781c0b1491000b81c0b00d29640d00720000c000d000720002024a000d5110000503142c180e0715078098a08500f90901946181c0c2714a904100015103140c518041c1c1100018001c01211001c4210040b80340e80c0070a04012040e55265602410b6400c241d000380003041c1d4103c2c08104030350b00100c040720070090f200f11340c00b030501d040c41602081e4041c3e40035203243d0030381d01d0301400c4101340214100c0d14010740050440b40d040f011440c00941d2103903103000b040c5080d000c1c0300c000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498967113 1250 498965863 498965867
    0x9060b0a1d4f0207020d020a06020114010b03070e0d030c0605101502060405030301260f010c0306052e0e1201050106030c1b12121503060b120714060408030a0e0306010501 75
    0x8a0964000940040c15180e07400c2c0607101941150300c00341d900602c41101e580041c0e983c1d00351a0010085600007040700d890424180300601c905078001c0c580072008208009020340d100c800c00f0000b040440c0d40d50a10002410700319112851a40b000745207900d8401406400790320411300741d0403039201d94207003002065684012030300e80074241c400131b100c0c0c0c0c418030060001c81080d500d01c0e054034000d4400108403e50300b002c4ac51800704400c281d204244d55410420851036818051200034000c25142d1038000700400f26103a203031000c4e52040d401c6003280d1842843d8514420002c10040e410010700f400034100d40c801000380280750031300c40c100c0840e1400981c1c854090003a0360741907800118a44070a01c51200740c40d0b049450b1102500a001c02c42c081c111307400715000c1c5218450a514034030b01c05044050551400108442007002014416106042074840000e40051600251484282c121501c0701c841d90111b1064051600980c1e55404041060b100c015480480e19070b01a07412012201c150741c0c1d032001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498968363 1250 498967113 498967219
    0x15062303070602160b09011b0b09120c06041502090a0f050306010e130b070e10080402030d0201110f071a011211040605090708180f0d020709060b0a1d 66
    0x24020303813143d00b64003044442e54000c068402d14106050001c0092502d40d0540a60b110354001221a00400001d103d20302404016010005182448031032405422021496a40000510080c0841c0e103c8034400d100d000720360107483c81104003910088104e6120ba0f5075112001d058000c09001c0d2103002c000003880400c901007280038510700c1d031000440c2800c54650f5140008002c000e1000d210741c29520242980794540c101010a0035690b8001e1241058810103040030164059182160b040c001380044410402040310340482d1001800c41e9224210b1170101010041c500c40940d0400c010400098001c40f008000b505191182d428494550400030402c022280c140c0100713a0880840d40c0050f80080c080c4422503040064103441c01812904016507a00c2d014070541c4056040c0c014030280d40c02e168040101201411003234070240020760821000030414090f040c188400c1009005c801d0050300e10480645100d502c0280c11842180c0004d107000340c10940c0c0030501008a1100e16200c0c80301120b00c19 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498969613 1250 498968363 498968383
    0x1506050109051009051528020c0f010c120818190b280c0e0108040b0f19060b0712020f0c09100906031a10030308010315062303070602 59
    0x660007141d0381840c06200300154085212010320102200c0859140c0e00d207a0320050135074190382c10542d42c5245149000c451300328220441c000701d5030354281811140c0c000c148403519203401e80c1c80005442120004840d281d14a5101415507110480c0c078901840d03216030580c1c854801014011034014004c213803581d4550b100704040d050181c20718203600000d6069a03001750845240702d94424035001c48103000070400076401503c03114940d60124401100d4000c0300c2e2044a440900b040c400b00c0c5840c1d01c0346541440010201081d4251040c0010501d010340340c0040c00c2641c0902c820084039803200c00c0c004040c0e0002105840d007103031444e01200101c1c400070342c0003c41e400c3c02c0c000e042d050342100f0030301c041b00d00c0141c410300d8050b00d100d1000c541e01c0210300c107050045008018144040f11039400d803541a40000d003880782242c12500d03040c00400d401039031050440350f200c014801c1d400702214124001305055080329120170440e6115421031820034488042441c4102d050761415540c8031000da80e00d5902c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498970863 1250 498969613 498969617
    0x313170d0534050f120103060609020909040f1a0a0504030e0a0b0d0f110a02011d061b070804030f03050705010c08101a0c03070c09050a091106130302130915060501 72
    0x1501180b1410120141c03078640c00d90606040e410320040c48204038182e0844408108100310340d200402c10b1101e00d0003098020000102d0031803070440104003080b0f400318000d201a2a0088110f6400104100c840035076080c2800e4496070380341814641601c03000340030103650a0300007507113481c1040d082d8501060404100c0300c42030222403811107180f8054014004200504010941d02c100c0d1034001c080d113000411448426500008102a800401210140c5420340b040070391380c000c1040188004115541e8400114683c3c4001c0c0c41c1c2406140c00e02d154841ca0300003e0405a040150001f09901700303001e400c00c00c0c4500000d2060140c0c1d80c404513400c1c90200c540150b42e109071326041240c81c003691b5407001c65070100101240392141c10207002c0c2c6075502c03c44003100c11260058082010b01c1e12485696085100303070000f0300c10740c120780d12001c4100001c80e00c1c0a02c00d136800948030150b003600d0138554008540c064030b860034401e10b0810020040601000644804d90030318003002c8004020b10035941981c20503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498972113 1250 498970863 498970921
    0x8040311040b0d030e0a0b0f092b1e080409060e070c120e0109030b1807090e06012105060403020c0a06031812170a1a040507090b0313170d05 62
    0xa624111403e112035600745d03410003d070441c0031a00302c007008002e1840d405140e01050380c603000035087c0413400007a85035803a455202c41e0301c1d160f08203040d080c1e01c44c0c0782a08030740102c0e401d42c1f13840001140d10014031401043d64100040001d041b50058204000707d8121000a10451352064000d43381402907040060548a0482c0c410042500130b1040703100b40c0c001850000c0c007982d103943d148a400345081d0f540030140380072660300440d0140104448009480d010b0400d000401014984030398031081809010031600d00c8845e55110b1180034489030350304941003400c4640d241824103010b0340303a03401000000c0c0550915500843c0f094024058039402c6440c00c4103c10100c41a45c4521203e200c4200d001c0040001000c03854071016640c6105500903241c06400042482c0348414607950410500030a0740900d04140800c10441e410580c120226507041480c0703607407595034910f9180f10105d9010010041d40e0342d5a048600c0280c0b20340034150807401c1241c01c011980360410414081d00102c00701039050540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498973363 1250 498972113 498972139
    0x903060402040c120f051f0807090207030e03010c0e0108130201080c0714150702070e070503190f06031b060903121116090207110405060a0303050c03120408040311040b 74
    0x1c035074007000182c00c00749041c08036526001c0200040d85d42038520701c1c0c07110341c40e8000c1c80704d00c06001d0202c0001c5041c501903141a5880e24810a03180c0b8590f00c5030b07070144d95020621009041c02490282500d400003402080240103400c2c025069825102c0001e00203080c00700025000e1503a00003c444642d01610380b0f001507503804c3d404002d9940b0940044075006d5040400d1141070100b0014840144159110707145c1514210000030b191003425409030042d00713110414040c07800d8100d01101d030000d6442d1900807000740c54911500280c01c01c501001e452921300340c400028861440039000128a00320a500c588030380d142c00464a02c0e819000250948861240414002d0b000307508080f52820000269007105e04904c6403400703083c41c0c41d8007a002964000a0990800a02403500008280c3c100c9003000305080440200c1d0a81d452800000c0501900060782d0054074001c005542004903000c004c0007182c6040c3c0303088000c541251008688141c41520b40f440c5a29007400b51800c64030b00a40144c440c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498974613 1250 498973363 498973369
    0x1020709020d020f0c07140603040b150a0b04180e070e060105070c0e01060c060507141605032514010204121101032910050306060a11160602060a110903060402 70
    0x80202d4500102c19820880140f031100c01101401d0310340c02050103007406500c0c2c04c03903000b58402c091141c1d42c0b044000b0010040002c0721540441e42124020014613402400754002c2a48608035403c60100280b010a000036400004020303046102d10f1214113010301104850b8141e50360b0725902800080c00842c0b400030700103501c100b000d0181c881c090304c061440700d42e81740008860305900303800500000d040b0302c0c10041444014024117030044498904106001c44000c0700b4041402540c20121940070b0418284042c04020803c0c0c400c11012100544000034a01302e010030700b081c4102040303e50704c007a104084051301040c400e8504a61401a0a160301b8230180e46481415004c1d0b404035062555540070402c48a000c001550314000813058414941d501d500d02700000c44ea154001c150802c4000c004005c810b0300c940c4160b500c081154280f039100c0200075030507203003044600510280c0040c0c200f80300043c4141c1c0011058000c8101040821100c10082903060341407244e120102c2c0c141d4440c40110340141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498975863 1250 498974613 498974617
    0x11011205160810030b011d0c0901080402040b0303070611030601080711030d020d0204030b040b0a060f0308070204090f0f121403010302061c0b0d05030c010e0a020109090917030103050d120b0102070902 88
    0x9580da0341040680d94403551078103000344080e00018140000782841800322051400802e4210a4145850f8113040c210400202f44540050000b80190786840c0b82d4070740c40d1410800d85107505d500110603ca00580c010300d191203038004980c040e0010392007502160f90180030305240280c101000c000b56240080b00c000300b802942c0000800070002c0e40c02c000000c0071400850445029901c500241c1c41241010402c01c0259160b54001e025800d000780300c00c00004420300201c420035503044e0707130100340462a42040030b03400b4402000a0940d4621803800c004102c1c0059401d492003440d0389800d22040070030458031130240824000203400400c20006c843c0c070390800d00300b104456000341c200420008010313000306009080c0d10700111a10340c004a000c90318030100303005079200d85600b20001c107002c00c0d80c0e40008160204520071180d400d40d0307817030b40d0000f400b0840c45617041d43d155149003d692943d407031070400c1d92010400d9205d000070380750200154107819140a1101c0100051b4014180303603062050100080d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498977113 1250 498975863 498975871
    0x260603191703161205070c03080a1419050f060a030206130b041d0c130b0706090803150f09070503161214100b030421110a110112051608 60
    0x425011010303038110780d003640194825041c581406002802c01000030749a030030400e400c003203058202070801543c03540c0000c5281c000c035058640400341d911400300d64002032a4103820106080b002104210070b2001035034841ca41150641c0c0c0401c0180d90b0b4800340500c1035405d84803650320400b074a200708003520b0100050140002c00c1000c00042c05d0381c650b00605140d0003075000d42844a48007a00c0ea100c1d00d007941c1143d611400780300045252181d00e04114044400b80d00039100421004641031080c41225485501c0280d0b100352001d0352030510b100080025402204c44500c01c9040042100c2c44d810711841d0729014580c40d44507030381141c8819641e140301d5070310303035100740200510711000d0f000419042c020b8034421a5a030008000c5410a03040300013891200342c0101c6c1044d2410000d0200250500c2898001c0480c0d0a07a01c0d01c00201c900c074111640c40300c0d81d141c02e0041c46010501c0d030034800e003440044250b880c241c0780d01e030f0910400305407603045da5421504c0044c010b410021421582d40a00c044a0344 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498978363 1250 498977113 498977123
    0x1416050402030403170106020c10030b031903050712050909090d021c0c0804030f120203070c03031404090228021b151905040807060509030a0213020903010c26060319 73
    0x1052410b071590341c10782a001d07404800140c0c04440d410f089c60400d40d030950004401480c0600207103180380b010079504c031107132280380c0c00184805031640d051620031802e582081d82c2c4088500302071000000c0c001d09603000707249007600c5184018041542d0301d41c00103682c42c03d0790140d005030074030b04a03103045141948400381c81542801403070180407000031300f2080244040c600c91b0041d0682c0c048182019441d100504a200055600410080700824403074024082200e9141c034042c3c0403060001000021030140d03901540a00b400400c1d22007000303001154030340c0b0006171044404405410305800700d070385880480e0280220390903403005003403504018001e00400a4503c0c102071914240b903d06405001c1132046005c001900800c0a000188090100c01c0040079030f440c1150a010b0a480000e0b200c010100000344076001c49e45001e03e1009081c0c05464084000800810000c1510705002d0203000034540c90307111207003290a01804198000903228050080034004040440e92a04520540510140c041d15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498979613 1250 498978363 498978377
    0x350a030605100c0b4b0907030201050412060f0c020102090111240a1121060306010609091d0d020f0c060c0705010c150218120f0c0d1a0a091416050402030403 69
    0x18512210701c441c070340442c8425417042c032104250845001c080c8000381040040b608088010409070303901806a5045e00d4000c02003c002421500c0e0000c0100180003240c1e071050b0810a01224040d0103502412180308203803a000c0c034150b0000c00450b1104062500c2c9581080303903182e00b503140303025442c0d0550300c195070550004000001c25880d080507000340310091124500d0292060980390503220160f041001500201065418404080d1442c000b5000703103000e443c1e6070404400410010455842c514254a0a880c9002000380d0002c3d12040c178580c0e008214821a440342d409800c02204507484aa000b0025108144c02c000044411007034045007a2610207d0000c07028100d15540300401d8848031940c041c049015450007440785001440c18050250741024401c0102d00e0380c04107000000c484110791408111071589810405c13100c402640d100d18400c55802c1160f80701c03050740010280340c0510764441c0a00018400380d546e0b00101c443c042c1c40b01040020806c01c60400d90082d42e0058800c1c14145 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498980863 1250 498979613 498979681
    0x1501030609090f0213050705180f0a0306050702250b0309070b030f0601030b011b0308191113080712030309080906031603050c07350a030605100c0b 65
    0x10155080320b60140c404520100b1071908500d800c4100f10003450007074605104518090038040d0a50040f0812042ea0703d018110000d0325641c2d0801411424200030001d603840303503c80c2401001407504850301d00261142b0340540170501d035a850182d140c07090b404101603440d0f092120741e80d440e0300040c06c54a200c0c030030b55401048003a043c4c0040c61044d5500019100c45182a070001000e0700c204115007414810340d2140703282c10814601c03000c40c2441d01402c00a49a0311048440803200e109002d60311003c91401d4880e0306c00b02414030080280b8012104e1011040d500c542449840b040c60b40702e00310f0310488a10b41c100001c0c0c01f81d0001c66440780140d044905041219001c81e00a40c0212003031100c010003c4200e96015805225041e000030b2034204060402078255103480410b0803107a86003030f400500b0000c85041003298144008030f5840200c40948442e10410090054411400b0b80d038440d0000d80e15521800c2e10503089070784105c0c0c1041c1c0050143c0c450080142030400e040c2c201c80240c07440ca030484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498982113 1250 498980863 498980879
    0x20d060b0d08070b0609151e03100911060f19050405040629041508090f070f15140a0309030201060305060106021f06050f19051c020102160e15010306 66
    0x1800058000c2c12002c0da51072903441d140b80c0801d802411035200c0c03043e0009004201d8200c1143e0b0600c81410b0302e641c1c1c0b000700c11829841805404000c415031500c1074422213030410b4220341111303a02034480d03442400400010000c01803a4083c9241103150354a042c02001c14840d0385170721071141d200c04d41c2071403882c0640f9000400d050ba11650406840fa81c4034188491110301644c1c11021544600452181800e0508070401815141c101c0844100001c2101003007000c1e0080c005a5014683c41040710403e5075108000c12606895124110282140071030388614503004480302100041c81c083e040b0304e80080020140c000b80700c0c504058045640c2d416020000940c1004506d001e400d45400501d00c03281503c085031116008008045944c1e420903100704240d88901382e01301c0c2d0364181207490a42c41e401d2031480021220041c2d02c05580400400c0030b068020304010b00074a17096000380d003030340e030071500245140c44084402e1260814110703044000849003945516110300f500c5051501041c00355440c404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498983363 1250 498982113 498982129
    0x61e0112061805040308060108010303090b0a1214040515060105121f030303020405130603350d050f090c1012060e100f060813080d140f1602010e0604020d060b 70
    0x2c9608520703611410b200506421101d0b6540c0103609191a034a103604658008040c0551885040d03401c0d0030119a403014207014000d078541c006503a00081100904680078001410350a8500751881d00804107142c0d015611a240a8070816040c0c40701c42ca4068240544040444014032041000200701c14029403200812007020045001b9640941c87c3d0341000c0070401f9010401140c04140345c5032181c2000010103040b502041c0c0303031548815818455513815010010b0301c0c10350005102400000b01880d84031129804103010307d81400e040350f410741d154201c3d26522810618900c1d80040389081c003d00da1441017116040c59540c08030702003403040c3e5403402e06d84d010030180c504202961a9134000d02c8400201390300c0300000e09403450910b0b06801d10b0440c04042219000c00034040c00320000399202c1c034260581024135400f401201260b01c510301090703550200f6100703480e461500c07100e6040442e950391050140b6071518262a010346410317241c544c00c00840700680718003101c0303d688607170030141a40e58203071b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498984613 1250 498983363 498983399
    0x4020412060b100507050a06020307110a1a060a080a060504140307030201091e080d0207020102030915070201030f1b051b0d08010e0f150f01020f06100509061e011206 73
    0x640402d103480d4200410460a03225610a4204a014040200803030303c00100f1074070451700a400140d03240c072030510072a00226148040c641c43d00c2060940800c1050240300030031070381082180302c0803940f5030700100b0007041d130701e40314a810a61100d0f06810100380d19034000c540142c8a00c2031407058001203981c160854000345419400350f5503c507100c0041c4001309407403040c0356410642c60700d407848090f0b40380800345c069107480400e040e60125120003164000c104907014410b005201c0428040711440d1035006500c0084100e0010381007410f216072600c21400340c080c010821588040c00c15000b2801107a6940002030207280d112407040382160500020b005c2009015917698420407a58189071511001c55400780c00300c0034042043e07003041408459076041240c1d10100321078019080c481200100d00d0b10b451082c500045000d0345c410300c420840c010150804490054a007400d40d50780c1d034010080643c041d0700c801d000d5070002001030f52056210328a0714034444d5003040000740380c9807607484010111010700d0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498985863 1250 498984613 498984623
    0x9030309211506050a140a03231005070e0103090507050d020a03150903141905033d05040519090c03140a020a090911190b132c040b0604020412 63
    0x83c1400241041c2119501034102c0740c0d00c041030b202c400000300b04503c80502c13000e0f041412901401c010508019070644034410101c0888400189078008440100f10503186038011404c3c044040c0356950103409500f08941c0c1103400f0307009007840d1100b400644201e00e08220381c8200c9a000103c000740103504181c49000e001c2d040007482c0240c1c0e11380034000c0c80c03100740b09000c00d680c1030000fa00c2140d0300c3c0e10000081e81c1d0500d0020340720b46640501c0750004e105040000d985200030303141140741c000e90032101000811024449103c071641c400501c400c1f00c40a41b505014010124114030348282e1580210342e400b8403621900e01d034255240c50b0b4201c1c425144042c50f00e250442c545140035460700d150034801500c1409001c00c00320b5a02d50f250303030f52410038215190160b00841d0340041c2e0a102002680000c0400c607014a6441d4102c0750390b030101158038010401b01c0c4581c681341c800600b41d07802483d1407480600842d044207440356100e6030031000d0028681e03980240c0801c40840c900340c181d03d050030b032280f141d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498987113 1250 498985863 498985871
    0x70807110114100e010b040504390f050c0c1c0f050105240102030d05150a030305040306110906040303030e0709060605070b0609070212070c0f060503090c01090303092115 75
    0x42c04000005203d40c0c1c1c401e1140c0b612807801480113100c14000c98007191011200042d101c100455981e22000b6282d6004050484081500300149a4107600240300d00003643d645107210301041e01a030f49400f5101700942e0f5070307100210041903414505800d00c40c4000e60107180c0c409500c00c1da568655444180c00c200e60b5039440e041406181c803c04d1400624131101b07140046420003800000030340d24004c080d0b9400d52709443e1004039440c0818202c0250801e10b006d85078580d91900c1e402d0103440d9900c284400c440341e40c44c3c104107420382000641501e500c000d005000c1e501e080d1968900b10060140d060310203000c0e002e10b00b0001810ba80c0c1c6d100c3c03070300185116180d441e01c41e000e0f03040030f40e8040001403a290203030085804001200d940444c441041807034011032140ca80c200ca05000c40802c80e80e0b009004141e0703074903c0214220390403c0265216600100c2140d81c00b02c00c01c0011600405144802808a94803801c2440010920425440c0c141008030984803000c016450305107590380801c0e80342c40c00c9551 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498988363 1250 498987113 498987121
    0x90705120a2108010501020a0209071d1e031e210408010c0f02100c080a02181201090c06030902010c0204020706020c160906080106050a0909020307080a03030b010801120b070807110114 81
    0xf2401d0240144000d0000c1c0c5090000c94002c100300117001480d000c200420300d01c000c2800e05507071801d2030385000090640e00c204420100c4925018000f400e2040c400d220343ca10050300d441141d107002c44414004000740c0000c00d100009155050001003071820700c940103020100b0b05071002d00c11010100c0c0c040d5078444c201003d000006e400c02404181810a890030a07440c00c0c03141c2d40109125030000c40308030300140e880c021042030190813200c011440d6802018080c2c82c00c07a80c0c505410601c3c140340075000d080300301592a0029021075882d604001e0125410080c10b101600d820786c09032041d0743c090000503150810b41050a801d000b0011013001407541c400c10144807283c9144508070180a894008208190038580050402051403003a04505c03502e0305880d00c110b48040c04200020110344082f90744401d01da1801030043c0c15000307901400a8004000000c90000c814000d0040c140c000a1900d4242c46e03610007220040e00c02071040c403d11050768044401d94100340700f1000110000d03041000c280c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498989613 1250 498988363 498988367
    0x50706020a02010515180105121203192a05070609060509062706241306180614010c0507151d01030605060d020304030903081908010b03090705120a21 66
    0x10301c803200d0300d00950716840c941c0e0000d0308201506e415507400300c1d0104200d84681040529045200f0b564648450010083c40313880743c111036040d801003110768024003400348005000181201a000740003685186a0801344005002e00000c090b024003034a0b02041000c241e440342415200243c0f40006594801c1080040030b65000c2c5c89003505910360700e0509610b90040182540d100805808440455002c5220322600b4035250b06c070030052440904080f90007547c14640e07800500702807003845040b00440001490442c410b1050390f0071384a20400d12020301c2190070046428a0319040c0c00c690900c81e600c00070455054110070051a030f81103580c1c0c1d551511640200f2550b8140030300807281814207040081c40f081da180801d488200c00c40c100d0040e2241d48606088a0701103c650007e44904400100b00c0e000c007001081c14490b80c0b1712511030382c1203666500001c0c02c0900c8101c41e0745950750815241882240b40c56030108803004a4401105d1000030fa40c0c41d0442d0084141d80c060b080c116040d402c0492040e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498990863 1250 498989613 498989641
    0x405090a03030b010e24070b0f04030e040618200f3c0a090f061106131104020705031207020607140403030807050a18060e0f040506030c10050706020a020105 69
    0x200f020300c4c0800c0e811044038046001510015042c02940c0a85010b0b81e6060210310b00303813000960001c10809450804c0032a520004e00b00f03460940008940c00b1410203a41014010001281c8030307010030510942404a000b00104070309920007030804001e4400c2c0c910303e6841d81c007820728040c5c031503a819070310201c2544810070340081c2c6201420019501c4668086c000c6030707a0030522204110030003e503482415a504840c20140c40d00b01d5429244250008a41c030b543c00296000100116021039080d602c0c1c04103103811403025614010200d445039045c910480c2001d40140600d680b04c5c004a904000641c000010411011200b0300c1c0142d2095040102003903100c0724000482400a90980c6031900f940c40c000e0904400501079030502000040b0000020b00c40c0c20b0300311074140d1121184800300d464440007019038035030f10b0310203100702c00900e504255460f2511a281c001c0c00001e009210070000c0e2030601000d110b40b80c0300c0809004052000c000400c80b40e00050000e14082c0d070000503a071800c0e1202070300c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498992113 1250 498990863 498990881
    0xb040b120303060120010513030f181503090203010f0e06180a022b06090c050402091c0206090901080606031b0906010804021203070b0105030705010e010f0e06090405090a0303 77
    0x1460a4040310240d1200882100d4202c4403e20300300c100450b0380a5402c45941c29820090500d42c40d0908000090131244004213166220f95202d4030701002c041c1c41141c101800e40550300046240701d00800084407181c071601c41c042581d0402096408a5400180c21a00500b505003081c03900d80b20300ca070300d048090200d640e0141240900c508a2100c4010007603941480d10002800740310704e003070001001220942d4024882038103c402c602c02100c2490a8005040c000c2422900100d5401012902d440c181c0241c074944040580f114820040c412805081c480ea9801c0c2a84c00241c01c00c4416200e0f151101c400d40a00f842c14001c08070750900a09051a201c40403071b4210200e441459a01950740e1742000700c0350414400d103402da01a0700d03240005010380b40c01426007a454400014000b00b0001104541030407100120709031042d140d40e071030040d1200030303503440c0082c002070708034000594a0b8000c0889204802001d8121401d0007001e401007000c5440580b040441e6610881c025000c15078540911504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498993363 1250 498992113 498992119
    0x140102060403080c0705010204031401020c0d110d1211190210150e060a090c020d110c301b0319050601060c05030c0102130305060c030f1302060d0f0b040b 68
    0x51815840003080741c0f00141c0741651291300040c203503050010035010744001d19002420303c202e1208521201e4000c0d40919101b41c010b000358050500d1603405145070003104050200034010310450860101c1701e1800300150080f2440e514501d034088000c80300b02070224216000203d504c400c6404001074507014030401d61240c002e08081c03500326401584210780c021280c030f031800c00d800d9071110300000303402c00515040b26000d54500742d03510303d09035030026009510040b103441d0b42070320b02c1309621900c0e214800c280c081600120007001c05002c201d072018544a20b030980382e06908031101000040c0741050714641600080c0d54880c2c04800c04c031319041c028000e280c00c09080800480c2006c0d03032107e0310303040144030740414094180b42c800203104060003119a548a031400071036403100e05446101c2020518041a16035104d0381d03000405070760007801124041c155002c952001559840368201d11105803034012a04403c00b0b0146070100ea0150017208600d0012443c0031070280103c5080c44116242d80040c00c2c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498994613 1250 498993363 498993373
    0x3190b01030b093009100e10090e06060903160602162411030f0408010e0105070206041a0606090301150e060f060f03060d021c0605060d0201020c19090c09140102 71
    0xc600020001c48407443e183e1030402074488074044591034458068400f0035500501d6807012032040c90b0f48085003007480740b1f0481c0c000d4056820080304580381410380c05000c24a69881022401c146000c20140610354801402c41c4c43e140a8040c003074400c2040b55004601690120b2150400300d016030708250040e144c41c904c020035484020118400c50410315495000380441040c040100340d10510403100b1100c180100c550707817940d0f40d82c00103000f00790389005071426510300707808034004610101f200f60145800c501110500000e65145a20461000d4442503001e0030400402c1e9960301c0078020600720f003980f2484509101c0c0390440001940c000181814810800e504406030316a4445007034071f9020304140c1c07032a91250365400104500c481d070a40080d40c021180d9140028414040c10446419845614288001d85844041c00242e5400b0040280942c0040d80d8529160034281403140162010a0b0b2240039195108901e50444858101c0b0900146280000344003c940d41d140801c010002031000300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498995863 1250 498994613 498994633
    0x60f020d0c08070b0c0c0102040311190b0403060f200d0b03030a02070e06030f0a080d0f1104060507021f03150f060516210c061d10090203190b01030b09 67
    0xb42d403900c5030308401400c0007521808208180c1400003070318901c84459000b10344c0d550322402c05042d0b0407140c410f810710039281000886c0740704c41c0200303400d004c440e06035003641e09141c10355590401500d1941c1e0854480c0c0d0791800c01e900c0801801559022040e61034568540d0b40d20b10040d01e50603188a2800c06020b40d00070031000056580c00984603048440240241c1041c2c2c0391200043e00b48810340307400f881103104408101c0c00740300b8020000d28040700c1038241044913040c50005102943d840c100d04580c101c0d4280000c01c00a4010f000501886200500d00a040300c2165144a4000446400034000a95aa1526850205001c1400c001e40049440401c50510700a0300810030302c24610f01e40000b024074807030b40b402c01c098942e036075540166164081c00800411503000b8641c00f50480c09843c3c060804411148041000f50700558040304074024140710760103070300d034070b000307000f0b07001e400c0303801d03100b10b42d00308500021510511510038131880f4404e026516508120070744a0000d030622950b900450180 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498997113 1250 498995863 498995873
    0x2010b03031b12030429060d02010f020a060e1f020309100c0908010911040f0c08040b060d050109060b03010e07121e050114010302011e02061816060f020d0c 69
    0xd10b021a038030310070a042d1407201d202018100780e084545210918404424442080148450111a101c00703800c502c1800407013401403c010f080c02d03640544c01c09281c480d40d60155204031100a50f524243c01103070000403941d902e0104940b68401140020b4000615a140d01c2003421103c103140c4100c41401d44c11404c1001c0f005445d4909442d2980185a0714200e422401d805801100c0042100500800c0b8404003411b0000100011703030b5070b945c4501d15208103000c484015200e01402c94410f40d542100950340e60f44c0d801008040541000e9001000380070800000c1c40074000c2031174151282001090b0351009106140c00e469520000501c070390840c0c1070030311120510140b2a030031103400412a502c00c541c020756090701c1c0504400c01074070755400c20010b00369100381810741c141268403e070b80d0b801041c003d6040c8001d0a850b61078060340107030050f0b00825100c2e845901c414040001110640707221004181e110b00440985078403950200f118081043c0304c045d014803c0003c0c41035941841000d0380e08d15522 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498998363 1250 498997113 498997117
    0x60c081902010624031401081005060f0d0602040302181b160209040b0f091204050906060c01021201140d0f3215160207120f0f060504060c02010b0303 66
    0x40600c1110250040d039510300c00d400c00801008a000e2030042c40407035040c80000c0b0510403801201003400c0500c442441005c05680f58120f68001d005401840c2211070719102500c030140015620443d50099181c1c607565a51001e00880c1c820040165640c0c51481444331b44504007081d000c80001070f80030049501c1c0701982ca0101c4401e06120290b8a82c04807101d22100300c0c40304c00181d0008400803c01041180409020f4098421a99800e440d60740340c07034030b60765604081c07064516681c8080c40f0810403820b007001116080b103401040281440d4403200340358226041403402040079103541c4c00410582400d030154400400341514001c40050b25500c5101103402e0142d030003020340c80f0148001d141107004a0405031401d004e00c0035900c10700d4641d007400d80d0f03d526003028a1900c03a401004900c108545041600e9044000d40142585600d48043d2250660340a842691020344846284000501c4115044d070440d1040e080041d4500f460305000084485400c6640b003568074100c2c03420110350300081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498999613 1250 498998363 498998377
    0x3030e03180907050f030f0103020f041b110c04091a010b090904020f041409030a1704050703020d020a0801020a0f031a090a0e100603050a12020706050d091a0a0f06060c08 75
    0x2824840b50b8890b4a41110301d8031505115100b42e01002c801c0c0440d0480c5500064120b9008642c0d030004000740d1401c001c00c4030405c1d2038031284800721310180007582d0b0144010b0005069a4001c2e6000550a0700104080e143c00c0801128800d0ba840b4100c20300e80d0468040720b024003e985a400e05005a03540030608810740640003a01c1542880002d510590740c54020200c0310712400034a01903401c019003107960321f0b000380c0700401c0403e0700c900c0d007880862800074915101c2c0d9017140040c56905d203944c00f404103500e92488140e07080f00191001252080d000d0009090200a540d68a0041c0c08174080c001c0480300d00c4e080c0840921186200740459a982016581d0803134449000020015010041d1610b400502101d24001e6820528008288040401e2100f03c9500607042c91421403100103089842d64454016113010138400c1c8111001e11049521201e45648664a140c440650252416800e40400c69003030300d0040e2200200c0c0800c043e140100c0b0003d00b9142454180b040f030a0b03076809510b01a0007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499000863 1250 498999613 498999619
    0x512070501150f0b0306040603081b0d030b2209050f0708060a0507120c03021608070204050114180402060702122d0c060c010b060301030f141207081318020703030e0318 74
    0x400454240c2c0d0f242d51023030008644c401c69140d5989155a41889094540080c44e1703018020b100d010309089000340104030072220010f001540340711081c00c00c2414160300c200401c0c4401e1f1b68071301f0000094010007450074445400c90003842500d01d0701c1255031a01c40000c02c141003a03810f06041c440c04682103000e00884c45035104000c62001801e400440090041540700820064040400c0c01841280c00c01081128001d4605105603a00e0303000c3e8016135030708244042e400206042d409526007020800700c5401c188010040b5151100c0c54000030b2400640aa01c903050b504002c1490031100300c880682d515812034400601415280700404e41d8807400c60002d000e0042d50300141d003260290b029404030303441c2e1364000e20580c0c4950b100d0512080c1b0442242048865102c504005d00f8024000030b840400c1d0003140440900c3c0c2620307655100c0654001e540d8004064503003c401050742c0f100b80000b0075800c0b0750524016102d0105040007000d44d00482c020740307443c1d0001c108203440f0035003079207800141038429 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499002113 1250 499000863 499000867
    0x80708040f08030a140604090b0c030403090306050a050108010b0406241205010f061103071e0501020d0504120215060f060a05040b0403030c02041407080a0e0a0512070501150f0b 78
    0x107410490804840c0c42401007001038008200700301c040c030640c0403454100c0002641c40d216640e5405010807078100c4103000e0715100541c0300080030422000010740e3302510a04d480f46109540340d0354902510015a8010450341c0c4400c0180102002440740d140320300d40890b0140401441d09050304018581c0360a40071381400c1f200c01c4085850b0198080107008a0b10180400c074540c1d44203248501c180e01c9006240004284801c030000840001060b640600c5e04440c1482c9022120351410307900c00c0300c864046030255002e000441c07405c0340a02c1498406c03406590145801c549209000303080040589411074810040420310602d034071002040b01010000391851580c0307140c0e11100b651103000d50781c8519400f090020f00401003561107040403c08038400e450600180320444070499050408403005000148041e0024031442d215402454034030080f60b0544411084d20344481c0d090480302d9190005090300001c2c000704218092140010000c90300010415142c1031075030580400c4114030541d1008000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499003363 1250 499002113 499002121
    0x60a0b191404021b061006020601031703040c0e0702070f080a200406050a03050d17090c10261807030b04150b100807020601080f070e040f080c03071101030c080708 72
    0x2840c3d04680400d0030000c240910300030b4510f0003039900c10007115106002d50301d101e0002030850000034540d040c0c0354800100c2149007460401c028207a00000c0090b00c00c8060402c002a0001050020368091070300355025282c05801d10312002040c03c00380c4e10444e8070b40d010881540201e8a542c019003c4081030300f004c03107015118040040c02810040d08100c1d0301a464400c0002040310000314803184860b29129408034500c400c014801000e01100c50100c9900a10620342d40307880d2000c1100d4042500c0d040a25040c0e8904000d0b21341c00d60159480c0d008002c1d1a070600c40003224211f00061100103000c002e1041d542107503100c6100410260000340f42011000343c140700c242141e0000302682c1006018041e031072540a00c004c1114006413020f60240c050a000440d615002250942030302142c0c030001c000c4185043c19055207040010b00684030070810b01300300b80011714858024804100b101004503101c0b4102d0401c982d0707031004204080d042c145040641d901c00c0350003600c000d50192440c140140a651 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499004613 1250 499003363 499003369
    0x13030b0408042c06041b05030a09080f07020f060f072301020315090a0605010503070c060b03010504030c0203060a05070c1509140303011e0317030910020705060a0b1914 74
    0x1a030308414022040340008080060004800c0e940c40302d42840049141d41360882404101d910700280303400007902401010070510b001d000150f03017103180114001740504543e120541142c00c41e22840b10000000034420080d0301e0b06004e5180200002c4915074039007214581c1101d854032801000800c01e298084e1034820b0000c03a440d031100f0544604c802075547c2c3c941f001440705084d900c3c843d000d2084a030f039030114180303000c0d81c810742c000c0d1041038680f40c1ca55100d1010541e0341e880300610407600e03030344c1b103501002c0f580d1000e000722406039100f6224903501441c0743c030400d0704002000b440354614901c0d007800c119440b980500c041241a0300701c0014180000048010700250441c0d2030040c0ca4028104907101c05003000000841c12a40082000b1013039103607106401a41ea4224030014105180c0782c407001c84e0060b040002035800c001c000003102e0100403504040016600000760076150341c3c004000304005d5220f50f024082d075019081306c141d4160720300607102900305c5002d07004600c1020542c07070101d180c40e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499005863 1250 499004613 499004617
    0xf0506030f06090601090f0f18020a0f181d01060f080f01050f040609140906090304030512030711060106050309161d0901110c100b0f01050a0e19140a0b13030b0408 72
    0x303034880307100040c40e2326500c0c0e0101d6143d5510171032030440089861519a84520310a030340160840f99154155880c101d5421507440600d0356050030008020003002407492900c100c5443c0d0000c05800141c002d42c50071602504c48440150160306003e030600820840c414030000060550702c00310303800d6520f0360005000c60002e03c0941c2001842501d040016010207001d240c0d4248121080070403070311242d1301c01040c3d60b100d0049100040a0303501c00358840a4050030600519070002e80762a20354400d1001c4504245800740a0b4800400720702d0000a02080360000c1c00103c50210702d160754044001d1030b01c6503024a619070741440b007903091201d40200c0e0040344290003600c8040030440c591030b101d209214280b502d0340c0100042180c140d20f04011a00c1c1d50806555040e07600405846460409501400c02c0d19948150b0054907805441040351190f43c50040201d0809014854284d20302d8040810070b005603890143c1102440e00d4084c442d9498a50351441c00340d0a880c0d0109032915551074500e4612003078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499007113 1250 499005863 499005869
    0x11511100509030c0c0f0a090f021e0c012d0e0c0301150608100302010e0d0303020403020d080d0b0d02090a0e010207050f030c210a082e0f0506030f0609060109 70
    0x100d041509102c41144008050001c0c0d210100c10b43e40c80c200d0100c2004990045034024640015950310100044595540000640d400b040b401514100a16800c15a01c0d00d40780f41142c0680000300c0e00d40c114640910031078250150020110b41254440d6003000450741c7c0208500c40c04c0f0341c9903036043c03400c072009000b03881c2c10180180092110598103900b01e01a031044d405901c0000d40c48a0014025414004112003103a4042c0c61312080c1c89180001e0210000c0b40300001e40c24550208070000058840040c02c5074207601410000c0c1d01e90313080002100541c0c400901451280c0c00b11200400560f44192500d5003000004e40000b03074107d8a990b41d0390181c0134035480540305001d0804003481611002c80201150a125016141d281e0380d01e52815203014412681c0b40d140c003030103109455500c0e000320394194111500c0c500c4604030520711172189621650100102c3d50b1407845130801c00c00008012007090150008845850075440e05605280852200400b10751045008a000c80c403c1d9000311012805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499008363 1250 499007113 499007143
    0x6060c020d08071719020102040e0112020a030b0411040e0a0209150301150b070605180a08030c070618050f0f10110403020a031b09090b0a110427050f011511 69
    0x2a110044c0c26000c0103070096640c8144411100c2e0300890301a206100b2941915061040000983d090500d22034100740d40b5a01207800c20b072102d20100100c0c0c0d1004401384260703c03481a040c20304010700180001d0742d182228074000307a40300b881a00e0041c0e0b141e5503400d50016040300c014050402500000303002d404c0c1c101802c2c0c1c10101e055004510f4a1100c4001e150307a5001d0401070011f034035103609140d04903146003001980c42e0042d00d1010f00003107052008541001078116030b6410411641c44a40845803c11144001c46038010782510811000384030040c800e00582c8080c00350500a505010744030302a0b12200c0040a40d03c0d100d0210140024003039030051900580591041922442c012140400c06040782221542c410340001e02c40400c2d001e4048a03550004c480c401d00c0c1c80710700311031010702051350000e2102d0b0028400400c14a1520314407a140e40c4007100341c0802c0c101d075005604102c81d0046c143e258030141460041c806546a04c1a0440f5400355242072280d0003144d800c41420900d2003104601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499009613 1250 499008363 499008383
    0xf060e0106090c020624060a0f0314190c0e0d15110c0f0f0319180504020a0905090109050402030a080d11071112060907150e060a0201021c06060c020d0807 68
    0x71880d0b5000642038030a0b440d0a4140c0450035656555444046c0c1c0c4030031041c5d11880c00c100c0c49440a205110320f400d442200e017804100c000c224015801c480c10200c07440070480d024088100b04c107002500450741e40c00a0b50038800724a9191001003082491540e001801207409000410744001c030ba58089000354192511046e01c808188840e1500d402d01c0204400d114418120303102c1c0c0d078030008000c6270245040540c0c9800141c21405059504038012024181ca10b84200d1001649440c1c90000300382c0d55402e0703592040c20b9428102000900307481a0070050000e8a06030030000142c500023290a11540c0010405803030308490700484010b080c0c1d58041a803900341c0440c04008010300f8884283d40244111201c1031034a95510302d0a0f0340718400c5a480d0651b074050102004100000c90b10007007418410700d80b0040074201d0710702140701e40c2d001090550041c1c0d070004000b001102010b45080b241881c404040c0f21903032a14900030680656090042d1003008600050800c01100404440509078003c81c0340c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499010863 1250 499009613 499009631
    0x40b090a03120e090117030711010309171903111e070c0e010513051e07050c070f050405060a080307020103181a04060507090602071406040830070f060e010609 70
    0x10240f02030703030b0509805820250000b04945107614014003110405400550500041d48c80e000d885024100c00c0303034149a41e5000c148086034144d10341400b100c240f00074545c1d0b144031104280003d100b1401105040503d020910321840164074100c8503461100d0f4141c10030360900740074111003403181010040c00d642c40c4640c002210445483c5807412030b5030881d20700d4150140c1c1d20003d001d44400710380b644002100d0900348104080ca096425410180c1440e01c1400d140145560b2482c02120b900b01740c0d116030780a081080300d494680102d5900410948035013100c41c0c0b801c0011690390240741c0d0001d0505885484000c0f00c2125001d080390a036811000d80520304103c10031280e4004e07829601a1001402c0c00b000810460241c94564125a80340d801080d90b02c0c5054003004100340034422542e44190708120003d49032030104003040b060105001c843e4255034040b1480c01403120b02241c442c200e1130003131250f58081170030401500841c40d000880460000d260f00002030061205401821207149030040724 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499012113 1250 499010863 499010867
    0x302210f100f1404110d030201110a2a03020d030b0112060e06090a051b032d1614090f01110105160e030106050906060d020d1812030c05040b090a0312 66
    0x120b9604204000c00b00b11511060720000b520010484010f0003001c0b00103400321250620107290310b40b8500034400014400d0a051401440d684003080b1980050040000e2410801d58180c040c043c1c0b5494041e10018030401e5500a91200c4944811506155960141401e9a4000c00680c2214038851070200441601c40002100842e815103106004801c0c2c0000901035000503c2030601400b40040a0b1010302402c111488070780e4001007802d4a0035002c840c141c118032a0444a180c0094069003071900395240070b002201448103101c3c2d103681081041c02107101d01f6489002100c080c1070054031003200c60038a4100594010798010007012880d03190004010045a454840c901500384c41c0d5541c0700b40c151564105420781d0500d0088503880070014011440a150840003440f82384241c0300054184124090180d0884900c206a580703051030544403401080701d2440c003c0440e000d94182000503070300310b410041c101e00071030082071981080044e203070703c4980d250204100215807160760162000501000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499013363 1250 499012113 499012121
    0x1603090b10140d08090d020a120b0402031b060a0804030e12010b101e0c020d050f0703030e03010e060402191e0518130f020621041101090302210f10 65
    0xa10725841c844100e8202980341c0b000f11100c506810054050414510104104e510100b95030100c3c4d02c040c203044005800660b90882d09059030107200f03101007030300e81030042c5800d0400c00c1075504182103e01c0c0801714550b588909503041280249001500c69480d481e041e00d1051200c0041e543c803600c180328491800105400041c50780a041e2816181e550f0022800d44840980244030f852a03000412220300d0140715110b500841800105032420038042a25102e040c054000000340040e0019502417083c140c10100e2500c298800750020402011400801503d031107024000a100300095180340c07040c900e0b214014400782400141c2020707143e8414100d900241d65038402d10340940203007203411101501c0e034044180b050004c052001019141030742c848120201060040f40d010138180940011102601a031541c1303c03440e080303241000d080c242030011200c01705c0c0720031078100b0094090900061b11480c0c4e0308018202c442031124110030200000504014410744410010300c50694001428041750700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499014613 1250 499013363 499013369
    0x140a05060a15030b010b031b0705070608070c080313050c1809070e0106050313031e0807090905070906050c0a0b04030503180102030105010c0206130306180b060a0e1603090b10 77
    0x40c01c101210342e90548078510040c0d4030010f8044220a8010040760050a0003940d03c4828549440344a414441038100c6076005100140c41c20b0340401020301801341c2003907401d60001814104018440900d607201281072000400d68004038904204510400108200200c1e8961000f440320b40c10b02c5590001c81d495541c2241c070912540b24030040041c1c039103a090003c2d0706070390035551003d18503680c96902d030202105d1420218100208041c0003186114481000c07080c80540744d541c807042e4200402c0040103050b040e00888601361500b8103000030603801c000036600702e0b003e900b4246e840d410301011f07081c1800042080640100c2c415002c12040560040c010751240d2030b142080300080c0da094440b0b41c201d0009004050110700c5d03945000c4058542076015126041c01d0138582a80280c03250788540940318100308c800124403021843d0020032610750304a0740c1c0704509454880c04a80f40c880940b04034400604554800001c01d05031420321840fa0300503106d0150084400d040ea402c0800041d04840c0300e42c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499015863 1250 499014613 499014631
    0x313060b0906180705090607030305061e061603030204030807062c0c0d14070e090c01080f011a070b071808010e070e0a0f0603050a020307050d081204140a0506 70
    0x40440c0610740380740e8450155002a1085100d030b4404405008000c5000d0b01000910206001491041c0ea0b1040284400c0340b1a030341c0880d0a080000038000c00b86c45040314100640369410101c1c1082c0c550809441c80f021000c005400a01c0550130250003c0c4110b81014014800001d94001405030b42c0d080f61010501450b220300b00c1e1407007461582c8040211410507100da401007850070030540386c04c00d252940d043c06a0000e1400c07080455941c0d107800f900d54400c00c004030b0440204014a0001e00a12904040a003080790152074008000c80b8049014024010f40b0101803200d03a140e100401e041d58841584203214524a090121020b04030f90a50210f50351000c0c44010082030001c0c1c180500118600c103d0014000c903401d021075184c1400c1d00508124403540d0b10030032208242d16038090700b0021400381c0f020704039040c000d00505080c00b8064215a0013030b40d40a8508000807070002c2181c42024031491102950344643c500205c01041a54851041780b01c0d06040310284140800c1950041c0210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499017113 1250 499015863 499015871
    0x60715090c0b0c060601030b01030f0509070812043813092007020f0609100e09010806010f0306020901020115090f0c0e061204210c03090506070809041a06031306 71
    0x1c2ca2080c0c6482c8250845a00035400000115046502a410021064005040218201c0020306101c011940d0844801c0d400d039002400411500000b88076509120340c1100e4003d180074100a5540344214940703054122501c41c2a464015900c3e101c0342d00d0441e06812044103945040141d50804000c3da14007404500318681070700da140343c4e016000180519800704480b503013010100e80030005d140c0313010507407283c004804105150b403540d180601c8254114240d00c440308040e01040510001d000140c000c800503030b10000040c0140c13081c4c4114401202d0b8403c801603642e00007100101e000d820390000000c03004010310804a00e440294003d051403100400040140c5084c035202210000303582841a60480401c00c4003800403954a40030b00e40c407900414a0349a4194071101850303a45880c40042000030300f542084000305503000e02c0400080c84211105070806c442901ca99545110f44072120348140e40d1901c043d240c44043c2d4440340d5030024024011500d80c034010b20010b420030084d94081302c03031034a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499018363 1250 499017113 499017119
    0x703291008060106090f03060c0e030708101803080606031003060c050301080d081612090f0b0f1308040b030711010e0717010218040e032506180f11060715090c 70
    0x1ca10301d01d0044440a6446e040400e1964507800002c112056090702088041203100e0042d0b10302b001130100030001d010040803100d000700c1820088035403c0b80c11400301d00303280c848800032039441540542c20050458103103643e41c4612105828401c03090f8401007130103041c03c0351409029002000303103040f1030020055a1098008050032034200b4400c40b110032200a034040584c0302d00e4425841d00c034011400080c00901034141c0d0f182e8a84a00c50810704a40190b144010803100c2c0341d002c4500c0342c1000703c4903450300041f070080ea40c4800c0740c001c60040001e001030110000e61340d5481489040080710041c00208184c501e043d4669840d458a406980c40c002100900396030384074014400c803100182c50a440c003015274811000c000141071400c032102c2c00f600c414054403006418100d1a000b00c0078103010b03202d14060403413502e84103841021741141035011904804001150301002c0840308540d000d0104001e40c54010700191140c01005400341806a19442020b004501d95202c5003e00b4060841c100c0c1ca141c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499019613 1250 499018363 499018367
    0x1116150804150e12030420180f060d0b09100e030a080c0a09051302040305150f040201270b07050f01060503070621050f07120b030703291008060106 65
    0x21041d0307802803a540040074146041042e42e03001408003041801a41d5062004900c0d9168a0708165426100003070380d189030404180f0707000c4000310380c07040940d80180030044401e4108020310009244006288540000512a0b601c0e03a001c1d245882c0d005101e103115082403800241d0b55891100302400d000d15281c0341c1c078041031000040d40d801c7c0111f90b440148503035409a85001c96008441e0580500c1900800070030145d5420194140c8014103102c0140c03294554101146841e900300e461028201000c005e00003040102d85030583c0c015020700b4105200300f41810b1a8400c0040394600300000c450740d5034042500c09806d4010951240030b10304550100c1860840319003215412b20850307601d9444030b0307030070000c030f5001d10f8032041500b02603220026580d00100e190300989000b101c400c03e13200c68100030045010b8120069894030380100c201006091001c9020035615407a502016120f06014001a900c65100b01a032910501000300382680e542058821b6a42030201401b07600c15a01452002003581c41c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499020863 1250 499019613 499019627
    0x16051204050d02010c0503041a0304030306060903080d091b08011a100c0b04030504050405042d15110c12090a140904080d15080f010c0309080d0c111615 67
    0xc800504042e10704a5940c0190740d07850108a04840e14002404005a80c001911070048800e00e4103000320390300c0c507180c0307801400c6607100e41200301440400300c2c1c1030002c80c81d0202901c5440d006214005815182030070503242c0003a10326214014080c012001003201c1e2030641103504038260307043e02c4821900b440c00c02c1003240154840524005020407020101041c04601700b00d4101b806400e1580c6001c0e11031000c2402c5e54000c41c0d0076290340058101041e190341c244100b03451881d0a00200b1419184565544c1705000c4c1c4034159104403680742d441000c043c2990008171948804108116250031542c10780d0018035412071110350344135000c0c2c3e40e000500360000d00b02e00d107036080c00204581da00e039903503980341170282d0801c24002558981e82c10300d4150021041c0c20000c05403462500414016070a000b032030b03080d2056100388400f05801d04807100700080c0c40c001524001c0a02e4a4007040e9582d5021045802c1880400b82e000c0300d1140c01e40c081180c215440da507505071140c8612940040610b10800d44080b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499022113 1250 499020863 499020869
    0x903011b051b01090b0a0c09031703060108010e3c01030b01050a060c0302030904051302191e080a1104140a090519020306060d020a05040204080304090b040605060a030c1416051204 79
    0x1a0a80009201c2c000f11f0341c000d40c6030b5961402c010340803540743c0d11047d9210460300741540c3c110a001007844440d603004120319004103500800034400d840c044034510f082e800707403000d07800b500c41011414507950381c403820156035480080001038101d5a5603041241c0545d200b0b100722130141690650100d4502c0c4a05100c3d00c14981540095141541007001c1c00020500101440c0e400c440701d04010700141d6961a0750384104c0c0000d814000d04605004015151800e92814944d03100440c100810941d40046102c3d000190071409014140c00588042000307020340700c5452010600c0e0500304503844411350b10101e40070b401340c1e049481440040c1c9000e02d140106010280d4150f00440000c0c3c51313841c0c004040400588064a101c0015580d000400c06981040c0c004000075003010606010b600784503c034040c102001201c0c2440780c50301d00300c0419191b11480c0018801c050700d50464aa440380109003500f0b451244030100c0ba685c1b05003520001c06020040002c549500403a1003400c02d60001c00c05941c15 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499023363 1250 499022113 499022123
    0x22b231b070302031213120c0302060604060609170c030304081e06070e060c010e06310309030b07030b100302040509070c050c0d1406101a0309030904020903011b051b0109 75
    0x2810485c0a20340395168801020440204c80c400000c20005442d24400c00b808001611041400411450302a003800d0000f0b29403030181d840c00b50104001903120f403500c03040350078100c592015043d100054606018420603695054840010001914030f400910081d0303600503800132680c00c03600c1520b4241c0b100390507110000001d00010030418240703400001040c074501d0b20800018181071310404a41011012190581001ca10780b40c0c41c2c0703c01240041e59003a205040c2c1c12407070808115034001e0b01506050101510308080c1c00009021203019031300c64502c915005003800c10750185504010041d500c40d00a03e03018034031020101d811f035805403040120b403c1c1c2c00406040201c480030140840d5041403041610034016560010518480901200b8015a1403860030700c005800d084c034001c07048401e010815640e103020410805000400f200ba20641c5d4022900583c1e1096030310300082c05411411840c050012400d442e00309407542120082c0519022001ca0b48044038046485a01300da04683c00030f00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499024613 1250 499023363 499023367
    0x7060807120e0a0501090803011a07020904030f14040f03110603060d080c0c060c010c03110c250503010c090602100b06030c09040e070b04030204050a022b231b07030203 74
    0x1010003650b005030b40180e0b029000ca0340e25600540381c0d582581c2800c070b03056405907000070050100c00d00420b15031124441d620011445c1014650105141090050002c0d017005441d04241c0200b41c46408402c440c0d40c104c840c1c0c5922561a004410032102d9240b104895015643e0340407141403c062090b00e00c01c0ea00100f10082c210450786034016507070b012110cc21241d020780001101d065440303001416221681000003d401c07102081c0103000c40c2d001500302c0030162002d00564034540f60004100418002561160b6000c02c4140b12556006241c2d4101d60740c15402d00c116440400c4c1d2108140c0110748066007215482011901c0b13041c2151400100c454010004000085020400b90000d049031040900001001491802804d00348611078018079202d150028042042d03140c1030245540040070035070118038000c0d0104030460601e21304086c0d03401c1024001011640710480d40c1c08a00710034001190380700f0040c1e0011201c9401c3c034040720780e01781d43c00d5040070310072241d100350042d210802c5d8103400542c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499025863 1250 499024613 499024637
    0x10e040507050717090a261911061605010b01180501050706050c0910020303040b07090b03070f11030d0c1101020a02060601050c0a060f02030403260a0c110f0a0507060807 75
    0x8400703410b4281e48100c0303030301c810054405d05803184d80c220401071500e400c5007411000700740103402420180c11041c035225400030507035135104030316040481070040e03112200050303101444000c135081d402010040075500518403114010b012041d04070040c5950240e0361060356132840c010005905441e4000d04c2e0004505005090000b81c007a40400e0f0042c5000c0402802e281c5008001404051712422a1005810120510003001000d03251140c01c01d9060920b07490706410400b101ca25400300a294808012603c0741c0003070310a001318902840c01c07d10030240c0c3d07034039484e040d164005485031090550000c0c44c109180080800180700350f440000c6280d0141409031102ea004481c241c010a142d07103141e0007891040400141a44034142c011102d840300561245001d040242c25407005068102c1c41410503240041d0141c4003078402c0c1d90080e0b040c90000348200065004491300c21280c00604d0452042c00c03d000c0600f0000140c8500c1148076a00b2100c109860740700483d5209400d641038404135210760200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499027113 1250 499025863 499025873
    0x408091014030c130f080708070801021809041a010b09010e060f04030b0c0c030a120b06070c061b020303130503010b030304292205030106051503060f0315010b0306010e0405070507 79
    0x5101e03440c3c42104122240d601c50b9405d240d490000d0707020403a960b001c010f00b00282c0c0018880e0781c000b403056a0003181000d07882c0d9a0050b541c0c10300b40501c1d110b522600d00180c108801990018516a032800300702c103281d80c40d60b42040c55030380f105100702d01142d5843c0515803203140100882e60f0008828640700d040030f245070344e8000000340240600950b03420620a221007601d00300f0181128804a0342d8100942e810403039800216440c84241a00030750741084004013285c020500745e8100d82d4180360120b0810280c44940c01d00c040803c0c0000d5040c000040c0c840300d5000c400c0c100c5810394070200d000300210000c82d410103030341780325521500030180c030f914140c2c1004c40d4480c591705050300c2c0c603030038101c1c80d010000c0500d4100000500055400d00250102409107050903c203480107403409a60390b895205045911001e14080100320f944a0401648d0190150324144407120b81e500c0c000003a0145941c4520040003150001c030341e002c0c00155184035030a0b961038503000b1180143c0c0c0340c1e191a85003003a01c0c2c03a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499028363 1250 499027113 499027117
    0xa0c02060307050903060420090702031e0c0f0a15050415021c05090610060f020c04090606080105070203030106110718050a14090a060f02040806130303090b0408091014030c 76
    0xb04820f03c034003401600c0d125117042c01002d104520031907102605008840c0c1c0380450021100185008d078403803004008100740c0010440c0c0340485400561500d001c1602400a003910404c02503401c05d004000307211107400b00c001002c914040c4a640c461201c1d01d88801c000044590884028020404c0415411600852540140f4001c0ca400c094100040725030511a025140300b03452521041d0720640800a81e115168070080103040766140c260780c0c42c291160025544d05d000352420b403180c0d0b9148001800c0101d940c1c00000180501d000a01851820780300c00794032034200744942d01c04964a8100421a82d1001c07a095041c1c41e5141c6181e10701c01c40c3c1c02402030060000408012215a0381c4c02112001032031901038a00c110340110003802820304618090041d20b2010480f082c006006000c184907052000c220951311410308180841c0c1c030a80c43c2411406040503210152000404209000c10f00504000034410003000b074400310041003095004480c071544848071540500f906002040c0c103107100c200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499029613 1250 499028363 499028371
    0xc03251e030803190614011b08030703180210050a0212090303040e1e101e0509060f010927110304030206040204050901060902042d06140a110102071104050a020a0c020603 75
    0x10101c0d070007011400b1980490f0417130b400400c2d141c0000e2440d806d056a010344186108038410314548180303070060381c500c21240009083c1750113240d19120541d50500c00254521840b0350000d221043ea0f031804100074206a02c0a02c210005000c0d07200d2908501d5100c80c1221603400000d070085180c680343c221900880f80c800360402a01594071100204a648101d8a0314082c00142d584001c00da464080180c404c9007030482039020507801d884041186a48284420398050003e69850740740a5202c0e00490790b2174000e030496424861081c080b414050413828561150603480340041040c41040d4200402c540030490380107005074040c0001a0050030680c000c40e4002031241b0020450350344a8907100e050ba0420380251241c5040507814407542003280412203440e922492035100503500b4400300905c1000502c4000003d07000000d68517801c81c1c810380009070409507000c003c6449021703910741502c150f260008071510807400c00002c5508280c10348211004840303141c136000c45812040e1709020355600014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499030863 1250 499029613 499029631
    0x171e030a060308180a0603150e09030c24060103140604200a032c190201051911010c0906120b150a050c06010902040303200c03251e030803 61
    0x1d44000009014100904940650461815034908078401485000f10040d48108109820f080000b5940300904441c4002e440c0880716900391980d600303054520b10311030104050954455003501c22024421070500c48840c81d070118540e142a03e0340c20044051700d07008600c03441142c1d4140080342d500d180c5907114460b114100c40d8840f0481c10505100ca84540109400d8030201e03440c2e00e9540014054021150101d0690301c2c2180020721300c1010146c0c0e60304801420402c038030a2040c0070000d42e8000d2094070082c2400c4071aa14840000150081417440820040000396080c0250f080b682401940c203c800d941e6070340d98500082909030360304070140103560300c0b080d00407280302480c510300c6409600a2441030f2043e101c86a5850103615450f1038802d05900c0321041034414441400041e91124500c10003c2034182481040c0f802c2c0000d040c2005240c041e40e030b82c58030801c910f84003c2c040d1a28007010400000c4050084e540e542e808805440514040c0d80800711741d400c5007480094412009581c008600b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499032113 1250 499030863 499030871
    0x1120203120c0f060c161203060b03040804171b1c080310060f030207020102030307050705010209030105150a0f030203030f13171f0207111e060f07171e030a 69
    0x40c180500c2e0340010b00b041800d4100c5010800400d10401c081ea401490b44042e06140211441048090003913424001b07000c00005c10360960307a9440b03500301102401c45859111703968102483c0240f050350040c8154900004a1400106194804500c503a1302803200080c000a802c0441c0401c2103142c440650140351010b081010320100e10a4005580b04011f2000b864852900780746003e0007070300720440b6800130180108042d40c0181d074040242c81c1c00c05050300b0040d0311501c061411502900030080115019882c0400f0001c4807012140c22411000054518102e555280c91443d070403001140070203501940104105040e2a02c910000c000c070344002d07480f802c000340d00c0d40244c003a00ca40c0c0100c0503030303298454443c02d0030f9640c3c1302100754000511641d04600e09010b0307617503140d9801140d0650910549851424030307001c0c58421044e400e00c00b0700400c900d54441c0795540c001c4240e04844030940301c140a1844210085000b541120301541c010840340703030349011229a4407460381c80180610011a11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499033363 1250 499032113 499032133
    0x2090a150c0c0909050f06010b121302030609011a0f06040e04210806030706030b2103040f0605120703140406050403090302210114070c06020c011815050f0f01120203 73
    0x84880c2c0180500f503020b070042030070046801c010f450501803080c90905500729000410884508000300d43d0050308076403642800c0d58501e0310f0050700496018010390940120001c02c1220003065001c9180c02016a1010b00e64140000030300c0344866000302619003000c1c04020510521190303a00503a8018441d88074980c0101d001314488002e21403160000002c02d4845051103100c0c601031241001400d4185010050030b1410000240000745100e02c603420044810b1403288051300520455001d804452010050640d580d01c00420303a0b0300694518281120100c01b00b08428868003946803ca03900c9080e82802d0b860f56101e4000610001d0812814000100360010050700c903c4c150007d01440308100e0440380d44080c081c54291091004240b01e640740803020808500d822030441e00f17403560030440068503681c202c03003611700500c04804440c0b41602441e180c0c10401448051070340707003c04036010a11041d2542611548091015189085121025001400b5400645500d9101140000d08403014528 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499034613 1250 499033363 499033373
    0x503031204170a0203070605070516030c06090b070207050112020405060a1d090a09020103140403080a090c090603210206130b0606120a0b030d090f170a0c06020703021302090a150c 79
    0x10100f2014005a000410303504240101403064076800065810110302c0c0c494120040307405041e14010007800c3c4203400d8507030001e011942e800a1403080e882207030f03a038131410042000f81d0381c0d9034540301c3e0700d0000e6110051001d0f03820b518020303201210b4014140c10f0800d10001000e40f21941240c00c03008148084082c02c16259540820442c01014005400596042917000040036281100c002d030440351a00e40030700001135440500c444e80482d103ca0005100060b515000000c03196540c032002041d420711101006220340d903981d19040481d1151400c41e00c600d820400e80c2c4401048034100c2580118200320000b160b0300c100341d02d1b0702520040c0180e2404000d265580030700042910503113905641c1d056080402e04040107403141100c8141003401c50f0524141007221801b11601820b4140c0340b040e0b8000244080070070024000681c00650440e03030684902c4000c0d928030952100340d03c112818180040080300314800c540d8100400380040e51120705112880f00c0f004031081320301e820080e240c0300707590100e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499035863 1250 499034613 499034617
    0x150a0e060c03030a020301051206040506060f04060503011119110622020d060902150405030c04090302072c160c020f1c060506090702010e101104090f0c020d0306050303120417 77
    0x4132000c3d4016140d5052005000180390840d04800c020750004003404042040000d1580d4016001c0b1403000044800d400443d016106030381c400354156081080d03803c03003522807001420000241328000004c1d01c144200841307040003414825070303c61704160301085106480c00c0303106da1140ca40c1c032590048098036070b011404007030401c2010b4420695410f882d0003140351031684d0f0038290a0075100c1d141060309001c006030310303401c01d512164411a5035060120405001b48480b800030302202120404010b10800400d201504410410115100720710018403000b14036214200034204541c0c964210946036804d00c00d0015450111075808210074030300c0b5501081c200103e2044520030400441c1c58105001404400600230b4489015641082101143d0804c00540d0600001c04000045900c01c9441c0c4094001d00c65904022000d80c1401d288503881c01c035940184260300e610b075003200d1400ba2031810032001c0b100b090050540c15002001001f44020a0414107600035000c1c8070b07141e001101c00c90405a0503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499037113 1250 499035863 499035871
    0x1e0d1d030a090b18010302130312080412080c0403030c03090f1d0603030403030503040816080a0503010e1003242408070603090c030605181b0f150a0e060c0303 70
    0xe40c000034907954820340c080000002411a405004d0401181d501c403006485114010181090750104400100e601c25183c2c007070003190402129801800c650340014411003044a090f00c00c0034800c200203500e203224000d9207206562018049041505584d811503092140d41810750402000000101c1c0c0350b07440040c03400c000c1c0040058074041c07035900b6211000e1090300800d5584280c2060104001007a041022a580140c2c41030359103680302a03801148038560f2080e0301c090800c003c0843e84038030050300a001181030b100d441103c22850750b80e101c0c416103072052030300000b040441c525003841200b007601c0110a201013075011002c1401400e0704c0350321825030007035404101200b94110040102200c00c0c04804080d15051509021124050325511520101c52100404003581c6000092800c82c500ca0000c1c0040c0c21181900c04415401c81d101445400034249544201491504407500f880c100003005500d00c1006071960409022000c155050041e040003260805010407106100b40c1c03003800107600c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499038363 1250 499037113 499037171
    0x1305010906170703170a0314100f0602070e0105010f090b1611030a050a03050c15090307110108010b0403030806010e09101a07050a110a031a0115031a0d03031506020105010801111e0d 80
    0xd6500d802b141900315a1154414819504040710a0115190b01020141961400e0070940f1007941040812200c0000719480101e480c82c0c0070850221001000a8083c80c4d40e010b288448440c8a04404058441000a200a010303601141c05140040c0c040e401034030b5044000010b440c1c0c08003050700c1d079851440c400c07111400c8035000000c2100c00c01c0203085500c0c03030342c4100317207400c440d10b43c10421051103501c0b031408050300344008880000c0e4a684039004000b040040079002d500b00e410000380f005142c2c80d8500850841d0180000e4007802ca010700070a0752559a00500108842203054a03200750f4400d501049075044294040c01101260184074492018541080c0c0c54400c0e62500b003403100c1840c040315256003010300300b207001210001c42c40d112090f810401c07102e418040c50b581c9030640c024a0518001501f03440000c00005400d82c040d80120704a4400400902108805130040032051041240384607001c6c040b00030700e014910489000e003d000201d0040004d0743d407683c40f01050000010510420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499039613 1250 499038363 499038391
    0x7151e05041506080613050c150c12090609121c02030d050f0f15010e030709090c05120d080405010b030318010f0f020c040b1305010906170703170a0314 67
    0xc101d07106400580602c814141003104030300303054046444110140401011000c910301040c18400701381b0550b048880c00421807078a01c440c52250000c40d0300030168000b018000c0058008103014100100c03107440600500c40d0b80307031140780402c110600d10380305110381c0c0300e00c9550541d210350243c07980b101941040e81d400441c1c55a01492038141512001414541000019414040e10a6000d4400e03074014508540408a290a0b03000482e8151041f40c041e81d854400c40c0030000d4440e2a9610680041c0d014040307200c40c1944590038007810200407040601e0583c81164418100740c443d074a0141c02501c158004155001d5103000245135401c90141c005000480e0f16501880d9a04010b44615a4035030b401c0020308000194006516120401e281c207000b9a10703550800142c1d580d500444004042c2c0290400407075131200c0c208001001140280485c0043e090262280c0d4400041c20f40100c07030303110003d203480c02031003034154600350480b000034401d25480d50049084400b4030b005691141f028000041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499040863 1250 499039613 499039621
    0x30709030b0106050403110f01020115060909060801060b040510090f1e0918020411070209010902041a070b070302090d0609110103050a0b0906061b0d0509030c090c07151e05 76
    0x10300d00c0040e8042000d00c5010071003000010030400c51742100b104200c400c4230070310440b440180c0c05010049901807840018a00120702e503900803800e5015070784100c108001403615000b41d50b08a81d454000d004020800348806c2041e4034000e51a03007400c00f0075240c07507400347d540e0b00c070740c2031072211103030051701d601840c03082903d51404040f18010001d0011000a001840003040c1600c0500000140640110f8544a001a20303007220703021111a2075020b00040c0d103c0da500c0075110000e4019000d00c162080c01902c038000048441000d40e190281c00201808883c0c0703401707000703178001e40c45964501c1d0443c0d40900400b02003009445034003400350050428883c1094054001000c5541c0284a142c1442ca032020740100340d1100110f1950154040d101c41ea5505402d40c81d02018070600307550300740c0500c5411761f0f040b0f41507400350180480c0402901244e60031482c14081004094080700c0360282a0b1061118001150b0b514800c2c00001d04c0440c000640840e14000c0c5002d40c600e0000a040a036131500c0500c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499042113 1250 499040863 499040873
    0x906030109060510080103080702100509061204050d05030702151b0a05070b10080309040e01020702121c050a080c0304140601080d081501020601030308070509031506041d0c0103021e03070903 84
    0x81a6580304502d0111700940c15551f80b503060303010301000030340120851b0032902d05e118000c03c122406018001e14054035003041040000420f10708940454444c0500288038031202c0c001c00949001c0c03203043d0007404410040170140d408145004144060342080700c41244c904042800c0203000000300d83d5112541d410150400c4003002101511809500208403402c00003007a0101c1510141c8a0444002c01d2025201074024064015801c4c040e6001c0c049284100b00458006400801d2207585844200340034000d800a036028064294204042205940041e0000c2e80700c00040da801445180901d41608583c01d030a450004240c21030b6455901c1104801082a0801c0209a0028031740081c0c0740000701200000307444400611008007441030000200785101d000302c0550381e540c000a13040310500b41a1122015142c0030680305a40100d140503590160203582000c02c1c240c1d03480200080c00615850b10046009500100c2c5801d464000201c0f6503a0203001c860045010316019900c000c9664251700349 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499043363 1250 499042113 499042129
    0xf03180a08040b192102160c0902090a090c08010527010f08211204020d05010f0f0e0d090e18072405030106081b0c0a0b070807030b0904140309060301090605 69
    0x815081c40103d83e2403400a17200c024442d034444050420258503040301c140041145109408020900c0390390301d07804205076103035034081d10b1010f904444800e100c3e9a40d01c02542201c07152454a000038407031500601650510b800e1000d03041c0f0b44e000010540d4442084a480b940b01300b030f0030140c03400c1d80d2003c041103c1303d0b04202003040b004003400310201100ea034042024851041507c80c0381d030410410000383c20755a84864a00b1000c0d0003e000b404000305071201040106451003b086040745801c2c04200c0204000038030340048000c86e00d804118038149040d4100a42c40242144c81141d042414026112001c3c42450014034020416158801c02d905460409000d4052603900700042800100304c0183c0c130290b81500603904840b50f041211030424159558031601d0303400c20b224429161200204810f40c00400c1c4a010540e58002d0691101e480c00c50035245144681584071a5600108011822107442c041d0141075400c00c980c64000f090003c95070503042688060b2601d82d0780d000400c028100894 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499044613 1250 499043363 499043407
    0x130f111516120509030a120915030509010c08060f010c020609040c080f060d1703040804030204110d060e091e0f0a0c06111501031b0b040b040513020f03180a08040b 72
    0x804504100080c4017203a514070480c40c0280c4020318031400035030b0103405044000701a15507844a5141d007400c80d039014015050964400074198a0480312120702840b0303c00c0d01e4042c01d002042031000c000301381d00440e88511801001c0e80d000208000d40042039a0783c1c460342c4494012911510403a00e840800199250070090010b40503450400c880c2000440c10070410401d50b030503201958480e11282801c03080f07030003140c0000750452300c1c0c54080d000000b01d4201800000c0000103045c008a43c030349201d160341c1041518584815400010140c001554952040140c1b042100c1210100d8003007081d043d2600314489000c1d0784400c0502d0041c40310f036a024080c05078600759040100102040681103802d820740c144405410780c0d82e6030040030021898189501c005144400301030703440300e454201d25140e6610600c2000d01c90580d550f0030310b20034810350090300d0500c1d8107070101c1070039540d54070800e201040340007c60319440e0047e01211000158002d019102801074145842e44507080a080810000840383c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499045863 1250 499044613 499044617
    0x150f08070e091303030f0216030807021911100207030224091c12030b0916031410090c0206130609080c03041806350106180b0306130f11151612 63
    0x554160355192418805030f2396130610b003a25980d03981c3d4200700d08140124100414030700921080c03005000038400304400d05c2d601254414000112114166512403181c0300080d006041c6044c6441c01d28003002207a10400400905140380c03c1c50765000442c04c84814110141c5640324000d078400b0b002d00c1290044900c903090130100f1810028038001104004020140e032035840e10f038200c03005d40030300c281c100008500d61390502900078103080504803007511050245141040c942031030b05a41c41d01c0020f501d070041618021041040d5130307503117601014140360350054a602208200f15880988200020320060203034101120705581c000c0a1075080e500180c2c4180085034001c41881d507400fa81c001c402220702e0018540203540c0c8001d0403600d015104230b40c042485010542c41c00c90081d501d6410445061600b101035070040e03520900f070001221000e41c00034110946007a55440090160074403101c00a0b80208209405d400e080240c100c41c1c0d10081010304101c03907410317022041182461480c2c5100c1018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499047113 1250 499045863 499045867
    0x9180906011a0904020912030c0f0c040614060c0f1213050609060904091103010e1f02040b070305130506030112060b06030c0d05060d0503031f150f08070e091303030f02 74
    0x3801002d0714040d1054040c40b0b10380c0010084240d0303585442c6000690049000e4035102d81e500e050954076500010303450402406540145480d03480c0511840c2e05491a0900001d560050b100a00c07840e900000c0f2070400340c0c410708400c40c2d0544000c0100b400c5001c549070005030384030301c1d4907001c03000d10655a1000e401a0b406200c00f03e000d40c0c0d00c1003130b1041050700340c03400660380c55142030a2001814003500320703805500e0071014026102000c42c01021440c1e011003100d1216030011108801c80c441d5101d002d01000d018000400082d01c07d40042c07000c2c104100e80640c0752903c801c0010000e80c02030380840702c051407402c130f00000c11a060096486040b0121211425031a09502c000e003603109258103039807070aa0b240d00085459803043e5a14442c2c0340c100e0102c81c4c603898662032045104403480100e1400f05071486000408282d04d21440001c0d0146a40e0804012021390042e612044050070200074045a04c0490590340c0b00c84025520601e02c1c80a4268007003e5400c001d0100d07401e08104807216401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499048363 1250 499047113 499047149
    0xc0f0f06121e0b0a031b03050c1c0b0705040801020d0e0118020906040f11040905040308090604261c061d040c05091801050405010f110901080703020306060918090601 73
    0xa090141c2c80740309026000450780c840420001070000d039480e040100886071306030619000042c2640c1c4602031701e1144003201e42c6010540100074280400103070106030400002e40310000a03185c045419000001030401605003500c60f50010f09a810070100029210b030765070108202c6003824050901201800c0c0b60403181c19540c1d401041d07210500900080c047d41d03d503007a04440030f1460303000e0455180610340094580d6100e14012002d003038252401e800144100000c5010204007288240c003803035020400e2201078000c900c0c940d0980100c00c5414101800901002c528290300c50041d003004a07144100048460410b000c401486850050000d1b0045246003000002010007800788192501100d2100c043c3e940d0060034655040080d090038070303035428841070208010054010b100001c10b9000280030803841c0122003001401045149400601000c0214440500903070045400510140403d40342511103800305400d0312040d140106500e810380200091f5000901c015805000300c400301c2007803055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499049613 1250 499048363 499048391
    0x3150b03091216050703121434060e0601090501080309010e130b060a0809071505071b05030f0a2003151e040503071505071b0c0f0f0612 60
    0x110000802032094001580d000310300f003104091554154000c00f110300954903850608400040f5100c007501195040000d07412056001d0107035100d41e15441396205150280c0b104405012043c0702e004501b00381014056004105980941c080014007100205004d5241140240482c0c0c8160311041031908140600e92050703901810000c0c11880440d14003000050503156100180308900103680e0086002a80b058000e8001c064980700300e401070143c0b81ca181d601e8a00940840041c10640001082040710f8030000305035001c9041014058040100b6041e07c0340c02007031a11401021402c0c80b50b001503411005c005c102681c0038500f00b03640210b1500c45002e08046503417464030344103202c201001180015442007040c000a181d58402080030109420f103410401d41b00c5e8004442039a58070500503010b05c0307c1240e4041c540c0500e28507500c030f407801d0800e0810f40c0300d0810070600c201c954821011002416030040b5013001e024084230102e0b010b20501d00000070b010391821001f900d054a080c1030840d45054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499050863 1250 499049613 499049623
    0x6090210020609190218010f06030c031a09090a1e21020a08030c1201091e0504020f0d030504050306071e0807170703091203050601120207110607020d1203150b0309 72
    0x200301c0d24070365450700a1000031ba890502c1081e0038040840c1c00c000181402c240f2400d84101c0e0740644040203054005541101074941140c6807656040e00c0c059540c5141c05c14160940d0300a16110680f41000725a581e054030f080014418103c040c500241c0314030511800c1400610000c41c0c41e40c02102034480350b44003949031070385040060311021004c00001c240e021298112080400c0b84420307503c507503841e455604024403154840d5a402100d14861220503191445014025030b00244042003a1141508020b641240990210100a420302c000941a101000443e005079450340381c80c0203503500e00c4401100c3c40c06011603202048504410f02c500d06400c480910a1103985c44c1003681c3e15680c01c0e40c281c01401020000419540805203151031069040e40000c1c0907140990720503941000c1040803406034002e41202801022504860440e6071810000411141d480074040840d86141611005224406080e90303002103610303002400107082108045402a121014030217040d400c284a2040e503071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499052113 1250 499050863 499050883
    0x1205011805070219030807030e0c1e120114090d1b020f1c0311120405130f1508060f010b1c0e07171027030309020105041206090210020609 61
    0x52941c1e200456656842800740d80350030001e80c110510665683c0c5001004d5401c00c40c1c0307060010b0311708040c00000701c04c003080c50000b00500a14003000440fa1044100008003412025540415840905881c0300421b000d00603540c5419020b02c0c0701403914000322804d1013030407140c0404103c46441c1e03000d030b4000403a40f003011854060311601000d01105000c80e110203c0800b8000c45100180440020940d00074200110011554140c4000d120700030349070642030085010b81079010804841c5159103402e1584001c11170002c1500c040b407410001c0032107540005483d000750741150400420010240003d004c82c90040a141004500d07100d0780c1c0b8101e0f104481090b028114150711000d480c0d032202c0c003c00528001c3c0190f014841c0d14903210122841d41c0d450004d4000c41b11b141085008181d4640001034201c03a010281e840100e104015078044000741145141203042c40070074440030a040c154800b0b030702c001511418000030503042c40e0040103040c2d20300c0801d1100310743c013440410048401c00b003042004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499053363 1250 499052113 499052159
    0x3070e0a02070b041b080f0c010309050705040608030705011a013516080f0f0c0c160b03150a03020307090b040b12011d0a0c060507020f1005040501120501 68
    0x90380c86a0095402911840b04050000d007152400d2105114a018a014004080b03c0c40b00e030816586080c1c0584502e0044071104d026001034000308140d502070f802c80460036105005940c59282c8940024046031080c1d0401111a40085500010090300344a584000a9a01c3c0c900f10b010180c2400280340080e061514264500c0000881d042071a40350720408120405401014072460700021541800140501c1d140020782c40001280c00c2450449026000b00f60303600402d161640e607460b5801c0282c1c4102c40d401e40c03910810742800f981e00d64030f440e42d402600da41c102c02660707070070031400c14080c8000109400c4c0c0304194001c4104010703900080c0e4070007294481c4001259842400c0b001a0040407181070140d008040e007000b200e00c83c0c00640c03100b02c81054040d41040c1180c4280041d9030707100038106004044c0d00101005010359030080010301040b5100400e0210341c0c85801012400ea00b54002a0380003181001c10244843d681158604416003d8813004201c19803500030001c9070340440b9124211 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499054613 1250 499053363 499053389
    0x706020d0318120e03062406030408030f0405070308030406050f07030216150204031a07020d17070c080d020705061605120606031803070c052d120f070611120301050307 74
    0x22a14051580540c4000000b02903407030300c0c41d0503001103564030701c4120700b60400600403440b40040d1230a0710540c0e00503500112002d0841e91105220600d941c4040c2c800e96075485010000000035400d10000c500c5544248000304107428002c50350040090081c3c000f900340350051007601140e21f4051a4203140d03d800c403030010450740070302d44228000d01c07450704082e0540310200c0030170089900010644c0c1c0240100e50071120380d20202b03542143c0031111904041b040116400100d42e01e584103841c3e285896001c0e541c003d20b004034828403101240c0c04603800b122150480801c210055407884002d00840d40c19080c0b00b4682600e06642d40702100e0020041c07480f80c0008004540079144444c0c41541c07521488080b25502c0401e824031311083c010500c030b1749201b81212514007605402210302e038072100206861044030340040c40c0811041300c003080005403d030f00c183d00034050384550030000200142a80c1e100d103044110b5100c1e40ea800d1120340c0811148a074003c100402c020f44000070310104960340703100e0040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499055863 1250 499054613 499054643
    0x5060613020f04090212061017070e330a020a080f070503070f06060b04030c05221817130501050a030b040606171b1b031603020706020d0318 62
    0xd0028040d160310380300704140110700072905040d00d50081580c0c808030205010f1070b56945081084558042c9a0840082d03000111a041e13140d40003003941c0c110210b41004440a0720b8003021400301070383e070f01c2c00302101c1e4110b40681c141d0101e40d443e4000c0106030200903d10f05191450003941d1024451001000d0001c0003581d8802180d0442c00c0c1c8028a0b40801925900c0c00c0a06018080615030002503032000d16210000421029000486040b250312944030307424545407500b0400040c101003240b0010142c002d0341084504040d03ca06028191074861010581074507013820b0034400040c00340e41d000840d082041840207070b1b01c648a0401c544003440d200c0d80d20700d0307103490490182a80c90703011030b08107040520124826410036041c00c0000100385a00c00c0b1a62481414640c0f010a40300c0391104980420034a40301d50b801c40304a40d0300d405a0f00440e0b14140780843c4040d074840080b00141c0058001e03100030b0201640c1441003402512485c50144621030580c808495024075105c8001e00603444480b02e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499057113 1250 499055863 499055899
    0x70e0c25120c020f150a0914010912020d020d1407090b06090d080d0c053006040506060c03280804121b1a221509020d0b040f02010801090603050606 65
    0x44e0010009024182d540180040700d14164110350904d40124a0300c60000c62031101142070140341c40c805175203a0203001c0c507003060b50401c0c501c030800aa0b0001e080859030750160300d4000301c003c0e02a202d19040c0601c4003600290900f80422a00003d040701e05061040e0520354820060b01c115200031242501e19483c185800d807075900c5484518100b05080840306511140c00c0400741072000211903001903410601032100301041c1072a58000010310550001c01e809081981c031855000d24060460b0f494500c020758000c2c50f681251442c130001e281c080040c80c0643c0034403402c010024001e030805101c00d040c07507514900c918128007040340410420218112107488507110345420b050b0407040004a00b01703800c00b20001003200300c50304002240701002100c401c2c00500300d54240146c2084072402040030002c503150141a00c01d00c241d0b8046101c20505001c1801c0f4501940141e2103414003800c550050703c005400800c0503880b441e0120714202c2e0070000b1510226110f42c0c0900b04480c0002010b00803241 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499058363 1250 499057113 499057129
    0xc0213090b04080f1b011a0a15030b0121020301080115031502070f0206030406090203060106021b01050c01110a02030301030c360e06191b020703080705070e0c25120c02 74
    0x400841d6417801c80c400000d04c101075024014811701c1161610308100c000003404210324a03031081204000320710b0030b1140d0552095012000741801450011041d10081100d918010881c803146000c03960300000421161a007403140707481010a14402d02051460358a44500302e010b103820303643c51142c0000d280b0042044101580c440b140c0e004105985a05050401c0f50041c0b400500132070280c455030f40041042400044c00085c40c188458181520211210044405400040c1204801e44d01d64108103402804080a0320075015a6401151079602d142442c10600525610111000b00e80600541022044101c603102c06028620740480751074000c04a10000e18000319040d16070b004400074405a51207003d0411100c1d40c448605000d90b402650302000e801d5110340c0d03c5000350303102040410000300150054034100d800341c1c00703540005d90303502e404500982d0b086850107501070000035007440700d103144540e0141c8030f29417103440c03030305148076030f0700c0910348071240c1104414454111000700440d41c801c18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499059613 1250 499058363 499058377
    0x1d03070302190914060301051f05010e01020309060d0e060a06061209030c02030d0f020c0102011b0804032123060f01050c030c011b1e080a050703110a0c0213090b04080f 74
    0x30f001c001d00186a181020000400d0390001e02ca03509090218452000c43c0310248880000d0240b2008101d02d0700f40151003124890140b1419070109002c0001c1542d10301000e000d01c1600e800012843c521452201828904018102500e035883c0c0307003061005592120590061944610780090789a200f400c0c00c0d2400001c46000135410b1240b00c00744a0141e81c0720008d140e810700d050702111409858200103a081e6002070261241e00001d081026002038490340d04541c01500030300381030480030480000f5101e20303000b50405040054440d00e5a01c0018082c9850020024404d0b21410090070007600150448150004060400c9004907823000040d4050007158000c8010200810010b440720304801c480f07043e000740c02c0f4041001c0c800e1102c4a61100c06100030b100005a603812140c2ea1940581e000908000e4000c20406540c3c00595505252440003440d00f604035844515000703d044c41089102134900c2003141619040c2913003000080c000c40f030300f150085c1e0300180c101d4542000a1410038140a410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499060863 1250 499059613 499059629
    0x9050f040e06101a3408180102010501090605030c060a181e0b04030302060a0b1906020c131b0f02190b0610030b01050f0702030c0d0b0118050c070f1b09020a1d0307030219 75
    0x7401247c403030f500001c101b4040070b00ba0024040b50380c1c2c0d0300f002d00c100e031003a10074a9010303001803030302010900e404c40082ca51304110341041044010782120f2403811100d5600700c1c409120f90500942400127011244a000700030007200703c2c2c42c040c00e554000303441e884044d00a40b00c2584501400c8000e640c2c105500707a00d0340e1810f2000240716601c00000f0350b80c0309442c40560145940790300c200c03141d0810340140762052924204081c0700600100d402c80d41603c0000da070008600401e0045081007514014148140b0702610100e189801c1c58070800000401d140840b84c241458501821000c0c5d8202c820385469103020b0542c075480c4c08081c0040b90034202242c12282d031080020510104000203441403d0580e40503c5084010700540c081740b0742201c109941128802c10305000250005006844d240038041c80741160300220f102c442040b00d000759042c0c00104055802003a8070381c40e541d004100c0c88000d9030814402c1e4401702010f010a840307000c47d01000e40510713140d03000380410404034010f44004007148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499062113 1250 499060863 499060867
    0xe010b0a1b1518121d03010b060f031b070309090c0c03080114011101050907031a0402030a060e1507021b031504030305090304120f030813020109050f040e06101a3408 73
    0x19100104080b17004d81440e40c070b40e000080070001d2424140f1966210080c00380c21140f601086203407005040d000281281030100c3d40c981000720300320081c40a042064400d8561003507444c1054014000d5620b0b040340c0400b01f20a5890b25004a540300c4d101a0441e4500c844058940340090012a880c0110356040035442d800c290622070090350004104080303078082e0348a10340d0b640d5050440420602c090301c02a5041d8003034440100810500c6d80030701c10b600310a108a550309604095000c0f024001140c0300c0001da0014101004d01c0307001e028503c8400e0004030040c01d40300f08050920900500050702c0a810143d95500181c40f04404108407030107003404030310500411001d0b00c0d103422140e40480c0200c0000f01c40b880401c02c0925440d90b03446c01c0980c140c40f02000203082c44180b103549032011104681c069141c41c0d44800421007805418020b20301c43c0702103103c0d60b0030017924060381c03541c082602c3c15211007080a070b40042525020400350282110088541c05202540540741001c0310300003038482000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499063363 1250 499062113 499062143
    0x2151305060901113c061501050d0f0f0b1c11010c0f0c031502030106050319110706060e09031207030f140106050d050a060f05190e010b0a1b1518 64
    0x1484541028200034030f80d0110103898801810301691740e4a068201150b105030042180201c850505003204030040c0f5255003070148480c0c00c3c2d81135800076600c01c2c005a070354020344030341800c050003a8100e25809031030014040d0040c560b10703d80440e0103c00501208410380b1660b0391030384501c5540c46040d8209554100818a80c05c007500ea000309271000321003100b0111001d41000200e8001d85c0d04841083c2c40b0103003981d6030903005442810108aa01c4819a40c81412883e1180e500740500707150340c050381000611909017150f00030796807809412602907a20034898000701096400956134803840910300802ca0210289008001d0300748121190660345040380041a1603a001000c0c1c0002d640c051340c10f0100e40c8a0384039100441b40c00d170007140061441c1e00310611407030902e01c40000b6880c1901c00107101141d900c00d5100f2010382c5c2a00a408948c03000034501c0d02d1281d0002070112654070315200c00f06e9204184e03662824004440d07024070703403003034451512480c10241348805201c0c0607003185842c0300d0001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499064613 1250 499063363 499063393
    0x120102040314060f011a0306010c080c0c03070b0c0c0d0f0f06051608040308010b0a141306021522060b191502060c250c120215130506090111 62
    0x1502c0381400019109030800036038100d81841d9450b048402d08912480b0604030012180d005a000800981c1449820300340b190010355180014034031960004050803034650399100b0035080c980a5402805090001e010071501008003080d40703803042c503003141d01c000348421910740700c50024000c51000d024080d481e00da039000c1c08070641059118807085180e0750000d450041040e15031000c00c1e41c001d00002c00c440014040340440324024269940c040c00c18180740382e001540c564541d488010030781c0205d40d284004228050f01040741514007000f20241882d607203004058071050300b103203c00a8010f000c2844124040c030131681d11150b44544047c041c00b000348410003d00000030f41a00c59508101d440350702c1d104241b032001c100140115a43d0211510f4840c1034581d0360b1100c8a07090140c801c0801d01845038001446100d207020081100c140041c0000032240100014041c00b10340c02201e80004014140704501048220300980300c007100c3c45610b484909004031402e40b03004880140606c07900c42409801b903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499065863 1250 499064613 499064633
    0x4050910180c0e0907170a020306190e030a120b120316050c030d0509060711090109090b070c0f0f05010f06030f110102010e0307110d0614060a06030c0f0503061201020403 75
    0x5001d220b00d1500250744400c1000e540c00c080b2004401e641100600344400c60030145e030084041c4c06030040f10085840750300002d0608200360b6a82d90b001204003044d00c40100a402921500e1322024040e509282c04010003070a8031018019041c00360342e403404100e00a98071040c202c0300c00c40310302044a0315401c2400c0004920b0005078010388052080940c204414600001d8000700c481d02643d80f1820300c0c6150041c07010a8120080031148840b0304114401c103070f200c9204003402000080da0200c1c0051150502c1e4058240280580d002c00000038418004141d05012941c101907010041e00c1203889682491401005d01c071103891040c5040401c00414401c2d80348807184128041c08820360600306030b90040e401ca07006120707012a990414420301000c01c0c0282c3c280210380d0006405144040199a540421030b400100c040010003807040c01e21404c0d08000c6071020150500e810100200d0329180c2018100b90484040340c001c1000c0080002c1d245d48600c80ea045074141c00c48001c1d51100e880c0e1500d03c02d91 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499067113 1250 499065863 499065911
    0xf0907031e1106030105210c030f0d0e0f0603070c05070512010c14031e0711120a110c06040b0d02040b0414011b022d0306010e0114041a04050910 64
    0x25100d20400c00c0301900d40507013228100e441c003c01550700b0034000558070004100640034840703075000701000a102a14248186624400769402070450140100d0029100412401d5000e0080c940c180300700b02151590402c17260408101c0c2001e11100c4024a03100f80303001c001c0d030842500300386444030342024004150000c1d0180403603600c81e0701640c6080e1458100c64003045800000c4110402d081008400f07660101d1900030100d40b4000c4e121031216104180ba0001c00300c0060350040000030303119103260340300802038045680c03c0083d0140c0800d4000284141c051409900080e40d030024090105441c04d50407203000740700103034406894641d528054405804000d0b0000d020039005c1e40080001c0c40700025204955a0003071040c0c142020150410141c080b82e04080c0700082d8940100290a560401496009241440392511203604000b0b9455104d80d2965030140990f003011042072001010900030b01c500f1070140d400081e0b540d103002e0000d203055002400e41915a160106204070a840600031441c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499068363 1250 499067113 499067123
    0xd09080c151909030c2f27100815010608090307030914040b04020c0109020102010b010302070203030301290d061a070308070804170c0708011b02060f0907031e 70
    0x65603441c80d609041404a8030311600c1004910414450a1590b00c6011518001d190000e4511016940d0000796508804040900c1c0e07207800c0c003610210358085c170b00000d8940503a00d03004200d401d1400c01b040d9440d400b089504980c540c000090000c504440090000c2c007081049540c020740f000002d0207a00300c00e001e080700258a41000694035800003085404160341561840001898848005450764008441d20350054940c0d161101c3c41d80d0f280080e01705030011100002e441845840061300b100c1d42c0d05041030500d40107001c5d0307001690300401503a045070784d8154601c6010218140301c4084007825800840c000e90041442002c41d080f5502035000d5580041001065801210300414107000741c0e9801400580a0300c0041e07d014451300149810a1003034074900c801400c1c52040d2409030300035044820181d4841d02003040804c109001e82100a000459a0aa00c0191400007925400003c0a002c40880d40e00042400e404041020a00840d002014501c1000c4030508003620b0700122401518 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499069613 1250 499068363 499068373
    0x406141002012a0306050a090c1806090b0c030d0c05030108010509070317220605090301060906120f1a0f0610030c0e0d060207060204030b04170405010905060309030d09080c 76
    0xc068014400d140c0002c0042c02030140e040004480ca441015906a80c1001c0644406002402c0d032100140600139004402011803914034020008004081d107000d82070803240c405038104070064011002000307030f4010b400c1691743e503001d0010103881c4d48a0f203c0e110500d030f450a102c21010a40c030101650588209038020301107500c40d8500c8a66400079804040c2984c5040c0062440e01d8000700000c0640c901480455036001d9440c00640d80500303031981c407402c0440c1c03000510403c40c0ca428414280030301958a810030070319040001030441d030341141100400811101050f4428000710101803001c1728400e0991a4480ca4003041c103e40212007602e095004e80d4001462811250007401130088440d1503684034246456840700f04007a0703450068080e26040e80c01c01014003c0745007400140044c60007140f00301d0b501d08240c82c10b0940c07054105034001600c45c040c0300c140031680e4841055811960220782c8140c690320341181803800c40c42060030310807d85142003c101304000608001d030a034a41c00c9405e40e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499070863 1250 499069613 499069639
    0x903020a06090e0601030218120106060e03070f0303110a061b0e030109030f0807140c03030121080909040c08030a0e030606040608150405011b0306080d050f0306010c050c040614 78
    0xc2c0e10745065010383c1851401150004581d54030941c050300c40030520000c0710002c0030500020840e000440051040165102c08040c011a500501142c030b280c02c00f81d0062450600e4105000c2c644400703408000e0811030720580000c1580e10800182e8892608204108902100c12040c1c1011007480035445020800e818511152460b040c8100c4224503090b0b00c0f80c80f04c40c00104d104490010008007601c0034007140f801d111340c4840d070307038406400080c3c110b04c0256500d5040054821106460844002101c28042c41d000c1c0024100f00c01d07200c40e40026244140350303444900e081052140c0c81d030411200307484081002160154003044c1c80f442e140c415400d540e026142c010504c002d980c250301800056070320140030700c81a1141e0581d10b9601600890001071424101f0b44501002d01d800710341000026180c4200340070003c0c01740800304102009040070342c41e140240180d003515000040a55061103103e006402c10300c079044c00307070010009004000b089a5034076250380b29140802d15880c140075005280c104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499072113 1250 499070863 499070867
    0xb0a0507050c0406062010090605040b01120f030f120c020604020a061d062203050616032304150e0a170a02031207050c0d0e01021515010f0306050d030903020a06 71
    0x420581d03040d51ba40b00305a128690910741d0f524545003140c0d000e07108011740c84169800341d104060109104c3d090203d00b40c241410480000c0c201a000049807100901c0d15100050291010304181c0b645403c203038004002e2403506460512044140022142c1407501c6144000d0b0301007030380b521030f0380f0031500f1810098a85008455500000e054000c400228400043c8580340420140c114841190700414894454800a000b500300651003164190311a405010010100b0001c440014086280c2049110100c65036581200085000079589060500c0810180300d40b540c1401050761001c14140002c5031b540010302d43c0e90461405c191344058003504114406900c00d070440394002140d40c011030078042044c221aa030910050301c290b0134407030308001780036440605101106503100300d40c40b441c12002c0000006401d0110583c11403591007002070802403001c6070b001003005050802e11b00528480181c100a0740100002e400459000031803445540405602280d110300780c03131003030f0b800286095440c402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499073363 1250 499072113 499072121
    0x10e0103060f150b0705030d0f1409030316030c260106022b05160609030302121302010801210c240f080103020618040e0618190b100b0a0507050c04 65
    0x200b0110040702074030404c1540d00c858041e00c4c00d01e0091040c0ca2620490030b091504441318440300c4810349440742010380905254001c256400080e000c091807551511000d005c0d03000b5040c0c1c044900341540c441d003290034144104042120184080c0c10202c0d801e41706108450b0b0b48400744503000040c8582d40300345071b401000d1144002c2000c4075107104014008016070540d4a40c0000040c104480510b00d401c3c00400c1e81c074007031130841d079000e80c0b80140c1d10090700000c8140d01000800e2b1307401002c82800780ca00140d900c1442141100c003644201e0101c146c040e000c0400082c2c01841c00780c2030f43c1d80f200020401d8080340590600b030719808441d080e241400e049094900c09c0c1100c064001280c1300000410242c145a8000c0c00c1c03043c81c0398a040c0c0041a0713103001500f200c580e05502c40c0203078084010001101500b950449008a155005081808a01c031005002d80703003405000340303015061008070b426051a02c0204001d44503460003903880c0ca50303800c0001c1150708107510540b614410383d1425100b500300303846 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499074613 1250 499073363 499073381
    0x619180605240a18050a0207050a0f030e121005091f05271b0301060e0f0f0901060b09040e010902090405062d01031b0b0f0d0e24090f0303010e0103060f 67
    0x82013581103850080080c0003401d00504e0010000e400700030a200003030b401d0048452040c0304200c0c4c1c052211050800a02080342911840e0040c806082960306c00303a000030b008503035800300c5103010809946e400392039414500c0a0f10300301c62490795081c501041c2c00c2d198002c00e114441003041d21150780300b00300f0304904080c055070908107142c00c528842610302c11103120010305050301600100300c40341e03101d4950764043c1303044400a003001c00d9a801d11904003040151071f034102c0140710090101d039040100e07034401e51050113542841a40d9482d00011004400c0d084410003a40040202d90140752078100951651802c685621700004440e200e60342100355007100201e999a00e521038903590303096680300d40c40e00d0990081c86c1840300d21030303500007100128100108a58003000d0106520f800010300450309541c01c0482050203a00b0154000941c0c1080c0280c4407001502c2e45441d00b000d4680c3c000c411b003030002140c6401c1d541e0200200119180800441d014100c81c800da004002c2084001003800446d40044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499075863 1250 499074613 499074629
    0x6070b01030212241518060112060b191e09030f0203011d01020d06091a0105030c12041a010918081b06010915080619180605240a 57
    0x1440075080007220820000101000c03600d104403002107140140c40c6500810028441250411185038480c001c5900000c4c026214501c3d10180c658840c030329406c0c0203001504022481d00c0b1600d00002980202000707241000c92242e40c2c12015950010104290805001090306003845e00510406480e031183c40c3e000700d40d5204851f0f400c690b2020482d00500b5016617043d9269441e00c07040f16884440c0c4071120f4013460005131307103445105d03000090b9903155001100152a000385c4c41ca01c00340031941c49200d00c2e02441c04543c2c81d69120740c598145e005120b9584411080705007000100003141186442041c0380010f9141300d80e0343c030502c01069942c140040039a0f040c81d0300113180000c43e0240600032040100da00c0210402e1040209440c0c172600f41e02400c86141c650301c4546d94413051048080203440c44034040c00d000d20700302d40032011105a45591101c929a1450407501d800710a082040300c080d4006014003d078100404d200342c0240030001c200014240c2c0746d034004068a01280d030981151046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499077113 1250 499075863 499075883
    0x105010503220303140f040201140a02031911031c050609010803120613110d050c120420060d0509010b03010c171005030a12080112030527190e060607 66
    0x740e880703070207090341c004103d0615450703118a80c008054170666500c1039805248031003039490180001002c200c2c04801107200e9036400c000031031800b90301004807081000c184038801d102e08001700c401c940e00e5007188840d4116020104a0225203c0f03e0310244250b80242041800180c691804110390404203128a04d0541c0c400c00c440001d0b411586009613125400800c07419000d00c1141401055821005080303200746000100c0a1182c4010700c549074004070404070742414030482d11074404144c24045d101800a159000341541d070329480c40048010a60080c0ca8075031124111003110000d0711060f00c00074215403e2512072002e5050500c10000c003014030303989017200454a9440032170009000751071052038994440b4049411380303040146d00d5504e407003000d260b01500a5a1002058030506801041c4408000540c542c08641e00400f43d40c5180b081e41030303070354201c0b011404250412f90501041c1c4d0b00401170103400901a4030a82c0240b00310b4030301c000d41000300e5480c202000315074440d0b860b0081c45007802d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499078363 1250 499077113 499077151
    0xa15230304060c090e091f151214070b0405040e0114060d021c080702011e0509060f1306030608100204030807290a09120203070b04030807031805070e0105010503 71
    0xb95000001e41041c0d608101c1051525000500f05000b0101c40102c0756a000750045000b201c4001c81032a030103141d401d4208900729009812a280000500c501d40c480701c0c0c030100302000d100000401c2c0a800103080221010035a507503031901103e8000380706241c4100e00c0e0114152a0650600a0020f06801080c0c1102c90303603601d004010514242e8a4260382291844c5440100c0c201d0040e4268465402468503603210041440014101181d4035040c01e118030b00c20702c050210b140c101c01910080f1804540d460b4880100140b466000d00506042c000e528000c01c0c1d0010780e03183c16601a105441802041c0c03000e06424580c0b00c0b060340300e5484000e1048800704214004503400d0030b09400740d004500e088101686c4103600d00c038002213043d07915104950b510550101002540b01b4031a284104c0f0380091803d110058890100e0480010005814000e80308001485030b44241d01169003003072400d0780c84040348064117003140d440d051402203103c42009000081055809038041e0303403141343d21401800d40600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499079613 1250 499078363 499078373
    0x503070f03020a091a030406150803251b062003031501110d0512060a03080a030c02010b1804050d0e13090503070206031806220b090a020a15230304 65
    0x2001100070010845400c0380441c591105c4c1250b41105040f812200380c40741018107026085a0b05890000481d44984608001c082804010b407000b080544003d0350341e840006625020400c000503008050b01000c00c0310001d40a140380c10a400c1da10075940362064684004840c0c54800c0104544151a0f40240001240d114948803002025801031502540d0707041a1001d41c3d10380a074108820f004118007058501000100c0d592103035002d50116809640f181c515140c0f9030342071265000400400d5110594003070b0550013504450304005020344200144082d1081c2d104940c00151001c803140c4c01403070f045100280c4604a16800384100900c8203070f030030150b0000100140680705c030880da41c0c002400504050fa940740003440c8075101c012a039030030b8807001030244d9080c600d0051007a1844402d8002e40d41c00504d00c400d94107001d590044000243c1c1c4c4ac1c0750845807802c003000030001c1d0300c04401d4201280c0103200c03c004540f20802030f01c0d5070000042d102128400c0036064a01c01d8442c00301800000c001c52 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499080863 1250 499079613 499079617
    0xa0903020c030304140f150c0a1205030709120516170f0a031b060623010e030105040c09020d0e0a0c0302030d05030106020d0806010516030305060f0d1203021b010e010501050906010503070f0302 85
    0x40f06c01802410402804e550f1012681c02c5800140907640081d6081c0c814800e04420900700c0321440d00e0401c1c9149006400580010000e0113425800e100034072001080000410170001d0b84808020388040c001d035502050140c14550540d562014010494640c0b5036060000d0543d800301e506458125851004c2c0c80d03081810028020142c8036103484850001c0c9000944c3d482004902c041080c1c00c1484009500241004400c1019940268500b20030400030400703940c288829034090309800b503aa107480c82c1c1d000000e8008034000060b00e005182203c02080300754540c0d44200c030710960aa85007032000c5003040d41e203800240304607000343e040b404040340641d100d4010143d010307005040040c01c05100c004101e940344e094403011000f10f80d07160b050040a1814406244a02a04940c2c52034910069a19900c0243c5110002d40034160081044012401142c4250305079a1541000301f1005e16540d0085020700030a11a0324010607110003c165507511500460344903209680b1441e407050340c950002c800039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499082113 1250 499080863 499080889
    0x30a050a090f12060c0e03281a0405070602030703050906030a1d0604060513150e01110d0b100305060303090d0c0b0f03180304030f1212050a0903020c03030414 70
    0x203124180400d000039a00421400b41200041d05100f150040c504401200d502517010382c00c1c01613907420b503039a03540c001501503041d01070740c40002e8070760040200c4403030040803484000b411546d0340342e03554680015561003180b02c1e5010700d04490078103503a190280c2e240c1c03048840140000700c1c1007024800700d0401c10011038015540040000b4541e0f102070030302d004101e80303c0e82c550f030b1a00410280000d10200d8010b00e81c03c190340c0525100500c0041d565004002c1c0621007400c03000e9181d9040002c0e90b01e00394811070b40702d40e5101c030f0141c2d11200c03a4182d06c010200080114400c03020010850901c0b4402e200d5a03104503005401946008444001c111440404040c201c1d01c1400010340410840280780140c0501b81c944070317102d80c490078690130141d07102d4403c010240302a40240400c101046a46516120603604118448101500440c048800f40c1158111084e018240418444400d2540d40301410a6019a007030f21a45ea062004041e1079200300d210304046058000c2880c50f191508407081400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499083363 1250 499082113 499082117
    0x90501180504020f060d09060f060602030a141603020d02012f090a0512010b01020708030f040605030a15150e0f100e03031902060415020307020319020a0b0109150905010305030a050a 80
    0x2c0844c55000515681c03142c5160891035490f40218401c1180c58003a40c0001c500f03c0308103005881c10841c000707503240a81d911910812400c1a0700f060854091000c0b0740180c824192054500d910710f00b0081e6450010b9841e21005618040060395089011241e01410300001c0700c0b040b81c9544007a1080e041c580050045070340c0244038140c000b64030350307a41e180807407140807403000403402b040d03001c001a0500402e0783c00f03000203800c1084468841d030b80304c00c01c8805035189401d0107070302c03926200690001080100c0d0781507080400c0000124600304082005d4186800c6503071004103e291140c1448203d03019101015006040022408601401590f42801d903140c054100c0b4140703080009900c43c9550390745c0c148009a041842404240450240706028001d1200e20551540c10041002590382c401c41d8422501c003024000c0c0010100e00c00d00c05106426003200701010296111802000241061032512400c89910000019001c09600400341283d4000d0003440c1410681a0141d5407a4400305007441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499084613 1250 499083363 499083379
    0x506010f050a050114222909040903090b22210303020c0321090c0d0b0a0c0e090412091a0412020f030604080c010c08040f020112110c0604050709050118050402 70
    0x514140c8030316581102400c03c0000480c240d14005102c080a10201a44046004d031450047c80e940880340c105c0d03560807410b8400151100742c030f048c21902d09001d41c10100c9400030000304083d001640800080c805082036403c039802135510409508000164a4076103081d40c042103038200807900a80c041c003203508490050360300c3c08e42301102d0031070b020019196101a140c020018010502c40c1003101041074034003920040103140d83c4c3d0704c8000c00c50500071b1040e18070580791090f000003a0b10508107181040c0018010220342d091600d015032194049400b594005003400f10006044006290302260700f14100c4102c1d858542031602c809058a1441c9069800a04010400506403000c0003013901c1140a407500c151604c6103413100609480d000c1c5901410441118140310105071468042c1940300c0e42402c2c603800e6500b010040001800300c4001440b04140045507041221402007041403107148250103403024191680401c4c812101d0a02800310000e0014280010620042d442a500280001d14200c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499085863 1250 499084613 499084627
    0x504121101150303050d0c081b07030309020405040302030c0c090105012f03040e0406200409021e0307020a050f0a1e0507050604090209130605011209020a1509030506010f050a050114 80
    0x81c1d00c202076503101302c001540000c0c246a1101440c07064503005e281c0381c5054142d60400308402000118400c0301c03010020000101002050b020340d0288a80c2903000c1c001344154501b81c10040e46941050b503214040f405040700d1910780c0e00d052060355060303c00507110000c4482c01d5107004014250114a044000380b000203c100b8513800c10000350004250242c4456141d241511b850015189402246040c140c90a1681c200321200c000c140d40950300001401a2a0f40749503a404ea0238031040310f045423001e02d0020a008100d540441c8403010b00703000700c0071550740a41c03032480150307912101100542a82030340c500300c41d41c00944410410600380914110b42c1c0c03258991001400b2940903600c011001c540c0007440040c5805c000e060b0800d081179038481001030340e103004000f800380848032030103803507590359030060000715034032242c80e04090f040c902c4603042805841c0c10301805090841c00140d541e4400c04000043d07000d50804401c007594030207001030410340c1c588401034403602c074655101411a48184080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499087113 1250 499085863 499085891
    0x6190320041508010507090806070504030b091603060b011b05070302091305100c0f181a071506054204031b0f06110c060304020a08060703050a0606030504121101 71
    0x42e030090024071000180c203082240014140041c0396103d410316400110421034190340013029a07003103c0d007101c6503980c680d44101d038190a02400c0522b203810881200700201c148401580403c0300e050080e250031402c2522030910700300c1c40c40211001004c0303612032203042c4014104402070503002665640d4801c0c0c0303110955078a83c00c114040b0000046556690303e47c9039080ea01155540c1c0c0100c1e01d00b0641400c0360030714500d2015846d075005000001c4071001c100701c0400c025004495544e50170040108040201003002c6025000a1081d503108051a2400401009400041441c0b0910081d4801040001c550740c204410340a034008658006080c440080858103426400ba0a600c1c2480022503550800f01d00100703007101c03600a1010050003400004250000256120384500e0442e48179850b41e6551002400395141394200c0c02c164041d02040c07050850301900b0a41c010ba0400e0f6041c01082c0c0c03150300840440c0c41c111405011809403002c10342e80c0c107000303c0d02c0002d04620380e000072410540391010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499088363 1250 499087113 499087151
    0x604030f03050721030b0f03150c0d110903010609020c0a030f020a0606030f0c090608030d0f0b0604180f0207020a060c02190609030c08010506060a1110140619032004 73
    0xb4a42c01a0004d00000c401c0754188210b80554500300d9640610b0895100800ea40305030340105021051444004108400c49840541d0380402e41306000380301600070b03240452025004800c000740250308211000c00c500c0651700a581c10704141100510080388240c40c102d49080d810345014040d4040c203443c1c0404500c00740140c2001d14014000c0d071141704401c2c507158410a03041c0c0e011454841c5410018009180080b0031545140454440420304520074443c000041a051400d107901c4480010001800d442500c902d19045404d20b108014230200403907410180d1285070300c0254000c00f03000090007418002d0920200b00d50018086c81407408910b203100d802508250881008501030f450200200700e0b094003003901a25004009001d1801d2007004540b16000e40c00d0317a41c0c140060100511400f0400b000f41d0605a10000410300c5907105407640b03c06e015106440c002e024040040c0045840c0250041c070008803079000005104041a40a0305551441a070f202598004c0c1c862041000480100720 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499089613 1250 499088363 499088393
    0x70219060204030c09020c06130507060f02100f240305030931270512091801060f030e16090509121b0606010c2112051014010309020604030f030507 65
    0x5c00140e84400c024603545c60800c004080c0310102c0100780e034080014102040c81021151142800390b103091307183e03d0070384c18028528640083c4515004001280255a800101e42080e40b4100c07050030320109609030002c1d00c7e15001c0940036500401c0360b07640600b4140c0c20200d6010307185001d01d4003901d10a01c00035035201800355824485440b805900320b45c40d00c00c1c0b11005050007a8260080e0714000d03503140e035111002c0040701001d5940102d00c0081940fa514800207503008406074101075981c440c2c2c0090104201c20030450002031130b14124000c4240c00090341203100c3c000c45080c01d4001e01c1c08440b0300203060010300540d0390380119418075441e01c4442001c0d1080022100408210b0503840d40c99900d01740000305942d0402c081c0340c150402280d031800c000c1120305151120705015900d029819500c0b07800c0b24900f145214903041c02c0101020390110113409940070491aa80c451140c000110107980306060042d52015003000100005895040090382d0107110741491814034005480b80045c00040032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499090863 1250 499089613 499089629
    0x408030c01051506091c0602131d01090c17040203030906040303030902090a0c1e1e05030403080c0f04050f030c281a03060f0102070e07030e070806070219060204030c 73
    0x14041c04a0f40e20020034902c0c007410203550302130800300d0720000281c0f507016000e035241e0904c130090300101c240301c0c03560110384040b2184500520855566107200c01c4182d0000045200002c2e100b0007c140c50031540180794280c981d6596000d0324448882c4908040d802c040d2080341d00d0704c82042111040d4a8610103000294040c1e14001101c007140c3c01440b04050008284881c002c1c685136440e003029405c08021103540e0150300540d40413000c1210140d8074001648134003040041d04001c034002c0c00c4e5021005501c954400d54404034140c48810150714a1b002c1c5131030810f400e980c01d01041c4400d040000b60411a040b00038125010f25590348042401c4032000c0e810064113078500500e5082e0700c500e0a075880c2c020b20103080b100710100010203103062907000180c055440340101a5543c030b1030341e108014690150840c0701103602ca5040c25480500104112843c145543c000d0707100004041702c0c04952144603403d80e07005800d43d01c0040b6410010000800750482c0c803141e00f0b010202c041005030603110003510b254 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499092113 1250 499090863 499090871
    0x20c0937021803010c14071401050a09060e011a010c0602040b0a0e0319020306040803041b08010e07140d080c030c070816091a120703021c120801150e04020408030c01 73
    0x400041c076490b58040e0070040c083d81c10000c0340604598800312103031501d00380f90001d640b161210720f0020580808100c002a0701d40c02d0600707120724440642d000c015841d118000030880c0d0b12019004a00345c2c3d062002c2a50b86948840c22b0314800d50081001054082c031500c401450300e07881c0d01c01151a50850b03c503c0b0300041c5840c110b801342c3d0408002d4001c5195072650540b944038401e07400290746030801080101701d184044081801c03c040011909501c10600b524004861f8a908000303008008040c03c015503403059100014140005880510040b00058402d44495201d91642d0f0001c0e4000c0d44040c001e0f200402c00e82940c43c2080c084d00014040400281c59005c440c09001d0201c07203800c0e000628814034040f8100d900c000d0201c00e01c45030680950b0060110402c04a886080c010154400f80d000b04c100c03010982021003500710f0800071803085062074401c0724040300c2101d034901c1c02d018101191800c034201d64680c500888280c070407814001d002510b8103840740e54590a40c2c000302c000c030b41e46a4507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499093363 1250 499092113 499092127
    0x605011e0b03060402070204021b01090c14010207090203101a03060301110a1d030705030a03030b1c0b31080a0e04020c0c040f09020d12030b01020c093702 68
    0x204210040c925411600e034207140c492440d510002e00003620031580020110115107564041d500c0344030300500e0a2950050307684c003150203440790303a00803540c202c00741e880400c404020720041c16100d0320603801011494103040c89131000358400b41c6a0580b40c0516900041c8801004e0205856182ca4404158603428180c00381030039500d00c0155131141c10005d0101c050501d07400318400d0b0038444002e0005100e403c2800200317041c0a15608043c0c0c141c06071125950905405800030341140b00c00355144092008414080700720150540c600411005200022500c01d4481052152070a0744402d140302146450300703440390283c0043c840c225002100844c01c040125009502458103100c2910250316080d1119102d42d1141d50040701940b0903503544074040301000380c61f0b1005500e2036002d001f0340168002401d00880c000d40b4601c9260009080001d07840c0d06503c0407804103024400901444035985034814906002c84800702450104106203103600320140380b001c0c0d11f6120303803210000113aaa0074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499094613 1250 499093363 499093379
    0x2150a0b03160815070e0120010501150908031e0d29011b081611030d17010801060605090f0d061a030c03210309030d060e010f061803030f0507080304060501 69
    0x1d00280311249200d003130400c14516004204025050340034070380842e41d01007a00303c1400282c115a1001902e41c03071f1000109020b141300803858070102054850f6040203a03207240040e528840c0f1100d290105007110a070700c50700e048010150004407094440420081c9481004100c0c4800b0382c4443c0c410070038902206007555801003800400b81c50300070900d800c942d2140e1030301803c900c542c3c0620007021103014000c009004e500c0c6141e07006048001c041d181402c0c1000e40007850181d0b4290110680d0000300c0001501756030500c035000845800c1c0e11018100001c4134100710550410b600820b070000c000500500000780d003403003080c88403411020401c03070b000f00960905143c01c0000110394081c5c0d001d64401851141581d40e0710760700303600c0c070216a9900da450b064810300714016100d00c10480c500304140403c004490032401410707100300d591000b4000750344240440d0624008540c0c0d00812022400a1010904c203840000945500303081482c60800142d4440c41194800c0710180c445603603c00043c04041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499095863 1250 499094613 499094623
    0x20a0c0605010b0c0a11010e190e010b0a02060a0c1106181c021f0905190b0703091e030320070c08030a0f11071206140106050a02150a0b031608 63
    0x20242502540c01c000400613601d43d0341d011140003034100c441054401c11941c1c801d0890003130101e4050807206001e003000c2003070080300440d07018015982c110b0b000086200b5404100b81d40401540c0e500405058444c1541d250082c295041d01104101c00c44100441403041002440d0290404042c02e03903003030f5034411040d41807100b20650b41a0f04914a11103401450b400205540002c0740001c0c5480d41d4514541a6802002c103c03000a000d0f004505400c000400e005211200d800c0c0100b498241d01d03503912208804179103032884014000401c0071103585040703005016142c0c40620034240000c1d42041c2020702007240381408180164440b001801e80c00300081d03c12001c0c02016030b1401182004208007001c0d100c100b039803900004210250000e21a503c00800ca000b0003001c400e50034074002c003141d042c14030281600042c110f404503160300000844a00c1401154400001d0364064541031004450101120002401c3d2141c0f1136140c1080c980540e6060040c0a0100410446507511710703d0400e50078246 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499097113 1250 499095863 499095869
    0x3070e0a0b04060809010f06032001140301090203070e0310020913020915070323030a0c1107150e0301061e0e241210232710020a0c060501 61
    0x180000c0300c0c0801508008000b0b45080d50418108002c0e195550a04280145130024001110720f0078030100005100840c140c20b021002e2110204803640f84035030040da032485501029510303003502000108001c0701c00e075001c0c60700680d1070f02d04081e4a10343c1c400042d241400c0c51010b408510341c000b403090f00c1451f00304842894011448410340c1011800740001d4107144003544000040c20700041d01c0d00803d44500024400658100c04200c145041e10304482420742045501c80c0711103107041e131645400d03400f9180b800c2c0b0030030404c0010b024842c106a00f1485856100201c81d0170700071a410200f4a0fa603003805028080c054400c4400112007128611411803034269000b000010000c40500825525010504001c40e5030840b400300c0304160400499245e108031260b00296000cac4621302031074800c0c1074000e04141c0400d00e18050401c4074100b5030703031100c420568080390030161918201800c030201390041034510842809840da4080f01c40e144006030707881340005500240d010030622003000342510a076805 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499098363 1250 499097113 499097119
    0xf06140106020606121501050d0503121512061303050d061d090115180203070e06070c050a052b080405060a0305090d05070305090415050a030f050111030f0f090106030602040b03070e 80
    0x6c0703101480401900085e045c001e00f8014540080b40c0d10502c0002c0044409200c11406d03011030900d00460b011200c0203201024a01c242551001c0d520380d8500022803502a0300e0003030700720134030803140c0e6016600c0da80616080041e460b181c0d00300188071445105482144225100b00c20058500840c5803821100302d214410f10482944200740316036000c2031030103030740807403400c1c0010703500e407242181aa0440f4100c0e5040e644030200244020070440c40f41400c03002c890302514068469034070341c410040c074002040001100c01c1c0110032449080980294480c25a0740145c0e4814901a1a400400c95640c4030569a4000c607450f041402103580c0304119541c1d8203087e0345071813801c01007183d038001d2107803041c03001192142c0d807100c0350b42d03d51080382d04c5410000c05005285020306d540c4c0b0b250545066083e404296115460402039030003603c1810300701c0e0710600000420030400e6544c0030400c0ca000710049c00301b008130343d40d034980032001940701c0c8003d0000c2c205070342c001d5451b0f10340f9500081400c41c00d00c4541740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499099613 1250 499098363 499098373
    0xb030d0206011203050412030f020d031a042712090602030a05031503010e07150206100f03020108090321010e090703150f200405090f060109030f0614010602060612 72
    0x9001640464035905456410710651034001c06818102e40c0c034081c42c1c10024281400c000c40c18201508212000d030318016513002e68000303140c0174078241c003101c4d21048460402a1701c203055440f14a8198001400b0103001c081c50f95070728903a2070308203182080c0d0f00d40464541ca0000ca80540780d5030840408001010b0358030065191028a20b4001c0aa00003e0000b8a41c154078245074000c554007900005203829002c81110781e46943ca1200000d546082c0c1480c00240c002d04010925815114009506848071040741407000c0e4036540c0110b03007007100100440c400303000520212103002001040700040304400c1c1005c04070340d4106800a1b080a601500c03161007944891401c100080d42c0002c1c5800440030040001140d0105d011072001400c803284c3d003501c8a04440d4800e1200c514008041c100340d480c182c5040c4603940c2d50641d19201c1c02001c1d500399000c90550a01000003a0341442210f010f41e00c031702c80206d410b01400c0550005c0709820307002480035030845010441a030900f4030041c81c5141c1c002d00100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 499100719 1106 499099613 499099633
    0xd060b09090102031f0f030305130e0f04030f03050906040b07050405041e051003260715050a0509030918040c0b0f03060102070f2106062303010b03 65
    0x4429158617a910b0510402c2c2840d81d0584d4070030a43c0044050a40d1003d45141d008584882c110900c400ca000c54640505104140511a04040e000940c01d00d86005444d04000740000c07020180303001c0410204440014243d504150000380100e5180c6a00038121801e1049822131a086400c00c2d0f4600c2d2a446000701d160850b0700880d204102c01c1d2180300e01c0b40c107062503920014000b0304030000c4844e8814403204110031403032014240c50b450300f20340f0796030a510044a00700c1c82c40040d61764403c110803802680206540310b81c0c4034018502c0c001704000061914544c0c2c5c18200601c003034130000a02003103400c00e00c400117040d00d10320041e150790344003181c1c0700c1c20f80c001c840050042c055900d0000300400d00301003440682e420304c2c250404080344660910f0b40d4550a4009440d10758842000051956000c09048244501500b5640c4111024011705080d50460a0b0090095005010712 = true := by decide +kernel

theorem cover : BRFrame.Cov 498920863 499100719 := by
  have h0 := BRFrame.cov_init 498920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498920863 ≤ n) (h2 : n < 499100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
