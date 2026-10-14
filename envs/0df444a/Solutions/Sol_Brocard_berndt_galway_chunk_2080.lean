-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:32.590517+00:00
-- url     : https://prove2.me/submissions/a4225357-bdb8-4ce1-a51b-5bc658c0b052

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373920863 ≤ n < 374100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373922113 1250 373920863 373920881
    0xc0d0212030a0b190902041d074d010f0506060a0e0105120a0c0305180604110f150c1504030801030f081207031d010608070e040629030606010c02090604 67
    0x702c07a4100c01300000080381c2c4209030180c00ea502c0c0068032180761400703072a5030401021980b01030301485814460031035408410183c0103880e034510600b003030004c8603d1407500820b8803c0c622034803036540a4410700400d81046c04000c045088024410380c0c0003c5110310448000f9a020f40d072200d0104500c50216010710046c0b80d882c4030505009040548409501d6411907013111310307808a69440304072045054251280d217400c104100700103200e1f0815104042d90391600a0005032500d000c14103035100075699901240c05a80c00507003541d602003010180c01865400420814444d80a1055940d2044103603100083c4616095a10300016074030310b86900d030180d05100740039a10140100014a0341c4180032030801e00402080c0d8001510004202000d4003440b941050f85510f0f0f41029401c00054100241100554440030b03d440a6510b4601d046c5005000e010000e1007004404c41d10250004100d1898580c03241060b070035510340d503a9100044035441e10f03280d0000d61050040021410900b8258880035031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373923363 1250 373922113 373922119
    0x4020f04140408041a07050a03030b0a1220091b03040203031b0d1710090509070f06260f040602030921090102100501050d1506090207080c0d0212030a0b 67
    0x6400110074400d401c01c0088400b03591a50b00040c1c204808a2050030700c1c0c03001e05030050b0f01c506001c0b9540d00c25880d00c1404c0e42c060308260f25074201504c0355a4900442000f8551541d140f0b089980c14540034403100d04003036161070300e02c480001002d00ca040980c3ca8034400c01844d07404500c0500c544002401e1500b006c0c0c0140d8140c4424131400d9820000406c11141b21010340000b0035030f08a030600f000701120044404801e624402d80c0038070100c0c041c424418425220307480c8000c01c0d103544400c9050300c2c200250b8001c8020101c8550000f84680e0002405840f500340c030301d82c1408034191701107100c1c440907069a83d0000001c1d03040c000f60110302c0640c065600000c0c00001c1d109a075102440b500c0b001c11040745030044500380000d8a94603503804003c54000c26a010005200561405000400758008a6000740018058000042540c0c07074503402a806000c5080c8219181c461a0078111041d03008100074030f60610130700310424405030002821441c00c0080c0395034180755949072042d107406002030640442d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373924613 1250 373923363 373923371
    0x50d0606030602070803090606030a121119080a11030f0307140d110d0c0305130f080c030f040518040f06021303050f03070b16050a08270a0201030506030d0804020f04 73
    0x400121240004d0003c42d01480c101d94580c14241c4189007000c07070203001c0320311079407000d140407000170880170758000100d650b42400499824100051410a0b584101481017610b054504108000c103400180043d640e49641d031101c107080600040c2c0e1f40e407107062480e04070708406000085010b4030031040f060074080d8044629003032141681c071a41c103447d941c0b403542e0003084021135030000028982c401c000110046181c03e0005007400d207071004841d80b81c1c030b0010b040790703000c443c5007400c0c071195a00310340203c03980790110307a0781c0d50740d4003400e10554010380a614810703d03060101c204a030458809160099400c462482620001590b40c800298401c414040489104603000404201306021400c0c01c8010034003d543c1d94110381c90503c08400d0300031310b84078807980c6844010504580c418156100c03082c00d400d040e001e540b0f0b00c0d441c160100d0014005261481c400c00741280c05100007040150f40d00b4402c0c0c03400c3c0042d80f01e02c020180c503484407010b400700191080300081c000d40740180c2c00240501009d40005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373925863 1250 373924613 373924619
    0x406050606040510081902070c0911130306090201170403050306040b1f090311040c0206010e0402010302070f151b020d050706060504090b0f1024030e0f100e03040b04050d0606 77
    0x30758805601d141d1360081071881d410007403450a40c1c03a0691584421450441c41c0600036a6000c3d200d1441c1e020705181241d5880b0400a041032090071070311032003080c50a410b8107e641c1d01e06440a0700006208900043c8058800194503c600c0ca2080c081c650607100c45045584d90018000101498140590b0182e41c1d044e0f5480028003450b10000170301c0040d41c8110f1014150b080285080402001140c000c518161071000031030b5012900f2415504504890105912140012006400f0300100038105100180815007048200c406501f5240c1c4005070030700c0344d4000005000000d180340c20088026030000034104810f244200001c0400b64410900020f201e6200c1d8007280072a05c480c00211443c0030b06109118850b1901541a603000c4c54405100050b1420320804d4510381240f5a4440a03c000b04003545050a00a401c0482046907050440e4100801607040c1961040910b0280031443d10b89100d001c020480481180e094414540d1400d140030316000030b221100b500050142e400b0380e42d42c0c0000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373927113 1250 373925863 373925869
    0x41502070b030a0e01181a0a0902061c0c020a031d040f0e06040219050307030206090d0611250b0c0307121a0a05220522050f060601021504060506060405 67
    0x145003e126040c000280c1e05002d41186806c41d01e10382031024196004009080c001707041c0030540e10f082100c034041c045d003036250215000003502d1705050095104401040340f98107000d207492401c048021a0b94103000c201c120340400c0c0d0b11440843e201400050380c2c4120302210460606901d5401e0602420019000042035207941c01c54a0a14041081d42c04c80d20501044d4a80040f00c01c1001001d103c0a4440f40e1821001030399460030703807000038010740011521448a07500ea4500d400d02640002c0300b0b104c062561044011194094500d1952030028410a21440c80316401400202540710728284500d4403481e01c100001c0e00010204400c2144c00701c0d041d001c201c0f0794010b048094268400c050a902114400c004085460703400803802034611141c220410803110081480d8451800000074458a55402208118003a0b0498005c500800050790b01001000659104042d41360810755083c3e84860004903207a0000c0001a00b0116010300403c011580592110b038200030020b003510710b071075903075404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373928363 1250 373927113 373927117
    0xf010902160c09090218010b12070318051005090a0302030304020910050a150801211103160b0d06050d0206120a1b030207050105070201021e070f0b012c0606041502070b 74
    0x401140c3ea51034040c0c08045041ca1807802c410300c0480c0103200210740c14450f50364528020b00c07456036002c02101003c40c82240c000d510105d030000700c001e808000409a42400b59445590804007004c0629113400201d0080b4042100703e2656450341c041c3d440c40e142e540800040850141c50800d01030094400000c882e65010400d00041a03800f80e82260381e040d510380940700d01c5051f40f110380d0128042005002c5449801e03103821404c0e07808012403404108800100303207041da40003008100c0d1140c01202251658084014008000c0c01420901c009511035060000030410718400a4000d2020b0180750b9800001c004026405200301800080749103034040a0a03210182c01185000300340d0000704103050100c00c0c056154482c0f8140001e41c50180423031015903906c1c2ca18001001044804620b84041080d071102c2a0300b400c1d001960980556103070b1041310810b09102c26010400a012294281c00c00307480c0406502c20b81008001c02d00341450a4000318006040c01034180031402200b00216040c504000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373929613 1250 373928363 373928369
    0x10020a050d1109030105070c111c020111100507020a050f0c03060f0a0f0603060504051006050112091b08010b030d0e0603150111010c020d0201180206181504030b060108010e0f010902160c 82
    0x280741c2e901c161045c1072504103000903628003406030000010912b500c4c412074280b002c5440e030a282580003a4003000c1000d00300004d10109007402400d2070140301e6900d40c0010118000c4c0d024009480f480ca807002803083d0b69481180740560150070500c0001c2c1451280b9601e0340d03006a42c0100441c3c81107041c0c418408851080e0801c9508941c1e480520042c05004c00100da080340f080d010030070680e410800080c00070600c1349052004031f61134070700d808100700c0302d080c0f00c6015000c0c5031403140b40103840b14a2140a00341d04184c1c103010707100760385a51040c0307845a0340052410801811140c07458641d20384503a940c103203480186050240c85402904c0030030b000d00c03c505400c007165018207002107813540000d0940301c110030b17420b08070180e001020015a840104441c000d1a080d68654080e00c0c059001c01c7c41960001030800d00c0480c04107000060044121074580300712002d9850f000aa80c80e60f0f05048244019a684c02000c4100c40040c405102d240c0e00502c0b00500c21001000e05c5081d0b690341d50304030100b5130 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373930863 1250 373929613 373929617
    0x40b030a050a2f1e040e15041202030f04140d02060a21020c120a0201110c03040303022e05060105090a08030d2712091503050910020a050d110903010507 67
    0x40351681c0303c0200342c0c40315002001c184004040a66a000018804900311680100e80131307442451203007981d202d6110010070071101c0c0503189882000d050700741840030301301c800f40c504200b0f0416080d01c1c1803000c801ca90106403030180083c109070501030041c84500316041a2074020820000d203070007581e00d804c082c0020704010317958120700c003500d0b03152045401c040d0061004110f0050001d0070f140308000c01c0c1042400401c01401351201c403142c000328050503510f014914100800100c5c1551104013000500030b40c0e000fa003c503001c405515070a5582100007207813030702c3c0081c88041c00c04000140f0350081d540246051400303d04000345000010558030390703035002100541c00060036000810301c44c040d07200302c000785080c0007100401d4015a044071201588006004150030f038003003012a03008050b95000342801600c9583d004000da44007500504084d01d4001c0c4078411400c0fa042c4006050080750180c80c035554a0301d00f070403014203252015148812503600442030a00c015000d58400b403144501c1139241c0d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373932113 1250 373930863 373930883
    0x622061d06060a060302040513020f07020607030f17040b0c0307090b0a0e011d013f0209040506090c04060e030a0203030c07151b12050909042a080c040b030a050a 71
    0x5501005605030b125842801814011f010402c1951b0f900c0240181e00650140056601c171184003c0301a18811100002c1d030000c40800c150003455400052000b4080e07190b290098400e000c4040421141c0c0c0485005140000300707800242c103001c0c180c2c080c54100400e0704015030040c3d00d41a000c0800d810054000000900350001c0c0303100c96a010350b004281003201582d02900c6540c00c40001d140184021000c4c0c49030300c208082400d2001120160350801003018812110402d007500440d000c0e601400036644601e04020100e4614135042d0369240c0201d0915003c03d14003450210141e400c0319050540c1641406000800e20243e1130520050101804800281a40da411b00c0c14100023185000c9030b050410105205000e841102c0350406081c0e141c0090180301c103400c1060301240d6500ca0b113942d00f600444444180b0007080718500909015904822034039070f6230250501c03841c0310f1087c075204200096201c521400490304180e44070840f0240c028003a50301500103a22100c3c41d060003407008407024080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373933363 1250 373932113 373932121
    0x602060a1409030717070f032f0c1c0219030c06050406140d020714010902090a090308040b070504030c030506061306080604241e0c020622061d06 64
    0xe2845050211440c12210422038205800540ea40f0b004500c070081032040f20321507507640e01d02e52405440440c0e074050480030902032145030046c03450050701e0b603000058402401011260340c06001402e40b00406a0003400403101c0314007004840710200701c1150001d4200303040100035807500c3d0302045186010510500b000d07848c500c0c0c1000f22160301e602890401c10f080c81b040c00841d41c42071441c44894044009186c6488070071203400020700c5125001048205260076913000c405040d088001024000c8a406102c1c0e542c05101100baa4907800b030060000d08880c4c005400120842e00040d005603242c41c245051548941d98440703202c1e155001034440343c1c412800c10896207400c00c400d0031205d441c000306001a13443c1c200f250f50703100340c094001404101440d44811400c280303072110b052400e4100230b0622109032482074001c041080764510040503030030120321443c940d00010f90140035030713011100313a0150700420f4a0481c5400b501c28040f984a516101d404a080b2290b01e40031024505401c041d00840c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373934613 1250 373933363 373933381
    0x1103061305060a0e0a060b03070f1403060625050a1a16080a0209040e070f08010b0a030c2c01140117040b22060f0207020108090a020d150b0307060206 66
    0x1a10203000d0800c400c0100b65203c58181004992042e81c128050f5240c5008003805803000390000b081c0300c00040100008030740d20a04d42100c19515498640d4034070041d10130124284011aa4aa00203d0400c00503025040000390002c0048003200f1003003c9002658600307052031580348040c0c4a042d147e0180076070007200152155003001d00c0c007007400c4603108200005405240d008100f0540300350f0210300070501d03840701c1c0c20a0b182008a81d09072803e041d00c0d01072340805102d9501a0b95103940c0f03400095691400c200040106aa420a41048809242c001008a4241051001d1606040d80c050000803072500700303003544c040c003281800f02281451480c0010b20840340202c440910b00c0303074542844040b400000c10346412030354034050000a03081012040c400490301300002800a4948501b0520180965014181461007640d840c8080d417140141c80c5e6407898015070107984840c1443c080f900164100181d04507822440502040c1e488010b80002c2c1440c140342c0c40000560091820440040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373935863 1250 373934613 373934629
    0x40b0418020412080d0b09070815040e0307080304022806030e060f16170c0405030d2102031005030105040606051507050a11040621110108060904030c06020d110306 72
    0x20050320011410b1519103a810036510070b00302d8018115850009050000540d01e801803102054003a04410460810400040a130b9208a403555180a03649250f19410724142c028580030a480d0f81c011801d150301c0d07490b21542980090012a40000780b80b5844055201034007c80350340c0c0344281c40b070401942c40c080c0003074260303014160345001c0707600810208200002020355241c1c020b0b129410301c028107490340c071003511801c03e1111840c0f04140080d08010025480e18001c006540d001c3d070984003031091503c4141c0d4800340c8040c10001456080c030964100c83e440360301951380485408982c1e03010b01d550b10007180c21590261406c0d20350580300c0e0418002c1c2c5c2030248848201d010383c00c2c207040c07503c802d41c1c40e003d4669030940310082444664010f02c030a1a5165003010010300300c1d4a0b000d22030162210780c907422800300c5c5142201d2001c400d200c0000b156000e8965a8810200a00700d440f542d5659541203400220740d60044a1b02d036030a2044d45070414003440303140380d04031140340960b07540d04050040040321 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373937113 1250 373935863 373935899
    0x2480a03080d0615170703020405030f01060f05032d100c030c08070801050f0607020f06030906070801050d030e04021c02030106021608190f03050c1207060f05010f05060706060803040b04 82
    0x40e500c0104d81d0f81c50035a006521079140c4802c21800c1c0b003d6241c500045000c0d1049a10040e4984295920103044030380641c4a0000c52743e494814034412540c83c4145501c402d4058003402c140000f02c1c03002c040c40a14107410550310410034054600c3c488135455400304880604119200095a1381f070388441c140c0d00907604682210890514085640c588070001e42c0b41b80c18104082d001e1000803d480f8215216913031000c00c040300050420b5220b01c0c05034031107541d8160840d485000218039500020302c5003045441e90403242d0301561440e484d44922010700010390310070040d16002c5020004411a11001803011750302825040c1e0141c4107040e2803c90409070b030362075600a54135a40020501302d411940b206580f40126602103684100e006407800c0a54450113600c0440103a0702885449070030f0a400c0302d004000e81c80c4030b200200419040720703442e001221402d0284004540b0510800e10041c81c5c0040a01141c600c991070101e985a1103013109403d41c1c1159201500028000c1000e00c94414080c1c404501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373938363 1250 373937113 373937129
    0x6060105070f121d0a141309200108150a120f060903020f3307050408150106030f091713031704050102210901051b0d080702480a03080d06 61
    0x1d04142802503428080340d46c1920070440322030010030111054100e406001d420062034100c0d076804c0c00310400200707a0082c445002070065000101d0320042c03800000580b0002602d0400d119062a0b10340c07003180c81030001030b01c12102d6502810006801406034090b002d10075806809109100414280f4116000324000264245100341d900030100280c3d00701c1d1114001e030f02c144543d49401c40c003071700c13039101c7c0b6000b9081074052142922401c03003603e40a241200e07102d523010442c04518440c50800c403005848014076004022004d00740c100c1404000d420744001524520502e0f903981c6ea00d1000d0f181450982d16400300010070200140c2da010b0014840c41c04e414038200040c20740b400c2c141c000910a0385c400905001c404135050b0103441142d0b0b42c0034071541450040f58000044000c01070b108410840d842d00041c80b40440d01c01542d038040c0303441211401d0204045045031b000d10012196000010204050702250b2a008050740c0d4440d9170030350046010b48610740d5074200011022044d2109a000411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373939613 1250 373938363 373938379
    0xd020909010b190e040b0705091e01090905010e0f040213060305010b0319030203040e0a020d0e010b041a0a06081504151a030c0702060705011e06050a090b0306060105070f121d 77
    0x400d860002c6000350303000c3e81c4062485187da44400007034900b40039420b001a0040780b10041a0850200030560705c000c488262100220300d6074070751411040d1a001d01510110b100f0000200394242c01c00d0900b282c00c1031000340000b56072070707101104001720b962951040d50b0307a17915200860303101c3c202808070f600385000282e241c15881302c071901e01940d640300d144906214030724100f0000d0025019581951070030003006105100d0000c2e4402c41c58081c0c21211103191080f880c1c0074210a0045804449034800d0401401c180c24403450080c080d521214000d01c0e0540d1240203034021011580d0303600c600d4010b41e1685074401d2a080c10110703142d902c007019168602040c07000300300b80103a07408071000742c44100364111000340e503030001440c0c914090091a00b518406800c05006180d4101c01740c1c001d40f080e5441641c0b4600f02c540c1d1260800c0545120040e002d4040c5c100c140840ea0b15480380000b4008507009000f00541065240d4460403031881010001001601c028007440e401e50745004441e052000c1114091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373940863 1250 373939613 373939619
    0x304030c1d070f230322030e04150803070c1706041a130c0602030d0b0303040b0a0309170c0318011112031b030103050c01080f040b06040b0d020909010b19 68
    0x1d844020140910341070194020720921418807800441c20400c164001800c0e00312099402c8402581082e50000030100c29910b10140c0031801c00c12164a181d01544c03500403841e9260706010080c840b65485242c01c0001803c04200188104024a28507110b0002c040c0ca0030710b41003034070700c0c0580e181e07400140c141c1200741032102158050180e00ca4051150322201c045443e031902c0400d100b803250070018041c0003c144001003464000c8090102000c04105c148401e000c40410907840e4410340c0101a001c0000b80641d0303141c0d40c8243e000b58503040c40303201d803c0212001da0864104036080fa1071903443c541c0c400140005a04244091040120800e007468008098010305c501d0b101c2000c3c03604a8108a400300c00112000c0d900c0c01000408488032980a0766541c49042003502d582d070141000c1d02043d03820010031280c0c24202e441a104d03640008002496407601380c104006400c203011426403191503010400c0c00b581d03444002c180502c0441c0000110000d0003014040d00309241c0004a2510712400020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373942113 1250 373940863 373940909
    0x50303040c17120a0c060e010510050105040f090f02120a06090b0a0302030a0303052a04051801080601360b0a050603160806190b0409050a020f0403030f020c120304030c 74
    0x460b400f480000c14032a04d80304c074139008072100200300d00c020b4111411310306041c40522040d840799001d07001110407a46050307211401580d0510840c81070035407400f00185c08000c0c507240d541c0000290075920030090b29058000040644200b004d4a084139066078a0004011002143c03140d015034946c1610011210307480c40d00000d8031344407207020203018152603038000346e071807a01d140c858141004002c004407403d9100c4e07955592150840d02903c2d005030114295081c8000d00602624102c40950f0001c2140ba8205058105000201048883d0510141003280700c10b821400b0345000301c108029000488829002c204200d54000790b10040c092401003003403045400350001050f80280080c02d25403ca91a031501050b10030f8000c158000c84e014152802042e00c0c840c0340003c20488111080074001c40d299124050100d00c540011859503039420001080040e003d4100307400761b0030560040e14a1000ca80000c20f0190184040700c00b855040010140104610150b002000d010381e000c00c4c2441c00000c6003a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373943363 1250 373942113 373942123
    0x20d0207030c0b030a0e030a020a110a1412120a08061e030c010c02150307030e1501050303030a110d091202120f09040929040605010e240d0f050303040c17 68
    0x8054020750001300090040740e0341d0304004142010170044036540d2003040d078000d4441d400c0500c12202608a85402c0a05240120000c0151409411813401c44c080c201c0c10400707880034844000c813003401031600e024a80b1001c400507100040d120703101d4032040c1c54504100a11035000111a4101d00c3e140f0300340d80e2054a00041110748000282018004141230740001400890015100704804100004011249a03d508040100c4045504032811070828002650580b2024041d950301039000b400004d4500565412035170702c80b0b1082001710301c1c10042004040a560640c502541c4854000840f0f00d4005d074104014000c0701d02c245602424903807002c0d09090b2600c91b22001c0d41c41651541c849005204402401d921610f20301c118091201c01007107518800e600d011142510164940000080c0c07007101c4000b403a100706240101a40104241d8400d01d004081d41c90f1400d800c580800380c03042c00a80040340d401d100c24040c43c003c586034641858402c06c543c07034a80000c600c500c00c42810180003500007074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373944613 1250 373943363 373943369
    0x10605070c0e07020f06090a03090e04031403061201090f03121a04112b0605010c0b06040504110a060903060b030f1209061c02030a051501050909060303121006020d0207030c 76
    0x10381803200c3c0c68550003203182c0400d10500030b5550065805010b0013040004007503078098460340302d5052040e43c420000f06c488a040b038016000c07031100100f400341100300c00c00440c0e000d1402810b0010030070300e06800c03e086802c4100101d40c00b4050302081c0d8141904041d2444076280881801d004002d500000c5d502c10202c0c1d104d25600840e1217030180302031102500161608400e2402101080c8155000003074071040d001c494403e08a49005400704e8254841c0d0001089242c1007002482e650f142d52060100030440103100340c80e41086811300b8082035441e607000500070300744e5689507651141507082c800300b06c5224002580c42540200002400d1800101c0c2c64110700e0030301240c0544521014020172070b04c0c0304500001441000c5031400c01174a5841c0e43c051406088600020005540c484083e0340001c18119a07182c0070034010b211201161400d4000c841e40240c0c041e040d01e007000300c0030410284103402907900a030103051240042c00304603410041c048a00b941d91005203402840c0d5100e40181d002240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373945863 1250 373944613 373944629
    0x2a0201050c010906150609060e09011e03060c050d0b040e0618070504020307050d0c020a080f070303200415050f04090e031612021002191115040b0708010605070c 71
    0x30465088000c000c0d4403c0d0040c5030058010700400d01c13188508444040c803802000b001c5082c1c0400824054882d041800640c0c8010b04140c01c00e03400c0400855442e0454280c61120f0011004088005a01401807107507401c00c070f0b2145c0b5120180c40f503159060b91045207030755000300d16248155600900000d10582c0094220440c032903840c81514803e0b08001035a00950342145c00001405060380d409001895a904400d0302084201c00d4068105d0b2141022540949159410f00449021148140c024201c40b40b003800c000900d1a9400381c1040400042c0c01e01c032880c000c0202d420450861115150880c042503464072034944204018400068096806640241c95480046640c0d8090810890743c0c900b08910380040d0500e07013850081c00c0302040e201c048006000b101001c0351201c00318003d8a14011440c0d91101011506c0907046a091554200b02000c601c100c1401d00100c0e18a004400d0107503000f40c1c0b44016a1810300f0000d0094141a4049010000c08201040108500054406c03d0321818 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373947113 1250 373945863 373945867
    0x270a0305092b0b0702060f061302040305071712121501030902130507031a0a030209090a08030901050f1b0334110714030304210f03050a2a020105 64
    0x80012503054007540d42080c1502c50b00c44801001c02d09280d81e10001c46101d08141061903440030012038680c02d041c1c40039030f000d4130b0450201c1d9041c0350100d8082da203485000c0005082c40e60300e032105440c0030115406008428080b00c0c55491600e4280284d000211805185070301c1c003910100c400d260316800030142c403c841420750b03e4802e580e00c00d401907410603400600d031f6000d00c44224107500041c0303c140d6484011a180070a0920b0791004000410101c404c0109200102850b580074495a000001c1126600e80101c1d00343d01d000074110005140118503042c000151454111108240424098590031401e240c071a040c505000c00001225402400c0882d0200322240040311490003c56181c210710641c5444140701425503403120010a904800d00105c80d04240e6901e9500c1815455000c0130741c15400c04c11003485407502c80120740d001014204044250300e902d640b100006080d0f0428200c0000c3e100154640c80c4507070041e82c2c14200810410310703003059110b12901a4190042c028000c1c140840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373948363 1250 373947113 373947127
    0x6030417090627031006060c0303050406180305070308010503061b0d0b12032101051011070b1201080d080129070b13050616080f0a150b03270a0305 65
    0x501001d46070700c42c2242000012554200c068a5004034401d1103e9020380303e07000070039404490318000e034070440d40e0319200c044207a046902e04402406004000b90341e10354868105030b80000d013810002e100704d8040c2c1da546480d1080d5190080c45440c060b401280302307500041c2803110800c40421512450300d48550141c5d6241c6a12400c80090010702030280c2c1d01519001340e0f1610f240c0c010005081c015003c0c203035030410b081c0c0c07003000c50a024401c0c0142d0307800c00171411b98030401328007071f1a95030344018825040b2401c29603581a04441030340822200000030384840d004118000c03040000f00807540e60b5040509582d07042980310202c1600414000c1542d44d001806034540c1880b200403120901c1d009681440d591400031610419882c0080c4110741740d2040174005071810300100d0840721080600d5070360104d5921094240d016800010700b090320344554070510b035112000515139003001001d00142c060f0712440d00241c03c400d43d8248110b1080100150001c0710400c62002c44ca080b515603043c20a0b5407900c03c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373949613 1250 373948363 373948369
    0x60a1203020c150408190503090111071205030403060c020d020d03020a0918090b0906090a0b150603040605220c050d03180b0702090c09012012130f050603041709 71
    0x4464003010f410204a010642a00800a00900c1960a050101c0c1d003d03445006a61a142c0780b5044080c042d0b400c2031111148961082c5442c0c4581d0007040d048681164440824081c80e88a0100c1181c181d880081c040003000400d000b68510f00c5c8140c00a4034400c0e03071500c0040e4480c503021101c4820503a0005d0050300890142c21050080c10b4100e03c0500441044148030005007580c0c5001d0702c58001c294001051404000340c911b102c0c040032409001c0d03204d410782c4c4071040388002034091100782d6071900035000140c55850146105600655000c41c03d410200c0c003d0b003a60100b0049110061103144440020403c098a900221181512103940034142400c08a5149104844c00b9203058003146000a14180d000301414030f89000702c1e44541503846980812001d40700d44070003580400c041c0303040e42e401031080148050900d640c220565085009511180110f90301501103102e040d090001d0a01c2003400e107001c1403014000541d90103145003001e80300c1b800320010001010404120000b08258192 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373950863 1250 373949613 373949623
    0x1050315041b0914150d06020d0f020315010e09090d0503061f080f06010914010c020d060e15010f1406030702070b180108060406033206010b0301031208060a120302 72
    0x15012245810b8855200d00040018081c0e0301403000c01c110080c400700301d1034920f212101c03800070380007004c41540c52041da41d8040a504165102c00c1e031969100801d4520364100d0004500c100042d96200300340011440015001002d00c1036158007034040c03d030800001100000e5048a088503d003009034595442500165240d8000d0b5081d0862003e00c2c682c0004540e084190b0314016030303800e58001030750307a5914011903083d00244a00c115585400107544110b500400e03842c8035076400540302562154281d1103400036110b171030204c0022540441400d0060048060700ca07800350523102ca00280b801d20f8004000400741165021390703c180d10000c00b040e0514000c200f020000c28800200680301d040402468486045100005010428110000700185413500c10700e001d9036407091010b03080103107842005000344c120002d1404441c0185030780808415041203002e0003009514545a6a581146000c001142650241c54140b110041c20300689031b44118203a0281c40c4000d070408014481810201d20b00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373952113 1250 373950863 373950893
    0x10c0305360a05150f060307150318080a030b0306060f010305072001020904063615030b07140a0e0f062106030c031f02160b0a0c0e01080105031504 65
    0xb4860b240340581003100102d1a007040c501042d04400495458101080d20400c0c01c884c2507500d500802428896440886d003400d0350b2a560f031800046a50300e40c07a40c44901624108103984044021503c02d2401e68980288031021600f64082d0285040c6000414881e060103030b6194141a26000050300740380c4034a6030f1001c0b882c3c0c00107641c401209100c0ca070034003c0d03120090540c0918105200840d01100c0100e69103402041d1824442c140300d40ca401007081c0c0c50200d410454001c0d150803101800301c1c0140c183d100991300610321000c05062100c405081c500d40c500e0b12021040d4144080c421458112810f00d06070001039131024080340086002406500c1040d0858400e0b006c2003e04d840040c04a94040d442410240e04440c031603035060b800c15582d406001c0d0040315041c00360000a90060a58026055101c603914407400700390100d59a04902c0001161800c5a40e65504440f002c90365012101212549003801c2102e0f007541800e000c01e17103030f5041d501402c8450031000c0204041203003241a503070741 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373953363 1250 373952113 373952221
    0xa0902010905040c050f1306020d0e030d0315080d05031603090215090d15090c050102011a040e0c0307080a03081609030f030207031403040e0a020f1b030403020603070c05010c0305 79
    0x35480c816210b1180500c0a80103032310043c8992000140358078091070703e2900c440c600800410041c406980300310043c0401400450301c0c1481e1078070000b07001d0020000442c0080b490340f03c0a07124a0117582e24034400a401280c00300309800c20a000001d600c03403004056804186801f003980d10000880464125404c80400801c01c110503845280e040f004eaa1004102c548103120200c0d28a6440e801203003030381e00e61525000948110840608580740551140d603040c2100e10a58080a46c1180043d0034a003466008581d1604000f0014007010340c00204940d0090146820918030781e0f801e88014910020b5000041881045c40c0c0c0038414103000700156401140c1c481e00701500c1000000300ca82d22078200c1e00c1542000d07040b00011908107450f40c000e985207008812050340c180b0303503d407000d40242c640c0c2c0752040c0b440c0d00007040084054ac0318070005500c01c04007074807a602000340f1031410310f0071903282c80381c03680c209072030001448440c0b6407040d40490440801400308482010900060350402034003e03030504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373954613 1250 373953363 373953367
    0xe03071e051f1d0d0f0e2106070206070504030c0b0313062c01090b040209070c05030d061805072c09040b06011b211704030e090a0902010905040c050f 66
    0x444142070390012090381c404003066100c149818052142e82d04e12624451011900512100110300d200350094510301000030b24022003040a40c0b070b81c1c2c1a1004020380a20303550045420400003a03010001d96400030450318110b4a401e1030350700c40211460342400b41c2454080000701084020900c481c642c2c91041d0844410418651744080c02d00300c0e0900b0030320600107170780350851032906d040e01031180728230b0541c0040c000b034113656850b070820a40d0040141880f040c4041281c00034082803040000d031510a015041c0020f00c981441c2c01074184403c61170601c42064108010000e825a115084110204801144000c4a10010715038111003a101c0625a00400600108414000380340d0321240104404c1e251000380c0d85d40c010150f9030071507151101400208110700301d40003801c48180e002d03000172b00518041151080400300c3c00104601507805500258580691146501c3d181c40044d401c4094494104a10742d2258006000b007860392140f244a01e82e28401c0c0421703640150101c134891445503020b65 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373955863 1250 373954613 373954663
    0x7060f09120906030c030608060c07030c1b060e04110904050702010204090f090c050405090d080a063302060112020618040c0801090b06030c0d0903020f0d0c05010e03071e05 76
    0x14940350443c0310320303c0040c1c10a041c94602d680640b0502d000d039034030340b80582a070350b441412a5946078003c40081701000691083c1402180d604a803034880307a201100c2c0035801504e0280000c1a401061a905205600d007004a811808500d800c8451314070065a0204840c2e5407010282e00a00941d40001d41b00c038140034282c20211465400242280d1050107921a507a484e441840b046a20840d4200311070340c040034040305c03010700071404a039000084031804142035407030f0b1035494500a040402d112203800c02032075403003880f10018915403403000140300070012913152507107019075052080e501074001d50002030400f00d6110502000b00044c14050014032180c44120001040c0c00424030071040b165281c02440302d1380d850403404480c004c601100100d41030100c000340d40002810f0b401c20480c01c3d0301c540d007650b1660404c00d0100940144043d10b4001040c0104e0078000d00f940c4200144050b9034000b000b01000007458081c80003404962002c00758168082e41c640b881c50040c11015100c0ca46000c02d07240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373957113 1250 373955863 373955867
    0x1d06070f140106060e150703020a0206030a02041806150c0b0711030c0f0307030207080307020904081b0f25050303030103030c05070e0903040312180311030a0f0b0f061507060f0912 79
    0x61510f0703505891b003c0c00401b044c82458114020b250004005801a54030907000d440c01c10091500184d91b0400185010744e10810011a007520711343c0c10007070320744460040214400041c00320085c1704160400740040c0c4890350360390503090f00c01400130b01400900c2214440c082c1b02041600d075002c0c45002152083c0460000844ea69040b9210440042c8a901c4000c07450300310100603503174010f41c0900144141d4450740e440c180c403074020071400001c40350720801d501c1244204204d13480030010030070050501028202020414406251304451001e608040c04201c503481c0082100c0c1140e0309442c02e20680003461502a041400c030b6409100131910010520a4044000c0010800c49203e44003000c02c8946100080d80c0342006402c1649504d0480c2d642080800c901d03801c0100620380042c244d0f500740e1030030364440b03007140b40b0702d4402d9640801c06020800c0750100c03141c181d504038004070760034101d140603601050141d10804100030b0400e41c42d01c0f01c10322850f4080e000300d0ba800e40c0c0080107200d0202c44ca440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373958363 1250 373957113 373957127
    0x130b03100b0319050304050103050c0c0115090b18011a190e010305150907030b0105130b12060d0f1e120513050910090e030f191d06070f14010606 64
    0x200c1d202e400782e542d01d280165148140111000d40c0f0030040d504080ca0132006400504000780300301a10740302001511302000082c40b0f51054401980219241395080081600c01c070b42c5a070310701a000d4040340d0b070a4900c0c242c0700403060b811240780121104182200101d10300d10350142d01d141c039107003840c0419224441a003020744420b040c507003a0385c00c0080d0354460301c08d00c2c0709600143c4800e8000507848007203940ea80c4607400c13824000b0010305102d40b41c411210000041019076070b1118924400105041c100c00403c0120700303400080455103100030454548410580043c4501e00424195240c501c1403041102030034882101c9410001640b024030310400c01400c00c0d8004002150740e20403045000c202450250a81d0307010717242c0401c1040c212401c00c500500280b160f0191181030388801d102000341c0b10400c0000340710b5107460340004150004140c0c1d019040300e2501e564510b40c00303170100340d0310300035110a401d5031040382d0400c405a41e2400c031070401c076100c100b040d8410007042d4213281c8041059900546 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373959613 1250 373958363 373958381
    0x115180e15070f020705150d11040b040f08070b03180f150603010c020d0e220614090c091804060b1201051f050a0b030c0c011a1302031302130b0310 65
    0x2e0b2107040e02d43d05030040341c880703542d07006007039109580a958a83c2009500c018044440700c6135400280003a242c00341c00f10702e0b00981c0c007c003030f00b11000030188922944c451202c0d000300210802044501c0c20302c50200340038040102039a041401c00084100c243e0340402800e0403c290b203030300381c95040540205044510104490b664040d42c00d0051504280d4800244c1b583e103000d103540d455084c0c4020f03800f0050345402c840c9108440d40246080009408041e200f854000c0020340042d1006001d0b000c10f01c0880d0f5002000b554086100b4030811a040d2600750400035230301d03441c8041c0c451a41e102e141c005e0050540710003294004606811040c0180700540c0038600644a0142800084c0b40c401683c955403103850090580004200d80208081c0c010740010b035400650000c5424104888641428210346000620326420f8122600c0341c18207080201607041d40b0000c2e10f0003540782d072501014a0040391a00c80b4002e00503a4071403003202c40a0074980c440d40d503e0500406480601c8040f80124000e400409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373960863 1250 373959613 373959617
    0x30605010306020306151216030b0a0b0705122d0c03070309140d03140309070302060304080706061401020a030f050d0f060314010921090f06080a0c020115180e1507 72
    0x746c02c440400400006482c044103054403000c550341d40ea01d55030020f80d00c0c89840f007402c0c540c0f5005840042da440b041d0311009802c14101e034070b031250313201e0804925141c5040d909400007081001610750b07061011400e813424440e0481020590492841d010f8410310842040a140b03000c0810840100365206040c2400c0700c0c61803184000441150081111001d81c2d140c000300070800401d6940c1d90218040302450780b08051100703a80907a039030380d0045500c0e0f5000321400c4402c40320005060080000b5445a40701626580c60810086803c10300040c0d950400020041d09010045042209640c400c10441d00340300b02401d0b042c465403001001078030280c00340340400c0750f0400303101401c500e510405120b011130b81d582014444024465000c2130071201c9141102d40300400688081c00f098a000214000300288203503500d4070101e00c0d15071000d004581d064a07807042107905010201115000000580c81903c0340452098804000503d120008006d070304070a62503030060030707000c914024500819a10030301e055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373962113 1250 373960863 373960879
    0x2060d0c11010f02090a050904020d05010204030b100e01060f03090c0f09020702010e0402340f0b04021f0504062a0c0303270b1b060901050633070c030605010306020306 74
    0x1c81403c806030301075880c1940e0002118070301000a80383c010440c940090002d0302e000d40300049070300c41600760ba1242c0c100782c8541c050031003406020301072000341c00024100c140104d0055414410003c0c414041510000c00301902c2e10b0aaa090102140d18a00200b03802d100002c10b861352018900003035000220180d011413805000c100b0141000c1c003c54818081800d0f5581a03a51240c860101444003ca0101c00b48000c40f400d081c00100e8a0441e208880e02511010340c0600e45881005405441500040c03000355003024480c48079500710040d6020350320f490031301c9584d104483e44a5042280d56030549600c1000640404040c03040b0160100281d9010355100c1c508002062541e100d00c401403452080f884050003010411070400c4809401c180303814000550044c0d9280b00510318102d41507800c80c0c800c2e551801841402e2500c1e6822904620240c01211244e94118105220741c3c0c0054400459640f00000c1050030440c11100350070285034410001c00844d42c40341803440081d082218014018007074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373963363 1250 373962113 373962131
    0x2070810140402121005250309020f010503060d0209190e0303010b0a030c030b1201062d0e04020a0803030a0509010f29040617060a0b101b02060d0c1101 67
    0x424041c1e6046804404072480190301c5503402d01c28601c440255080003030051005044060b000ca0085900400d80f12088408409800725841d804c4000c06c200702003410315004e80034005131950700313a4100c51700090820a4480d80c505000c80c84128000708001d50103040c00e0104031070210302c00d140f0340050741d02075810481581b0000405a480c4028003030100000360500c540c4140f9071081e003201d16500b40c2c519010500d9406040443d040c107407620180c00385030f51500b02c20303c11400b1100407031081441c100120300e03441e808120075041c0b1400c24091004440241c500040542d03c071420114002c00319401265902d28091892800070071064a141099500700041200c0c180c215010b0000c0311461100e03400418001550720420650502044a4000e902c400000449060114850b09030018040290541e8030300010710008a0301e596a815120b04100d103d45080c0070b5115000e145850380c41c82d0b02114007049400051028064000e04203640c40c03c000d120404264000121f000d1070301404c1c024400058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373964613 1250 373963363 373963393
    0xe010e060d170a0905011e0c0c120b0f010f241716020607020106050a050d0f081b0d090f14040b04110d110304210e0303030103121b050d050d020408061f0f03050c010528020708 77
    0x603f84509a081d244c2e4803c0010712100f4103840030052030742c90504012202840744c00050800e012545149000c1c40720130000041501845a103600c070703500e031008000150a09000502d95641802914001c0b503403003031010100500868609140c83d040380c42c003601c070f07811410020542c060320f1071154924040c2a8510182c9406805000d0a4540002680c1c280740e040406100e45218124550b55100b900c1e07041010703060302d4a2058100c0b0841c01c02801d0356522622410340b0a5500c8045000341c0d0200402c00c01c030100c0c0682c0740c1181080d40c00004e655900c9507108044a40c030441d54040b90340343c003000000000f00700e0007003e1a65114801d0311102580c006209003a0b844007100c41010306070b504201c03050f0709018860f80040c0100c040cbe4100040c00c2c140c55441c5146840ea045071910389104021201c1520804083d8001e401400a083e0540c10503046907222a100c0c800c1c0742c400303818044040784200f0001203105154085c1020b4035108021114026402580c40060384a545040d000394441096011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373965863 1250 373964613 373964639
    0xf02130b1c0f090b100f080c1302090120030703091203020601141306090605030c1905090a06030206070501090b0705040e010e060d170a0905011e0c0c120b0f01 70
    0x180c2039003034004207050311540520150950101e0480802d0b60b0b81030100001d401e10300114040c445184d2800c0100b41441440240c1c503c3d180c00c18140c81e40004840303915070351511031039209100c11640150b00c84c254400184d0365240c805000400428404603401c2780028004003401e0003a00030703583c3c15000d03a40c13040d0350100c000030510042c006821200050000462950074003405003800b901c2000d8106815510404a0f50180c0040c8003072038175002c080183d0710303042101161414041b070748210519125800c45074080f500344501c40c0600064800030b680d0450b01d6015400454002d031005035145020315040d4002c0c01d00725400c43c0ca41c564680030a0b80184180180c806036800b03810b00001076400e2180c149502c41c0700520103a40099181c01020004800d2000c80d0241a803402d01c00d500d9854a0304094420b080c5c41e04854104001590f50010800401900c0411180b65040c43c1840764028201180c903600550003400d00041700061003c01c101019440e50300c203012280b29400f80d03907241c2050340f60708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373967113 1250 373965863 373965877
    0x10903050307170f030c2104210908030a0c0b0603030a0207060e031903050a02070b03090c01080928170f040b03060d0830040c03140f010c0c05061b0d0b0102030903010f02130b 77
    0x7185a50b0000c0e1040403949e90f552103581d401d070820304a2a952581c0061a650210303803044000f43c0351802c03107800c10044985403904218118051401c05000002c000e42d2060300d440341104114801c0c50039a0740780c8042c00300704228100e1404150101030303681800b40c4107520242440e0018412030000150381e07203051042c1c074042d94080d0f014000b403074040310044800c11009031848185026a480e076515165415601d1603150480c2d071030300c6110410600301404c0c0c03843c0701d040b000d104844c00c1081c44810f484410481e0255014241411340381d0721010049035000452075801000400d0014030780c035400b0801500301103001d02420341c858920061620b040020034003a03130002d181c090f51017010b00c0007400061088124041920485031031034000c070505804e50307040300811004101d452101500b444401d00c40a1f40c0320400340f56104003000c800d85c03450302c40e100310300c400050b007a0743c2e075014440c1c3d030301c01d000320780300d42d00000c000b40b10b021864190000254810000d08060041e0b080c00011180781e40b500380e6542d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373968363 1250 373967113 373967123
    0x603020c0c0301060b04050d05031c0608150709090c0c1203051008011503121e0507030806120a02060307050d02030c030601030b0108070807050706020720040605010903050307170f030c2104 83
    0x8040c03501d1f0a1012901d1468030494240c0400d0042c08010f50120300010100e11031540040b840c03501d040070f0036082054044186450410300c408000b0442d800251a1044072401500000e1441200c20f0454078105076002c001c007040040c501a0742d20a034150801e60258443d803820346402580c80601e03600300d43c0344440f02c00380070b10041000c20106e2098608c3d01840308980c00e15508800c12071260004408002599001203030020914005241c0d001000355445042512403070945140f14408a507030760f5034403000a1041c00004000740400c0c0c0b080b0140c0b0b600007880c1c0c03815502e905090101d06a15002254540c0c00a8502030310f2040c258402c40350345d4041c1d02c00d900c0e0384c016a10b0391401110580d002c0e4100359112b50b001c210f1100002c1056034824038942d1030000280065130001d0401c0b00b0740e220759110078100314550f0814404240040f081b510107503802490010310383c0500101b90350300e000c0d480c035101000402008105001d00c02400a0001c9220720241048123481c10445090745501540c020748 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373969613 1250 373968363 373968367
    0xa030b040e210901021e010207050114090a06090212030703030e150f0f04030504050604060f030501091b0315030212060a2a0507020a05130b09011508070f14040603020c0c0301060b 79
    0x10600700b1203000302040c20040c8140c1c1c00d04414442c0940404d846081680c0450398005800c0092020038440da07500e00d560702e0810788941c2042040c0d6651500841400b41880e50f6800c3c44c881155100c03996040b0b03283c112000d80361104124240a8001e001605403c0d855005100302c1d101d030500f01002080c4204041001812652076012045070501e400800072070a00038100008102d5a454001510051040e0795808072414103d00005007684c20680c01510200d00780700541040694020314041140400d02d00090241108165440a01d4581e03001a400413004000840c400c0303404141c07503109003000c110510011004070030701e841840350346040c0e5000541003002c0003100d0b44128001c18519000414001515880d500010300d4806034981c202401540c440b44031040381084d485060061074030052100203031581550181c00620004d1583c000c000c80002200390b450b000e00ca41c0b600001091540c01c0c0c42e151110005030080d8041c0c00c084030b0500c80c85002003c1407805008042c141ca0310340c1d0640e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373970863 1250 373969613 373969663
    0x9060f031c05040906030b01141207141f02030406021c200f0115080705060c06011a040e070e040501140a181e230403090b030a02040306020a030b040e 66
    0x703041e0620072104040080030000010740070645d005490107540070304032050349540352800758003814103080c00c003e009520621901054000c041a464110303038003c5085800e10f4400300c00650304080075441c40341e03054802c2070450102ca60000182c004d4490310703000ca4050b41031980d140b00028040c0c0191000151103500f180500d840750400c40c0314040b200750110b403c218a51801e20b800d652010708281169000355204000c002d504111210061605980b114a4441410741940c1c07104d005000d80d45c82440c00a11000c4403c41013070481c1c0082004c2040d920756410800802005001350f010124400c03030400e800070039920510f103c144804d0500900440019260095400f48001c00f401c20f0b210351607858070710071400850000c4c140c0303200400480005903c0d407201d03d06085011070202c18221100c03079004000c0001d030001d0620003660b03003940c810342c0c5a507102403003200684502e4100800c04c60010a44d9070849030190400c68000508480c28040d5071030000300c2d80d59803924500c10668540c0c10120107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373972113 1250 373970863 373970893
    0x501200c0309040b0d050f0c010e010c0503030f0403140307030504020901090605060a200708030d1a06031807090f050a0b030d0c020613120c080c0301090206250b1509060f03 76
    0x410249015050101e29001926a9802d00d1f51810003400140c012016190340d03586c4c0800c25003089182406c00b4104404142c45041d940d0000410200010100e075000ca8181801000784001034003945460b15600d00e0a404001d01815040c2c030101c0c01a5001070022a02c428280034203001e4610146c2801d04110b0502c0084a200382040100c40104900e640e02000f00c1d2800c0c09100090070004008640d55014202840112449a01038019000b04d14258482507607401d070860390031000000180d0f00c00008091003d0134000342d40e0003e5461480c111740010203c100fa00818401c8105010400420712001705140e240c07025200110300040c008480e010041c0313041d40151110003240213166510a4544418240380c400c1aa402d54030000140c604015440d81006070403007640d010340c020b1203440919808900d070760280800100c0782c0c0c0c031114001c3c19000f208502c020800c0e9004621240e45080500c2004410f20b03d9402580c080c0039003200060042c00c00502507000d0001c050000c3c036841606070703d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373973363 1250 373972113 373972121
    0xd0e060702220b03060c030402010207050d150f0b040c08060307122d1b0312120b0d1203150317030405031207030524030d05030907120501200c030904 66
    0x102d0303100100c0b24025082c03000301031400c00501e4001d400020311110300b0f0105880d1540041550019400c02c004000040c1d9002c5031000c211002612012801e50440c82d2a2000c031111a4030301400a11304040e22000802e00e40043e104040c05507001c0008102c0b00d0f008450b181030444103a034040e40241c40c101b100760300486032106070760702036503d001e40c01c0d13581824511142d468100615905071205056001d03c007030b48540041c0602c080c00a0015245169118039000c0c03010406181409441042504036036001d802582025078000d06020a4520501d03203500070110100c00c11000915101200003a081155424010b40382c010794400c80c010201c045c1214168402001154680014040284028003c0030350fa4091240c0e0340340440da80c504184004011840e0910b20f42d800072010304400c40a071000718544040900520306956a5556001001d2409016511090f0b2464000070002c0501c0811342c800d1540070701140115203035180a8603041c1441c01400c207150101d800400001261b45011380c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373974613 1250 373973363 373973377
    0x40528210201060503012c19030302090a0305160f1401050301120302010e07060507210c141f0608100203011d0a0b04060306022d160203070506040f060e030d0e06 71
    0x10020602949620100c0c0c2554a0400b200c0701214072101c4910701c801c0b130902c0490170600e60b01c009268492502e02341c96140e01c5113a0024050640c001415130150321961a403e001c0d580003001c5600794252030000b061020364921070042e642008000100d0050b16585820380720040507540d150641e420141201d0400401d0034045095650701c000c121b85144042c00840020440ca03150a6110a101e081a0b485800c07651841902459000720617642503800c155210b5049400181c90600d0758a540f00d454908022400d07130150007000e40c4e580c4400c142881d086001600d200900395011707540d41d000301e182070780821301036520b1045603001c403403842032626640c45a002456400c0882c42080401c0890112000d5800c256540c1d500011101b00300c07001030342d00711260380e4003000280c03081300701c005c0782007850080200c002e06000740c1901aa055640421000d000341800500841d91540d45040a0503141418410000400c07901d5014400c0c5203000709103c5000c0c031320340c1c84012222051004000140c0d101c44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373975863 1250 373974613 373974617
    0x406060c0b1f0612060f0506030a05060a090e160807030b0f07140a1e090b0906070c0302040e0f070602060c07031b0507060201050a200f07170304052821 67
    0x90b00384080d6281004441c000c0405072580d26006803210085002d071a02500080380b042d0480f0801c00842d12524102c80e070112101d00001110786a450000c3e80000313203580542c00711030070113403c194041e4010036003d030b202404000c0300080701d94510069071200c40e1480003405540070000001e8101340d240140c1035120b00c07039280076072004080c10100d112542040350710600046500742154262402c440041e004a4550f00380040c01074a040100855442107420b4907011b074201080d013500b00300c950340b444009903078003c000b40f040d041c41c4103005035140c81c1038190411910604000282c0c081c00400d015000f15007010a452816541c1c0d18140c5008081d80d001c92241c0b0403000007040401c0c802e00051000d840103038004241130401c0d00074903040c1c4041901c102516030307a50f00d0f51000b030a0311004a5100403110900c29813240010309280d040c006d60350100100303038040001040204940030458883e02c491031401c05d0742418020b807640700814070000000700104031184c140c1080010703900b655924039003a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373977113 1250 373975863 373975891
    0x1090207020a0f06090312020312010515090306010306020c0712080d1a03061f0605040f151b0c0305060a090305030423010603031d101b0201050702040c020c01030b0406060c0b 77
    0x5128040b0083c1c05a1303c00d000056640d58188100f03c491000070210034081d01c025400c000c40624030f404646010b106052042810700301010030018880b042e61210380005080c0c51240d1f03982d06085c8041e43c401e1007031884502480c1e002040e4000d426140307820440d0898003140c2016410000c504c000c0044081f142804864a40c05404541d07003000418130910312001c8480d002c043c22150a00315088542101007440300034881881501000b1504000320b0303504c21001d0300c2c0094142d1003600ca0340189c96854140d90245000b90b002c1c051070f81e1549045078030400441c1e0b407581d1842011811608241030040002d0701c1080402c0100d8000d1400000d10081458038000c900205410310703003181c0d202d0b4400c03000b00f021200141a000d00d955840000c89206549000089494000080c5103c1d1454544101460008071500969108400ba114180e41c040c104102e42c200803c0060b54402d581c540340f03030000b42081481c2d600c608003809a20111401c90b216181c10607020341d514040c3c0c1c0b00041c00750f001c459407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373978363 1250 373977113 373977119
    0x190f020409021c381c03090f060e01050f0d060b1206030c130902030f16050a0e0610120603080f0c1b0a060c0201140703080117060f13030e0a06020c04200301090207020a 74
    0x240c401010f0a81074500160a417014a0380340240201b059640049014002d40741c0805c1020303009260064041c0b424604681e44203051802c069047c090481d0004a2510300703240840c800302160b0042030f1284811060a80f01d9450204061f0b5a40488130410b270460801d5091000340ca01503003101e03c0040c402000d442e022048202202c0c9054043c0001100c100380701032041206083c000301550140460012605070303450800c0120340407289824020080003a4905a0034030012190320941c051944420300d103655140c010022000d5800c0002941160302410038034030725803c00c00c0c0c0d14416a01d00901061851403034070f1070a5410200014040c1e062141d1040440110100d0100400c6c11510035202c5180c1c2d94144191040300001c0c0d00c0b5000030961103241070000c100cad81c01000650109403101e01c400c07040740710300e021101daa5404e6120394220704010800b043d090340100b00d030545002d041da8100910703251070000405804445190440c101d100f04010700c134001e0150006d1520a002800301100e141da = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373979613 1250 373978363 373978369
    0x303031d1501090e0601152708060103060e030c0d23040902070c0e190b1f0305160e011202090f0604030b1e01060206190f020409021c38 60
    0x3041c8020609800350410051008902c140b2450750071a2007800104050b41c184001c04030a0488512514107102d202c800c2140007011014482488192018045095503512a1150b80c0c030b0ba000e01088400c181422081004041c0000640e01c400416100500041c400f00d6000c3e500381d2a0400c003495056420503130b00e0041c00800c00140700500d01c880303005954a5407030030042c2c9990304c2500813400007040001808040030080d603c40e00442040480025500150301c0050242e9034104ac1c1074804201110910b8000303038156019a1003404600d8000d0301300c8a098400f2240c01040b25500346c0810741d4106000150301c80783e40038280c510000360030392400181c4013000480580140c2e004503000c800c417404000706c0c101d00354080e02d02c54214196646544d414403802940340d48004001c03140460700c04c1c0a460540f291504035000d86818103000319075440d11003941d0400703548041d82c043c200c40381400048030440303682d101d4101c0091603012641074006010b43d16102002003d00350046190b4150180302c5165 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373980863 1250 373979613 373979623
    0x14160509030a11030601050103111804021c140c0f0d05150d08030103030f0503130f02040f020406021e1b09041113060e160906050f07050a030504030311160303031d 72
    0x2030b000d02c0018400c10320340804c152605005804c071a040500b07044003540c600604409960858003603500c507160841c0c00700013180090083c1051f40545004601c01182a030301d0642c4110b00d0340c0da2a00710001d903903858854818151103034888031000714108000c0901400d10a17813007da0803001440d40401990382101c0001d8518141c0c000584000b07000200400c201034001c0c000254482240c01e2080c11403a0202044007030401e0658054034a20030b46110004641e40d5030b0124440024a040c11511030b911014025500d00c808030104c0018502d80f10740381e602c034100242000c030718009407080c00c0d00c00c0117882c18401c17003d2024000b220541032201c460941c44d40d90960400a60b420784c540014828504040884400000b810411200160030103d4890f203500402e032006441d00d81c2025640c034262120035400a1182e140041c08a003e00708d04041059403260092040b0b9019940320038418100d0702c4d01075241d030701d40c0c03042d1051223420300c504100180c0a03402124032155481e0021135442e02c02c2c1461410701d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373982113 1250 373980863 373980883
    0x9080604030f08010806010602030706110d060932130302030c1218060903060403030c0e0306101a0c060415021209070f0b0903060f0a060314010e010f1416050903 71
    0x89403159080c0c10b9981d61060049004012a000034841c5525140000c1c5d12446480300107803042d80c41d04141a1080300c6070048843c0d58a0880742041140e0b91040314030f000b4584c4662811100f034462210503070089900c80c100501c2c101c000009503540c0c560207180c4856840b50303a411425400103004180c4020000d0140e40d0189424110a0f1f54411402840100303a1181c3c1c010300c0d106a80070b20a400c4203480000e000e6500c00d9042c140003c4400c410350040e80d05a01c0e42110690511a010420800c000810781040071074800700c0d8070901c4409803108040d5140585201181240c2c010000170740807400340d1003140d9032404100c01c01850441c915090089026007120040c06940c00314a0803c240510140228020644900d075241480381844c0069112400a8041c81003508000080307a03800085502c00d42c005c6a2000141c101c0e600e6941c0e00d14080c1c1000c444804955190484580d006030060060030840401c21946159550314090000d0300d0050745514130040040a011401c1551020000c0d0710b60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373983363 1250 373982113 373982117
    0xd080c030c150103050d0e011209031d061903021809070c022103040612060b041d0907030b0a020c0109060c050705010f06050a0303110c030a03050d05070306060e100908060403 77
    0xe12040c0d5016030b07151a51190440b1803100780e110040001c5940420219101c04261a0201e1044a4980101c5074146c20b071030416130161409600000b0541c218150030000b000031601d40c03801c04858004c00249005085a003c0048031004400130200d2003503005180d80e0341500c04c4511020041c1002c200c441c282190140c0108001c1e154010039468102842e5023480d03002e800704c0c41c0000e610a88503481b07005912802e4140908032401d07009030b020303640102003d05410811aa221641d0300c0352080c6001d2050002c0c02d0007800c8501003003c2c4800032400c801601d8205524201135281e070302d4120002d5110b4040c81c4400c0d5a0741c1c01e0100040c48a00441004440e5030b6507241c1c40350402c0c00c15500b150050b07042c0c0694140780900070062030320f0345800d280499800d82800f80091600072083e03130401c2c0014406030307414040c5003003040815030020041d00403c1c000f40c00401c034945d6841e0003581290761601890000c40c1c21411454200d180c18507006244040300d103802c0224590314054035150070829501140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373984613 1250 373983363 373983367
    0xf07150f0c0f1745180709060908010e03070b15030609280209060f030307080a09060f0305040309030602030a060b0f070203060702070e0406020f0c1e060a0b130b0d080c03 75
    0xc504540700000c0400c80306840807641c003085100c2d22010001116120040d11040d50b0844c600541c1c0d412910400010881580e05210310382a4001000d003070a6004400201e006c2d100c0c0420284414030541c1c00682c2e440000714a81501a12058001c2c2c9004020b81e4401040039801100c0d070300c0074050326011300c85410003030a070358018a6610b48c03000305442010706d148551200f600d002da03032451505a00f011090b68154050170410010030304520030340c0d001a10001c0000f4605841307a90001002c0300319842c3d9074a640f0300208101c1d085040e5401a900500042c05a00040c0045622907005541240408200081456603044214210340200c40090460340000c10032070700f5802c00b8402c0540c0314056201512600342000560a08605e0107003007d48a00d03400708080e00e41e801d54004a8401d49000c6049403030152402c84280d2150000030011000b81c003958000c81c3c0c800c9140c1c0100c3e919503000a040c04500042c0d00300780b40041031f84c001d2440e4020802d85002010031224001007158140c80c0c0d0240d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373985863 1250 373984613 373984627
    0x515010503060112020319060e03030f0601120608030d0506130612060f0501050a2c0103051f020a1202130e0c030a110a080606090d050601080f07150f0c0f17 69
    0x14100700b0168402600342c10001e00100050358007003004413031100c102c0180c4010202500b0813500a245a4885949910002003448841c1e48192134852041500766075000d20340c820030004400762002441030b00ca040e4403d00c00c51101c04003c1d041980d0019014215030700c400069098542510419803241c010350000c80110741c144050390081080501003000c00340030652510b008980480c00b10720a420b50a14440303078803c0245425850b002625420710a0045c00e5612410f1468a9908c028040340442d198000303001286540f0307009907041c0c0d0f03610b82c480161500381c028500c2e000c0c3d0301102c4a03030301d02c0032210008115504c4031903809000d540c48024440e00c80ca017001107402103d081318100c80c0800001d2200c004290f90020115500041c103984041d203815682d404206410340e039a5004140b40100d40010501c6034001404201250216040314102540d4107180342c00311040303100610010f201c070501f1098a82c06800c0080003035100c1c1c0c40141c0e6682e040d07110803c03c10300716849031094000002c3c020b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373987113 1250 373985863 373985869
    0xf01020d060f0f121e0c0e061f02070b070203070806250203040302060307030e03090406031110110a0204020a1403150907080609060f030717062203020a060b0a0305150105 75
    0xc0000c3c1c080c0c5030b03490500714148408060b030100c0020000340025005a6038a504038001d155504240340c1c0000c1006100b903c07501c40c04071b0440119056401608103250304401524511845503124445401820000b42007401c0151b840d4001181030703070584904007000410840c100326591081403035012500758002100c001400e1070b02c2c800c10100465009000c1480942c1d104000c0300d030230013114140041c208010381012421800b4501c0566070282c0f078484004140000c1d210034890700c0740121070180070074986a01c16150000e440300c54107495800313000145d0050401d030b8014136000f086801c0c0084400100c1c207a94100394401c0f1f4074051045940f5a109206080c600c03030607a0060b0720b40c2441c441c0d034075203000414450b0f00300404c41c520640d0003245030000d54800b0700011014018401c00700d0b071100681c0c924669206026030703402060404001d00d009058007001109208030358194007403c0500301644502010b48203a5000720703442040700100100080c020003d0502c1c20b8101ca0071500c1070342c501410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373988363 1250 373987113 373987139
    0x1f06080c010906020d0e0a0b0a030606080a060b07140c030d02030a12020406120c0e0607060506120307020d08070611030a05090c01020106080a0f080f0f30180f01020d06 74
    0x5141c103015800200b800000e4000c550f1002241301440c040080341c02c031100080003138249502080500c0c01c0040d107850280c1e8160803070020b55400f61601200c0703881c0c0e031018008840c0a0700c0350750130b40c040c188140d90000b00f0902e811000301c0d4051381110708294455000a0030001c00b1002400541d20001c0e03404603054104d43e082080140740d45003141002d2500307401420500e5104068025640d49490140d0b4050040301020030f0107502a00003078503030645203001801840c1c2612124480c14001d542490003c00020485002503070191444c81045559a07440c07426030010803080781d4881d1182c10660710007000d00082e503c60f61050502207200d04085494505000c80d112940c4d0440e410302c2424800240c000494019a80d071040f800000740b580c038204074119000d1003500c2e004e0440b0014034504a020003101030007004484020b05007540080b8402120601c00350300f4038010038009a0000b4045012a4460490f00b0342d000c1c050b5050403d45250144c00c82c0c0c80880300503206684c814090040000400d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373989613 1250 373988363 373988383
    0x41707212022180f030e030f0106080706170606090105071e06091406060f0d0305090604080c19030b0112140f030a020f0307230a0f050a021318020609031f0608 70
    0x280e41c0f14418041d2102d119101d80d02c00b02409221405140038895181001303201480000702c40200211511120015240d988070310901d40000c1503e2100300e40c16001c1c054042c001c0000800551030400c0e0714006507040e400406040d56103000440700105000f034442d004008951080100203104480703850084008100d46200b446070740d001c0703820003545450b002c0c8a891501e80c200d88481c05651a454211414071415015641000002c82c000500c90f00009407070100610485a00d000a030042d20f125142e03c034188400f4100702c818000402000301070800d45247e50b800b41c640d1182c0c0d044040d213901d15015455000800c6c0d50b00c00180c0944442d070600c4208640300c1924055032404603986c031b841200c0038402011403824044d8407402e003552030040242040300c550050b00241030301081d040481d180c0a842d1400d9006541640032100210b01510031412008140107070380e9200c107021b800b400032a401c80a1859054444c0c10365502e030504034040024020301c0300c807070081600c60802400c41d04200c5112 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373990863 1250 373989613 373989641
    0x1104080a0c1d040b0f0a15030506070816050f0d02071b0312020d02060a0506010207180501030b070507051b030316050307120311040e130602041707212022 68
    0x5100c000740070654001e4000c00502186217043e2038041c0c1c0d140c02040000f01150382141443d200000b0003401064a034840c120b903859103002c558401440c070140307906045c0000c0000744100f0000d607104a4110113000c000c001c02800606089003641c860786844d18281000d024aa840001041001032040c145c1d28032003010720190002480c0c80d203001e036549a000e48042e240356114400609a81d20030003014004014a40031020f54040121020340240028002500e00c1d1001304002004240508100e512507517100c0002c140405940441c0c00c2010f5000701c026130315020403c044070b0081413051180d0000f44c06000999580c490500d03101514015458138601410300b00459640140300b41c90969084440001d045ca0207655842c41130000d03403441c014000c0016202041c0880ca0080103000c016054007544101c414280d15400351203120082d400e50790242c1c030507401c0180c0014440ca080c42140484000302001c6603191a00000d0305860315440d810180344401c482d1102c10003650040c0c1104141d16 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373992113 1250 373990863 373990919
    0xb0c1e0f0a1b080a0507030e090601050316021e0d080906010f0302060304050a06110a0e0a240207050622060302030c09010f21050114011e031104080a0c 67
    0x803100c0480c45004240442080c8141c08241c5420000c04841c08291168400070341503684641c00380142894206240c15400103502d1100c02c3c0e90780c203245c40301c40e0140e00140c40311821a40c0701c02d22090400c400e000710307000314013800030301a0b00c10000c48076043c90811018040c0c2061412118014003004000313082c2c001942c4007600401c00454800142d0003540d40644101340c1d01d90b42c600f0312a1408040250040005140c01040ca00018848010b00280c840c05c3d50f41c1c101052140c0c04206052589004124070f000410080345149081007030103a1401982d80180c3d1106a9142c2c0020401c0d0040c805040030341034540e0440701c440c04001002070190a00307042c01c500f903050011489103140250b550040c1031081003503181c01c100f0301810041d0040708103c0c080c4403a8460003500000039202c00e1188121025617143e00f2803c2d903000e110740344503d42010010402405d00d8420440150100703c42403400c000d020440802c034200c00703018194650703014100501c2020320b40f2a80d094000028509003060400d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373993363 1250 373992113 373992127
    0x60801180b100c0309120c0306050a0209011e0309080c0d0f050a2111030a0905070803120a1107050a0305090a270519090c05030c0102010c02150a02070b0c1e 69
    0x38079142c1c004407156514085644010a2509481c4040301e508540c81c1d040303419481d01d040241643c3d1090a4a2040703030144802d44481030110305070700030403002d94081414444013032422084071401084242e41442c002c03c0350911601c1e2803266138000d10f85e4244580180960010f2613400c00c40041c981c1038503181c514582010214018204800e600b240154083d4038816103020542903004414001e1102280c2c41d92410101c048000815a031242100c4902916000148483c008000d0b5414041225003019550340c400c01c3e1180100710b001042ca4000106024409c0401d60070003105916038401d031242d0313a580c401c000401541404562110b21200b84081c00c0b03d0000103140750700800b0700c40c2010003140e26181c0c660680c1080c0c8003450740c59455451700d100001400801071070f01c422524181c0c140c070130070300c0181d004a099405024500d8090703800310b00c05482090040c00816400b06003d0300c0142800e0050307a40e9041c115080d40c070b885a050000c11443e40660bc191b0b00070441d20150500103140401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373994613 1250 373993363 373993369
    0xe01050114011709011b02010b03010605030304120821041b0510140c120c0706080604020708030c0a11010f23070801060e060904020406171602030304111306060801180b 74
    0x4503c503070f80300c25010b07100480c0d1004801d403c0f91084041c4083d51224040011500a0090017401000c85c461b42c00c04400150506002c030840b415501001801c0c0c107090500e48aa140a03805242d407050300000200103652001c3d00c8100c0f0501484c411f101101c1d00034030207181e210591700560005403042d105583c01e03640245d084162015a880084c3c240368540d50040501420700441d00301c02c0c0340107c0c00007074445002802284500544095445080e40c541710202803004034011802c0003407004108001140c10f0b800210040d200e90421498407440640000294609403200340c3d21040b541900d80c2c80703d000416054070781c1c4450540b1791324a0309d00c518041134000d01d448010711868050007041280d1611070344501e0129080311101500965072255a80e40040c2450403448440150303a100001050240c0001c0c20740002661450380158116107554940c0c1c03048100000100780d02c003201084502c808041070056070001e1605455842440d0302d0b02006001c0140c070709a004800a02d4442c008085d0341d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373995863 1250 373994613 373994627
    0x2010606020606090726180c0d0611041e09050901090515060d0b100504050105030a080708160f03030902100f2106030b0f060102012007020409060b040c030e0105011401 74
    0x604403802819621001400d03140e5140c03101c4100002d00100c4041d1004042c105026405512a0b600b03064047c43e100e007030280c480052441d01c6030300c0303480d2902c00b402003082500080c0381c90320200d40040c0b9066550030000404500c075400380440c07110b1141c0c00c014840072886207aa02c81c0d0441e000340102c41c101d030b0322a904c07503289031000250701040c0310104840751140b0020074650f540c40201103103d814000c916100703491480c0f1070244101c1c01d000000c02c5c2402e02150000c01542e0000902c2d0416100f59503250f039a8005d405819031015280c1e8440c4040741d618683c820800c0e019442c00213051403140140503030290786644030014080e0020080e4202c0d40d200750040131014204542031440762514600001800c030350f40c40544081c0b0a6800d1000790805034031400c3c0150000d030003c124170085000359a02c59001130b5071442d072146e02440100050b05207500300c8010b6030302c281000212400d00c9400542180d0f02103241c03000113652030021801182e000d00c03906c0e01506010304144000c00b2800b000030054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373997113 1250 373995863 373995871
    0x915040506041e0f0e0d0810120203100c0e0402040b1201050f03030405090c12010806100801060303140903210a170402060301052707050a020d17011a0d05100510020106060206 77
    0x82980c0b09904d81003c0400e5000c3c020b441c581d903056454119075502c00a01c80c50066880d24a541b20a02c00019103c8000b41c00c0003c00e50b014014000342180008841c004098a2182409100003400000e00940d210320040c000b60502c80f4500e600c500f1010340040042c08160001401000c40c510441b00c5985c0010943d0212203007181c50240d81e50351441841c40d603011f20030000e000400c01100110308220007250ba64400d00162904241055071603068a00381d07400d0740700103808103080101491000390074100a00b4a00c0c4040c0855602140e000c0e00720a0000b84070b0b40490001c0c2010070344c4100c1c82d90200300c80c82d0396814010788074082e0a194000410300c0c48188103640c8181131030900184903c82060f26011403907a0f1010720320701803801c4100a861079004115000041c05980400c10704580203001512401d009c10454195681c20580d89a05080314400c8103c0d0801081c000280109a1030144c0380c81030014039120681d062400e02400002000101c0070000d40e4148501400419400641181c0c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373998363 1250 373997113 373997171
    0x120510090c1202030a140f070c0605060612010605040504230112030c0c06030507080c031b0c10021803010c020f190c030f230a0c0506070809091504050604 68
    0x10a051600042d10741040801d01c00040c5400442002024a041e03400100d01c0e44000e10f4825007641c2d66000e6003603240e8111a400c010a42c0c0640003408100c040c1d1059a01c501c01030300d040e2501e0024020a1651002640014009000081c06100904040c0501500c601110740030190301600d40d62910b51400301402040940001c10680205140c41905090219038002d09080704103a10f441c8010081d0804580d803801007100701021841c005481401c880c840e603141d0070002c2200910b1040d0540a5010300301c10741c4644a40c00469982c2c0707201d0b10041600c40c00080c0500116103103003080c5400d483ca42a004010b541010504c5150043c02103150543e85600304100c3e0f0001d425403602007481c200c1600060050061b680702401000614407038101200b84030000500071503030b010140c1d40ea80c480004001d00c4c0404900017040f0710300700391000d04205481608118181495140841e010031411204a0040c5e040c803484180e076414948a9250400402e560078480100d0800b415a01d4100b268803910b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373999613 1250 373998363 373998371
    0x411040e340c020103050f04020d06090302010f060801090b06090702030316021203091005100609140d020301050f18010209090402011b02030105070908070e06030a0b070c05030406080712051009 85
    0x560000c00ca540c103000364540741c0c01d8a4401c50030807030081003015400030481c0820715000110391850304030041d00b4401e5900818130420345160313665031009000d802c1313011030666485090742915070800c0e0164401800803c1e000080c8190142050403404901901300c4c1d0286602c5004d0006495020045940c0598420400112040c00c0901241350903811003803047c0002e404428031020308404035180303900c1040d6900c14410341c1c03242c071180c007603551881c820340c004030ba1040d40802915800d40da03440030250f001800c1d82d1500140b0f03000700342502ca040310240e0100d4082000c00070402c040c22203010503074420034021402c104802001c10b41442c000b5002038103000800c9203008035003041d000210780c070ba0741c050001d02507030403d1940079101c41c00b240601481409900c0c4081030300449204250301c9004010b0042000c000c841c0c9039480d14001c0507051408200038040b440c00400c2c0200000c0c00204121f6031516414641210008c168240109004001d41e0030282070085043d103140310b15040d5160964001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374000863 1250 373999613 373999651
    0x111070201051222060b01121b1809140915061c02040e01110915030408310602030901080117070501110f1906060b043008120103020411040e 62
    0x249945068120002da1341c1001d40c4d150700300011074102189216003030700d030401c124591007500f4050b0340c50052240112401c00b2a40918541701b11003020140c401c0008801d200e613110301c85102940c5540350564204d9a03030205008400c0c10821940000c04030510b0254420300307040b800200588812019202804003903031480c02595240c3d4006c031011305961000700540c00c03080c40c2040882d0032004502d80320f0844130700c0c0e584143c0040310031280301c4c0354080340051a06041c110000107034181840302c03020f0503024070208403d0420410420000e440c1c10340003151140b0f65a4001801810140c00c0301d40303a84400c41060001034030002d01c2c0d00a44109081c0040751112608a9a140010703006000001c0d124410a41001034100d000c000d0b54a030081e5000e0180548424000000b441a8803a003941c80c0e2810340d450070b50715400e81e0b0741504010b03000041e001d03403180781d10f8410080d0800d0b40390301c1e0017030f000358010411417078942f10b5540070030129141c4900742890003000b4801000014001e4034400241d81c145 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374002113 1250 374000863 374000881
    0xd270b07080c150105090a110f0705010204150302030f0c160201030b12012414090a0b0f060324091603090c080f152202040209012001020a0201110702010512 69
    0x158418a00c4007049400740d5003d921811182c140a10506000d103400501080d02882c017409030003e140b001c4059189094488082c0020991103180b0982d81c5d55130030301012074403c0102616030300410180c5c0d405a180d003080031094259040107041120342100402400c2e801c2c251a60914032090b809080028002d2040070200744a01082c1d00f060110f94608145446040b0301c0301012200805851101d15079262038000342c4080100002030258002d1000380042c0e02d441c81034220065091001e4000f03002003121201048542d0416a0007a00c0c40340c00382200d24045c4000e00d131039407947c02c08486194840c205400410400d0a00c6680641015191000e00050008210b00781c402051568112004500c6800740300d034407900200c0e800a0890a42030200d40781607104010500130703521202038100c0c1441d4aa081000a5000b006001d040c480640f84c0d203080030056282031401200410000b680d210700c903400003800c6800e5404012013140091202c44c0141c1d80c40000d0700c00c04503c00035501d94503103d42c200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374003363 1250 374002113 374002117
    0x60b0a0e071218030e10020a1b031b1406180306090d110a020a1502010b031c03060b03011d090a0b0901020414091905060d050109050d270b0708 63
    0x100300e40080900081c8040341c0d81c40031103a8080a201d540070414104590401810801d1190b005800221040d1050a403403502c0e051100240302980100c815200040d541c0d02203036041304e40c41c4044e99611720b00030014000e401c280f460383d04002c041c4800c441e6080144580310a031070402c00340c3c001c0f00d000c1525203050b280398180510011005045500500c2c10403104d560358100780c0307010740000c0e0f1080214010102d0014400010382e500030700e2170801030b043c86408524540d403944070314210340d210f805a00183c0c0b402c4c041c120b41c03045146480042e0402e090006416140594041e80600404200400200702c00103210b010038282e44d05698003646032040d19501d0281169400360420768a0010300158020542c0141704442c0a00c25160700c00703d050303040101200e0101c80158003004c25504012694425900441e4060001400b61140309080d44801e03003120340c0307038000b01c070705c2d034401040c05a500c2d4025909038507240040b002c58000504420302010244c0203442401c9140c0c0c0003003015020080d07a802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374004613 1250 374003363 374003369
    0x10902090a081207060e1b0103092306071e020a021201110f0403121b030804020114040f0915030312090f02060d02030601080c250f020604080d020705030a020904060b0a 74
    0x2003100c51580f1101c283d61074035842140200c460398541b1044451410f4007060399410030b1203c031401c54081c5291001540541075a0100319003000c031200740da0b07030303078840403207800780240c041c04024642c40c03800010140401e008600030140c0b0b0420070f0b46180790180d000424506055040c1d0315400030a4184074542c2c090560014038020000e004101010558040713409002182d0017600c00300500d51510310305482c91418a41580202015110000c002c607000d080211380091040c503050302190003203540402c0d0b81e002034022407150b00302480c04118008607409a00d890b08138002d91041c4140c038541c1c2c0a00181307081e008019180f03449218510600000440c2c1060850300a004030f40c1d15260110100f00941c070448489003c1410b6101090401d080c1606440140340c4803000500807000c07803102e544041d0480502110707091030303071812440140c640d10040e000615103040144002019604003a040c000d6035085140a9844800c0d4034025907500030015800a4000b10700159013044070340810309a11b001d070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374005863 1250 374004613 374004629
    0x60c070b0a020d030f0c0c080304022b0c0e13031404050303070c06031506050d09080f0d05040c14010c0809130c020705011b080307110f10050412050c06010902090a 72
    0x22500c1d0340e078250085140c041c004040d070760400c02840e0b010070345811980207208103c002940212020b000551600055800900080c90703000580c49041c07078400401c4165191050300384083c00f20318100099582c1d40c60281415030305400e00c40c90f1989210466100340c00010701000108481031225010460840c1c01605e8080c2c01c0d640d0310320755428104110754413441001c0020b46030a9003132031242d5000000340103a6109560b220700c2c200d03c81c002003000d80b01400040d40c1000c000c0100c41c41c43c0f645540107141070000311350041080c3c0707041c0c100040c2d000100d600c244a074000141100d88181c1c0d00c05003228042c0c0d40080c0e0981c560049402040303038100d003081c10010007031a010f1142c0c1d159130001001002c44200341d883c5241100f07180e4203100b82898001e4010074082080c40403540d294041c51190846000c14002c58a040410500302440c10304100d80303d88459690b44140000d100040c900303c1ca402e040340c00c0192401c0d0381400ca1664840b8140304c0c4103003081e4040703017141d610340e140500d03500244440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374007113 1250 374005863 374005867
    0x2130f122907050702130b0d080a0e1c050c030d022a090f010e0c0705030f070807082205150a0e0f12030c0c0409030503070c0f0b070e130e0705060c070b 67
    0x480006040c0e03034444013090b403062501071140d110005607402520183d00c0d0140c8910603011041c0c0c1d403d28a5000400c4000601542c00100130042e12a0300031070107800300002e400d05005916082c443d0400c48680307286070083d005014680390058002610201418844211400000c0322080048039482d40050a81d8012200001d000490029a5086040e40e00810030443c041c2c40306d442c0e41c1e00c5413140c0032000380540c00034000c0b00d42e0010301101420302c230707401103050706d19000c590340d50400c4c968002e044c000000b4410183c1800c90030000d80081300a8402550402d101c0300d014600c0c01c2d0b0038083c801d82d220402c0100340300c1815a480c1c064801c0d42e03113640580b284408240810707149803240c0001d150121913201c0c14144041600e414001ca440040e01519440c1c81c5032600d01c4102c480d041030f034806a4480c07912082000c00605c1e208a40c40c0b00c1d03486503881089044501007008180311040c0c0e0f1314042d90b410641001e0043c040829040c0440d6801c42c0c20075a14912615036030b0a02001e80d01c00c2250100c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374008363 1250 374007113 374007121
    0xf05010f06080c0109060206070c02060304080c0a080c06070305010308090420030702010f1b0c030f09030804060507050d08090601050402160c0f05031504080a0807021f02130f1229 79
    0x40003d05194602d402d0302da441d105515800200c0c0d5540040302c5540008961032121009810100c0082d03400501984005152981e480d41413032812000c018200e030700d0f043c001440002034106009003600f1440b50300c0e042c4243e5140d03485588140c024000950b00c40c42d034424140c0f20000c420b01c5251140d400d4081c3d041c0d00c034a000e80c0007034000d001c0e45100030321140c100720429203070002d07014000000a145807680c4200a8403030b103041300c4102c45d4003941000e2164141d4044049182000030388024501c0d943c1c0c0301d40c1d4000c6c030f1801c80e040442900089007445855001e001c1100c401007201d82c1960b0342641c0c0141c456118070805561784120314000760100294044c0803860703615111601003510001e030110f501e50000180000c0c1004002ca502600540080c0500035101b48030302c3d001900040300344100d0701d44103509044e40c050200080403040b01e0540c0001c03841102e54552003014003d240c3d01e40180ba000e4649843d804030b0f2255440000c10341c01e50125455a4201400000102022049e510301800d1074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374009613 1250 374008363 374008379
    0x1e031505120c2d010201050412110a050703050d11010516030e07120c05031e0c01030504080918010603050a0b030709020306040e060a051f0302030c011101020c0d020303100905010b070f05010f06 85
    0x104504201d443d650320300300d21105540140180750155a00400d025002124440200ea02c2c020540d1055480c0c09411441404500100450401b65016101501101e425904040d281001d01807005015904220410511039881140d4168103045410003003000d011005409060010344c0d04540c2e0162464000700090000007580d1000303030340040d4200c0341100382000f08442000f40c0443c206d0203607070201e06401882d510079000250014842d814090402d00003400080d902c200000580300d510700741c100104911541405901d030043c40f001010442c4501c1c0001180d201c28a80c0105102c0503000030224401e40c6072a80f04501c80142c0000713840b26800d0000c0c0c40c40c0949030541305149803e8811683d55103042a0344203480031a81d00500509219030031400558070701071201800000c0395428010104044420700800c80070009507405959a03140140c2d404000c01000e400c8000d20924110050050a20303000c00c0740d84194101c00200814290703450020302400c482c645401920303050010000b034000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374010863 1250 374009613 374009659
    0x60a030605040f09080315041d01091b050102030f160606170c0604050a180b091602100c0818010608150601110a031407061b1e031505120c 61
    0x107404880c140305014000c8003c5041c2c51407080c0140c08a2002c1001c40c070503405000200600782d1307003c1c202090b002c81c20300c0b0b440071880820030074504a9442e15204030070058034190500d61451164044c0c2809400e12000031b659001d00344054030b803180d00003501604c00441080c003090103988844240300f80350b162625107144007400001001310348240c403080d1082e850300c001941e040d928040c0480b82c2403440c0c00900890a580380d14442240340c1e030b440411116481d11501940f1460114100013440c8041e020024039105d200d00a10700d030289080e14910b55035034440440c68000c04034200d06414000308044080c014103241e4006031080c82081150f085405003003281611400e400d803a2100c80742e00c0011410744410941d0f000034006030419281c2c0c80a12034580142c840f8600a1b280081d00c104915410b0706100050303848000451110b8100d0242120b0304515101104800d25050041c90580e81054440740e840703002e040c2c8643e545030402403040c10108144003041d40d0003407110b42c80107055501c500040e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374012113 1250 374010863 374010869
    0x2010603051002070317151f141303020d1b08060a0b01020c030a03210203150f0307030b04080306060f180a0602010608071e0807090213170327060a0306 67
    0x79020380e5030360701d40300b011502c2a10440380d09900c442031007540e131110626013004002c007a1b0034481e211551003440742d250641c00055124480704c00440381c04044001426034100002c020001e500100300d011282044281104100e070707130689180c41900240d107003101415182d035148003080002c045000403072800005081d4080d50340c3c070310100720921040c0700480c0c492143c0c5015035016070010310100d000a22582c08400d80f5244111264916011003000303505036031060700c0b021004207190700414158a400c40740c043e50051f007240103041c89032440d541c0c405902401070010300080c030040b00040700761312100301b02c40c0e443e02c042011a80c0c883c0701c1c05a146580101401480c00342c0607803480411014014401d40c0c058030340e5000185480c503c2d000d01031010008035005000c0c3c41c0c40d1002c000403010010000e11001e0a208000984c49050034400d8540500d41039200700021405900e404003088804811500c1403114614590001d54015001b140030181c08101c1903000480090307521503a51b0701d6030241d03081e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374013363 1250 374012113 374012123
    0x807060b01051e1e04030b04031404150513050d12050904110a1e030e281b060e03030f040909030e0a0b0d050109020a0906110f0102041d0907030510020714060702010603 74
    0x100203084c4c50300b05050156000007001c0c80404000b04000c640102604503e1004080ea62468642c840801450040411320000702054000c145008000004600d02d4050602500c40030000f080302d4840034101654803021a09001d80081d4620701900c8682003298030090300d6460503522150700c0c80041a2604041e42980340d11030101403210990704c680607411920500304000c4c110354029100320703a02a20001c4102515800011301640001c5030800f074441c4145460544001091900038042e004504443c2d800303201e074201b082402d40d04295202585c044d82c5c10f0701342c00660a01ca500e42641e221141c110601d0703111280001c0001e4513184032004001c0d009030004144000e0340e039500c04006901580c015075000c00c0c207048041c00f078140714000e0340c2d02c04d449041c100c41540b0003140f00c45003241d0190b005904d0f18055130071000c541000052419400424041c028194a40b8684400391a060906210100b65800154800910401c1c2c02100c10300741908081c0c80860030030001c007034020091440203e070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374014613 1250 374013363 374013397
    0x4080105061027030510020a0f0f0c030c02010c02030604141b0a270501181803090b0309070b0408030903070f030f0f1718041104030807060b01051e 65
    0x1850034039440c90480c90101c0c1d101d80b60010340302c0034080c2c0c58443c0c070141440703103c182600020208000308020490b50050040c0180d031000c000400400440900e0303d580148605121030700c2600e0351128035a8603441e098030f44444440c01d1840102d4458540d401d0184d8035119460900061101800c0e41c0340051408e4011a21048680400350755880f000801d1280d10403003640f0f080090381a50920401c80312220110b05480100c1502e245080311000e8104450046014401e2041c0362032070300c00d02c940402ea10003007880403000d5540c0100684200c0c061081400c10100125501107400c01c10320025013075000e0752946564840000aa4075001200d02e54428805e600d00025041900320181d82640c0d0071000609101c041516848a42c40c6d0040c022580d0844000c00006070300e1004018102d8046008844024410306004000568039401d070b4100151a080100b007000550880484c1c1c051030f44172030013103400707051741e40180d0309405900a8000c100070050380c0c00c00c030300b1400360003004058840e401d500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374015863 1250 374014613 374014621
    0xb2d0706051014031e0c06160b13110f031014040c0e01060804030e03100518102d0902060f0c0f010603021005130312030617060c1e040506040b04080105 67
    0x544078004205046070980c01c204032178003410044140c1035030904c0c80d81045900301e00ca1040072610681c007901d1030728508039030101c016003000440420180c0055440ca04451100b02c030b074486055280500c1d61091041c81c890303009111586003403090381f0100710034800410484145548488020404aa086900328007120000c0f92030800101c0c500d059408076600c08000355201d42d401d441910b50951311580c1442201c0141c0f503240f14601032640704e0709807900001c0314000200c0b00c452901007104400c00d042406c0103080d00100c41d5002c51201c1c181c441c12440051a2010b0002a008160032107019400080c00100000c0c20010070b0300410384c42c0107039030844140d5090001c54500b03c5982d400000d40c00200200250066807191000e02030045419011051071960381d5559002102400d12010100c0e4032050b0030013000700030108040b00e0418a4000d0010740c0b920b07089010580c4140d603044080a40340c101300208410104d401e1f9000707400d01520f00b40d560741e220040480e00b9040380c03150407039179801e0800107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374017113 1250 374015863 374015879
    0x90c120e0303010501050a090302041d010510140d0312050a050702120405090a05060609030d120c081306050702150403032913050a021c02070c0506040b2d07060510 72
    0x4820300d51011005541140d00742001151154000c28001d0100040900c0120259032244607850324880102c810100145141c05008e080d540010500c080101100c102000000d01c0704008600f410f0b411200518404010310b41542c42c0c0001551a002301407406040003c903442540c841070140b00325400325044c58104002d02080d5100381e0040c03981001c254000b06404001c942c01c8a5000000104044c0c10100d840d40424a0402c2c8602d988000550440d455000700007103218580c00e050342031500b05d1451610701c04d280015140d481008001035500c400003011548240b205407080601c1307400c001018209824000c0290480c81902c088154911071040743e0038080c14010404044081c1c600c0c0d400340071008240700204802021002083d40130850700154402c440280700ca8180404401600d5904a04090700c8484140d0000c50146a040005004c030b9541e4038240d5215020382800c50503109404c44003c0310810b0ba2000c00190241d004c40c00004003c000e42040d403040c0394007064103800956038106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374018363 1250 374017113 374017121
    0x190608130602220e22110d1b0b09010c0206030705070b040c0603110a1d010306090606030203100609030213021602060f03070e0301151707030f05100509030901120905070807090c12 79
    0x84002005610205d01e42a8110401010180c0e00400c0c91081c5803103400081681c1300700a4034219803884081c0328100c81c0b02d02c1c00715418041c040300d241c0c8a00304044403001811007081204068468080171000aa5103445201110b00c0b199200b5404052030409140c825030b2250b8900600e00400c4c10089a40c2e000309925042e5074a400071595050820072880844640e0003104188490405851328030200d2030300f0b00b6016020080c01d4070f0350016901d1034405403c114500403a005401000b000110420240e40d60329564000c04004844c0140d49640107200409a51180360000350003940c0465500340310004503000d076100c0d11050321150410703c500030805080710201000d000e0030500034a01484240382e106540340c0d00101c070000300c602698907903c0b81440c0d0425003d08603803540c0151038104d03003001c0c18050305801c1144d0300c1c011400c1104c0c10001a1450f1840500d00707400d180d80d450703d2002d0250402c660300003000d01d8030a80d403a0036242c20010000e040c1001c0200d000c00c02c6038009201c17901e10b41c42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374019613 1250 374018363 374018371
    0x4050a0e0d2d0c050c010c0f03180906080c0a0f120b1509070f080f0708070c0302010b03070b07020310051009050603031603090911030105090a021e04060201140105190608130602220e 80
    0x4031b00c40c00f08c40e5015244080b81050403c604841203c000c583d072411440b440c0f0140011000402c0e40c103042404109020300325800400c95040019000c02940d81f00c021780072062613004035102c0307460351400c0640e03245802001615910440f05420300101c590815580100c201080c0d0f01c2800b43d07600e0000016940c1e205451400000c0c0701100000c0c0483d00c0342c1070004210340b080c400420613580b400c000a00d800402d4003c4d813000040041d00d40c0842c6002c0040f840c500c540d13540c082c025840c2c0f110110000c210188216402c0b907403943c0000d41e19a500f03200312003010060000284459007542401810710101d4000d4414580c5051224903003044c401040c2c9040304c000410b488a541d07141516038001e500704400c11300001c81d0313006410000340c0d4000d01500c0504120341c0006041c1d0603441d1802c025000c103030b00c401d000d0b000503200718560703591803116901513920500301002c0c071703490707130310074001d0742c1c56400b001906c4c140c4041084020603070a10184030b40700d20065619084c06031111408a40780300151 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374020863 1250 374019613 374019623
    0x9051e0d021201020403021807030501150e0d060207060507030e0c03011109120c121c0c050a031110020d02041d06010207060e031e0c04050a0e0d2d0c050c010c 70
    0x21110051400010b061041c80e00300d800981001d5581c0d01090300c6500191241c441c0c02500410041019454428940103101c44808030449220640001c0c0454200c15203039802030f036400f202c2c8400d1094980484903490b510220070052443c020000030000e001c140410496800340c5161489989014000c0c4225080a01190752034241d02600b0801a0340540032200900c5c0940040b8508aa4581c0000c901207500e090242003d04111160200c611000c2000340342400407085a1001044000402d5600d55a26080140c000c1b481e00902c07a00d48910780c108802d00034000100c0c103603851403540103042110700d2504070707031250700800c0204102024111400707401a40080c8007088694490b19442491090250680d9103100949107921a03060304111090820307404244020710760709103131048543c44210301c0d104108141c603d40c1c25075100d41902d80140e0401180c070700462000d009014003020080b207810421000c0e0101214003408025003c04203840500540a005240707500a80c6280c0c142c076842 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374022113 1250 374020863 374020879
    0x91f020307090b27040e07080a050f0109240609060902090f040b150d09050d08090f0c011409130204060c0b100b07230105070305090724050a0c050a0309051e 69
    0x1001009411844c02c68000c0d03100e912440c0c1c40d104076030248032100241208201030034440203181095890a00d07039909003501d070f03858414100042001c400c1c585281807255240011050560984400900101d410a2100314507040c4000f030300051550091801d100207036107003240c1c0781c2882d0800040360442c4030901e820540589003c0c3d6414a0000280802e5150100004a41d4200d40303510345040301b407000301030100303100c0300c14080204c40801880301c50020000082a1100c9130b000000c4c00c41c5007800d2180c03040d0b0310110300030039156035041e005901c1c0302c49003900f192165556140101001c100c1c140a4482e010440042035611446c2400041a01e0034042e0a910b4400315550f0120314107000000715007075034424201c0380c1e500340d001e000d2140640c4032540c0220f00f0b410055081c1e800c05041e80d0140d0390804500d003c4e50030b5221950501740c00d070347c041c2c24031944070a140003050b540e481040d48020240e000d007101c0035040540011004081c1e40d01034814514502c141c42040d05855110048290301c603480b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374023363 1250 374022113 374022157
    0xa080118261201090605040207032718021206030d0c02151b0a02130b0f041107080d0c2015060604080a0b180106050d0b091f020307090b 60
    0xc00ca4039800d2460424020440c81c0c0c40c400754012076004000d01e0b2100008980c010842e1041601a0001a000494045103810f00c0c56402401d0300804010400c0d40c61101071030301e0341c0c2c45aa02d00960007030031442c500c0c01000b0101c11241000350720448031301054001ca500414151700700026010b44900c1c00e904d410313226800fa40c0810030341d100e0780202442151400c0000840c07454100e0030442441c598070004040180c1107204020f218800c04540c95038561a1040039890303603841540709000c5180c2a14006680c1c410000c05030740038443e401e030190218070300103040e0040c000740e81d101d034804002e00d41d5101031059202c2200ca01050065000d00311603404900b900b80d8007c0402c1c041034010f040104000d16150392035446a0400306440e0b41030343c0602c181000c11a0541080581c0311040040c070000b0001541030200043c1c840f00c403401d0141150701c1e07000c00145100c4041050466020224240521303501100c440c000180d4401c0340c065000903a5004000303007403860042500d4011b081054102c2400c08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374024613 1250 374023363 374023373
    0xe0322090e07060c051006080d03050a0c050d0509030c060907150801120816020a06020a060506040603050d08070309060203160e220e07050a0b040317041514070209150a080118 77
    0x310b24503080e170f001e00490445103038070407840c49400020b0200714042c000300d031071031003000d001c0311030007800c0580050038031031498000c80c0d0100403104040c3d86003030000b032981c40305245030740b80d0700440524182034440c1c0000d1003081500000c0080c121114040303034808101d07a03683e048541d50420b10503452601e100305045800140040044c145d030044c07200051500356015000200d0303540f4954000e001581080c0300040a007c0705001d0142d22031001e403030600c01e1600d1740d40d806903268051815401003001d44400316980d54840d801044146d41c0040080d03403241462901401e8402c064289000807511000080519060803041c0c82403122607114034907820708150f0508000352800c03a21884e4103000361040440e460356000190740141640a840c2a102d0b07055103054803055106440c041c0c083c070000d110404c8460791000700c2500d5030000d4034210038500c5640076191814003030480025403041d0600e0400c01d07105103060b510701c8a05411121144880e90b540842400c03101804404c4804502e140701000203e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374025863 1250 374024613 374024627
    0x1021203041e12020721030503060307030822060305040c06140403080d06050f0a08060114060d050403020f061503060103020d03110d0809070911030402130e0322090e0706 75
    0x107010303800c0b8001e4491095001c0c0b10000006038115080c40300440c10741c54050741040102c01400b09410005101c002c0c01d158421615605130004041050000004804d03840c1072103840c00070341d4001c4035503444610017091150300c0a1002900c81600c81040000914184a03000e401c1c0102d802841c40b00c2d5660030803004480b602d5001e1103000f4840010800000002c640700018900c403558070300f0018845080400300309103600008403051040c283c402c0e00380a400d0012a5160450b501c580c17440c0c01d680024000300300d0134040c900009848501d08001c100901da00401c078002c40700c40300c80039540e199032803420107003181c400741c8640f0390168055401400103040140041d001c1c940030707003000c542c040010b0740012b1508002515481c0041d4040302403000c190f101f00070f000c000d44440710044c003003650000c0490302140001000a8814440c41d12541c00d9016280e008044000014050f6541c4d8a406280003504144205140c1c0d4500741045000510141d1445401c200058a10161940a142543c101c2d505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374027113 1250 374025863 374025871
    0x10512150f030d1106010512030d0203100909060507020d1119060f020403120206010522020901030e031303020a0e01060e061315122301210501091a1501021203 70
    0x40d06a407500c1c41d03942c1001001400021070740d07210306111220080c0c40c1040c106a00c03240c0100102c83c940a009200801501c4901e01c0c3c3e01c03c0180c41755690803601003003000300da00520025142001d1042404600d40245d0700c222580c0d0200ca0380405885070855505a0091680c01c1982000c1e0700c80010b940c110403200500c5015407c0418044840040c0d88200d0380680c3c01203500004a2452a039550f8045c800c1c5401000c04840c1c44505040c891020b41440104100400200c0e900050500d41a802075001642007035401007100d8a6600d4800e944031424900e0200f0f074450710070020001101d0303000e05520f43c1a81d02d0b41d03641403049620b65040c000c0036040025805469150f182003c15101442c00c00d0004516691b5100030540b04602d4006c41261200440c00440a50400c9041d8610007030300e416904440c8400884100341032441204110704a000f80000c2455082055040500644e4120500741444840240b22a0f4550100b124070a5011206540c0503070001c1070f42a04a08800d0003641d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374028363 1250 374027113 374027119
    0x6090506070c030e1c020909031306020102120f040510060b0c120f0d0c0c06050c030402040f0504031e051315260613020702041b020709090206030a090519030f030b01051215 76
    0x40110031b034001580d50000701c60702000c5d82c0c408140e5a00d101c2941e40080300a0409000852800c40201500b24210100034001a0b10fa500d000c04282000b03001c110400030b92001050400c1041d40b100400c0030f03a44d00450701c403115481422105024030740fa00c812224420003c0c8011450108560310410144c60344012050a00222440d580b001ca0854041c1521031540070300e1069480c5440d104000c01c071610621400d41c1507150030100800240c110f060002c40d1005181c40560b000f45104003200c1900c9900d01c0720000c05416100061581c0116110180358416a15138009402ca1418140e454403941c69500323102010150200e20a414480040e9541070030310385000d0b00e010b0030b0b500402c05031032102e0402a40040442c40384065a9418820316018019078030081c01008925000100d81d404040e0001c032201340e851020f40704111040241108000070403819419144807414003818a0740c03800d443e00701080c10210441625849a4111100342c5035094001d9646e440758401c581c10307126201d4010b90 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374029613 1250 374028363 374028409
    0x150c020d02061b48060414120a0c02031c0504140a09020301030305070b0f060114090a120c092004060c15110405040e030a1403101206090506070c030e 66
    0x24a03aa101385031803400415602d1440d8651492220b0002610503142c18a0300d40d510050404030024070218407107802c070390440c54140c1c0d1454000d8540741414210082c442d81010009004a1195000b04030040f1290084050f25a142e1040b81b11b014048124400000000c1d8104000d121a8156079000140290013038907000d103407134803602034204a034401c4e08250041500419410b040021815140d988010b0000b8102d44a081c0840083d146544421440000d0306000c1008289521080082401400d040420a0048803d4100070080d0680390248004140c1041529104040382d180c5024007600344004151030326180540884418031351080445100c00c400701d0313080e0b18000a0040300320303c820690b101c546e540d18250402045640f90507030540c0303d801c180003207500503402441d0380020941440800c0c2d80c07035031030311581003403465603030807080505210391080300900c1129404240c2283c4603004440040e02d446000303032240312000000400061105070100c07041d061900000017500d070150084c2d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374030863 1250 374029613 374029627
    0xf0504030203101d0705090112170424110d0503040204140709060f0e0a090902030f03070506070f181a0f041d060612010e07050702030a150c020d02061b 67
    0x81c03d200319031204198007a21903a11852525098404000000c1650700a043c02440c080204060709014030604061000c03d080c40d07018001080411700c060f200031554607070313100c1e01d800a111560608900075502e018241410850b820702a00c05c3ea04032a1000000f4443d002e10408115003c2c0e00050080b60040d846802c00b840001da540942402102c07240c903100801820850014071900304210400200301e02c0002e108666140e90782280c0c152201884c0c08100118180003091030610055044003a600c000a08901071200110702036028400c1542c0b55200ca001c4041b044861100c0c90340b4040200224140070045111120005914a1800c40b0440c0c00c0280040c27003500c0c50340040d8428065880031034188404080c0800304154884e10440e040c40c14140c1282e0508401c450500070340010402d040049080a4094010b5070070280e4000c6c1102c003011500d207011442c0c00c0792a0503003000c0c1814008c48250746800422500d01c40155940207109a80d2400300c2c1a6803114142414011604204811 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374032113 1250 374030863 374030869
    0xb07020409021f080a02070305030f18030d090204060e0402010e010c0c1211040c0302040b0d0906021215040c08010605090d0f0c06050408070608041101080702012706050108010902060a0f05040302 86
    0x11299000d4240000c03c4155940b0203000f101e0000e05425001e0302c10010480007a41002c240c94215024003a010a542d56264802d9954150a400032000d4440030a40d440010750540151190f91b01c20b480030301c48943d0710f00311100040700c196802404600700310500707001940f1030300003505580e00407008404466502c01c6810a80d6034205000c2e20120071860020308142024042c590307007202c0c6460110303d03082c80c0070b442d502c090007a580c0b0100324179110817145050010355019a20500035011270410310341070081540700d4450801500c00d02550401e00250002e03401464001c0c101c940c0c030340342c0c103152140c1c40c810011016650b15007185c402c25502408000b00d080c0405800240c40346450311035581d41000b10480c0b815003258010303405c1000c0542080300084082d11403d00d14442800c0950480e11500c3c02607002d803120245031100c9c568036000300403c0310300343c0d503a07050790a0044008000c0c0343d80b1006c2c0035098a80240001e50800000c06ca440b071701070f01c00c003643c0400e60498644542002e40fa9800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374033363 1250 374032113 374032129
    0x212160905040e01020c06060909060106050c25080c030109020102030a1b06020a170a0603051e010e2e140f090307050f01150e0402090c0906090a0314070b03010b040b0702040902 78
    0x43d8001d180c1d40462a0861031100b000004d0708130104a450403c140307001c280c01c0f540d0f100140104400c0000c00300e18600440030130400da02e82039000320764442418440a1070b24800501500c203030380a030300c2241f0141d016820184549442d0b030390180d024614141a0185c142c6014080b00047d062040805026074089412440a000303009640d030744d0341d00344070b4a05150b880f980b2401b6010116241c5000000c10003c2c40000c0e141030340000b00750412482d64542c08105004007000b010b00b0543d8014071883d038142107003440c40388017006064428904c454650085903002c842e0540b2003605410030b60400704402240074503046500810b150122807420381303240d4800703003000c08446040070b941e034498111a44103a030b101c524101402245807250341a203465000540303028800780a07060566030000c0d810540c1c3d22107804403018001c000c0c1584011035600c0c50405c850601200703001600303000e809401300c1c8514620007264103d40c1d080c040309050034204136010308564020b040480c2d010f55a81c2c0342e0001a15491a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374034613 1250 374033363 374033381
    0x130203030d0204030c0509251715010909140c090d0510060e01150f0c0302010e0a0305031e060d110109050a09020a0e01020f1905160f06020709021216090504 69
    0x250701c5a2842c5004174007031113240c000600c03583c0300c00204100b101e4480c0d2208844c8494100a42071040c02d503c054605e200074508640d40402d02c041003203000c000829010300e061000f80e9491042565481d024421114034455450110080c0008030f2040c808140c09020405c0c00240140582011541c030700385005000100720780215108c2104100c140110402540107114175000c4015800c00040d0042c5900c2000020754140a200c4001c80c00b4180700350310000c240078540d0201c45255000d400e0142c5030f60000c446079400040f9100d01e004204d41b8010201d4010320740035042c1d09a5a1040d41c500000742c2d9440b00b014100b1085d41000250350340d40d4981100281240038005039036441014000b400707200411300e480c0c10343d4003020007060316000c00201186c41071292048242c40c0c0400e80b40003410000031039072030703a01d04d1803030b05000c1045c5964812180c2202d60540880c1c1c4166900d140034002d030300403485070704d030704144180008440040302050565146000c0c33130111111034850002404a8036900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374035863 1250 374034613 374034637
    0x1a0d080c01240b0f03010b070c030203030a120509010e0309090a0b060d06210224160803090d0c1a0a0e0f011a120c04020f0705010c0816081005010813020303 69
    0x4280d02c0000c20001c240c07400580102c40c0c0039480c140001c0321601c103d1006210720920054006050030910540e003401201555005040d00e98900b11036900030308a103400d41c103d000390341c85e100c080303280007205104010f00c07582e0f800c0107541850740c00c00410280f01001003a0a030165140c140312a410b03542c40000b80190320a55238002945401c14403411030107001003c599181481452001c80503990b82c00e01d002000354184210070000700944c860041c00c0c0500803180f0b0f0900e05030322944040210440c06140b041e00200115000e07802451003c88031320005c65805403100340c1200c41d12258401e0071420316404801014003042405075031030080c2c5020600c0300d4984c00c0340d565904c00442003220807200058000d0441e686a203070180d0a80c00780c0c440c4d00d401a5207104039400281001045002c2041c4e030446d0381c00100811000d0f80016010b40b95010444001e00c440c05000c028500090182c41094018040501c9030014582400019030300030360003070711030300c008800030351180c2c0180c4e4104000c0050081c1c030303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374037113 1250 374035863 374035901
    0x41404020c0f0a2402161b030c120b0f010303080f04030e0d05010c02060916050607060902090901020d0c0f08040b070203160615051503070e04020405060313050c041a0d080c01 77
    0x70742c504e0f002c2003c180000e18034030307401003110031031908820121001043d0840c0700d0301d03807600c00c1d000c6200c0e103000d541d4401060034503030007000604082240001e181c03450040d440c000055482c0354120352591403d0100402190b60200401c10500503e40c809a000d0710a0401413203400c02c00001911104e00800102daa0380c2d15a0061201564103000ca684c015188030001c22070307030342048245061241c0d03c0c00b42c00c1c020900130030b0300000c0c4038a81d00040c0c2140d401504503101818403032102c0c3d020b50722803002450b0030786c2010110f68020b03100b07202901c0000c0c1140d5801020f526290703141702c1c100b000034295004500c0f0910921494540916a640134035101e0140050200e8050042841c80d82c820742c0311520464184517654460300c0340c0d004480e40115146802030144a854002400078041c80c1c0005802140c088204500100f00800c1584410b01800c12100c0d0281c040c8104026206110201c02451190706d03251081d03410100c403201c00a40c1304140c0107040603403c40c500c17803c45200b003404040394661 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374038363 1250 374037113 374037143
    0x90901020711030705181b0708071704050d0b1803030702030a0215060117092e0b0d0c091805011b0f0311040b0901050d060303020c011103041404020c0f0a 68
    0x41c2d0740064050500c25405403907244c0c9030200084c0481029080d280703035511500005020140b02c042c003450310020003030019407a500141000c800c4c0760030100c070441d21044184030030700c01c0300000400c0d54120b42c00146a41090180c3d955100d1400e00c000e04044021014035900803011041400a0340c0316014550003191500d00680c0020710303000c0d164850a175078280181c180500c3c1d9a006058052100420040c0c01d01e2740c8901d5241c6241c036036180880340c409a4403d4610034684810380b40c03900e1070f0340389000600900e00944104810100f050200034a1b039568141d00300721131002c50f0482c612440300c22240d4401a4181e031a0f00f801e54111140fa408000026500d9000300c40c2c000c614200c0304096460100203561207410420850701c540d0081c40d0f0784400101d14200d89a104000f01c0d00011042c1e1030034409581e40f40741c040e42d01e140b150300c01030101c3e1010100c82c680150001c2510100c07080c03400c101c036202e4020f906020096100c8002e0744401c1c024804407000d001000c00101881a11515400c81c4105c3c3c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374039613 1250 374038363 374038373
    0x80121061b120617030702010f021e01021306020d021b01120603050303040203010c081e0c0d0903080907050d020f090c0c0d090302090606030105010c030809100608011512030f03020702030c0909010207 88
    0x1600010844400132500380d000c1c440c004240d4000d9503080c24016410808642c1c140d2610180c100880300c0c400042e110207030035050640240c40d0203c00c1d05049180300c0c0c0c48000aa85800e0f03004132550041c0e000d1121103580c1528503030342c51400070043c1800c40e40b0489001e03100082d070f10f41d5041030f00c00340e000005000071070609101c0c001c1c7e107850070319014981e0708111a11444040d0181080c07403005000340e0208403c0b0400000300e5084843d401400c10a00301289070292241c141110b05510f64047c0302d000044074240510030404690307000b024948010000c0041001c6140054002055900c050000c07001180d010000c50840500c1600c500c40540e10307510410012440c001d10460140320140700401c1240d8100c254010119410304140c54a0395130645100c0c070300420301c015046100e0400c44005034800e01940110f00d070f40703240c0542420f4a0348940c032200103011903110090002da0401d4000080c94400c0c0d000d80a864801010f846168402e0b42c00629035a1096614501e00d135800184013003084 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374040863 1250 374039613 374039621
    0x7050d020619020f0909040b0601030e0705060a1103160f061112061c02030118030e06040608010e041a1005010305150901090e2a0907080121061b12 65
    0x41840207011510b404003180840d09524035024401c0368000c0340c0c00d0a01c000030070540b6010310f0054000001c6150905005070f4402c1c2c151003072400310f46010f038100141000401d20788240c840c081d00052500b414840101c0e0552410900400180010300c12046500705005101440c01d000d40b0350398415543c28103010040b07610035840f641100b0010803540078502d20b0f55404503401303401101c000802d10030245507d54070020020000b54907501c0d200c1c80c1c442940d0494030480c80180240d60f10040c492015043c00741ca4407481c01a035012a103280010084007408141c51a07109102e52100c2c003c41b4017581c040014040b0a4482010300c440d095014005964148103150340006200c11810752240c00f40c001c101e040c101800707032a80158880451071154841081280c48020350800d0b0045a10740405503480d09080444a0342c0c4581c03800c001242905200c1c90315141a1148940c441061028000020140d44442801243c0c01030712000310240000c121110b56927038500b50703201d44200100011070b8400316 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374042113 1250 374040863 374040883
    0x2010b0d0f12090812161a1005030303040203070504110412060c030c020a170f0403020d0c1d010f0e1e070309020301180b0103060b19090f0b10120f0f110705 69
    0x1c00145010041500300080f0611101d0700f80c5e01d616030300c41a44007a0410104510009080701c200300c000c0144007490a07030003d01c51030111a040c4205a2110304050301e0313100949010f035050b0300001c3e060141e0325240e03014114010740041014941543c48007031202030188035405443c0982c0d0390ba00b215009405004030031981e191403010300141842030380c0712104100e454400c008200c0c0003084e21408915282c04440145400034154010581030340ba05551030b003142e0240e24902e03501004400701c0044c0810800b416540980d8100c01c1d6142840300f2800d03030210080c00e40310a18034030700090b1114002580c000b40101c809540115880d031460043c5425910f8000084005003050b000400214484100140c1520303480100821540380d0b810008030418240d05040c0321460411200040e5400a644141042d90b1409810300290810100b04590600c1a084410106500070220003080d01a40e02c0388030700701200600000d806401d1200201150104030304107070840d0000500d402840000c128903484 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374043363 1250 374042113 374042117
    0x601052505061308031f0906080601090b0a150806010c0803090105060a152001060803030108060a050a0b0105040e0612120417030c07050d1707032d0807050a02010b0d0f12 75
    0x3e00c4038503a100c42a91000419050191308a1003044401c4a00c030201c08005011080062007810388489090741c64400038030525007020728000084511307081c507000500445001c10f1140c041200c4a1b54140d4122400901c0070307040209a1002030005100c404c0518040d161003000000c2616080090201600b40c5800020644546040e04000aa44102101e03e550350120800d0700749280c00326a0b90141c80690040e0600c1e00011001040c222000549203115140307111040c00252100308801c4200c520030000c450015404000500c800401c42d560303240c0005015100030501c20741140d1490400b54224008440b000300054104043d10303055412a04001c0110040c602e04012a242a5070303440c12441501d001d0721820352184180100c0c003074824540407052285a07626000e62400030202c091429840c4803035200500f041d111140301161940d002c02c081e48032205103031910407041e14240c025016044c2190b4030b410f020740b1076480c3d011511090342c0c4116025445104149040185104c4400807201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374044613 1250 374043363 374043391
    0x9030d020c130c090f0b1905071104090f06141506190c21030b1002060403020604061a0a0305010f0e0a0503090402030a060506031006030501050a0b0909060105250506 73
    0xa440d511006914500d55600d4000500030360004001e8036040603a900046010072540070008140004000030b024071400c580c0001f022100e40d10040c0c6003800362500140000d40816010299828154042103a803405503015001e10360440d962101030710000c82e6009140072706003040c011082d000300c02091555408a03444c500304001840e07040944a904d500366010008560400c00c248015040000400c005c0845044050300a42e030001d8041c00c0341a040d18020305440080c00c0ba424404103a036030095505034040c3c4080d49494032104c01500b07400b20b1140304004c0807540c0c0040b5680d020a107030001c612410011640503603481c0b4170030444040c41c4c0900c2c81a00001f0410000840200403030303200400880300162031351200d2050400038070183c2c0110b40c02c800e0002c00e20460360300c0b00b4100c000b2501d41e0b41d1b0622803aa203620901031000c086205549010900348140b200b6481c00c42c11082e40500189030050508082c0400048101804a00901c068a13203205403004e003c01400403940c441440000c0b65 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374045863 1250 374044613 374044633
    0xf02010c0903021e0103021605160501030501080607030e030409180b0c030115111e1005090304080a0602091305130c06050a0f1d10090e0a09020f01120f02030c09030d02 74
    0x3031680c291321500d40070541c148000148050b8040d50546102c12801c540308047c40519143c00383d9039100e0203544c00c11b620914000040c1641c407034003800d41a2800800900500d48954205a024055103d4014010f010620003c00c1c2c2c94001d101c0e11401c042c2c032202d1410303008942e081c11913502d80c014040c00c801c01c0d0300300010300c4085503400305084010307014035000003003030003405400d810310f180c030800310402030850840d410320042c001405400491b010b00040066803540010300c0c0d17880c880d601c10100c00d80c00c08840c1c00c02050780c40c2d02400c075414010703203003035043e1109104440031a44100c405a6070011010320301c40074401800b03c4e14000c0d03c2142065881c12031100c5001d00f503442c00c0000c0da002c1140c0c0101c010100600c40040c1403082c040a01784000411240c600607142141d10300861442e4141c003c00500405505c1c000e4544840c0c01400035001d21a094004450f0124001c181120590b01c5400301c0d4001000c034070065109a0707407800034a444d41308a404240c1422146000c400840d88100d4081d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374047113 1250 374045863 374045869
    0x5040608060c030c0409020409060510020703051c030603050f010e0d0906020309090915091e060105102303090a02010e1801210204050a0c030c30020d0c0f02010c090302 74
    0x1d1500302c185440281c0c2c9980e034946100880b0300c12034110b014868000f0034001040350194000d01c041e07501c11030300001d1411104104983e42c201600c80a002c0354080b21124000120800364400000c91034070300490900e449884440c6415440328110b211070b91b40f10302000c5204814000d950950300c0524044a4044c41c120000b982c03400b440c40698400c10340f150200320041e5041240b4041d0050041070030700b540c94607511464440b040e012900802c0d80241e11101240c080116810381641c0c801840c09101c00700f600004c80d41800544e04002080080c2c0b000c0000c410039040141d4811207401d8024031f0301400d10300c0010102011542c3e10703400303100005009681c2c0003102115505588481d01911400540c0c040900070010440300007035041843c0c4400c3c007040346d1858104608424064070140280341c444034003155501c20049507640c0040c012040500903400b2012244251000b076180582460f80500801088410030440c84001c2010031603220034040e0280210007a6840c2c5050800301076180d9004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374048363 1250 374047113 374047123
    0x160f0203130b09010e1c11060f04031401021608070c0b09030a03140f0423030c0d030f03061802030906060402040b0a03110d050c040303030b030d35100f05040608 71
    0xb0180c1156000c01c180f00c00307902c940070f003281d9a071009001403c540c0c80303150102e014109140050701d07000240b90702c003012420884100d500318400c685209190030b1640d103034980e0702c07081c440804110303540030441d0401d150b20181e4124281e130700031060310b59608540e14007211882215481003103850018080c41c0c0303a50f900030904481e140e41605000b02c0e04075070f1640c42030381e84c4110b50854107525400308020407800340801d001e02d9580b403004910024920701008050b40d8010701c254407507001c2c1c0d0450403800000e100da490050010128140880c00e40e8907804210800f40001140751051a0301104004c0314010402030650000825202107203494200208501e142c4120b00c501002d1507240c0a00310240c00302070b41181c240e1814150704000030306004001c103401c1d81c0648010340010b401c0100641c0c2d281b0303000c40d684002e20451388a5801019404c48050008104c0d59400620310036642c202c841c9942c1d481003814803811b00079100100381030400d000f0011342ea00300e401c030900a40c506001400006400a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374049613 1250 374048363 374048369
    0xf0f190e0d21020114070909110f030c21010e0a0b0405010812070c0b0408151e010e0a140901020318070506040311060d020c0309270a0b0102010b09160f020313 70
    0x20a820070302c101c80c04141e02421100b24117050b10b00c20301c420030944540c40354041054611090043c01400d4076100c06401c10301404407180c01d4048100003064404050100400c400d411a00f000140e10a0601600c2c041c05030036403007851032080d5001007090059840c0b0828000318030031102040310b54104402e460b40c81c106400036a00440d8009100001d00407148180002001e008100f00d580d55180d07079000d500c84081c0402c01100030b100c0001324000c804066141411a0800051403140ea80b90003000d40a400c00600401c0d405035540c0707583d00384458010b42480c80f4412100000d80d40f0304001560070990b84003a98070f01416000031506000e29906c06040b07a0840e03070007424145589840d0700009420f403040242042c1228070019440e20f01d0100071015007032030715048450004a01701070003003108160b80c040101c0e103111002d10005400540d40d500c04480c00c401840000346600f8100e0101d00d00e0f035425101d8481d8003095029404015600259042541c0c480c2d00c0030310f08142e882078940607130541c580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374050863 1250 374049613 374049653
    0x41a010806060d09210504080a080d0f291203030a02180a0801050103060f06080307240e0c04230708040510050f090706050a02070306020f0f190e0d 65
    0x11001c12015a291401c1d03c0c503050340000308201c1e916040c030300341c0411840c603151808000000d0160061841c0074606a5080b02c00b0303000a00303c018510f98403e200c13584070b4880c8903850ba558210051016500d4414000c03105103201c05006021507811001c1d496604203c045481104240441100110048141c81d041540071801503210080d070781001ca01080e196011903042070000d80c0014168005401180c100c034001d41007003202800442168040d60600e010703070318140c1d10820400002030200844100040b90942c41c02040e00100c1c2240c905031024804440034907481600c4501c2035241512a0204509041c5440e0107000080d20f441ca40c1074100412103824400480c00080038032105010400d1411900380b0204002d103440d90550152401c02d1351644101c1c0320382c54003c030340c1c603000c0c40440d00710b44c5498000301542c07880c640c0c4600c06944200341c828960700062112890a040d06c00c0a0b26121018180001010141400041071108c801900c6c500c605480041100860400c5480840039415a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374052113 1250 374050863 374050877
    0xd02030d0e030f07050d0306050d0f0212010b060406050d0501050904020a0302060705030f0a03020408010c1814010201110a0306060210060b0901030f02130e06030c0303040b030f060d06050705090f041a01 89
    0x1841c401811401007891240600d40000341030010442e0100790059403002d203880c1041100c5d164014442c075030302c50110040c1000700c8414541e0140c5019900e401c52050039400106a541c0d203100480c0140e0000d0b0b06c428040783c1d0200718850300c52828011607001d0403060781c0c05c000d21700c0c01c0d40003e00382c03200030301c006405150000390b09828800e0502c111412000c3d951181599039a403000c0080080d032081c4100000c6500e4825402841427082108910200c201c41c0201c00003820402e9404521030020400340c190b6582d10000e03840281d04001418582c80c00d5200014114504180a4103141086a40c420010f10713151060044070620020303140d50301003e180009042409540d804000d1040801c501c61641030a240058080103541d1010b1142406138203962840304505e043c5540d90003540500b0481c668140001810a502000301c40e80c060300c0140720080300359664441c2400c40d00d0a548100c006000000c0e640081e041c941c0340b161648209940400c01c002c0030003004001c042562010713904104113 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374053363 1250 374052113 374052131
    0x30c0d14212209061211060306101101060e041a0f130308040303090204021206010f14030411180903040e06010905060904151a0c060708060a060806011e0e120d02030d 73
    0x8a04030700c9002d0b11066400f00041500c03040140c9402d104080c00300d0346401c2c24083c1b03070706c3d508080c82a0303806040c02500004100300025025664442e018088100c99982d0320740019408029510300750145000d000c00c0da4240e1180740c81d41e510084010a603031480c1d8000750500c003a0080400302160144d03010300e800521030f2524507048010b0000c044c8003a500c1400410b14540040d00102e015008800c2600c2d00c002c01c1400c410191a462041c1340c0c14800b040c000d01c002000700c2d070703424545c4542900003800150003118000c0d242e518240150f84030446070780085410300c007240c283c407481504035209082c2480440e1803c03002604603c178100090f80615203850030408029408549500645421403504050204240303001e030894114140d590854800c0d000442c1c0813078050b070400d60140e40040c3c0040e80e440d0030410240d5a5580c003030443d504212048104807400c01100007034088041c1243c0d104800802d0750710070043e141a01d00003411058224400d01c0d00d016400004076800c0d02203107803000c210099 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374054613 1250 374053363 374053417
    0x801030314040f030302100b030d1713020409050a03030b010531030501021615090c15050d06061e2a0f0501020f0418060501020d0c02030c0d1421 64
    0x29a034014685110200c0c40802050b4005c80c487c0342500c00000100304250940040680c0c65000c0840100842e0248001000c0a6202d03412140d000d40c0140c690544e00b10036501103011200064015141d40d00320130f44d80000c01d03a0601521848090900c0c3c184e05000c0d0610201c00028604002c81804040342c000c070442d42e44881540d14015500300c0c000319103521800805410700f0f58403080860307001240701c0071236189816600c5500c0e91580c00c80c03c401c02d02400d00f900012003100803441a010b20400b44640706102020b07004450240986030380d100d43c1d08040310034142d50000381e980300c0402d10502482803001403054070f2140a0100ca14100c50200f1320f02810801c04140c4400c4020341154000619008524550402401124040800442d00c1c1030f03100b4640d011a8010701440b401a0003000c04042028410001c82443c14001003c1e10826020040040c01d0003107902822501e07031580481030066803006000c107480303240c00c3c070004040300020034880700c40e01d1140059102d000140000040305103e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374055863 1250 374054613 374054617
    0x50613030c05120d0b1c0609030219060b0f040519180b10080c03070b07020108040c0e040b07030e07260109150608010f020906070204050603010e0d030e0f0a030801030314 75
    0xa8100065600004400304849150b13484200c00f100314a0902d0080c44840c24029401420001e6076100c85003020610380e2001c000e041c514806070114403406c014003d4941084250101e640e1107403c1c00181d1b404290140030b580c0b107083c0d0105129a01d400c3c00c00c81c00c104508800e02c10130200050000c3c0c2803c0658075800100c1c3c81d40c0300540500584002c0090341075031040700d9000c2da0000700881d42d0207010300c42010f80c0c9100b103008a02204000348000c00055000300d40c2c041e0058441c1c54211240c40e11058070f0155808100e80c10b90f149080001442240d5405d840388c0c04130450140e003e04800c0d414204072300762a141e64030801e260402000d003650150b003400e40c49444081da000e080041c2440350100c01c00080c2246020f03a041c15460903e000100c2c00701842100d52150014052a0401e01c01c0c0d002c0000a11009001325015500c0c4c004000c2c12a0050095044031951900c0000b0050080380780740e4607004540070820078030303440302e01104007198001718911b04499051522200b58405001522014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374057113 1250 374055863 374055887
    0x1050618041d03030609060306060a1e051e0406140a05090417130f05010f0e0d0312180b090102030103080906131a0a080f060603241905030601080a05061303 69
    0xe02d03401c18030a0040004070045000c1c100c111503600580d20f03034030b04240c3c5a600030f481c1941c0c013079010102001100343e0242d91b8a01544451000c0100070741d1003021034520300e1381a01080c401440300c0d8105507585002e11136940604440c00d0761464903003013840461440800d03401000e105645120010b01008110801d0a00b1820b09011441c0c86129041c5036807070b10001801940703000c1c0c00c20a004103055201d10f8075001900c006035103800c16110328609001e564812040c0580070004001101405004c044c041d0031800ca01c01260180c5001032420b00003480100038001d0b64407640108010000700d04800d055401d43c000c1254295900e900d1015034180314140b40d800105000c040380140c0d82803003034200290603004010348a40c0b00c1c1740d40b0b45810620292040b240f8540c00801400400c0e044044002c0003070000c3c604070b154280e01c4400e0307800608030760030391084500000c6420509001c03d0034244615401050290003c0c41e0400f8290703191611761000a0003461590700100c0001e090500ca03943d00d40300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374058363 1250 374057113 374057141
    0x4210f050c07050a030b011a120402010c0f020d050c0114120403081f0305070e0703140f09120f0322110103020d02040b030403120c0f05070f030915020708060f0105061804 75
    0x4c4c0302e03a41d20340400d0f9110241704100c03101440d4107407003003010031400494050484069410300190b640354015500c00b000b084069036104024050400142c588502c1e03040568000c00c010030740c0c0e4510400061401340380d4942c0102003441800342d502e208407000f200075049581410700e422f160b40c6100e00982441d02d450003040202145440000c24440003043c40c000ba140352079008600381ea51400d0603401e440300d50358100320310b881010004022920142d906504a00344109881858074003c4462845030065800d08040701d400006200307500f180f1050300c2d041d0868805100c440b07004252150f4259402842c81c0390f05040c7c0000314000c50404a60454010b40f25410419031a81024240241410b102010915616190601c00004139010f240f10440c1c900c0980c0d103051400c0607543c0d40e40c10784640034608a0a202c1521404105000500400a803000303d40d070042c541e652030040c02d6440c0c034002800c10119018100014485522620b007100c080e06a550180800c0714040e00106000300f00f008e401e011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374059613 1250 374058363 374058379
    0x20c0310050105030105180c150d15050a0509091b0d020604090c080604020309030a110703050a0f05010f0c0f050a0207050603010f090b1f0818070b0304210f050c0705 73
    0xd2000140c0d8000c078140c2e030007a00200215510120441e6440303c001e01d1011056001f04840580c0d890483d017180720101140d11a113041c0b0342c206408106a910040141ca10703c40700442c24051414154180030081104980050190900c283d40584500c10391034841e01e40140b42c0440011500c928020880c2e060340584001d9440b80e843e00700b080107205092102d000101c1c0d12010030020329083c003e690081c088107018502d0302c0500b0106940074181c0981114043c0140c140020101c0d009004810300030f4025802c05000c0403c525085003110341c00100400c04601c0d1002155241d640070f10000b60f074000e075003402603540c098000d00b43e1402490340d000a611280000011801c000c2032211802240d03000d0f401032100451079030800c0042c4406040c403429504001008103101c1d072042e080d451b00301c5031250b030f04207042012200150812095070881a20300c0d000000740010480c41054403920000e120005c1c15205144410041c0b210400e81011410004041080d000074041440b100c0020007006120603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374060863 1250 374059613 374059633
    0xc020303030c0a26070e04090203030c010917040602070b07021908100b0301020f0901140f0703020d090e040b0c0c100501141c030804060f020706020a090905060a0503031207020c03 79
    0x12080d92225804500244c981d0280d44a403102e0400000002c0c590500400c0f02c50f51119000c40300b2404072100d1960090311a00350f01301588042c40200a107900220020400d00c2142c00d01d2041c0307080105032540c0598003003004101055000c121441580c04484070385907030b1002030002a403100c0e44c1880301609100b04032000a078414000a80100482d204001842440c00c440201400c0b0300480150300e0602400b000b03945059845640846210b4514036a10f50400c8411105100d541e006074100301c0140c0d200000840320140c12134840402000445400711080c60300d0b03072310864a654058109000340c0c002003040c0e80b0314802440080381151040d4000c00c8039603510841c51300009404019140203031050601062840306144018903010307019211108991220b42e100002030171f4494030030480300d0b030070300c01c0c1c000056082c0000c044d03081407031799800e001c2403c01d6400742c03c43e900600098410309580d407040090351004000c0c3c44001008444a900990354100c0c00d90401c80c1c03403021694035000d81c400784 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374062113 1250 374060863 374060881
    0x1809070509010506071a071413051311180f030f0304150509100e041401030305191b0b06121e0f07120f0204141503010506090c040302100c02030303 65
    0x501110001c440d8503620780da9503030030701c2014400c510b409001c50141103103078010100064441a0014010718006560b1036040300318094540100401540e4900003a008100524190144400784604100100314034404590f65601c0c03840307504c12800310400b0f148034218040d992808030b40c0d400e0380082e0950302548490410603450b43c0c032501130342c0d11060802c512032458031700c00c4050381c081c0580a401100d210000b410140c03402c1010190003544142c4071501c0c0c0803840c0148003298002d5100e43c859540700c1c04070044504000c0340385400c031410001d88984140c407189080280c580c0c1c180c0c220781d8504007030b200c030008141003030161200c0000d14030610b40507665040d0152542c082240c03064090700c0f00406007072540e42d103590700362156800c200c410702603000200d0752200344c1c100b502c2d01c0140002142c003d8012040c0300110212464a0701d01c000903118819030500380240c81d8001811551015249014852066140a05d0102074014a150000040b01d180100040440c15800034110380c2c40e0b1600c03d83d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374063363 1250 374062113 374062123
    0xe1801090606020f0c0d02090901061a03070f081b1c02031510030615030203090316060c020d0c0b0103111315061b02010c0303020a09210515160305061809 68
    0xb521005204158941c0540c0401150340707895110000c012a203484150f070204480200701801d110429580c4510000d90080e0a05a204003d030710750400949070b1628020242c409103081001c81e0a00416804000720002914480320030711f0070700340800d61210040c0b1180030740c1c80d51003440a8a014400400e025142103180f124044260086a42d40045610700c07600300c3c191841342c45880007105c3c41e0b00c16039105d00c2c0240c02443c0d100c2e464004803414200d40400705013110141101c20b90302580d440d402e89a40d00d84c103008400c1010342078180380710407010315580c0c000030107014400a02000144684e045440d680c1d0394031080c440355040c030705020a00b806481c03052003124900c9a0b80c0800c0c1c40e0305500b21003500400304645050740586032907107201c00584090b03010794803544801c1c00300032400c00d000c1142d50301e42034408154030709201c0da04540d10440c900301c4e2800301d03910444082d000414003041b1115442412456075005e01d80380101d2591529008100d0701043e02999529460340d00c81080300c2e07840000380d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374064613 1250 374063363 374063369
    0x50304030f2102060604050402010c0605150907051303021c151b0c1a060a0f18110f0d1a121b06180103051b0301031a010b040509070e18010906 63
    0x58101d00c8000401c9010a50b034000040c42000740c0c02000c0012030038940796100642c003078018104007508501913aa00d20445d0406c980c440342c050f022400d000d895040528465600ca401c505100e45015410000040c500b0f0440c40000e01c1750406900150707009942d4129050f40c50f42c0000c980001001045490024000c01040103020310b10b118056070105104d100031829407070300000131022900c20346078440910f1070010801600001c03241c0d400590000b16552840042000e000d50f5802680300100600540b10180942241800e040c000d440041d480c441c102e44405020081c0011701703a040016031743c55401c400b114240d00c480886240030700650f000c108a184c40010040b2034861200c1c1500300065402407a90f20303000b1102034100f03403889500940c41180c02001103080011190600e983e24203c81d80300b40c000b210b188800312012580d041c0c03000031450140290406c003a082c40e0400d0003040c102603000b0302c440e0800c1200c0c1481d0900780c82d0000c007078100144d014907200c181d40c0c4540440c00940400c2c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374065863 1250 374064613 374064623
    0xd0602121618030b040204020304050a080a0f02100903090b1c11040303080a0c080c070804080f0d0212040312121d0606010e0d050c0f061c090308070206041104020c0109050304030f 79
    0xc01e03600e0144030900240a0304d51100a24409849036000d0100a402c01481151203100d100700c00c2000c5048040a4a0705000640e00d0071800c0300b0002000b41040801c0f0f100424a038145103031000000d422442d200141d5640c280744689503801c1c1313442c001982d1258070320829030318900409442d1020001000707001740c2e8002d45402c101500c03081c07004402c4488040120b00041d1800001c10f03070440d1400028408140900021800c2035155a091824034030010040e0030700f070740200c0341c0720344031034060000300c02c80307041440581c1c1014a140c030351941000040705404200a80482a000000c00e10b6100c001024a100810307400c03d10b01d88081c0c0c1c0d0380c407805c0c1d850501280c46400c59084901d48400d207040803e910901a00c40c04032000244100400111426079120300181f00601000b44a03811804404031422008a00d50b550390070090104500901020704540050013004080f4481900460301c0e003e00361401039031125010102030040c200c1c5031004082e8000002c00105100d1b00d03e6108480c3e42c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374067113 1250 374065863 374065877
    0x315060628090608090d050c030408012901090b22030f03020a060e0106030804140102010902090a0c090611150403020f070e0a0c030b010906050304060b060307081f050f0d06021216 79
    0x91642958011421105002d444d403011b0b082084062150016040c4212003208503410245c840011074251000b1b040d45a07048040741e440002c006030540d00040700b4200038201141e138103040c00c4c6580010722550582200817907910382c3c00300f40c07280c0044031070b0000c68100a90b40b0301c81c0f400b442e0003900d40740c2a44003520602e080080341c4521010610501e01165070000c44213203060b180094114601441c26503041c159540c0f00203420260301c2c4d207000544520144040000d018007036240c0500396010a400840400029248101c1d140c000065550144064182040200d40c0c0d01d142c102c0c54941034100300c01e0a13014a4100050003045500840d0040e0700513030040c00400341a074800c4040352817084180740000d007800307020469980124020364200c0d02580d00845c1d0841070a0205050b58400d81e411400030360101c0c00c000c030420b071142d4010324000c10010482c0c40c0d6464500000c4c82c0759072514071030b44591800b15840c020030410360304032040e68195041228480c500740c05041c10001d8440720032400304190b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374068363 1250 374067113 374067119
    0x3020109120e010522050301020a090e0c0406120e10020a23091f020c03010c0c0204140603120a170a06080f07031509060902090c210402031506062809 66
    0xd01030003001c085060b07480600b45140c80d041790540602e0b01d92191501070300004042500d85007800105456031894031071245644c03425080800090004110b45030040c410f20003402590f0340304201a141042d20000400c40404d0750003201d00b04018840301d00a07040c40022080300440e0403044101a510360b07586860010302414182e5101031103141c908541c001c0228510740c00c03d6403001d0003244d0a01591040356908041d40c0b01007821900880203510214000342522021072409008a2407045c16100740f040490a14001103940c44081204039a070401000ca000d240d420b00c1110404494030014008102074102600d00c00300801e501d004800442c000c00e040030038540c20000c0c100d01102e60121500007100b51002001c0000d0070a010121115512603100c940542d07141e0405a00803090809401e56800350740885627a404ca51014a031813020350001003001603138000c9004c4440e0200c03190140507550b12500050501d200f120030711140415802100340142c0c48102c020300b0f030210103455410340c03503032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374069613 1250 374068363 374068367
    0xb011d120a0b01090c0c0f1217070305010f0512100b0105070f0c030b06030613032a0501050a1d0705040c090e0c120a02030f0414030f1204020307060c0c060302160f0302010912 77
    0x1b50f0042c0150944040d00d046000140031402441034218151522481e555032441c082c4500c80700c01d44d02032001035100d030010b0000c83c013106225001441e040342ca041c42240783d6101940c0f01d0700520040701c14207941c0d81c0ca4056a900a41c2161a51179229100b008000403502c0e00d84c5c00c6203098001612900360000014404d400d000416501640580b8184000301029640483e202d04030f124042c040d00c109081c004030410000200c460b4880d215100104403840c0113000030303003251000c000c05d0780074112200c0c90300310084000c54090700361042506c01180042190074180d500c030005a001c0c0360108170140030044800c6600001e400303510005154402c03203440b001d844400340e020544e90500200000070203c2c0c005442e5880400705400140b06032403c0c14648081c218143d00030605005030782c00800d04100861400b48036003c00790446080c081884400c81c1c0720140d00c0e5515003e51010301d0f50006526420301c002d411a141c0413640904c480c13100100c1303450b000707000c0c082a2034115038007144520368488280c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374070863 1250 374069613 374069627
    0x7090609020a1202030c1605060a0c090605180607051c0f170114041415031e0c060c19081206040c050307141308060108100b011d120a0b01090c 63
    0x991150341d4060f112620202002c002d5101910300d03c5020750400c00e02c04002422260828190302403005450585405075201041e500360400c01d604100e404d5000303000d10b80d040815035150041c07030302c0f04501c42440702000c5a018800c00d00c01074030620a02e400c0081810000444c01c030740c1d40c56031752000791700107401c102642d0010040300b5104080d01610010303c141d56000d80d80c02d000f1003000f4408281c03000403030600724403114144c84c0201c1001d0960400750359030030700b000006004160114410202d280100d0529101c101d5881d0661240310b000070125045041004200ca11812000c0f0340c0c040c2c9041c910341940a40d010050b920010300c08280040c900345000d01c0746281c41c02264598900c4d5a40d042d03421101004c0c908030003010310006000d02d4140040d0440804082d08203100180b80c0f55042001642c601030400742044007240c10060202141e9034015a41045040b02d81c0c10789110108040024903455100b0610041030f1240c4081e075003d0181d4182424101c86619800f004440c2454000f01c40702e03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374072113 1250 374070863 374070877
    0x20a0b0a02100e100f02221401170103020108041b180c111f0908131a031303050306131404020f030d02030f03040f020a030f11091513110406020709060902 68
    0x943c0150181522884c0e1a412800000300050401403074600001174040c4040d20040324207800b20041724041c080c02c09040724212800f034003402d110161011042c803d0340003000500000341007296000c0802c00704a202c1258148031484040140b003925140c00c2d020740000b01030094072030340609042000c08943c3c05640245003150031a070140c8041c03000c29640094a140303c1c1c8203e01226512280703840442c0716800a080c400d9a10300e00c0c00c3c0c0780c524022417050455051609400d91300c00820074002c0d80310448035501c200681c54206103449542c0c4030b0004c6c0072840910300f81e031100707800c042920741c00c1480711100a206d14405c03a40b1803c02e08118042c1581d0702d4503c90b003100580ccc810480c105200d0100070146a00620070303a80c070825032149902080e0040019072040b2250205040f03404108040c0c41c2007213420f541d00f5616019a40341c152808202d107080009030500646181d9051a0744c5502500034103100180844c07090703035855a4230b000071350b1802e0a2081089a85c070341400070502d40b0700e078000c50b03a174 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374073363 1250 374072113 374072141
    0xb06092203080714040e010801060e10030f0201200d020d020d0e0f040b03010e1e0111070305070507091a21060c0f0d0518061308030703021303020a0b0a0210 69
    0x20000340c1e0750644140b1400342c80d000502503100384204810b202c0e14000c10140c40c0c801c0088a02e540f401c800c00e800c0d91641d8100381c9420030000d003007061000da5000c00c01c0c11640c10001d6418183d1035800141e07200d11b8103584103a81038511000d49008000300150f0300c02c40070040d0303003210703030380441e0b01c408a8803190307503040300c50010302c0002241d405490101e20281e0700c500010b100143d83c1a800b00084d086664403120018650400c5411800741441010700514550444c0e00910445400c0a102e40300c5204101e40141400f0b00032034808140002004040043c0c8501601005070702c144c090080c030040030001d80688502126580050755010a203001401c0038207000082079152600003045000303800c440c0e08000c10110038000200111454007403140a607052030505d0111111504095081620060842400d04100750384c030400201c0c19030850781c1c041001c1c50010384814440c51140c40702900c0f540040e603c500d54486c04540041c180000f005d07622065001c8070f1030300701c081c07141d9000e44e00e0400040c48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374074613 1250 374073363 374073421
    0x5010617090303160e04050403020d0810031101030c05090409080301051504080a03050c0a05010c050a0e0d030f0e0301090503030c0901090f0803070f0c320612011806080a0b0609 78
    0x2190780521070b0080302d0002e0301d08241400401c5d0b071740410100e890480b803e80045e03120420625030150045050360304194512402c0c59094110f4a89620320700301c404090741003607a29954a8600c07071040040c0c500303041c002003013031118010608248001d03400a0041900c2010a202140507002005084600301c80b0b85601405101c2d03035548054440341c2128a000440b405480c2222000030020310500400034000d444094940440e80300040070444500e41c054050721080c2101c3c00880e41041c011003081e000d44c90142c2c00888003002090140083e0003000380544404810701c000702042d4005804c01d003400ba40d43e00c511503a14603101c14883d01c03c0c8181c900c55001000500f001c2500c0d84419040c0d03501900e44d0101d450f643d690940108452a100c8000b0300900b00d04088104014004c3c0617000320b000c4411a09000145400d546a681c061091140c0b0501400c07014502d58601d800030300007821f40703000356030420f811400c0001c1c64140071140a8420400500094590140000380b903850005d160a211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374075863 1250 374074613 374074621
    0xb1b0c1f0b062b380409030806210a0602030f0a0603020a180b09130507142214100905090a1208060a0f170f0109111c080d05010617090303 61
    0x3940d420410600c084186844103184130550b680f507031000000c0ea039004500ca400881401e6144600c1052049051045003803148150100340e0114000fa000f84044071301400c81c821807201022104518094901503000309912101070040507405103204a012258480c3c00d50341d941ca0603006c95046002c000e5020040d000305000402c001600b41e140d240c0030a000007680e4100c1030000e155240211003d0142e4104030302ca00f002c010041c044600101071010b0703500c450001442c0050056400c107814561014a4900b03c031841c0401600038026114000c241e14100b42450541210404540c1c051001d44506080100e14a403a001440f10440f541090b000703008404859811169500060402d0740e011100c1c16000c20520f0203507009000503e00c2114202e840c0002400c61420f00e4044440d0a20030303458a5440d4000c222201c101446802007150f00750325a80c0c155002141103108a50043e01c6e00c1000318021248003240d90226050700c3e070035110b9514041c1d8442c408008030b0000c0300e54043e00e41041c004030f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374077113 1250 374075863 374075917
    0x40e010519031b24030c0309050619060e0a0903111c1d041b030b0102163003050904060e0601090302040209010507022e0c0b1b0c1f0b06 60
    0x41c1940f6002d207030f0060015079030f4158820b0701c407124010001a1000c4903c001d252900343c4200c000c2100715040c184070ba18859200da03a11940010b001c080e004259039044143d6102c2d56001002400600019065034103141e0f00140080074811000c401154807841888501100000e113082031980604500001050003030381143d8500501e0420010111840c038a200c682d40d03240039010703080c0d446060390056800e080700000c1c180d074610030405046d50806158141c40c074403900051401d654032408840e503c03051a492a4104e404a8600d800422101c110030301d040680c85002800440000c0384c0a002042d22009204201d81c02550070341d010403800c03030040005040c01c2c1c01900030420141403c9003000c101c1e8003c10321410309103042103440d64000c0410150030750318100d018002c03c000d2500122800342c6550350001d001000c0c0c210414a0410002201c200c0340d0700c01190340070900c081c1550401c02d51903d80404d6201e1303d22072600214180307034807410603090400c29a4407210300c2070694203800c002e4100c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374078363 1250 374077113 374077133
    0xb0310090b01050901030b06150d0c180b0c060a090c261002090303181201021201170c031e07031202100501151d0609090f0108010507021603030807110106060302040e01051903 77
    0x1848949e41d000b07118221001c1924440c03810076564607150a034014502c900c15007070341c912540218941e004140070b2068100c1000610300d42c0f04840c010005080074803420034000864640e03000c108601d10510141c03210046801600c0c03218089102144c1c03030b0400780e40600c001d80c0074011029405a1040c0070881c0920001b80b01401500c5002c0c0801000c440030788445400d985c421104449050b0304100104136212844416007405100e101c05403c3e203032101c07400079841d600c45d040034407884045480840221041808050011035112091a031502003804029480f24203d06a07400e48914000000845170040c801c110f80c040d605664070a840c030340c181c11031540700300d4600e03051750440c40c14803a500700394480c40c03001402084144040b100c550b01d058151802d540c03008049400715041680404110741070740d140c0303106030b80d81030812150556940c002120b0fa001484900d00956007800310000b141a00f5034024401c2d194440c008180a81e00c2e9000d1054012502c420307089030001e252020400324030b242d05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374079613 1250 374078363 374078389
    0xd0e09130b0108010c110105010509131113052d0c0f1204030905031011040b0304030302070f0311120408070b0a0216030c18050412050c010b0310090b01050901030b06 73
    0x18030040c148000391038001040e0002d8120348a44ea56800c1007080f815084801e0025440d11000284101e41c1810003080c25070002400021408002070b058008010081e8001c100728000509030589010040e007051028000503145206140012882c807010a40b504101075124076031400710904907151407040c002c1c1035005520f2401c0c1030800f84080030121a021071654040c0380240d82d03489042c4e081a0406040031094100d14285c03c0c90500346405080700705045e40d0496000c2c1d0780c2c5603102ea480341010b9019114003e4010a030b0b51640220404040d0045040c1c8801c484400c11a4500341f000201e0121f54804e074041e034681a070100d1000c01080c50f000d4001d2034008451310650317990015004145142c049141c004966080341c0b0301042c030484050300400006c591300c0c10f40901c1141015218905c4001c2c0202182003085070004502d1178825003504560b40500002d030071a0b05105420032a040205110b1200310380241c144000003d031807500500503410b0320f8000100040c0e6442d07800030403840b00c00e001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374080863 1250 374079613 374079631
    0x40609090e0c102d1e08040f11030a0c03060c050703050d0207110a0e04060b04050c09240c0c030f15070305090a0b0403050c1002160611090a06020307030e030d0e09 72
    0x3044c0c1e0510303003c9188400c4810026681040804030b030008004d03064884000c1954000b2a80504480c001075115a5241c1c210360040880c075440800c071304141c900400c007485d200350540b044c851410100100ca901600c1200c1c0100020866100c404008498901c43c08901030005502440b69480140c0c560340141642840750019001c40d845035008a80114203541c00311050701c030403104100500806005100500804850400c2289006040d0b04160700613251041d000b0b121542d8050a100807585a08005070441082d1076152481120080c3d510710800d0b101c54001c0c05450021014103c00250f6410122803c0710a04281c0e0b4444804a004280080000582744200c242810105d0308120764140554001d9136003a50314141d90340d1561501d03a14584805c01c031441042149288049c2821308490b07642e04c814045410010561080741c1030282c2058160310901490300082d103203800100a14049100e81c41e000011222007082685410040708404042481c1d0241c250700751500b02c0c04070764060520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374082113 1250 374080863 374080877
    0x50906090a030b07081005010305041703071119110402070825120f0201051e150406050a0902030f010f122315090f07030c060c030504080102030c040609090e0c10 71
    0xa4071083c40300305054030468040b0704032105001c0318404540380c1c13101410003802c042c401818182e071402e06003141c01c100314100318030200c00304050a1041e2921522641d400f002c071407926401000b001d10314040d01c7c01c00c4407003030000c541c0c445141c10315000396012180c0180419003801e110041c0d01c41001880c40404141903210544403000031104882e01001141542d9951a03902c0701910190071104040c1c9150000280c14402d000700680c13010741d056114075440ba00d4640300010300d011401a1405400c0650711104085011a0001c4142d000c0c520401c903094031040c0c42d984e6403070640312000440c05804c101c42c102d42c401c000070401d061011042c01e84081b00c5204128651400241840c02080258002c1c40443e01403041c146410020113900c0d9640a01500d11145103507900c0f400401d05104010904c40350311035440171f140c003410641e03005001c5580255602e11300b180701407003954020f00641000c5081d031080401c0d01c2c51b40d4442c0c604200c2ca0800100840c00108080003080c1a40341103120821082c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374083363 1250 374082113 374082119
    0x114060a060f12060e01140d050c0f030a021203030f0f1e13060f05010f060203130510091728150b04020c0a06050a051e041205070c060f030c05030106050906090a 71
    0x4034401c490040107261140d500d1941001300801d00e47c080400b02c00c2c41100c10004840201d10081490040403d007200c107031070b1052414010a0130800401c03000382d404500e1550081c054039010005602c646006203503814a550341e40340840390402c094400714417a01c09200081ea400b12a44010790b0840110800b01c1c14546042c1d072490b0a42c0ea2880d5409000c60725000108038100a145c1000c0191042d40090750414843e42c110118084407403040d03a101d80003070b621200c40ca80c0076109070b41c05044042203502050018030039595582210703403c004290f912503503420480080c1c4a40f200e000d541d000103100f2596036500c2a81002d04a4a40c1141c0d00a41c00c02101d481c00720100f05504140d403107000c1c0807d003441c103026040125a0020039200980d401c054040303148400d0001d07030a900c9503012500c40040401c40c2c008885900820b00010090a59980041400350300302e0f6844160058aa9040c070047c0c08100044411380800e02c29480495030500c4501c1c218540b40c3c01809881c100900701e030041035a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374084613 1250 374083363 374083397
    0x91106030901140105012c121911030c090a02030a0e16030c0e04050c2b0f02100c0503090d060212070c0c0e07170403170106020f0114060a060f 63
    0x310640703803051039a55450070100d1070022820142d00405090074200700120b800c1e81500d402c4442421540e5000820680b40c0c0ca59543d480140d0020704036442c112044008100c0d401440303128000d005640e800c03818103034600c41707107000286501919000703003120b0915114107000101a400207032081c0320b42911a0742e20503405000f00b08080281c92481c034040e907003901d0340c00c181100180a400c8900051300c503008120110710001040f0205503000d5450100020200a4801804242950540715590310a90304030901003684903d900071402180c02c6941100c4007201520b50004030040107181350420301c8020410301d80844c4810710b00f402011301501e00a8440c4d5050780344030b002c441c0580400e80d0a124a402d00604400000184c20490480300080c104003a014210040c8080044001c691140016082500ca203140b48840001200680c0780380d610b0360006074807100f490020307800035841d002c1c2d900303498016020414085c18019007025800d80c20280207c400510441c4c24400b4481c0405038030030b01d14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374085863 1250 374084613 374084617
    0xd02040905060423210a0909020415170405060a150b030103120906020f070b0307090302120a0201030b0a03020114070629040b0d02011b020a1502011b030509070306091106 75
    0xa10074858508000040826214211452148140c80d035101070211040b440050340c5c15820400901000d40d1610071031031084560314482e800070380d2070350700104000400d01c660040202d42d02e404d80c0c440c1c41c1849482d041207400024102d5000d03241c5d910031404243c441e18598000204581c072000d001e8103807910350340f010105900c05e81c0112603011045401711659a0b01583c2d503805000c035031002d40a00d2003190340050f0760b0720305801100000100040401c04aa0103105031070020f5034050702c0c400352514280030003512030490541c2603001c41d09040003000c0354a014040c3d0002d580e416101c1c418000f080d40c820300c1c001d40026000b1616070b0707903c0c1d20034003004091880054480c8103610003210200d44103028401a160181030703940c00b03500c1041c40c2e540140c1c3c201500001c800b88048036540c420841c0c7c00081c258500d0b5a00c041120030340d041c140849103034107400c10201b10310030300c0c8003855824482d40110100c80d01203c5c01429900501070910000d016a000551142c1c014000500603c0c440000a0b5a036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374087113 1250 374085863 374085871
    0x50603010f1103011a070308150402130305030319110a051c181109010b030703180204020a030f06051906050c0319050304021003050c0306131e020403151107020d0204090506 76
    0x20000120040002142d01700030444200130380e804c01410445903580c040c2001c2c2016142c1d145400c00c520107481d0390b0300c403541500c10130400c0c69080c0c03038255905c0c10060340b2035105680c080030702040c1c0c802640300c003c6503016043d0301e07103040031800745414600c00d4126920f801c82e044803101c500d5505044664070005009409003103008420a8490071003d04e0180075544480041a024000502c010803104606c00c0c107490b03226009003000b140c03400c41090b4180d080c0100d402c000358000d101084800c3e00743ea040d44840c05082c10140100501e0313859004001041c1c00f130b000f40001c40ea0032950140003242c49440604841c000c00d004a904141c42c01107203442d00100400040001000031041000350320b019022004107151900701000b460920032240382203480001e00c82d40c004c603000c81182002d001070764081c40901d01c511384030071204401080b1190182d8454841178a410072001580600b2410310f00c0b071340500c80010443c151a1103696030030f214617001d2504080e07030b01c240e407419040e020a00610050b40f03d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374088363 1250 374087113 374087141
    0xc03021216090504030509040b22060807080109050606190e070302120c120708090a151505060c030307080406270308010602010614060c030f18032e050603010f 70
    0x80040070307044405060308140d00220000d410032050002180d0402c048500000041c0c40125000503080003084c09410700a101d4038100301e507908070300b039a1001c0ba0710030019104204140d4210ba03603580246421303034100140107000b0781c11200100c0d290385001001d0100100c00a80c8444620355222880e4030300c03250848002020030380010318001490300300c00782640c1c0080741d00396890500080514610720900c7c01021142440111404a281e001d820415010f16070750024044100c070b0701441c1406c01402200d074940089020b0700d031010500d4a49402901e05c01c1c0c07001001142140d46014007154000c1c0d019205540c01a652b10201e0303140c2d580d04151450b0040b01d10301c500c002c8011850014220f400580c020011645802002d11011826483c120180340b41281c1c882c0c0c440c00b20708000360561045030741408a1450009600c031038000100c0c05500802c0c2c0840641d60a8102440d031030031102000043d041c07a0003420b4465160300982a40441d412441c05000081c0340400030021001701c6000007420b0003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374089613 1250 374088363 374088373
    0x30f0609010b060309150601120f06150306030506130c0e040f03140301060207091a04060608070207060f0923041806051b0702010c140604060515120d03090c030212 72
    0x14409000b405600b98881054500500d90320380003034001c0e101c1e0038042215440104010204803184e2003907013510000707030b0b9481c0100003040d074048407180207000c14460441d0401c42c411750500761314000d02c1141c045a400001400142d5124030020b003014080b9501107404000c80d0038081002c0804d422010702c21841101441c0c03800f042d5050207001d03624200608801103008200610045038080303002c43c1120040c00e070106540e12170301030080c901c5140e0048603401914001c00041c0c40e80e4000b01e018001e0480d60260b8001a407920310465405803a180000040ba084810030016038040c4c65035004020301d10204030001c1c0c01c6000c002016901080300c1e084c41e0031151485079050024601c20710780c005038001890141030000016140079030054000290501202c3c10000c0c040c4606400da00b40019200000e0f10303490710f0716242003002060280c55140c080c0c05041d815280301d0403d20109524400d4050040060030305a05045020f000441d0017241c14151580001005891710000103818242080c0584 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374090863 1250 374089613 374089621
    0x9012a080c06150a09020f07080313021e01200307060c02030c01060f0806040305030c040305011e1b02070902180d0c14150405040c03060e090a05070f0803040e0a0902030f06 76
    0x80c0342c1030019141074031900041c1070516a59807001003c10840d045401c0c05600c1d020746000d802c04900406a020303200480001c01c00030002590215405510b100f160781034245c08600e0100c0c03070035029401300e4178049074691030107421515840305030a000400500403280341800b0b1703540b884240c480e084542c00150340003051400c1082000e00803500a4003c2d0580707600b100d03107011101075039100041e101900340700000010540e800030400c1150b002c2c0d0380200080c00681c0701104803d0003000c080d11000e20581c80c1002e01030072080d000809070b602042903802066024100b510b40002580410000701800700701d0241031102e40c071030b19a041e0415000b10001060280303001680e00b100e000005185120758410032040790102c1c000702c00e8a05a03031003683c000030380070b0380000c0550050800d500070801c1c8042c00b10800403100000205c00e50118030030015514001d079035815500b00b18000d40543d2689810601c018400a10305000703280e400082008045012511500404d0071300340c0080240300d607078200b10104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374092113 1250 374090863 374090887
    0x1603090504270809090c04061704240b030f06040b1e0106051318150b0c0a0b09011b020d03060503190803060f041a0406050409030509012a08 62
    0x680051100355001c1c481d05510842c20300c034030070303640700450751403600e001c419414009010b0a9520214000e403c0d0301351030030944800b4190781c11511401000980307032992254501c07905200640036a502612103d0745410085074080c01c801844c980d00c0700f040d0789900004031903400300b100010300a03824003d0f1a0030f08280c18408a0000020402c60b410011405644120410704203054119419443d05030f031280030464059002175002c1d44170b08030000c0440c07120200c4003016440310103401c442e8032410079400d6031202414401d01070381038018200d400c51000783c0b001c1800201100e5000010b14000503000d6038034050b20100c405400d25040050380802c505001340c40d05442448042c101c220000c021411501100c080c0480100078010190000880850f02035120030030002c0b00ca0b900200b09001098030340e406c802c03803182c041800d14819400e102d40003c4500b800e00c908000546c040c1d40341c0303107000044001582d918a81403032a001d680c202201d802422001c0348400c42c00d10340318030895035840c0810498 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374093363 1250 374092113 374092127
    0x1a042f0a1e02060103080307110114150a05130b060405030307050c0a06020a020d020105070311010501080102190e0d2d050c0f120607081503150907061409090c07081603 74
    0x201c0990491502089410700d40010b12541100d90051401d5501c0d03565880c1290400d15007141c0300d100e9030900d0700f0515141c108091462043d116200c000c21000518400c101c511400e40c03140b0341d0010b0444603915500c02d20340d04003a00341640030b442c0c14a0180e50f1070109145511213107080d1001c0e0081d40d441c8566161485e82403000b822107100500b0564010f400003020702da060000207040c40000103640003014022405105e401070444020070503981c0d40d4888902039401a580c0e440345454500006804a000e66400c44101401501d040005400c613a691822070703c40800400b42d90110041c0051001d880305040f02c4014400d5000c0c00340940e10702c1c1481048611102d10601c035288030888043c0065001840d154042e900c0d02d030041c0543ca0f04c800041c002200300700b541d42c040c000d103041c11b10642c13840e607802c6010b40d40603c103c1e440c1c00d0b0b85176170403117542805044074030880b5010403109640e0b203440092160007020740b0780300e1440c050955070382c0502d550240910000c10780a20003100281500600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374094613 1250 374093363 374093387
    0x40606030b10030c060305040c05030613032a08160f0609050c040506010e012003070303021e03010b070602091c140f030a0504030f0c05040c051308011a042f0a 70
    0x20803900d14900350383d01e0031600c04d030783c1c01510101607440001800388401d4111810003001c001c0d0a03036000e0300700214060741483c8181416030100703544901c5101511201140280b0011511854050184090740c4030300180e80103841e071007181c003076071021036000c11180c82c0798001d401d11940000076080102d241c22810102c6080803188924500401c010942e41c12403005040c0038024640b1080300d41000380905041d0801070070f101c0107840301041840426030035900a0200c4140c8502611010034240c184c56100d00c008d00420403c0c400c1030040800040300d9801800035050024052044000c00d1146214284805d020a555601c3c510010200c2a9800d108941306284000c3c055032600c0c2c1d100001404503c0b40b4031000b031850803c0000c0d007003800204611000a800001c0086c04900b412450060040d0000c02400c1d940c420b07040000144288148541c0408410806c2403110a440070002c00c001050720800d070b84c107100b00300030301d41e070414400760b00c88010b0440303100110361070b1328079140d0003080300701c81d41c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374095863 1250 374094613 374094631
    0x60c0c010f02160609060e06090c010816050403020d0c0b0d061701050c031602070503030a0c0b09071a030604090c060201061401030509060c0322061d011a01050a090e040606030b 78
    0x40226009800d0f6200b10440035008000400ea5007a6460080d00a00800d1000103040c0500409c5c000c1000c000308540d91060401da03540355182c0c5904100b465500e4000b0411404554108070030401802c245140182c001d00651040d0010307507032481e280e00d1691150140ca000d1503070743c60040c080c803154049100c07a9504000000c00c86490002e40c0f181c51ba200c042d00c0b082004001800c0e140a03030b8401c20221000c0c040150aa0b6214040408c0140c110569540100d40400a1200141140000040c0c034000c41c2e001921a0504505070406060194000b610550308152a4500040407135508000e40000b403080768000a8050700e00788080240f01940c0205a0405042105100b5040b000041c0701d50040041c520003652611050802882c05c2c0740b0300c00d4043c03021003129001c010700405130b010b05d0300102e080d81c000d01b80c0200d00d1040380c00c8a01c07001c0311001840480542c0d01d541d52054010b0310031800c0c0390501080e6142c40300030014410408640c03c460b802d4582c035050040004040781039411091075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374097113 1250 374095863 374095867
    0x6090e010b0a1d03030409020d02070203190807081308060709030506012102040209040b09090610090903051b0f100b0411070201050412020d0b0a0203180705031e0a05060c0c010f02 79
    0x2940b001081042d0b1918108610083c040c5250300503070b418400c0324000d041001c81155a50342c1c0c0c6484002a40084006900c02c3c040c0180e030b140b4254070124044a0140d2001e103582c0f900016540b500c0c115041900b003061090504000400c1371307441084518021030f003980390007000314075601e080e91620030160412071030051034400e07004502d221503c07c440c9980e81101d0150b202c0e28010b000c58000c214800c0401e600041e4841841175264011a10038041d990100d03005802c240c0301d00c42c2c642600e807501c400031b0000300208030111403c107410720f00b102248002003c3e07616601c4107161861401950703141c10343c0c445030b8406008020349081d1080303c03862210190000d01384200341d00041e04501545c441c225040d00010b040004640d100740e0400c0c13500c1c2e07015070140d2290500390182c3c8000c1d001150241180d01c0e2008203198120000100070b0100c030002401448030340d110705c00300d180c2e6030081d2036155007902c1001486c5000540c14030030203201e06074490b5003039281c40381c01c080c00e42914a001c40c03903101d840c41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374098363 1250 374097113 374097127
    0x60504080708030f0f06120a02041a100906020c090615070203070510050c06150114031803070309030615030c17030c0a060c09060908150c0c01050c042606040f02130606090e010b 78
    0x2012405100c48c0d0380407200003402500c3c141e400e004e031f914411010380d0b00a004440b03280e526900300c00914181d68907542240c00031541e100c184a0b8103401682d4080c0d02440784010a40c483c0c080c50001c211462020f01034500070f954070b0010031114120322040f20041140030490713081441007001036542c485e800207540c002ca481d007d00041d124000d4441c20316041140080000d0b00e04120014820a241540040740e54809842c01c4c0200800d1090000f2188182040c02891f010001d604510003a00d402c081075244080c60000000342d0a01a20303100087d500041c400800720b01070038094980480e00418000c100100b92080007004020701d60048414803101d1038090040d990001207500a0f2503004041d0349aa4561f56409000350150740b40d039941c00e40c200701c104580040190b0207001200c10141221200d00c0a06040c200c08100d0711040480d40d82c01040003a02007000c40d00c2140d16940060401124842c800301e000d000d6413210307002100410f00c904020841d81101411b01030041000d81d04560501d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374099613 1250 374098363 374098399
    0xa14240d02070c08062a07020f0f13051e0711061501050d0c02160902070b040f03031b0512060f03150601140c010e010e030f0304060504080708030f0f06 67
    0x80d030303880c0d04112507010036440108005042c082d405043c02034200e8100340342c64105041d000100110182106501c5490310110f003103d0016a2600c55000b040642810210014000d4243d0820701c8607900052000080c586690703144a071a000b8941454030b542c07041500400c006455102400b10420070842411403a2105004503095400c61300102c400c107040090710340104c400c5c0c010303c960303601d010b881c024240e00c045800241700e50030040e0071864a5082c5a580158000724020f0510103405a6000c00000d000160052162040d1034407a0400188984d5003803180c1584d010f00d10111030121720b0000f034103174240681007031041e8428400c40b031070030384114130030042a221b40119081c078244900e840082206a17015041d03e0b40c0d804415650b560b01e4081740840c2e2800382900300c0035000c1552034510300c000d25080c003100302c074018400c20101c41c5c9180c0f02c96842100802006000380d8003030b401480003900141165000b18091084134172007000c1d034200118520042c06014100c24481d106603081582058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 374100719 1106 374099613 374099617
    0x7110a031403070c08210306030109061112010f0b040b1c181109010e1803120103030302030609090d1d0301060503011b020f060c0306100309020a1424 66
    0xd035617583c580e131100b0142d480c4c480300e04c6011000303448001c1d201e030040d81c0008001e0000601c0074140d898540c210307510a8943c0c004070200040c948031000e40030325294003400d4206844070700189008980741051080d413190042110b4003190244e1170030740c14101c2e403541480048042c84200c013034030b09406150106000864180011855a00443c10010001d5058074904459100d41d07850f010b01c96080c90300110040151032204002d450315a8400c5015a40250b10076180540ca03410f250003000420300700240249499030000b8007014596a0000102000c030f00d43c0041e098045c005072000c00e0160010703802850b010744c240b10301099100d082052403004107006a00723656215001500136601c0300300c2690802c218030323000e0001c03604038540161030300742c0b18246007000600300c805603001c036000ba13020780e114000c0b055250310000344604000403580d4101c0c1c1217140389034120702e00d40308000300c034 = true := by decide +kernel

theorem cover : BRFrame.Cov 373920863 374100719 := by
  have h0 := BRFrame.cov_init 373920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373920863 ≤ n) (h2 : n < 374100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
