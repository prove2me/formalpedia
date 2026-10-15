-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:43:41.52427+00:00
-- url     : https://prove2.me/submissions/39b1c0f5-7a2d-4ea7-b3b7-799dff4643d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 970143884 ≤ n < 970323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 970145134 1250 970143884 970143893
    0x110606010815010e0409050102040603200f09210d0e090709030503040b0a1205010303110d0905010512060609180a0b0f180702070308070c050f0904020907081801022d07 74
    0x980b4400050411484400e100e01c1942e642e8090f0b20b103160800001c40d140c0c0e8407550058010008100e02058128203010303203003966610002250043c1314055207040c146186001884600c801000c10540e040b80090f817070007802c5204110f01040070b18140d071140843c500c080180568003d0143c00c107810000114001e002250001003214100c0da101803030b50765505840d00c42168180d81c2003000141440c280070001041c1903109606400548a20041e1011075120006c21340d40d40d0344030f01c04e07075022a400780000b20020f4242c104242e0b01c04005400e10b45000140d00c00925488500f46801c0c03400034034281070200400b414030680704c40020580f0340706030204100340010400300c14a40b4030301c400540382002a000341d00c20b000b04002954001e650343c1d2112620329003603111500780d0003103502070100610010050f29100507010701440c4c02a040c0310098039071010440e00700038000c00b500000c9822200302500c10b2000d10041c002c0f00028008050140401c9404e0064040400600c9240781c5c0705220100118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 970146384 1250 970145134 970145161
    0x60309240727031e0624060f0804030c080409021c0609020702090a0b0315011d0709050127050a0f0e0604050c0307270e06040506011d0d110604061106060108 69
    0x220b8001c00c02004d240c600181c8104141130820340200780718140503002030110102644e02c901d4041001d94404019103a00d005c45001004000e0031000a05c24004a001b09010300442c1c0b0b1200d0280c19605c2c509502d40004038242c0e400780014007600c0b083c020140c1c0602519124030381c041e12b0000c8055280c40b886400285184201600803a8000da07510300040d1280d40802400c1000c41e110f01000c081c0d036940f0039490f0415440c03543d030200c1c2a402000000c40c1140b04540250503204142c49003541d031080c4c16805c400a50054441c1030036900c0d041070105071a0340c1c0b2200b5034020030080c6e0140c04482c0c1000410307056010041d00720780c0918141024011090124401e40317900081071b01e0310001640f2090040c4941601a103d5001e100a070280013191502d107480070940701308c409a0b0107000c10b444480046503008180c201000000d10f00c070b0f012a000345080d500317014040c2e005800b0307855024140d13400504a0b6105034003480c049824500d642f02104018050140c1c018000d017008a50fa190092002d02c03c3c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 970147634 1250 970146384 970146389
    0x1b0f1c050709210c0608040c09090f12120e0d11010504020109050d0501060b070f06140606030a020a050904060602030406180f210c081f0614060309240727 68
    0x80300d0500000302108480030700703035804d400507014440d150b40c510000e840d0200580701907819404056010503d481c00340a080c0079242d0044142102410a84030b40e901d124024142c2c030100003c07000014103d403441e00503070810070000c4010701b04000090703501401406840d580303406240d06010410016030f8101920404030303401507407109078041c19894103900601d203640115880039008036039001030003101412a02694861101001240b009030b100c11140d21040f1681580282c0400001d1404915600503000c01c81039400c0044c1040051b0002070203581154014030016880400c04125a079489080840f608140c2d541c120744040c280b1042c100040018028801a49104010606906008030b0f110082d2500008491405504d4088858598607003c45803036800c080d07202c16054203401c1d48103813030496425a403008610740d00340c400d0005079000100b100b40f06d800703080c2a0041000f2041824100022028040c14851510040240c0405030011080841010300b0754900071079207200c1c034040c0c00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 970148884 1250 970147634 970147649
    0x618020912012c0f371b0b1303030302092704050f1f0c0207031502030702101b030f15060203040302130c0c08031b0f1c050709 56
    0x240c0c0c458000c089840500d028045030300340e41c039045041c16030203102c9020314250300d500c3e00341003107260341401d1aaa658400c0300144442e50880b03502030105071441d11400d081d50803000e504221621090000c4982d00702c51000682e013810034508084282c895803590a0098030032030382c0b1142070007a50b25906000d0892804000c06040d070005178a20240e60f03500c0740c88006940a000c402c911814110034009801c0d0642d012a0113210740000140c048034040303240134010a4081000a07803500c0194220090003010080c0019806580b0000c004200c4200e10301c0c11a030122440581e42e42001c143c028503151040005805031454002c01c440c103100c0b55406209261410f19001c41c3e103042d1314441c03070010920703030506802c07884100070001002c2d078001c0080e20449008441d07100d01400b1000c264070680c4d80c086092400551416203882c0010742d02405140c000c80b242016100405101e641ca148130782c41046d8040c544d078404248881001580071368000042035170981407100341021403003c0d010302c00500502c3e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 970150134 1250 970148884 970148887
    0x171009050a17040e09030a0e0105040506093d0806010503060117071e020109060609090203070e09010e0d1d031f090813030f021203070b0105060c01090c030809040609061802 76
    0x1004110001e0a0b2005004e80781429a140d041004070300b42d8981c0a850407c000c1981307030008003890340c0214181d81c120b85018014915049541003040038400078031440041d5415120081d0030304260360a8a0340b84031960300680231486a0201000c2c000c10130080c581e60420108104000c51641d01c01030041c920341c0407086540198039410003d44001031040341d00c0090503610700d101e9885e15415003041191a0003030070100000c0c1d880d0a80e8609617001c480010b501a1f0007100304105070007003c0401e82d842030701000002003181450000b5810010055415400107600e10b064030b42003602004e004030a59401c03002464808402202203802e106184c15455409036101c0c80c502c14401d4a1084a40c180300c41214400c5440d02c80c9031141c081811540c003039010701c881d0045200154000021140c080b074004099072401c0e841d107c2080038030750103203090104c03079500c075420003000807020901040914031582d0312640760034000307043c04115855544011613150a01c24200300d0b0460a0a0070b500180314000e026 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 970151384 1250 970150134 970150163
    0x3070e010308610501051f03050c06070309270b0405070914010e0d23030a0203040b0901032309010e0c01090513060305061501030f050f13110307171009050a 69
    0xe0108840d86001002900303810804081085811b40c0070070311415544005801c1c0541c1d00c000d142c1603056600000f00164485d00080031140b0b400000b0b0034183c0d00c82c0c9000115140c4590b418590315560001ca1501580c3c10208000840900c2c0100c032206c03e030030785080010303107800d880083c00c0e075000d0301c107080442d000b44810500766446040d45802040c0040e00c01c800c00812460080c0741c80c0010300c8590601c0401d8015107050725000302c201d44241480e6401103040c24206100314040d80e0101000d0f0b81455569040b014200c0344210713010b54840b0861000c2c049501d024080c09095455881e480d2280e500418015581da0b038120240000787c1d102903030301d00a8151074140450003002e183e013024060340700c0d9404121887c2c10780785214080c0c840070b0b81c0034021202c28a00034001d94900b9100c500851500340e00003811900b04604c00038031503002e0112502400e0880c2c007c03a09089040e0000d125606d41500e1070310030048100881c13184240400400c08c01d03610b5607201c9903100c0b032010030f0050400c031281d00765 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 970152634 1250 970151384 970151527
    0x60103020a0c020f061912061a0d0c02010609090308060a050a050a090504020d1b06021207080315040f020f090f0a0609030f1523071e0e03070e010308 66
    0x68880046c1304404000c414008508082d022507881c02d1002032141c00d080001c101c000c0d020300c0240e8160300c0034001c0c0c0d050682040110004d40032140f0514210740d607039940000ca54182c0e0181817107450284d00e40c00802c0c2000c8090100346695904054020b800343c0000700595222000380200301c640d00705c00018281c803a440050f4501c8070103032001c0c122100849085110409000b41c900456080740c0885410042d90203200d0b1840c0107111003e0314a00c400d10004820741002501c05040c00c40c024400034024031380c40c1c850001c0fa000300a0349d20b1204000b1035000b07090f06054030484240d600171241c0045081c50b2440c000c00016440c08010002640c55003c2c07001c0040f00140c001c41040e03214000d2201c0701c01a400c10040c20501030415043c071000b270010420f114082c2404800c4c0a02828039061485801003041d0f84c20300440c00202d40600c540a000180703020f001a445020754450348441d0340c0c50750100c4081b02c89a07014510580440b281038074190390304542100fa01500c0780d2401a05903903941010300d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 970153884 1250 970152634 970152637
    0x103081c15031b120201021e0a1403030712020f0301030602070c09050703051914221403040f1a071b03020603041b0f050a09110906040609060305060103020a0c020f06 73
    0x81c980c4111000a01104110080e03104800400428501440d12950b40302c81d0311041242c504040c0c0540c21880600c1d840c0781840c103039040c0b50041c03041210140b54942c2c3d45c41950940c115402981a0408020310140a0340000b0884010582c480c080d41043e4900105540303510040c400102065800961041007104560328013000b44030040f010004e51500640190143c10122014801103c1d0a10080c00414540c82068030145210b00340051607580d02e00d0790076611402c50b804030407100c3d40c09980e00001e81a56201d8544080300405180c030f407403806408403903481750390b0000d401880c90052941172020305541a80c24440c0c01c50810f04071680796074080001c0300a0f940010750001c4000040006000307034a00307007034070038030010b81445440b81c2d846001c4041d2030f40ca401550740c4804d54000c00c01007001f240d0082050741d110054003a103001c24500000d09540d101c0e40c040ea0210384540e200700303c542c2d00351107641d5104400b8241545004080c00c0020040d620300ca00007481030072000082d841d103840350380 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 970155134 1250 970153884 970153901
    0x302130b1f1707140d0506011b06090b100602060c130e01031b050f0f0d0212010c020f0f0d05040302121006060507020906030c22090c061d090103081c 66
    0x68040e104500e2400d0014036108102882c01e008902c01004584a2442081040c2004100c0884d190401901c5010780d4098800601254100032038180d052180542c440940912070748680c1001501c405245440149001c0080540041001c041020010a03401051b16540003854894030340d6140101201c01210301c81541003103080d4203410f0004010058000036a00aa810b4100d00c40c1141d40d0310402c102a24029800f404c1d0451000c5082c6400307810404420700c1c165200a0060310b41079001c40d8240c2c00c449586412400503405542c02d0090300d071003400710440103071000000c1c2c44030052100020f043d07031180e880000c3c05241e0306d00c0b292010134018483c030541e41c0e00407030060181c035548102c01469130300401c400303034840c9001e9030210345240f0300000c0304120401e018004001c4141d030150824669004103002070070007034941c80080d00091100c401c540c0a0502922410030b0900e9a41d0010034400240c03003134602480c2c0c0c000040c40818540000d03075000508410600000746003800321301001c0c00114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 970156384 1250 970155134 970155169
    0x1020a0b130c0e181605060912060403030c0f0305011a0703020f01050f1b03010e041410090503300a0c03201e03010315020f0c062e0302130b 62
    0x325020501c914811449030155401100f01181400d00419107604d411100080a12084400801b00b02c24100140603050880b8003d015205c90351103140c64904108084808500103581c540d00380d4511508010001203408040c81c0400c15981040b644082c40f40000745d02d00c4404c0382c0802c10104041c400c20004040001c072030001e005605100c42080e443c03034030aa440c000c000b21601030b05001c0c175610720300380c038120b9994807a00c0c2d8081c0c41b640c50300492009140081d031464002d144c08803d50560714044c5c0307640f80d846030004507520280b0000c1c1110032a031894148032002d901c010013000000280f0307150f60f0030000c0e4131400107991445c2c0c20281d00a14071500e08910a5486481c22291014810040c000515003941c144003008050070600d1214071007400700130415203000d030b031684030406154040d2480000720810700f494032500c1c1c0c48103460704004443c00e1000300780301315445403081029103100f9031070307002c4041e03100c1e10508680c005002600c08840c0c1c040150f41e070742c102111580c1e81802000811620 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 970157634 1250 970156384 970156403
    0xd18080c0d2108060a0b070c0b070303020405180105130501080307020f06040f0b0d06090c02191b0b07051501080c0108101e060f0804020d11130216030806030c01020a0b13 75
    0x1d0b80c0003400000044031000c0c40340705003110001c0c0a501c06000c40f90540d600c10300500c0c1d25802d120f04481c0c1d0340c000d0350068042503401d020100d40ca0700c404055008078803100c00ca180c1c0e070790f1404080240c0d903c9805a01196142002d0040202c131000005a510321507049540c3c405820b0000041041d90003158054803892203540307400141182640000d0032000d108403424091661a40070400641c2c0110320b000005034414032074040c41c4905030291740d00c554420050300d0340b018003d1406402a01254200031450140015000100300d0200050f00c6803185a5012214640c903050299441c0c81c0c80b0500310341400300c1100010001002e20100d40d010342010412004000b42a007200c450400d118052040494450246c03828218002d010152099900414032940400e07543d40d0703202d00c00a10f03d1030b240c021001e450030246001c03071030025080101140d00580580041410024801d00000c4c00b541e00903040a2400c05181e4bd0105071481180d400c03d4100c510350b11441c003401d0752001d2103040a00403003130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 970158884 1250 970157634 970157693
    0x7080d240b040513050708040f06061d01090c210f0204030614090708060402060a0c030203090d050c1903020a050f240d050c0a080f0603010b030106080d18080c0d 71
    0xa207002c1c01c140c600c03c1d52920b00030611002d50701e0480d03030141c0d407440118911070000740001d09070000d00e10340d03d48280f401154041d525040031200c1040c000700e0b000904a42e10060080c90458490103103900f015140640300c155504003000c0c1e0f869400c3c1c51086041d6140e032100501d900141d01140c0056500500c2003010481c100400410300074150f8041d0101e0141400000e40c46d4000180b090003542c004000d2454460400c0064501c3e18940b0300c1201540424070442c40155125401d40004902800140007002402010800451440428400c141c0c3c0e1880d0b007071016803100101c510580d00c050382c6814000181e2000503d503969025015107140c003444082d1540c0080d00700c064403c4410000040c040f680b1424040c201c0e50103584100742c0000c3c0d41400055414418080507034202ca0064000140070f0640b20120f070a49240e5003041c0d250b5804142551350159000c00c0101c2003007004959400c080307007040d244c581c8035581045000d204034000d0310410140401044d070034045400f04c0188135803224 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 970160134 1250 970158884 970158899
    0xe0a02030a0507240909090c081b0103060603020a0914060412030e1008220c081e0c0319120e040207150f050c070615091d0f0307080d24 60
    0x10741c0d8010610300703c58165011000d0740032502004041079131a21011034007030070840e0040003880140340582e4101e02d4081c0000c1c18000c00d21040c0703903020900074841c401e0409100050259011580240100340c8101f00004450740e005282d036050750342e6500138074001d280d4040050740c5401250000f541010302c26100c03104044d000b500072842d1007000e80d501000c100340814181d409000c00c48060140c5841d503001c00100b89034403682da003400340c400c1d90380529180c1c981040510340340141c036417140e042400e008003025401041089072408a012801465082100c0310141054a6442802800100c91840005c0103078007451a040c0c01260140007191106176500700014280514486001d07120318100180c44682080c1c0100380c0b107141d03507048141c0b805182d035403180d008001000d04400f00620040010802c01324074000c0b080d144400c3c408002000c513000c42d9490a2013640c20031046582d1003042810001040202620081c03000700000064a4a01002640002003820708910001902c803c0116428 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 970161384 1250 970160134 970160143
    0x50a050102120919020d1b170a1406010305030a05030709150509040c08060f06090102100504050114160c030e190609060212090307091806152c0106030e0a02030a05 72
    0x240070308001c40b5104122280854000c48401c41e0103034208072a42c41c40400701d00c00e5942003900020180d000c6208980e6610081c0d0200c4c40085c42307a0362078005601074401d0102c20071b1400c94000240b4064280d07545160b9031503989100e002d00803c00e208020002815030b0340541c2c00a00207062094954007420f0202000410551100308810312961826550540040c0301d040d405100d804040d0021aa141d6642c040000ca9000071000700d0440c402e0340f103851464081e600030030380641d128000120701400c80800082003203000030200080141d00030310229621782c1c0310030074440c0da6400d8200705141140390b44c04140c0072000d100030b460316880184000540305034888080340440341d040d420f03502c0880b5800350b580c50342d01c52280ca05031305a0000000740101c0b200c66221010b84c10b03030190f40c4021204c8a684003420758001c4101c0243c402d000700e0f81000000c00c600403001700c19070314154040344148e420315500f154007410f0003110704155640c1a4100c44040400ca40101c0507001402c88400008501e0700990381c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 970162634 1250 970161384 970161391
    0x5070803030109050a14010b09030a0f06050f070804080306010c0204231006030b0604030605060301060e13020a0e070f0e01050906121005040b060708030c040308070b06040e0c1c050a05010212 84
    0x1607031328040010300206014460f003410344d041584210b000b031b46884543c0310103410903600d01e07a05000e010190400a0b41e40f0390b0070f400d81ca00c560340204062920047d0550b180c08014484c4061080200400002401e8030040300e500c0f10090030b103042840d250b0f00100380109540b241c5400c1003883c00b040c03490356007169a003040c0b04484052410110079210b00c2c017102a9945005c58a400840a00c03062000501c5034000d0359000c0000f80001500c256100b15607107445000352080c4566500051a203010750500c25124005000c1c1000480385501b400d4400900074030600000c030040180c2031010040ca0707803062080301c1030b081008020503140c007889a221900d010781501d80e000c9a4484000015860400d40500456900024401420001140c031802c410750b000908203524507008200100c0020584e50244c0056409945e600d006441d00200340401c40d651000070010503405880d0402c80d50380ca41d00041d000310040b00c40409001107902d481460440300400082c05540041000e405810201000920 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 970163884 1250 970162634 970162649
    0x1b020309040b0a05151e22050108060904080705010e03030a0e0105132d050d08090c0f0a1203140c0c03060c0a0206150f090106050418060b180a03050708030301 70
    0x502d100802001803907000f9100381c5400c11030101003030015165900203000400c9980c0716910f922500a0900702c01a40140500040c07011480d40e0b85d0a81d1030412102e1015000030b0802007601d0425000140081d4001040181606000036003441000001e41052082c40510400c40782c5900b0005545009002c030307005c0e181540c0d03103040d00180500c46000b1244441503044031740394054004004c600c2c80c00482824110444c400b060000200040f41000310300584110f941d00c14699041003408070b801e200c0e01d44c1c2d1380b40c42925010340b00d40346943c800240d60b0484500a42217805000d4500d03042e10407032001803041051110108540e4a003c0001c6a0785c82d0402c812000d0b203e0994815001d22950700070f0004007001170b403100d000101c6a06190460034500301c1c0080c00305044000343d000242c00f1030004d07000040007a401080c208000104200da2694103d40f40205003c0300e420940c040340240154801c1900b94015841f4003070b880d49032a40c0c02000356400c0320544100a4070340c09842c1d40c4e07600c02c1c81141c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 970165134 1250 970163884 970163891
    0x1309020a061110050411010806011803060f0e010b151c0203040501060302040b0618100c0b1608090a03120c0311030906011a0405010e0111070b120108070905040302030301181b02030904 81
    0x340c103d82c99104403445164800d8505424206003c0119824030005120343e0500040104604141021610380750046108020109800804039601015102d6a1400c80310a0781000551005582d034031000849007003603450000c7d00c54803241107803074000340042d440c8140c413880041801300340401034000000750b0f402503c003400012078110a0004d544034490500f854801d0b4820a0b120514048110f0180844e42e4642041c2e0341405445604400b10160791860752045840092002c00d50041c030800d034084840800703410b079251182c402030010308070141c5c0e0308001941d82a20144141c040d03804a00e9500502c2d042075181c0c98200100c0396100002c4c041d41e40713400080c18542c54003002d600c04803800d440042c1c0d030384a4080030600c0191000c2c03000140e400e001d03019102d404950138152001078041141202c0c0281029450101d4950600c410394002d58002420b040c00c1001103034001080300e044501070040d118255840201c0440107100484c84442e243d0703040403454000c10b6001000d0f2120b03403400c89081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 970166384 1250 970165134 970165153
    0x209040905150f010b16020607080a0804020901150c030806060d06060203070303051b090d0510020a0903030e04110307050a090e16111f090c08010e0312010e13021309020a0611 77
    0x1c143c1120901c0707103a0b0518403c2041c1000d40740f0802d100504107201800c001d00f804001c1c0c7e02e544484e00210001000100a0000c00c401c1d40303414000c481c010101030b40b000b410002035001c0200301e400b41620260502009038003041c01c80c0c40303510450318a255559010414652920303002901ca0780321450690000c2c4c107010100d03001016003050305009880b00c0c050280703080e42480c01c1c4070400400c030005640e01d02460300314003003001d000c2c0010544400d06656800f25a411480e02414603108420b005002d80d2a18942c1010602c0381000c4940044007030900645442880c1401c0f40e14006940000d50507588010501c08070300c601026440c400d01058466000c00106000e80c599903403c10054041c82c0711014240724620807295100c10311a80c01103811418140c0c45034051401c1d41c10301204140c080d0b04c0003d110304100204070b07c032405050340f900d440001e402d02810359000300348a81400391040c080b40189241e051581c0d4414984294090b01c00e480a5680d40ba015010441034000c20140d405800c1c401c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 970167634 1250 970166384 970166401
    0x219030506030a03030903230903071a04030f020d05011e0f0e07150e0a03140f0604030c080307030608150115030605130b03031b0f19030215040501020904090515 71
    0x2800d104440c040d00030030440300030713072012405402d154505905001d01c20a0361400160b02150120140610254541d5151403600916290007803507449040b0702c0a0f01d02400000c000c24004481c1200d40028a10312085414000a0b8070743c00c94800c020300d150719059420301e0b050b150400750707440d42c5403164023003000320300780d004000c1540c0c910340a10007a500480340030b110640b0116481030114059103040f03640b80c080701c4007184402034a43c01c01d4501d03e150002da034040040410490303d03c9403030000a0106070500760350180c42004403440080941c000400021025842a4041801040300d04111104002c0210308002103640070f00030f19621200d0141140d403541d000b8012403040395400f0300ba80c0700500102d440000202503010503150305d800100142d80c0c01024140051560703c48075005050f49408041c0b0440c904020314400d0300c2c0303041c5108904400310b50045422000d41c203c0d106ca1500a60b02d0346086802482190103e660203481c1c500300c0010f00c000000e1090800544c440600c91540740c4524 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 970168884 1250 970167634 970167641
    0x60902040b0108040203030d05070e040608010605041a0a0b180604060305090f06100b07060f0510090608060601090b03070306170c3a0c0f0e041e081603140409021903 73
    0xc000c6c0d010303442005044d07648c3c642c55000c1075000380d040c9095001c5c400c1c041c00040544040364800c5125a446080520092801c0d103d40005650000300014011070580301090100d45903100c4c040341d6000c0070880f40300490b000c1d2904c00310b00800400c0c2c83d86c2c0302d480341c00141c01004191034094a520651140082e01d143c0000c1c3e07603000d4200040761040907490012080385030390203203004441c5c4d181c0b00c20030f42c150b40e0ba441c09020300444194842c861100e003000800c07001c40d1902e900511003607024006004481c1d0b040321144040d50740d2558050342d29558032034150054803080d481092481100340340300c108800c010036401e5032401c044500c0001c10149581940e0005188007100c3c184031209161001140e0014402c908828851743c01520322560752103901008148a0748103004520220082008101c0d51101c1c1c031082c500c0780050030b1526015a240d1010314043c9441101e000d05054907040c050501400c01c031070071020000081640c40340c4a40398000a90481000400703544590f50003902c0c2c0e00e01a01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 970170134 1250 970168884 970168891
    0x11401030b2509050d08090a141302160f060e0a121106010e01050d0309080d0306031205070506070806030c06030a0c0201060501020718050705120915090703080f0d020c0a060902040b0108 82
    0x80d9010055801c00d010070030000d482107406c9600d21004c001c3c40d090741d120b041c0c901e0001e00c0d0315221516001c1240c002d00c01882039204803045600c0c410080010311000500e5107600c00c0303804c0340101420724103c1c40d02c0c600402c81410b0091843c800c501c0100100040124400703a1200310b5690080c04225040c04140d90746401c0c043e9a02078240f0900510403402e010f8647d91040e4020b02d001426070f85d840b0f107001d00f0309100380040300001e6290003050040c402d9010703101c08c14940c0340c6002850802c2903198192541d0015000a08002d510000318100ba6010400c40d0b040200007441155642441ca01c0303880145160300c3d48a0140d42050780000b02507001103132020880c2c0ea2112180d042c2c00401050300d0007001c0082c00d500c02d020090001040d8a108511403e104c1c0c60500020700040955020f202c0318000d0050500d506035005c420240b00041c000000da40c1c01d6140d010b1082e441d0384060366180082c0c0200c4001104610416282909109250300103c201c1030095404100c58000280115079801c000c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 970171384 1250 970170134 970170137
    0x1c0b01091d19032703050610060e0f0406051201150803120a05061306030305120f10140402221502010b06030601050a090f1502010e010204050a0b0c011401030b25 71
    0x244042c00a1001d000500d251042c400e1803d24400c600c0b81d00700301c4510920907040c61900038414810b0080210801010741c102202d030b10400d40c0b9610f80300e4000c00804e0300c19030460041d40069008e00540d1601e0300082c0103001c00800b1b104150480d00007241c024610703003a840704100304d89100000d10700030101c110b921002120512010325524080300202501002e0005174100400400040d1900520b11550002c1c51080c0d690f650f50f804030b92100307054850040c00b0080d400001c80300703201d910703a42001c2c92801c840d4420780c4420301d1013401000400030300940790880c0d03139080c42c61070070322401d45030b01500d00548400810b075115424241c40700703c2c200c5a500703060541001e01040410f02560182001d011541820b18200f2111030712a81c04030748002190340551a2a129404da210740281c0a00604d0450b480307110013181000e24020005401c1c104a01c241d518107680001c2034030030040c0a4210b04648401040e000c807841d6500d00e05400b181108070b40001c0c2100001e50300070f14500091482d4104828a03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 970172634 1250 970171384 970171393
    0x406060507022412040506160207060f020f0d2309030c06030a2a03060e091c11070311041b08160903170a0305010509070c060b1c0b01091d 61
    0xd50074402d00074404108020390068004020300c00744103d41c024203038182c0508030881242042c0ca00180707000c0015010750041c503048000460441d60018040044401516200c1003103503502000342e041c400e118078204014000e442a1001075500920b0151040c174162040e807a6000c2450340c11909802441200ca5041d0414110220340b440c00780043c5030001c0188000142c1c0840400b0031114005103040c010301c01710030814034491615054881d007070080030b0040c2203024a10b000c1c26082c0d202c1402d41312510702103130000b0210380c01368420f07100b290349080d0b01c07402ca45d0744640b03d04000c00c10410341c1da4003070f20445c202855580940124401c10a82d9816600e803504030340c0300c480f550703020034198040c0e4104100010800101080e51400101111410700900b10b0b5900c1094400a0943c1c1058000602841c2c0708070a004850b070f0b00c502510303040d0740c01c140000b0300c880d844000500e5400b80103032001c0500c0341d0104000240f0600c5188181260504201000024200c800060745081c1f65031501959070131 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 970173884 1250 970172634 970172647
    0xf06050907080c04060c080d050a06030212070503060c07111018230d260903070602010606050d09051f05310f0602040b0301080a0c05060f09040b150a021b04060605 72
    0x8103813040d00035100d807e115040480032040402160703022680580c00b030b501c4110810540c1040c044041103034075444064103402d400c100100c3e80d6000e01908251803440d0019404090104811180c1e641e800c0c01492040400c9200710000c08506011f40079140351286001b00040e260415035140754800c0326900002c405484140811500110511082d03410608108040302c89007181859450420880c1580d10340b9201d03000241444d15a494200e00b09581c50007030107201054009041e46c041c1d10307a5400c089854074031890710324105440c004066248541e200740400401d506034100b03900c03e40c3c014200c0b400300e041a00071407512401d80004901d1440c030750b0b0f0809012541401d0500c030380ca4000d10005d490176540344c0406c0d1041e0303c260300a900d25040000c60400308400c6003880c0c4028a0b003101c070942090b1017004030310681c0c0b00351031300c00388500c0d0f075032442081a4a400100210246414504585940c0b1101d0041e40f00d8040300d68070000e800d14420300003514640f40c8100c2c0140c81940e070b82c50781800f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 970175134 1250 970173884 970173887
    0x110312070f17090102070c0905070c02190b0f070b09010c0f0c05031e09100203070b0a051e070e040b18010e060109030807030903021c02030d08190f06050907080c0406 73
    0x500e508440010403070b010300840800307a501c0740d05901880d00203000580e19615802c1c9142d420000c0c6d004100314900706028449415482010203541c80e80480d901b900d40300c9506c84101c84000c1e560302c03c5c900640c2c0443d064070a08520030113042c1c85030054030307503c040b5650b2181d07103802c0754442103c1901007201000702c2000948100300690f10584541e007282e18200364080d2180f00320480c00e40400001c24005681380c5541401e0b5030807103084015000039800c1030f078180d80f5545042d10007031100700385a5803038000440c83d010305401c02d501031250102098060400c048018a2014401344060049052000140f05404c16a006500003071303038000681d296909002640c6090700c005807030141040030316100807000c0340361007005203480f520944a41804900e1403043c1b00203025461040301701000d50301c0810b40540c5000c100000651014501880c295a80b402010b000c00050765890341c0552420100e0282040280d0004003030f0750044034101507550b01c0c0402100c1300030f0100d9810580410912003001040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 970176384 1250 970175134 970175147
    0x171504110102030c06010b1902070608040206071104090b040209070c031b0203010e0607020d0215061c0c090603051e0f0a110a051302130b0a090e0c09091611031207 72
    0x24030144156807402c5140c1c007100703107018000c0e0403c2c83c900b0000540710710805590300c03c1c20070b4042c1d9800500810303845c244000e0f000b09002080a0300030040003600c0c400b0890400b500c950b0040c0000d00810000d003513030401e00d00303025048808902408250020801180c042c2b0b00c40c4124990565803214102c00940c41c03115420f20030780040360103648415080940000501040d8810140c0707a0080070038540c240300c024075282c10804901460389450b0148802070b100c40701031500301600c82104500105452402e0200032110783e00250300d09151007000310030454081a040e401c4c07524643c80e4402c01c5442001d00d07813a00d0300c111138050198441100c450009044443d1550b80580080c004205555202e001ca008030b250b0284928040d41e0014120303403000508a400f4001d000000f078800c0c00e00121440281c94111240100d80010582c600043c0f20707840120111040d10101800301d000c00e003422079a444410810841c40700104010082c3da2412a6000080e076500101c056100d1003291904801039400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 970177634 1250 970176384 970176413
    0xe03010b131113180606140f0a020c03010e010213080c010e0913061b1121090a03060f020306031207080a030c050d0c080610031b18090603080301171504 67
    0x5195080c802e0361040c03d40a0b040c07600819258070b115403101191600b410441e4181e420072010303c000d0301040f2400c02c8000c0c0030780e10010344003414a5a91000400160b1500b9501c07100720340d06600b031a003038a03800c00701034000e46054610007011910440d1507202d8aa107480820103900d000a640f1051016245440c0324043c0d0003a6400c00e80580710501c503103c59050307980e02c5d00b00b012500b458079041c1102d56804203a55920303003100009045282c1804201042c002e07802524030a00a601044503601070303540c500d12030010365001604100b10701c804414803000c1d40085420718801d00440032051180e1a20344210366946078002074591a1a08826050f402451408050400c009003400b014040406510820441142a803100c64041c1f0708401000348007418a100310040505003c0894002c4403610b202c20b2044205040c800904d001090100d41030740c80c264801407000b81014400020300000c50000c6050b00e0380903004140107060404070b076503180b19421000f00b0800140c0000750108441e2203582d6174 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 970178884 1250 970177634 970177661
    0x60d090c03050703230a0f1103070509010806250f0c0804030b0a1e0c39140c040e0303070c0602091203040509060102010e190813090902010e03010b13 66
    0x401034481d260b05140400540003241e034a407500021540d1a038034600b84260380c24040c0010a0f00d108260380e44c0d10b0380d00030140010000e0043e80b920784680d44d0103028040103480060010302d0070f9a0346e68803265882d003003552150012802c580801c10300c040192080754441009031921900564542002c855420304180f0654004000307010220005905100c00e40c043d2100f00b0010402c003041070b10010b80182c119101060311860210010a00d580000c0c44814012003400580060a004400311340115800400c450764042111104402c01a100c01d40314260700003071045607420300c550300a000846220706280d44150740184005501d0a1080303600303200c02403041502508000300040440c4000035102845803298201103820f0040b42050a9065401078092000f0720007103401103034141d2107207419040070100090404001050025000817542445005220a0841a601c1e082c0f01d004141d4010100d00041100c1d9400380c283c41d05001c0d120103244020b062000c183c04414001000300b20820940c407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970180134 1250 970178884 970178903
    0x703050d1803020c0f04021c020c0f060c030709080705211e01020d1526010222150206010608011712071a010f03080403020d03030e01050106050d1406060d09 69
    0x407804020a000c5558040c420b40050040000c04001c03c140346942c0c080d02d034040c5105100022800403001da08220700c90f00c0c50401070f91500400c0079241440d030f20310300c0303052582728507000d01400308180070046110385a29921100b26544411465468408901ca0340360700140c0c00800242c058105070491011102e074108480709100c8401040210f10b516502d03070142c5035404101d5500488607406a003401040303c40760000020b05020400d0fa4161a0600c0041c6180b02c0c01c0c84040940c200b5030440d000340b001c198034a42298480e0104051095042c015107441c0d20066840c09070003400040d50754140e4071203868a12180e800d125425a210f40c1e465446105446071850b48110035285000404001d4050500c00c940c0d0b090180350241201e00c1a4098103412a58500400208600005035400d481c0e044882441c02141402c086014003d5200c0800c04c030751070840002102c503000002400e0300d101d2804180441d41c83c50081501c1180308075500c07500b00408010004808600303600c00000e26124031900c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970181384 1250 970180134 970180151
    0x150607061a09071d0418060203060109030c09020304020f030102131e0e0a1d0708070608070c02031e1b0d0b0402031e030a031b120b0307090c08041401050108030703050d 74
    0x80c40c0304400741d5860000c00c800a41d8039000c02d41350603150100c4101134030300f8840311026502100e0501100c1c000075100990120125000e6031040b841c0b04019038010280304030403521108464000c0d0310540d42284900b12044031380d032003828103000345e41c08102d60042c040c6906d441c0000325414405000d66540203910405004100403600c0001240a6400c1800005e644d4800f492030382c6e80109140c1d01071146501c0640100540040041c540c2c3c1030f5622490158065121810251362040e040703c402903160045e02c04081400700390708211a54039480100311103440c110480c18803c02e5607510303040c5030410448118807010500d42a8001d070080e20181c102c0307030b41c011202d850621502c0c02003110002a000064000c2b14542d040c000e07160400c041c200c6640000200f0718001d400f5054100445542d20307110007292001f95001d0003c44010045144144000d40c181c24004003883c0e000c840c112a20040384604180302c1d00f0510a4905a8180c54020341c81d04089483c103a4a540019061030384164482a92 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970182634 1250 970181384 970181389
    0x1e01030e100e0714060406050d230f100b0909220506070906021b040b0f0913060e0604081b0102090d0b0a0c030e100f0b090c0c06150607061a 62
    0x21000c2100070018005642da480e40b00c0d150501c4040d0b402140081081080c4200540e1039204171811607140d800c00300d549001c5200706a0140080000b5080180000c8a4000d050a00320020502c5000714400b02465591408a040d4101c00e080c000c0d1140040f0500110f030060401c1c1030700d1604012140700b16144141c1c8295489401c0e2024002110240c2080d4244103801d83c102d4174175400b030072050015260180c90743c0c280e1011a10b8004e00940b0841d211112020a625100058240d02c900944002002d1605005042c20320110803000c0f0740e640d280103c0b485260f24081001809598007506491900415000364003044964140700c02d4503541c02c00054004d0354540380c00c043c090b0b204400540c1140381c401d44003030465051050314014941000c800300c804410104543c0d04542c1200310014284554071403010042060315211504404c03944240056821842d01500c40400810700321500c83e503416400c2d05c8603080c00310005400c00c0043c081c540c001400c54000c40c2111504aa50324030740c0c070b040d900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970183884 1250 970182634 970182643
    0x30e040b011211041d0603282001020c040b0306010308030612070e160c03021e030c01050a0605040b0a08120f090301021903060815042d0302030901090e04021e01030e 73
    0x111801010b10004d410080b800c03118504804a586080640c68071740740c1840480d4032051145411310b43d20b84000b1020000c18024104424415048840da50300c00100482501380440c0046010380588982610443c041c581809805580310000e0040d2100c1c6c1d00c0e6640e0400d083e000500f410364008580414220003c90802004d0001d1079111441201e6040c41d042c9000d00020003034503130703080100301040480801c1d0001607004d400704130420fa0074010b031400c55281e81503010b202d98a1943d54240741c00e0041e01319564009409444040703500b0004100c01d6030400068000c0e0b4030410f0b6141e0401c6c0c10742400d440079440680100c03001e400c025494030200301f0000b402c80c1d10010854118520780350403845820360511071003002e404c0d008000c1917814494801c03c0b8417610b00401c000e00c240c600d0665503517240c4844403500004881304107000310403140307450069102d40014041e14001080401c0c009034203142564028003898001e03000348001c40c0405241c00c1c1c00003005106605050b1101e030042c006d0b00c030402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970185134 1250 970183884 970183901
    0x90a12050a030306050a08061501140d0e1533060a2001050705040e1015121406010c021c0822090605010806061303150504031209030e040b0112 63
    0x4080c101c803203128540a411580c403034021074040c04080c1002d0007003820024601e81c0000d400702d0b8190a05110000495404004491100c0840340c00302ea0340d0407102c21a0043e0305000700d05400d503000f5070250070f01d051003a14226540701c11490751504003000204280b92591080400310246106000c29801048855221440c6103001590b800002c074000b40c0300582044501050300004d1025081000c8000c000f8021409551500003245020542d581c0030900407a0051072401499003688040c0c04010f00302c0d0080c00c0d8801304050918140000500f200c600c0b41d8030684050f180c58407818410340074011111b400c25100c04903c011500c3d041d001c04c185102500074440c5c16808201503c04059605c01582d2140d0f000c03428071428024248401da07000909590b0003a0182c07542c603111490740402804140140d800070b0300301c00c071000081400070560340110b482030340291a00c0400c4c91184421000b1544007030b9020740095540d1588050500d4170341c2200118100502d0700000d4800c4000344181102c2c07011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970186384 1250 970185134 970185143
    0x90b031e15071106100303051e0d05040507030210030203062215080d0e0a0b0306010c080f030405010213120221150a0905070503061306090f1e0203010b030f030f090a12 74
    0x160f49041d4402e10400c1200d070303c82a91440c0203102440c50342d000d815802040c41060700029150f080104551000c001e81c3c8820805040a02080c1801c0c28070703940320904c5000c02c0e0b0044401507032400c0d500313001740200d03030088074083c201494030822208207062503d41c415030001745c581c581c00140aa00541800100a0202140034158840e45c1c404060586000b288100e03024540104040044c440d03018180c0b0b51281013802c140c4907850151504481602c90070801c10045040841400180f000550241c4000120038813142042e030b4030340007884895801044006d5100c1c1d4003041e043c1c00000960590340c48410b1103821101080070707d804031041c603042200d1800010750b032102d0b0707141400020090103005000560281000d800c1a4848207000c9075252800f800300d07911030200404105007004044c10741a0440c001d4160b039003041c0c15825506050304001d074825070070000300c4281c51034041440300620304d03030500a52801d004c000364000301e03400c01118541e00195400f00000c061101111070301056115 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970187634 1250 970186384 970186397
    0xd0b16031b03060f05011809090302150c0d1d03030a0e2107061506050a03021e030a0207050f010c120f0605060a17250c05101a0a090b031e1507 63
    0x101119890f490b004c642c0481d04000c1030325050540e1505071201c076130554400c440d000c00d001c45141000c0e031403c0e80d080f40706c29480703803500f0030000360725800e40203002455502c8030280403450844120b00c246500800d01000d1503001000885e1074001d1540c04001c1c403507030110a079141d00d80c240d078003018809081c04c0840134100002601070200901c520030398030f48804601003110168200304c0001c0c8540610740b040403d160380002e514140c401400c40807404810100070301c40d80d80c07400c0e00800001c1d411284085a16104041d5052000007041c020a8907589503580d0b0207000c0c040d80c400c1407014112082e60441400d9964002141603180c140007001d0849194a0304d0a10140c0c0014024882c10300030010071303201c010202d4425110034620010340c00f00c80280303003107541d4a2031400c200f401d20701040c0d0803100481ca860040c0500046240031240319140c08c0312030409a40e60340645a040d03402e9807880c90f50542183c14044502c0d9440c025040341001e0000c00c854103260085c01803011100e0641303086d0f000c03078413 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970188884 1250 970187634 970187639
    0x2120f04030c201518061c0501090c0f02010b032104050a17150c070b0910060f080f240405120f090a0605070302100e0a170301140d0b16031b0306 64
    0x41601d22401c0300c210300707a451485c000c1400c0301500d8604080400520a00000504909103403410300400c4000302c40c90404c201a594501c5054010003c840c3d0070303804901c00c107402e940f0250062040e1000040040c02401c89040c0140d90f144103141c106030720414020003032002003910b4440c510004003a00c0b009034084024110410714616000c0101c81c454503110001c01000f490170400c00c10f41c0c00507071380b01d02d082c01ca940380d4122150030482200300801c0c04a151010002d500c00c801164441103614007000c2c0c1c2c044040303821a464591001c940f00074980e01d0240607014141818001295010303009000b07440091410200035812588a1220400740b00e0011503880c2c03203441e000c070f0314400408490411501d4911700d40d03000794690480001c8001c68a036501040031400009100303001035130303901a12600c51b04826200310403460300207016502000d240d00f00c4801702401d107001001407054114014684e29a60900c100300c0003004100280d0401d600c43c0f0006a03910b81d0680c6050303802c0025180407600a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970190134 1250 970188884 970188889
    0x30103060506121209010c020a050d030c1502090904021c0c03080315010f020c04090c051804050f010b13020c030f1603032a18030215030f090102120f04030c20 70
    0x300200301c2c080d044d0b0050720001c0884400b41d800c9a206400070708010803160707214000076049201c203500c00c1d03400c00505203040c010598000a01508240314110500103034960340e42c41802c038003604911a07000703000c000121300945030144128800c41c40c000340c2d0a05603e01030707840d100d0201c8560f204554030b410200603c200c0750a418403850070100c003841c10340c1080341707a1500207503101c604142c4180155136586907401848941103c0d0f20180c0009800c80c455a620f11b01459410304040340c0603182d034010210580050394041c060304900761001020583c10640740c41c01900203600441800700540720401894100b005664050020200c0503840b1207190451410040d042c1e03200e04181e0141c00b10700d40c5403103c9101106544d05208012441c1100910420700d10804042c0c0c0b5942000e9841410307460401c10300043d5000a6100d45504c2981448a4840103100c60907406803003480d58007819088001048200d078504c1003075101c2d02900d40300d14400960303103990801030640c0c0b10002460304000d5440d8001d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970191384 1250 970190134 970190149
    0xd050f01060b030117030304031202031801110703080609070203071b08010c030c1706131a181015050301060f180305031306090f0e0c0c1b1003021c0b0d0602030103060506 75
    0x2c174003561441c586641c008040d031008142c41403c4030b6011010174421101e0000b01715440880c80700070032100303122003401c00703280c1c10512003100058001800a4000c1c140419802c0c01280d040d0001d41c100200b0b644c4a80141001c101074074010001e119000074665003d0240342e2404009460001320702d01c9483e00148061020040008444603030000d1020315180c040350a04418941c0c4000100081e80b10010f00280d1400d941090303011007917101503020317129222500da0081e02d1002030300355459078422681f07000d440703101c1e940c07c04502c6c140300400050340960325210300c2c40c0040c40c001c5030380f441c500c141c010f20300c03e160070a40b2540d01c08a410480e0380c1803010400003400e51070030000d065900d030404042c0d00c40014000c02d006030213100c01044240b41181c1c00d0343d46a9001380292407520340003000c50445000c002c1c945c644940404403860480314002e01c00c035035410b807a036a020300b94090084a4100905503605406070070944018454002c00c0321440030f9806140316513404100d9050400420009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970192634 1250 970191384 970191419
    0xc010507210b030705040c02070e0a0608010c14160c0302060a120c030e071e030209040f02040513081204021201060611010b060a0c0b060609100206060103050702061003020d050f01060b0301 83
    0x1102d182040c90b140070b07900000e440d02190780403540842c03103400c1e0203070072410f003001c9900450b0071500190078481c02c54002d42140d811307915050020086940100c01c2100c0006904100c105602000c101190351050200034605805005150055010355a036001c03540d00c0d4000740e01040010002c00006c00c0d2500240503c008001140c0780c01d01000c0c06880b40303561036628900c02c207034030411801c42407885248800e8a48009680041c02c80d44149403a0074100c11004241108234402d500e410009900300ca18400682041500402880c0c01c180101200c0c40a01d00701070001d99201414505100020000b402040301030500303596401517903260740004609607052100c0b4031703208110500038981c1140e803012404d01e800b0b42140814226480d13450109005100c0d8420f0507400148801c1020890385c4c00040041c00340000380c1e0100160356802d24100e841c0c00d41500c4d441c503c1d0070044010001342c5040044030300424007070415540300781840300c1480d01311340e195800519000e13408801080141107081d1500032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970193884 1250 970192634 970192697
    0x5100e040b0109060e040e160602240403083702090a14091603020d06060903051506090a020d0b09070c0b010f03050303131e06051803040b0a030c050c010507 69
    0x88003410844c019041c13115200726103000d1580e038000707040a400c040041e82d80c031841400e40c1e514882d84440d070080d21a4a0241c10345884061144001000070b0401207540c4242d805545130551030300c2e94081c3c81da04c92a038420700e11400400c20910503108041000e40060002400341c0141e0310b211800c00d10454841c1c2c3d07403010b400042d10300c1d40c813846074650081032503120405c00010000d840028406030024007601182440203403500c400450344903000a4610b050b2406481101d03041900b007003088004103000c0701c49035041150340000c245c0070411500030f000b200340d180c5000b04180030310304040b403040601100c6220000300003558080c14018183c0b900c502429120362000a4203085031100e91b40c9100c0508030300301c10003090002005010890315400104c40c00d58200a89640d820705011000c1e00c000d448840785408a103021811815000040f101182c500c5d40203a400d018211100340c00078600300c0c01000a21000704074400040c03d080c032800d80b05c0e09840c1c46511402d001e4001c054124400c5085072030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970195134 1250 970193884 970193897
    0x120c070b040305191a10030c050d15020d090f0c050901240c0c12060b01030c051e070f0210050c01050604020403330c08060f010c0b0f090705100e040b01 67
    0xb02050001c07441104d03540e992038009403a0266441c02c082c1240038405a01c0c8041800030502c40d1024601c103a0000b103a004481901d80c0c1d5455204000395107072000781c01869030540504003821112680c018149801510400044108071904d03241d1044c0400700c4111214603194005010b24600035444602400204200c0b03002064902e541d0100010401c0fa40f1061050004000d0b04006540c800000500a9040341c01c034003255a15200c005030520700134440c042410001d01c403175524480e6058035000341c9162400000c40003918910b8203198031840e41640d22122208415015072206009041403206130703991070350346010040a81c0c2c02c550780500694031440c010003040000c42c00140c950311200d9214164452000e286d01d03d100401206140344000890410b01c049800b035407c021050b1140b641036503403200e00392110f001140d0711458001d00034610041200404c10700420b41240c50b5000148804440d0780d503407070f2000a46070000d44c88054000441021180765141000d02940c7c081400a00b4080b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970196384 1250 970195134 970195139
    0x1020c0102070b2a07060207080a02060702120c0a03031503050115060801051e060306030f06010611061e1602070315052205060106050903010f050103030e03060108030a140912120c070b04 82
    0x9804211100c4140316046402261017418030440da8102c0b079510360f0094100d50b07159101c02006e903c5040480c0c0320000b6018011024054201e090121211a00c0d280b001d0100038040d40d070140d00a04070100c0010b040513540c140800008d00074032440e4000c45c00f10702048145e80c60103400034032129058005034051302c0c0e12100c0018217054240903000650342190550784958900340480c5c03500381e40d03100716112072044a0002038003039000a0403850019482c0107960842c1e6070035200500b1a82c00c0c1108605244070000064885445c1c20002840c0d0206803040d9484a41e8a807280b03a10303e4404030b01c020301c0a81d105c0038441c03058002a11031014040c1e0b944240040341c400d40307030b641d100e400503c00c03e420b1040025006009540030341c0194001044050308010710350312820003e12a640609141d4000d105000010500b520000306850708020b20755141030392010380d045414030f0341d0480d60b055500a001005004c803c00401d00c01001400405405c00351a403130b004020500d4400c45900c84288540208001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970197634 1250 970196384 970196431
    0x1c020a0302070e130f0b1b07080702040c05130f0603050703200d110708120708010f05060d0e1005160908030409050c070f120f0f050307140c01020c0102070b 69
    0x400311080c040e40150365903182c0c0860010580d604d2001001400180300c15410801c0e81401680118480d001800f4410820654081c6910400d20007928204e81446401c0c010315064010b462200310314039085040014060480b05450310756006801c0844018109204155251007030b00d1703000c0044d1800f442070580792011030750320a03643ea400c0d030035010000840d003420340e200740c01000c40c1c00e5a2154850b42ca00705d03030410804a400c00c0c1c0da540321600e00706001c5214079100380c6001781616a10504200160f1500081004507404130381118644e1b41c441c440880480418041402000500d950104003031401400c21036248641001c8001400300742e4000380b0840c14000243c80648151100000daa5140c60b00b860450f8040d10b20001e004620607152007040003030b01035000e80921100d440e918000e40d00000c0a4402c172003e0111680061010300010b0401ca01c501d00c050440020f040c1c406280c8550b02040b6420790b400211010300e5030390009030390740c108940c0398001580240500100c0d1280c0303014198 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970198884 1250 970197634 970197643
    0x414010f050a0e150a020105060a0f0f06081504050906100801060b040e041e0f17031510090f0b0714030c03030c0c101e0507030c050d0f140403021c020a0302 69
    0x500d0010070280114480d1a134852000210b0715121440c0080d455510440d0000d020709400c603107040c007551074043e001401c0c44c0d03484181c405030303100d80a80c40d01090808500b2180040d004203c1001e610703403032021101c56102d9205480c0031b10000d402800e2149440c207541c01c5000b079594846801030703140c2901002000100f9040c0c41c00e55207061074400040d203c4d41403e0200d20340c503010b615404407640b0ae03d8030030040240103aa040d54070540c020004a13200201c0034820b40006c5a0380c29404490060408841c079207917032042d021007201d0420060a58454040d05410700c001d810203950042c0005058050000795103034400c080066070020340c58000c1604051ba22804041c0170308681c40c03404240a03100d0307001405052240e50082ca0100034000c04071602d00c135046a1020900b05c041c0c90280802d01c014801d0003040341c03810301c94031014684120052484014044a0344503507407103917121540800310140d01d200e14010340c0240e0041c1401e00a808912503410091400242598080b140180010360040b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970200134 1250 970198884 970198897
    0x709090b251d030f03030c0424210f060807090f05150f06071403130806240d050601030f02040e1941070506070804030f02030705060f0414010f05 64
    0x4a401e00b90202400320b403404204250100003400007008205807031074114068000c8a500d06220860303031814814010100e4000601480003490012402100040070312118000040c00180061804034800400044403c5504100c0060300030940401c42c0c684039000ba000340d904070075005c20060404a40d08c1c82c102d09103405140c0945545060240c2c9586c800b81502c6403540c0003c1e030380310051080010140c40f4ad102c08840154642c3c94800030034100e50000314184140901102011800b2074000071980100c4505039099104280e000e5080001e0700031303c00d6500952280f5691a02d0f841c00d40304001c240c68441800b04601d0b80484e010b0142c0ca005144201f40d8241c21070441124000351509698506404400c5000780c051103140d20383c4800c0b28045500320003200030f400e40d44c82c59196400c04c090b038490500007402c200c00c140024000b050410703404020991000781202c064070340d91b80101d01d0940002d00000e60305000801d0030400780846502c203003045c074824031b03003d0405541d46601070010701544 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970201384 1250 970200134 970200167
    0x81206033a0302070b1003030216030b1b04090906091109100605030a061a0903011a010c030509120a150b0a0332030408070f05030a0c050907020709090b25 68
    0xa0703200e4031426000354112002c664008591400740d19003404500b6002c812444200c00510900844d40c11003141d1071409001d586d4068134807945500e0320311106540d284480c4545011440410000425912500c565020684100300c0892080500c5c1082940440e16091050281c01e04a040200c0800001c1c40d0100790381c09030a200b6200d0b191070a48600418564000c40d010b50340c100e01004040fa001000341404c900c0440003800325111070981004e40000b107c1069011030410103800000130300a50141c004d0000c00341c800d0811540c0d4049061515101c800d01380e85808080707400f5a54a006030203803480c0401c05580c111101d501e5655807228000c031510016100e103407040c07111a4401502c600444441d03a2910449840c0c0b511100f400380c8500c440c2c4134920840340030050000e06401c003c01c610004035004408179126a21308028400c040900608641c114054100d021500d0500d5201c0c2c001c4c180c0c0140c1c003130900e51801400345003170b05025400704885000324183c0040b00c568030064110385003038507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970202634 1250 970201384 970201483
    0x20901031b0902030103060506040b0a060905150c071410052a0c0a091a180103061e020f0a080705030f01170c0411030f070c050a06150308120603 64
    0x10700c8060388030742075044071001c035000000010600c0410b400c0035000701070494080100b0000b000402911406d18401c110200e03902100400c1a4505140520b15055000e07003000c6c43c00b031a1010301c9003800341540010b000010350901901c17690414542d100b245a5460030854649041e201611b1866600350014040410240140050080d0144181220100060616502182c4440c4913030f0292403800d115152111010082d11050f10345070103022441818000611034036420b58540300050500b4440000e03d030808100701c400081000d00c0105250701e840d410080c4ca03114811030081607148060007600c00c11000b401440b140c0c940034069281100c2401c266054000300b1000894100b0304038101301c130341c06494100742c2204401001d00443c400d44d00048022540d644801e0706030341168503100050800d40c001043d041c000340c2c241d0f101444880c00748150900f0607641e581c5510349030784525030001d04110020180902030030b040101e20305101044c55800f401392001d0b2034107500382041a900c1f41c9041c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970203884 1250 970202634 970202663
    0x140c0c090a0f0c09031502090906060306060c070e06090a1a12010f0c05031803030906040f050c0603090a030215090a0201051e0c0304032607121403090d090b0702090103 74
    0xc540d024000b41c0c801600103000d64a0b040340301500f41d010a10007a41c080f810196507110701141c502c02c4071a00c00f40103002e15031a0300c4070740a104054000500c200e0704450108803450003c0020041d178001030910b102d00700240c1c5030030f80501141000c00f400080100f42021240d4020024410f1031054a00d81a500c031843c040b00301c00c01c04d02400c0c111104038100ca01d80113215182580c0700005620845030b03148031403904046090200d035a07200440301c144664020101090010f2981c0c030300d0141d50340c0603a0458606403130050000c0d800394000d50f060411680030200d500c0405030103014211107403800b9265591a441d04004040d00e90640a00003410010300003040104183c1080308001c03005200c924403030f01c1d8400304140e5680ca90041c04255641105040c110b070301d980b12500301c20260181100320340d040c40c8456441c503141d12401c0510000f0f100d903101e00c0f1440c04130718001440c410004d10005004030400b0070005042060142c01c031040300030007004220f003d62101200d880c1101d0740320000000000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970205134 1250 970203884 970203901
    0x705010603080d0c2606150c03030c0c1506100f020312071710060504141c08210c19180303020a060b010e1f0c08070f03140c0c09 57
    0x140c55000106500d10200e402c441ca5440c5502121080c160340c0c4a01c03c403421803542091010756405000240c940060001035824148001c0030208003140002e0325003000c140612072811508210b07036590740e120b40801d6807008081c040005201040b20030240000a05104001c143c10315405510760080c40700da03c640881c000e200f00110360301c1c01e40401040c41c190078020300007807840100c41241d0b2907030b100410124900d8901c002880040315030035251180341501e00a6106910a03008207001c0d8400c800b60801000400c01d8484407240380d2146944030f42da503049030042a0400040443d01c5084280c1004024503e01034030b040b2407540c80d21910401d502c0900381800c41d0203407c458003900440c102081d0000400d0340004004070341c40c1c840e940501c01c5605200c0110b410555254006a20090078100750121030030903030030b52486503168501960310380f000d61600d507040e83c841203048402c01d004030316503c00d05501c03508511010048881c000e10b01031410560681d00c0d91030460041c816a4484003140c040c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970206384 1250 970205134 970205141
    0xa06060803090109140a153005010b12060d06020904020724060311040f0e1212010b0c0d0e01050d0e0307110d2f100e0301050709083316031817070501 66
    0x448601c0500441000da4000b172207400808d00051025500b003900214400b03020605660125288810807806070ba0740c44100840e95200440c1030710705903402c1090b00c195031150b00080030690f00074880c890315a92803c4540c480d0180540c0c031038200c1031400030180005290701021000e01c0d40c00322400700d03c0c100388400260082c003070404400080d20483d100d030000c041d42140034142003061b5560809480c1e90350801a80184038440044466030000c89034402014007480d900c0040f000185030107420016075505600413511080c9202281d07a1021545100300042243c5000164400392003102c9550350b40c0c0d0742c8030702d80802043d41c10720600070001c0300c0c20a40c10000d05140101d0008240551091030f5180c09015507034045000c900a500317090020315102e008452500803500745c0d03401407400c040b541c0106030b1b5918104a0b00f48050408008549510501c111600c0c000c02c11400d0b00b01d0900e032802d00240440f00d03c0000c003041c01400c1030002000c02e00182e1404619000041255a10f072a0742c81c09a004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970207634 1250 970206384 970206407
    0x61205060604080d0807030b010804031209030e040c0c0c05060f1911060c1215150a120f060e071106010608070e1206190203091903020a06060803090109140a15 70
    0x40c0d201d02c0d80f00b07091066028800d40d01940303268404108e00d0645400450780c410084401502242500070310881500d41940084044c2d0b006c0d00e014504400740344005425074402c0c41040c2c0000d2541070b00d601c240240c00c900340000b45170440301d1604d0042c805070394171481d019524111445024100e0041046406912640c003886401400d80340e89251100b0111103580001e0350b20158905250006810034807400c0300544000c000408459000d00744c000c08011303035031180d2403900070826901c09043c5055601e0203400154480c5a0340892240d040c01d80030105e101000304030000300078001d01d0950485102180c49030645040b1320308161159502c0d08140ea0a16070049400c0e000b8150140c0c03807521007404180315005000c0340024041000c01044c02d0000c3e80000d42d01c0d06e0745600503011460084810007420760740c5510030700540748128000e445000c01c4500d16440025a60070000341e503142c0d5030340b040110000e0490810f4540f0701411803004155044400d0240c010900d180d8221185503034080e2054903607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970208884 1250 970207634 970207649
    0x170301060917070b0a021606031e020307020c092d07080702120406030507091d0103030e030a02030613170301090204090c050c06063304150806010206150d0b0702030a020d09061205060604 82
    0x110707d59074803401401024264064000c002c0703020b40900d01d401b41802128015035565000380810240d100c20011903440240c8a24a00f0240440c2c00b01e400c46030f480c084c801144421003510542c0b602450281c00460000d040710115004201e035032680302c0885040c0d8050b130380b4518001aa55403850402e4801d0725041c0c004003660304540600050401400356814181c03442555203030700020440083c10740c0c035a1550002075241d08060006150915402164650a8040c240759584a1203040e080c03c82c50b8802c2e08401806030700080d091000c07200f40c0c02000b036441900d00d04640b40440912000380c46000c054120380c8922211b040180d94040c1c156120304111100b00b45450401001a24000c21948584100c60512001140c5562aa4011400d1500c03646c4103030080c166950b1881d00e41209001007031039540d4001640108200403a00c920751061040744290022360341c03050a480040d02c0c00d800e403c8424204455414280a41684445010600c46070954007184135203941002a14500a6400010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970210134 1250 970208884 970208923
    0xa0b0f0904020f09150a05071104090212070609140a2303030a03090b0f1005131107060b09090f07180b030f060105011106130b090307170301060917070b0a02 69
    0x10044003d0002c103a030f210210345e0f200702483e1090411072280030300d941c620082441400b01d4400728420690204085070010000034020000d503002030b1a003880c0303400f0001c0640c440d8a00b404030a4104506902070028881404184011103001413200445801140c051490040ca9800d550510480d0341d551000c00809898071056000e0006006001c40d001c2900d5071030365500400d650022040d0010b004450031360010384900d05101c14860f401d900c60720101421a61050910048110f442c03b52114600ca6400450320b40340c103c0070400d83c0749026105192507000842d00402c08040042e00008460101510607003465282400000030180c00702c0305509402040c000d2041a80045682c905945090300ca0040e00031503c5840c1e40e4030b100443d150041d03c648501e010000c64415510b1944c088a503070101c2c3e14060b9241d6503030480d541070201015090501000501070503802080c000c5c003400c0aa045d8440d403664441840760f890b40c1921800b110250005490800a4070030311039204c4c40640c1c440c405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970211384 1250 970210134 970210147
    0x5070609170a0e06071713090504060b0f041515020f0109050319050705031204020f120a0209091617030f1303050d050705032a0114090105090a020a0b0f090402 70
    0x81d03499a01802104000554070340304001030340303003041c00d5900c06900003150003c1e600f4004006443c035400041c50800e80317004020006000601030003114402d81c400c00f03000c00c1030a280710500070070520181010740300314101001c03120280f40c0070450008540754000c9020305150000410782c10b0070000c40030300c5542c1d401c003600070051100000061038201c012180c0131403c1110803000320350710300070b02a00500940080000001c01d0411103242c940141c0000c2401ca0301d40c0c070280000e50240303a000c03100e005d10740006d1844410f52800b49507069015812401402c442c004c08000440806003d00680e20091058819524401d00810607100e03426072400016985000c0c446007800b60880c1480112039920075100c041410030b21600980d052540d00c10011070030a09500703010381d0010001900082c001105d000350700d0b4a41000d014100782d4543d00301000700d0504203c081e580c00c0d203400612281c0c15a200403010030050b2901c1c1c00703180842d954500666110090305000e141c0c0390aca100f440d070340d0140c00460360 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970212634 1250 970211384 970211423
    0x8010501141f030b1c0236150a0602060a05070516020112090b0709032f04020903010e030a05040f0e0103030206010303050c0f070f08150f010b131203030b27040305070609 75
    0x56040709008448810f40c1201d504000e080001c5400c0f800180d4907d0b40540760b283c803114a85480c0c01411510350ba00c2241c1240d40030581c10f208075441040103070700c000280a20b05d1031350304c10305810040c240303061460a84610300507030050a42c0c0c0402410809100224008522150b00841c011a400fa41440c0311741401400213000040301e01095800c44e050b40108101d48074100c40d80b1440d107010104456244030b20b1000c0000941003442100d07003654951017070303000840007032008004242e01501d032140c40724141400d41090001c65004803280c41800d01c01800482e03000240380d411682d0519080342c0c2c6503400c07440e072030500005001c140d459225400001c52541c9895013001d00340d40c910401c4414014200e0400c01340080c0c1619030600c0c0407080340c014048010310300010b001d04030503070880401a40d65203414001044410206400003940c8100030101441c21100b1074182c1c04a4803400b070076080b00c1081c140c2d08024050002014814001002410481c3c10703040b0340c008603048605603503940ba0b0601c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970213884 1250 970212634 970212679
    0x200402121314010219031a1002100e12030f100f08060a050702060424060e130201170103030e0f0f0904120f17040f03050c060c0408010501141f030b 65
    0xc00322040c208024000c6902c0d901442500e04c2034459081c0d2840320002a40160001d1985005643c0c4007800d10902e10740c6920381a0360060100e00580c02040c3c20700301c00602204482e0095981520740e0880c4400e00d100c90b01c01419250000b08500d2902102e48031a840360140782e01e280d01c40110264007150000b200342c40411820b01c90b100c1d294080c401c641c2c801d40c0490300c41d50110307402400071580542400100400b8000b1102640f000300c800540c0301d0316501003950014084809848001c00804403c3c1156800f400300c100c00e90810155003525411130b54068510040100310318002c80846110588641e90780c0e842520b40d503c05480541d0f203042074100051300a0200500c54042003041d040300040328400e08100e5209101c1c1c07502c144a80e260390b601d501400520040a42c1080703030078400b5081d192014030a043c061039524000c15500c910f13111031142510030581c02a0b883c2d008a00709509191640300c80f0300480c00010070a01e20044426400360300405007280d215811125103d042e82e203414a262 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970215134 1250 970213884 970213921
    0x30503090105011406030712180f142107020a090501030305030a151a0c032101030605011a0313060608070b180904020d0212010603080f1801030920040212 68
    0x28002d00035682c0b80c21903107455040c1d084034290010b500f0400511814841c4444e4000c06a81c501c001c180d09020b07805160451810780800d8405602d82c64a03042040940000901079080c2e10001d804249032204211504c203160140d1000c440300c3c00683d8100719900c40151000cd0100303543c08100958407030074014400e400840e04240c0d03c500e440080e59034981558603d00031103c0114071581c41503501c0001031084e4000580220b03070741c481401404800e140041e0600a41044a28500707095071541c200a800d0318410f0b88030444002007001c182d039802c400c030b0044a5004001e883d140b00303190050b1400030003c12a5034030030300d028080c1240128007a40320100403e852800c201020741d00032600c3d01007103913151007a60700a502002600da00300050038004400403080a042000048403580c0341c13110b4041381d00c5198000701c194800a101c0d0158510f01c055092401c04c20b00e010081c07100d050359507810000c403082200e180740e40ca84040c41d8840e602c0d0b4040318032001e03003840d110f038817800d1180e103500301a100ea4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970216384 1250 970215134 970215151
    0xb0109051e0105010e04060503010624031407080601120c0f0e0405090a0209101a0a030e0c180a0216050c01350c040b1309150501140322030503 63
    0x280800d064404050503041107403210100700c8000d91a2900644d404c8442c0e02c41e8680194807040002520740d42031258000418030401100300503e0701c001e20486810006408000341031030002c1c8400f04003514900c0c035610030b0481c20248580e07219440140c0d0200107881c19400041e05105c200c500710340c1d1001d00300760b5540143d1240d041c8030300301c04204015a00200e42e0529298007407440b01c03000d440c1209a803a00042e8800e0b00c64003081e160191680004080f48613410010380001d1040542581803242d0074024422401420030107400e800014a00d0544480b0321640f061003001040000c0c82c10b50454161594502c40a0f01340c2074207242582e1038000800c03282d030110f410290000c0c108054001c1008139859210300d051a00468003c112a0390304000e1711017400c0440911011071041507038402040b003c51070300200201a17207041c03020402c0c2d03076032014000c0754610852400c010598004101c0c64540103e0b02d85580c0742d0365200400c16000c41c8a9140f211410311601ca041c2c14160841c00550288190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970217634 1250 970216384 970216391
    0x50705011d3a150c0c050a0c050a1d070804021332010b1b0a12030902040f0c170615070f0605010e0103020d020f0f19080f0c0f1203160b0109 62
    0x46101000d00d0042928015200c0e003402084000e01c0c1c0116808000349460604040707150005e142c445624100307410500315039040c80c0c50304c188a2490448a058010900140f030300b40d144151443c00303c0b10b104050003003c140011180420110f541d545c40101920b02c106004200512040c518030038189001c6940907600394071001034010b41141c654296050342c0c4955a0340b80707880708900361081051122001c07031000d0701502c0c401c20002104180b06492400445c1e1380481c3e48503080c0108011034540a202500c40d501d00003014205a40142c1c40c00c0700c0d003041c4c0355000001d6840c1340c0030401c40f100d021840304c08108002000410400c403540c00c01581070040004128603a21b80c0b0701000f88103001e02003c0c1d40720100000d100700500d00003d480070240d4000d091a81a004003a0119424001c001040c04100c0301c420818070511b18208814a12259a40020030384071405102040e0b0307a501048200340030f00055541ca5240b02010070403a11009003a02e041e107065030260500e0b0110400038040c00000c14103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970218884 1250 970217634 970217719
    0x609020c0a110d0302120f2101061b0210120e070306020c0d0f080f0c0c1e0c04090c0b0a0203071a1803030702060a020d0b0301020403050d09050607050705011d 70
    0x240b0b14a40a0200d526800400c0303032464410030002580c00030356181f00010010400b600ca80816804050030440101d03400e079000e5414000040d00101004940e01041c20390110148051baa80614100d4010428244040e00c1c1c84035004900143c288128001aa4400c01c0400403c01a1a0380140b220800100694441c0b1891301003c80c1c1c1051010802400078810001159001c520710101c070750842241000301e4688101100b81d207003041160385000407101100c2e1001d03070307041d50140000c1083c00401c4504001c400e60399a42c0803c081c00034010810710f401c010601c0c41d6000c0c020000c6400564000814104c403a2001c10460710035841100c2605644199208415a500d4004243c900420b1035801034406a40e031344600c1d81c02074001c070b488268003a48502c0c90f15985d4600388003c101039401180a041c03d400e4500000c3c01c14509640801c0c0074140402944010034008200e1f0030580d0401d180c60500980c0c1c1031003d0381820444443c0382d0703100a82004c000c038200e0304c4100d90002c403221900000001c51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970220134 1250 970218884 970218889
    0x60312090f15031e05040507030c090b150c01060b0412021912381501050306030a17070b0f04051002161b030602070b011719060f0609020c0a11 63
    0x4400b88554030101d00740030100c0e02414060340105201c2880704001c00000503030142a001a9181a1b44c1502d041d04894010706c244098807910030041d103000070b024480184190046040c680828941ea24034410120300e40111000039007100c0002c21421455985071030301c8950f85019010030000887c4036091080f810152044424007050440d8400025141d02c1151521454400703540c02c048130107180701c003024002c0d098450700105d501012070701090460902c0e00244400e5861015a03030681446428010410240d4000030b40d080c00f1a4819059480700400301c0b1542124010b0303101c0185143c5084042041c1148010700452085002d04101c4088180d0704070900e0407441562000003040d140e020000c00402d240295000d0921f03824903c09207800e983c2d498a108030380054004880120b0700100420480d111034240645100c1038101610b10344c40d402081c00c01e01d081c940388c01403c1c291a0303002050410411380c0320300000c0c0403105081d0f6913142c0103035034140c640c42c940d0012540410a002440403a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970221384 1250 970220134 970220159
    0xe0c04090c0806280305010617070e01080309011202090d38150a15091a040501090e061f120f09050303040201050913060f060f082a0d06031209 63
    0x150405041440726148061914900111000c004c0d040140710703020001c0050b60034030840d001400c85d090040400002107020f9420101194812112a5500e400501828a011044885260b4242404518201000903482c040d01a440071b144e03100b42c4454286050054114018100c00908948003040345290341d450000c0c01c441405166100034208002442c0c1e0707114034620011040c00a052400c1d17a030b0707218104403a2403034180d44000018031100e010000f00c45142e00300840d000c07184022906081c10100000c1901d0902c1c0705100c0b0300b10851020451a4a400b500c00204941284400d4241340c00d00ca0003405210007031408420b030515020311303000351044620030751a20940c010081e5117035489a400440300ca4110080c03a0b130f0700040c940101c0015400340d11801b0000d0000e411500001450860080c00c40343d850402e510511621034100401c160b072a0400e2101e00c040400a08800020804c42c103009000d21042203e00780d290441c04003d010358486a4401060340d6681e9444561300c81c24140b082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970222634 1250 970221384 970221391
    0xc0b1302131812030204080304030f061b0f08060406030b1602070909020607151e0b0f060304110d1b14040f060602060a09060212040803060906030c01020d12060e0c04090c08 76
    0x4080030b01c1040008254000c41c0485503000d2402606154442c8126429076110703a100321800704074801c0c80c0040090a000701c45c1c0194404619060200c640e44003d401054161104420880e02c0000600a90782c1c070380c400340245405ca00b40c007159141c01d8446c04880d540c1041c000004d84110310340002d000920b80100d1a8295018140c6814200940c0c4e44242d040000019030618903219440050419440750940d10b41c40e81e15603000c40e4a05140050041d00505d0b01c6901c0e018100c10000c000200d03022101a03883e2590590f10b00c2540300d51800d04200c0c0c04041004e410420b00030900018115410404c0c170507071901c040f5001c01010300803160580480302c540c80b072400541c012000103a4803001036800b2200c60b40c01620090b24242c0e5110710712881040464040304c2020002c0706100d114100101c0c4150300680540c010400700d0038200003c1e41da47d8a0f10a0882000411038103811840303025003040c2d00420325850601c017942814035440d21282c00900401260321725000e00c0701c107001d202c1c0d003c0030300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970223884 1250 970222634 970222661
    0x25120b0a0b070206070c0e2e03021f0e100e0a14010c0b090c130507020c01030e032a0109140f0a0b01051e1f030b0411030f070c0b130213 60
    0x2d0281140e09124403a00408000e44d0403011000b000154104080d640d2440340c0340c02104000810000a40c1010302d540074841000200801101880162034010105c3d00401054080701060301020100b00c40000c0c100303802c1500056401481c81c182c981180b125080054202c40c800421a00c60480c81100481030580c5400500c0c1c4d0b246a41c049160401025004080d00701030701d1883c41150081040740c906480c212095070754450410034020341c1804a403c14031400d2a06002d0318020840a96490065080d07110015111400e1201a540c42000d001c0ca441d0040307009008640b514140300c6038040105c07280c85800d000c0e904030b03080141004540e52181079880084038001c0d03400c150030302010460b00c0e02806c00303a500725143c6010030b5407508651480c582000c1c045d0415140c00b5034000301a140d1080740240a60f00700045e55a42c24914130540b03500c030611a041649543c0c1311302d01203030180d8445002810f0b901d03440c400e118480c0078407075886580c0703402a26040102001c0700740d180122114282c1052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970225134 1250 970223884 970223887
    0x120c1b0d0201050705070e04080a2c1323151f18090905010b030f070f090203070509060d061d091903200120091003020325120b0a0b 58
    0x100158061070190844c1809981140c4c520383d1210249045c41c01d0039941602c20440118030203030b11039070024034a02c2701065400141c500e1001031101c0760349044510a214814840191500b030640a654800701c07034203040307045108180342c26245151840c08159900c01c04089010700c60314803810001c09140b01c00da120786240366401d1a0703000886825000c0c081200030000c00000002d08104a40615003156008a000050302181c03182014604100744507280341d6a0407644040048000e0001c42600b11030b145000507070759548041003101c091044000081d070100300403071040007400036544a60103036103624403004580394000390303091038101703007182c4030b041d26480340e000b0b0b13400001c80600f0107082d90f102e41050100e0710300c800310b500c0c00b00740a42e00700c0d81186e5444004101001c0310a5a00125192000c0d0310740c600f020400c041030401c80e00c010341c0c0e024180c0010200c4c1100f201a02c070084843c42c00c80546400c5981031000a080c80c4030a03c09001142c01e00011044900e0709540c60000c8841d6981d003603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970226384 1250 970225134 970225159
    0x10e010c080c03060103090f2a05062b0e07080d03050f061e03010608010b090c07030215093d06080606040f14090d02150115051b120c1b 60
    0x40d002da90004283c1e904054440c111040000c80001035240601d104040104078000185540440e95070707002a01c81101c4000b010800c440d84580046480c061100b0024206100c05a944401840d8640c03c18440403882c0902c031010720391004c618a010b0b610704900307464000410880440688409954000455948101180d140e00d01198000341c007400ca4038468060050010009086902c0c1350f012a1075079440b02c00c1c1014900d421a001507100700741200309402c010158800950300c200900c4c4040301840300e4004122409000c1100680d82701031020f0500000e41c0c5c6450701c020700000001040d20781030042501d0405250359000f9030042d07130051720060400390703600000c00000e001801002c0e000c05681e0404946240050800c0d50301c145820002013500c0d220100c1c000345054148441203082c141c100d8018410711080039990036817000b1034076106881d002c4101440200e161010b0304210584507010408074204190300c050081c036440354090340c0b0050520f18580326188115508140c0c841101e0008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970227634 1250 970226384 970226401
    0x706140f1c0603080c010b19330513120f031b1403030708060d0308011406220303020f0f03030a090f020d14060a0b0108060111120f0705010e010c08 65
    0x151040340840c0584400080500350940100c03442a0000c0c1c0f13038844c0008030200c41c3c40090141d40c1d00701e5030642c3c0565901084900300d024400c000d00904481241c5082000815011540d50307000d9000d9045428140c0d040001002d001d0303601c9020b8107045111081c10014044c01040890801180c01c01030ba6003070100680e40441700c0c00b00342c03c80b002c490941a50000c0100300780480e048440b00d1000c0c000c40d56820200005000030740018201c51160b2802d9a101002a82c050705113411600d0101e81c010441181c0000a0304a0050740300205c0c060000c101010030410300043c1c03020469000342c00f5200c54410b244452a1609818084038540354010008a01c09083c140e0140c0d8055000d100c1c10300341c15045900182541c14421070a035444018110310240d688818440f035a0003085608041003041408000039040c410014000740c14800380d4001854500c505200c2e482c1074082070103180396075111a1100c0c201681103544141c80d1980303001081001e0b1001403198600c0f2113541d0312030b00030f00d6451000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970228884 1250 970227634 970227637
    0xb040b090702150a1b09050405010e0c0d020c0c181f080304050d08070b0f07030506190509090c03010e0706021209030601030f0c12140105102301020114010e090706140f 74
    0xe0102e80da580d404006a05070b14010745c00300455040d81d10140d40703916100c10001600c20682001c5101c8032600248620b10078024100c0c2d400314284500562640e4210091a0815884443c3d80307411401241c450b0b42c01c116803200781c1c0d00c80c0c2d0303181c94680031101034202c44004000343c5000b5400e480d8002c200502c014900340700054203c5204072036243ca0b1005994a80aa170041620715050840302c51091200c0f084c1c1600440b584200241c50001c042201d44101c1d1900d20300920407103000300308132404100120407d00c1800003600c3c000d030003880046284149142e55010b188038160050054002c2091080100c404595113100000d0041c0080d034250b8482c58a02649800c04940581c6003500000fa41c0c0c21514116003568060184190f071440c02c2d1f07100078251600241080160400c100080c8620301c80007040914800d00d0056002d02030b80031070f0050340106030090301c92040e500c01000000d1566030038008a40701d14000e000750b520f0b2a68600003510030b03503032021029a82070300501038100791300c0d075000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970230134 1250 970228884 970228891
    0x910210b0702460c2102030a020103180507170c3a0b0903072001020a0b0c0f0f1306090305031603030615021b2202030402010c14010b040b09070215 65
    0x154003080300200e1141c00301200140c80c004840013210302c18100700c0c0d40c401110b08900081004c600a615654a50019886081d0030034002c1c185a920901200134405180b0440782d62540b0000b150b66485d20380805518007901d00407035040314821100704000e030b81011101c814072500508003a0110300c10b008020b01c9884d000d0000e02071002c0107419484086000e02c0c034903d010b04040c10244d5601c400305c2c1041517207101109100e40038200440d009a405036400151403964540050652010b62244580c280c2988210714200508102c0400e00c2c00c641952000200b01d00080c01003100c183c195200c90590340c02c40c061001a0843e00f0912094040c584901d210008c9503102e1b140005140b81c403074000c0d9660702d0801b9418401a40000407440201000740700f41c170758802080b03584058040307509040241595180c0b01c422201340d008030101d4216402100e2101030560701c80b182c0e00c1824401c0704560300030514a0310691041c1d04201d4060818101504440d0103101164050b120461000e8890f01d80f104014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970231384 1250 970230134 970230223
    0x1c0e0d052118031201060f03091a09030906130509090a0203070324090f0209150f012102030c0c06010e0c07030503090a0507090e0f010e0c0910210b0702 67
    0x10b00d003940444030284014a003c1461140015075541040d0000f0311100207080040103052401313000b000032401503070340321148502e022103280199542c2030070709082d802504000c680000d008035005880040840da064107440055406074075680e00d081c116a6130302c08000001c0d4040e0012481400851034a420103130505200a107121000a05214018200d41c8061002d80e003424407200c180045182640b440c903000b03405000c1c1d2200c080394141c0040c02059120030400d042c40603101801006184000d0705502e2003803603440c00c5440303240c00c0301c810810f54400d5002e8125809200e0010a80201005000e80a1000742440504082083d502030720280d00240c20740300c0d00e00c51204500b001800400090015180d861b00c0840c10380036852034141303001103168140000c0e034140301079130201003000200c0319403200086480309500e460701240413000c94001c1e0840c00c51b115191000a129240c125a00312a1314800c4c0d0086020345d54100040341c480c1c21104115400d0080d01804000c6072280e00040c81440b80070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970232634 1250 970231384 970231411
    0x409031e051603031d0d08010611070803040602030a090b120f060d060603061d0f0604060c1215060f0e0d060b010306080f070e09030328021c0e0d0521 66
    0xc24416200b641036002c0100c0009841e08071000c0040c840021110f01030030420000d0484c201d82d207502408850f814020034040103c2c0f00c107402d4140d80c1c1081504000c4c2072980a99075115142e800c000c1d165400310000d10041000050002680c1c5408000c807400042c4207075036100781d62654026100e12480240c00981d014011403402c002149061085100840c41032030000342000303240c0d104071080d4808485070401504548084080000046242907015612140000d00d100d0024401d032040c28446101c80460361901d118074032070b44000303071a11040d100c01e034941d50f00700c02c020300d0708841d40c3d03402c0c03c443c2d504000c2e40141c080c002541600005000a414103011600944460045141c000035140352805070b4000c0c3c0d820402d04142c1e03000341d81c0000415002d10304d940b803c0b040100c62864001500e09202006030210001401e5940c142c0c1c00e40002c0081c90b00580d000b0a50745805050b81c00c1c0082c9030303130203540640c103000c60141d000c551030300945880b803120704807050740c4800104000814800403002e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970233884 1250 970232634 970232647
    0x70e0c070506070f1112031308070b010b0702011805060712030e0316020f010908031204020409020901061215120201260405150702060c04140102070f06031a0409031e05 74
    0x140503051180749144c1e03409a00803080c502c014176281c502d4514502c10b4200807080c4070f89603008021207a01100e044180070100b5040c6ca05400b861103078807000381514072040008034284034503034001e10146000b40c0c0c03400c140e40034921030800e1221191091640c405010441400043c0c10054800d8818030030381000543d204583d03c540741168440810a4101c04c040c0b203040c42145020000111400c0082c0f03003840101e42000d4003280d9030321816208091b031080302000541190307920f80284a0140d40a01844569691014040c0000d40c0c4600001c0405080542c24640340d00e086a41008a5222178144541c030034207074005407140100c003225401501030b80c3c3c00b07140c1c0c94070600b0b0126020f51f20030801071084011041c00c9801c203150280c9110115013064050100d10340c032180594065401100080811410010050f45007140c55803214003200c0701400001001609030384801c0c4482403801811880c050000100320442d80303402c4000300840c0124600d402c51203003244451001408034144a440c082 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970235134 1250 970233884 970233893
    0xf0c030c0f0602070e01060203042d03060902010305132f040504030504050907030207110f040b131b0507152403050d091202092e030f050d020708070e0c07 68
    0x10080d402030251141c0c50700c0200810ba03410020310000380f5400c5c506805a50510388000e407a446284100710440002800c1c01000e40d00c0d50305008598504000031140155884c40d0000240650b84400c2c0e011074604030000e10a00303900d1601c1c640c2607a11890901c8008200a203e40501500d000f101620006496560420751520310130940141e00a403141c2c1d480380e00c1c00b000c0281d50750000340940c0400d80184803810000364a0307034491120718411030301400201c0c0045c001c01e004010850300385603c0b182c1c4184007035044043da440713050300d003000e00c492200e1400029000d541500c5a0100206080e502c3d41091a014055520503c3c6504032040e4114400d0b02d010081c03991004c0f141c20039102504501c0d4880e00302508080114010081a6203901c003210300398001507a00a801001002d40650707454a20302940246041030100c804002e500a44694990804950300c19903ca01100c8520502074501240c600008510003181c420100400d2036078101703002c0c0350032103c1c003815002d00d1440500c122030026 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970236384 1250 970235134 970235153
    0x5220911210c300f0d05040e0a020a03020f0a031b02010c170403030e120d0f090210141605070f0509040203071505040f06050c0105060a05030d08130b070f020d0206130f0c03 76
    0x3500c000010004c3d040401d0150b800c040b1951285004d000e001c100070000f00714035800c1c099000048803001030700e915107007005402134820b24011019441c80061102e65884d059440540e5a41038079402926621003207c043e4200c2d4400e2a610001c54040700108910891a40700d0550281c40303403502080101e0364601c19490103096900f1280500008034618010a1a6101e800305400741120103001c85c036481d03004501018101d0007524100141100060350074807500c0c04079508003500240c8810040d00506100742c03220550b01402100c0340242d09e0004441c900a038100d405142c008015240c2103150007010a049868000180700384402840000760704885458400c0040c00700782c448650362070080310940e00315040101301d50711410951000740b0160300c4c0025440424a50742c10079412548400401d1070950701080002400b0114440400001d07650010143c454042160211007585022903800c0ea10368100f194001c9042441d460a039001c03841141640309040d00805124405580f40c0d21000b810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970237634 1250 970236384 970236469
    0x2040e06070f02060f0403030914070f08120304021507111003020702030f0d1d01020a202d210601170c010c050705220911210c 56
    0xa60008010007807129001190404840240d1014065501c1c000182180071034000d0720207010076507100e18482c100700001701001d1b404507040c81180c4200d5601c03200c1440800c01401003d019010703040c0703d410b5a40c211400e0324051075004140c11104488140d04030382c0d50300a41030603580d83e00d001e21001c1685c0c0700c001d13201d140d900960384c0240c0d48011a005042c50034005454043ea95400724482c080515400314004801b05400c2109581ea083d29500403440e1034401000a4056511a11580103030380002d550740b540140d06070740001d02007a000b501c00354407100c4a5100101640450f007051281d00c0c188130034550420301e0081d1a000904034040302ca281c280709030071a6000685c00014000700190801030040114030034a042000c06e41c85554a40e2510031602c2020300455060f440802d48691b56509845295120441000f000113103007052088800d100b02c0d12070181421183c40000c44242e440503071705860700d260040080003108000d1044500403016843c4081f4243c0318541c10204040200761007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970238884 1250 970237634 970237661
    0x40c05041a09210a020f0114030108070305070f240c1a0601080a020a1b1a0c0a081b12060105090a06050304020f0a120807020301020706020406210b0d020d0602070204 73
    0x4994019009111208100588501c800c4007420f42e105410703900010b852201aa0680d6440820309290700141d51409502c0d14121244801000108001c04001aa04201c074080d8003102c0030340356078907119138401d0114040c0218451010ba403d5070724007900c05a02c40c0b01005440d041c01c07040c155407105681080c0b001c4512160480301030a04c1015039124001680141c101c410840c80c020040b040070b40902070300c01c00c11645090030001c82c00ad010501c3d02e010180c258440301000240b8107407070203c0c410343c0110101404114010003144520404007000d0510703d43c1e0b4054286040c908440700080d8503001000d050401074200400c04003a00c0340e03820700c4000c1c000c42e141c10b41c803806c0c580b04120340c2602074420b25000d041c40d07c03010000001140c01461099070020f81c2944d030f40110340042800f91242c9100a0070481c000500011915030018071000c102d1080700c251101028140008402d8a010100340b5078002e05050307410b005031520399883c0420728030444005140840c0f9902240a41c8d400c840e200c0e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970240134 1250 970238884 970238887
    0x303021b0c010c0f0c03080a112503081b0106180f09112115060108060d0b0c210a15090c12090203032208011103090705040c05041a 58
    0x140d1400844518100080050000d0141d40d0980d9000809408050802500500801d003030203081c0420400101d02858018016994038914888054046041c10344001c000c4d11519454601181c641d042c4580900240030300c012101d40307962208c038146d801078620798028211140d921032002000740314210080c2440034134150352079050f40d005011900305102c00c100140c18144408000382109040c00900740c01116441c0c01ca0100d10f030032582c1349003030880d100f13005c7c45421204264000b150000760310800007660745444940c0c1c0d100a11881d90784c4200002c06140c00034000c2014490008042e00d0301417100c0103022020038070802040e030020820395007945c55a0b66081c8070004001020480c2000d0584c59000f403050043c1458010420601c0010500d40b0540e9080b4000c1150b90600456103021480c0c0012819810501c80710480f000140c41100907540c0380806440d006048102a2807203001171801030009103184c4802d03c800340c060a9804410041d0070040498070000940a00c0c6003c40041ea416 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970241384 1250 970240134 970240147
    0x123304020a03141006020106080703020a0302010503041b0906030c12030c0b06131a091b1c0204030f051b0118140d080415020d090b0d0b0a05040e03030a050f01051503150d030302 78
    0x47e084581c50f81090fa0b01f0f401500c014005611141d0000c07089a9080ca4003994130307940c504204c0840c038162070154510030708030f600000d190106034200d5030669024000c00c4ad40743da5101200d5540501c0c43d04000c4c0440c0c2d0722103010b00882d8178405507560040e405418044602c00c603042c3d00341128600d171401c64032107140c1c3c2c00384c0100b814146a42d641c0114618044031101e4030f0703a404001c0c5402a44140c40c0f8a4a4000c2d8000c0101c00c00e406030b400450784084e00311203040e002d03e483c54a44041038000100c6200d42240700781c403584203c20240720b000043c610424010309240307503402c2d116640c1218070382004070000131100040606004100405d011100708184e030170507408c02070510b03075001d10100402c01c880c84148020010701040380ca03424800d00c00000c030341c001000880daa41e80e055000c03c0d03226140c1044480f62400100007144155201c501c200305a036500d11a034624450280100e9401c581c2d075600d58503131003c4810042d0f0300040d66100c001001d1402c200001d07100c004080d02100080d0f00031400e03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970242634 1250 970241384 970241387
    0xc030c20030d0207080d0203120f0c0702060f0304021003020f120408070f12021615030527010b0f03030703020d080c12010b040914060102030a0309080f123304020a03141006 76
    0x50080c1c86c541c8055440e0030380307562102041400240000e40c0d40000b81c0007184690301c00000311790b020356026145580f6081c3c0000c00024070307001200c0076070040e1545044680c08511038402c03114640321200c480f60034100024150b2254600080044410500801000b00422480055001c42d64420300d10400b10f0025003000074100103003144103603590109030809228109450b80040c40c840c501d0f1800207100e503200c12607440740bc2c4401c1201c11215446080485103810f06402c09400d084007500e1202c10000c44e0380506560b80700e00c0c0d10180042e081075241185c0d01d4821007686400c421400c500c2c5043c082c2000c00c1c1c254181081e4455038030313214001420003082016004180102c9250007002283c2e01e08040043d40341e110f280c00c00c20030580d85012990070400b140c3c0995003100c861681c119281c08a0411030b030039052007611002c003600c1d140340c40b00d03065403117034034209440c42c00000201201840303140034400030f508110300c45c0d4141916009070850003850200924480c07041e441c402140c141c50b1020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970243884 1250 970242634 970242643
    0x1107111302030403080622060b0c07060c17071415220309050907030608011404050c0324100302180a05100b09060703020f0a0c03120c030c20030d020708 67
    0x40c0542040c0180100b00110b42c00110195100d40309880e080500080c10b80c1500303440d05e8103c2e407803888a15041003ca04810001e0150903840703544400c60303000d00e449540c00c1c2c60a89034a2401040181c00b500e002c99007103800340103401c65903c00d9042078441e907c894401400c000503120f28120030344407002044060a05149a010000010340b109054000c071510300070400b00c01c60160a01608031403001c01e401500c40c1d07200000403c3c0c0700f0000c1058000401c008801c200003903c058070030b071013600d059400758a80800c48411038085103042d00c00c90460003010a5020743c00400b0205090550540000540c9865503000a5002302e8140c0e190149498001082181c2018040c003030500d092071014850f200c01201241c44500c82210200d4903452649812031400c500036208080c18003c2c0d94160040120036400401501d205108052040c3c403100000c5802104072100a000030b510307041c030341c030228001400f8046000c0500c0f245030322001c0082c000c85e10b08440321445400592001e4400c0109200a02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970245134 1250 970243884 970243909
    0xa05060c0a0c050111191b080a051002131202060d020c06100b16320a060c0302120c07060906060b042603030720070b0c0c0907140c01110711 62
    0x1700112207800c0c24101d56030b14404200e0200e100307983d0440d05006d2150300003882d264120280001050140c0710042c250b15884803510803100c52145c4a24500302d04e5a500a45010140d1501c00c54501e6143c940c0424a051028000380d0304008200301c00c0340070309014001440540200c0c0300406c00750a140d0790380f01c6854202d900c1004291014005951001441d5000800240d004a100e0000d1703c0c10000642c4104460078803802020702c600c3d40000094804100f00c08618040c52041000c401186c2d8280c059205030244500b1940d4018000b45d20802c0003000703040002c0c0142e1000030207401c0c1d51b0b60760088980c81d41222244e006c01060030800c090170100b104000e007510005130700401410399a280c0e90b034040600f05405002040200080d408805030030a00c440f4050f1089a070402da40d101040860390010102210a00030b000d1307040081d084c0b640d5a5406600300c0d80d0b908102600e014803410385500109009072403952102103601c813408254024000190040d06610304030004001040300840141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970246384 1250 970245134 970245137
    0xe0601020703020a090c170a0e1b0108040b0405030c0f01060f06030608150405031309020702040e0c180c0909040615062d030b03031201051c08070602090a05060c0a0c0501 75
    0x55030900058036240d00140466020500c00714481216250076159140c9070403940f1252001f1800b040100b0003560040003aa02c0c80100382e422000e141401000c01c002c6000c00c02e400324025102080004281202a5034094041c5090341e0400c004116000e0070040c06e891042030585d1501014440032000591040040540d428100812482c180c40540c5401c11040400c08002ca40000141132010074022501e4011500041010305500e5004d0600290448a400e82c0290314160100c14001c1c0c0c00138029150b400028592540d00f91462200c1108010003050000c403d801449062660f80b11b107820725000740d22403080855000441e01001044020310391001d010000740c0034040000741c0581c12040150a00352054003002d4454850680141036000c107200d80600c03001501c103a160008294460681c0c0d0200e9050910091810200816903020a030160150608110b11000201158001c00c0c00003005011400c450380c0e10b100245841c0c0294404c03400b82c0d0840c805190410090000810181209 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970247634 1250 970246384 970246393
    0x3050d1107030f1116090906060302030a0510060b040810050405010f091a1521070509010b07061a3006010f06030c0201050c0a03020d110f0c060901140403180305060109060e060102 79
    0x31745c410040100c00d01c602003c19540d03010782c1d001d100d201c2e000170300a950040c0c03c40c0c41c9040d40e4076190f070b42c070304d8501c28054590303180120110b000c0c4000e13000ca804440b11600103088058409024400500340640126403642da612843d100725146401000c1c1201d000e100c014480d007051260303502061b00c004000d5002e106c518180120782e66240388815118041210984c8915040020900e02d08044c0381c10940d440f941c4400005610f1560a0084c000188500c10034442c1c4202d00007038024228031941c1082d1721070590741318445c6800000546818108910103ca04a89003070325500c0d02304402030f003280c1c4550354806428400150503001d205800806880200302c1807501c89844415170240e41c1c5480c04041c0c00007804602201e213500b003107030012061040b06070b0324802e001d1020843c0c0d0007006800881d010710b000040c40d4020600c1512806071020524400503502d40c0c2c1c046506400302055803259801059001c008a00c04104050103484032086c0021414100a1555003910000b041c01b41107520 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970248884 1250 970247634 970247653
    0x60f121703100b0307031e05090c030d0e060c0307080c151302010e0607051e010f0b0303030f0402090403020304080a050a020117070210150b130e010f03050a03050d1107030f11 77
    0x300402c0e007000c440c035490070a5282d4458003c214042c0298031038608608584080c82c940c103c046078000c82c02480c58500301d80c291807001042c95148c2c8a240b81c44000304d4001ca2111000381003540041411501800a43c0d10700032695403040a82d4000b5100b6035601c0d40f00c50107001c0381703005a03102640c000004140440c0800c100b540000c0240411828541c000c5502107007260800500f00700000c0c04090703800003401c8882d0043c2d03001303000b000302c2da08103070b51281082c89500b40760a000c01182e0040203100031611b221b598503002d00c52504400381c0101c1c2148030401c800103002d6402e102501189101d54003400001c1c1160000608420796260803400400b904000d02020035000261603101180c829004184e002c2c040b08203d204904603131200d9120800043e00d49001000e481d100300c00d698408000d00240e90325113060160028842c00300420540c00f5240303140100b8003500180030300004ca004081043ca04840324108903802010045011400403039804810fa0340008150040952440c000c103174551 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970250134 1250 970248884 970248901
    0x8090303040b040813030f051f0e060123030706110d030506090601080405120c01091709150f280207050111071707031b180c08040204020a03060f121703 67
    0x90054030041071182d00217281200500c5418500e4011900b086298006580c0c6003842900d88076405004200e1000040c0503004034410381c8a50260701d1210402041a41e0a008111414120038000034250003212200804195401c20000c80a4007903075840b420759084041110b0f00e040c01e1a603c00d010305040074204080c94440c001c0700e551243c1c00b440c00b441141c0302d07030400f20f04001581010b44181c0c180012641c0c10ac6c101504000d2116100300b1f0220f03e210940000e045250041001305a03001283d014003041024000010b030108500000c034280c9003d090412942a5130100a003600315070b0420390940383c0d1190140300c05001044c0a00b85010414580105141c444005001e0f402c0c03104c1100000020749442004042d002d142c2c04501a644002c500c8125500300c020f62003503030504500d014081c06494004d0294142001583d207450440f502d40d60308020183d001304481d042059a500c00003c0c1801098020400620400c0d001c003401d00c0b03450070508400c14180340b1800c11101c040040c815840c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970251384 1250 970250134 970250153
    0x1704020a030c0810060501050418021606050c12010807030203060c210406061d0705041e0803070302070f0b070b16030e1f18080d180501022205040e061807080105160809030304 77
    0x116203200050750344332801190040d207205a0405080d8070701c0d0004000461560000500050b1181e284100107681d954509c1c030340c1c8804a000007034040c3c00c044040b40780300c10400050f0003000c204183c0700c4c41d541c00302070203400c817503104560941d6540e03100c1100f0001007942c0e46031441080d1141e40640c0c040d20b000704002e403292103a031207243c0f00300d20a01010440300e80d0f0341080d10042e04e04041603075580c4110b410000e5035140180a041c41040303051000007901020041100c3e0350641c8070304210400d50b54025640081d152502c4007000781900d500052040d10010300c5601c036510301e80050204698134112560044071030f0004a6080586456050004949080103441480d4220400030502038007075000100c3c0e1004400c002000b66001003010306c2c8207164003000021001400d030722000011790314000c0100b56440c2c0c400388422038003c00045400085600d01c0728001000303803022900e03010390b0342c1e11803030850b4030884411500f042001002c004003035024482503040107094005500703508007516180c101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970252634 1250 970251384 970251419
    0xe0a03080a0c05011401090b09011d061c0f0507060f0c02060c1e0d02120306010f030c0e030f01020c01110a050d0b0d0b0c0a0f0f1704020a030c08100605010504 70
    0x18080301280404446100d040000c9060358014005d114402d500152400701010030300454922504103c07101c911410304050f0039041704c40050b201c401c801c5845070b28036840b0340050034098000451980c4229000d07103011079800d24602c141c100d00c0c90902d00341803041c00c29015400210401c80c041c4016400c2552080200307400b5501207400e10b80e240880b103015441c0101d42c1001a001c00b125040e0810f00f030f10041203040700c03a9203a0b02a80c0d0380742c02e1104c64415612044030b485000c15013400d00c55000d20703c0703540500c00628103402d000254140d5040001d107010a02402c450083e0340008401d00c8201081c01010910004100d503e810001c27840360140842c0501e10381c1e0032071f0340d070f84905034102651541c40d1100c1040e004100c5140d1fa08000500208542c0b2142c290300209000103440c0041a1050f04c0701d5801c400380382d40705c458609000c2c084003000345c0051300a0360b015000d0180803010a181c143c4a000501921006000c0503a0681c4c5c2c0b203003550030542c00181400818030080010920440c541c100d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970253884 1250 970252634 970252643
    0x130801110d02250c090e0712120c05120a11030301030507150207180c02160b031504090b0717070c050c01030e011b020d0909020c070b030c0729070e0a03 67
    0x31901c80b080810103c0000012040d07641c0000001c140b02031000c52003039041924070204092111700b03801c1845130740c3e98403284600b003400c50303020880c4000300360100c6128046203040d182c90f10240007562219880c00c44000040b440c0008001640a4416040041c0e013180b4240880554159071541d102c0507140c0c10a0322403001c96400003668610a240700388615406840e80c0031a403108007901749000320080005890401c0948100e280028038400003501210031102a41840f5287d6555503c02e1041c241401115503003290320742000300d0014806a114a1149980da40c80000326846944cc0c2807100700050312007000d0050240b910f4010807004200c400000d0710a0802141240c01c012509004140d5260b520641d0715101e868540350070340c0802c0003641c000496a505043e191100854022441032181c400581d0303014003000c100a5401030051544074840c0044a0f0418209440b4034580003810382c0103801000c0d00303182c0d10304404606640c0941021203441d090200400c00c0000c02c02e010100c0c007010f0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970255134 1250 970253884 970253887
    0x50a080c070f0801020304060509032701050f03010e061f08040f0f0206030a06050901170705150f04030c06030c0306140f04150e040c06020102160f0206130b130801110d02 75
    0x140306508200007801000c0e210340d0290220307a1605007500035002900c044070410304090104041040c000b0944855500c490069012403440c82e819455240f00d200c0d0f4181030001c00d01010010b4490301c0041c1d40200b40c800c44600080c5050340820000154030303600420ba50301440c015000840e4403007039855105030300200d00d00c00c009590070001c849280701d07203000354410000810461140c00d00e41080c0200c420581d891440e42c0d0300c4060340b0040311200e42a490040d40111000c0004d8901a00c0c000c00710807a10108600d0864041c0e400b068a9200d90419201141072680400006615200b8950044614602004034030309220112144d5025480000c6c810140b506400201d5038480d803107a80c00040c0d07503210400b076659465100c0150b00c01107809562100410f90002552401070003202c0b611040c16030484455000b03680c0d0310040640c1c3c0e4030180e8020b94244030707012540c0680c10b044e0018208118859480781e462a4000345030902c01e4010b080c7d10303410004a5502070509400341d41c001110b002025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970256384 1250 970255134 970255147
    0x712050c1213050c1002030d150506070b090c04051e190c030b0306061021020d050408070209100f12020105091905100203250219090516020a050a08 65
    0x10221801031079500062034070a0030600141c05480b812161485101c2c0050f143c80e15462030420007100c030344c2c00e01003002d40c004000104460076150300202e1007580350000340e4009a152000700381d00e40c0150100716003008000301444804c0d41d04000300000d5100031a02401180b8020840e40e0f03c0c00d80d0700705495403000170200400e07284d0780610100045100507440401070f6010280d4010007416411041c031340240100004a079082c24503a000c502c400c0f495480714400c2045002c2002c00c0036201c801c40041c2c1a6090110182204050240c02d000d54040c42032240c9502c0c80340104080d413031000d0817102c010620340e20100003c030b5407219000c0454000b04103032040c5410a0006807800c0c072500f46050f900076101c542541e50304018124032020b60310265a81c815034101480166038078402d000d000700442101142c06084055168000740b02c440c8060290300c000301980400c4494601039812101e4419101c4040108480031821a041d12203024401443d6040d5070342c440300d49490010380041c1c030144000448 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970257634 1250 970256384 970256401
    0x5060d020f06120c0a140705062a0703051c1b12060b03250f0c0f080409020d09030e062529040203070e010305100c3005070503071205 59
    0x2914010040c142000c2e0302807500201d20783da40d9014900160114240840d408413092030001529801940000189a5038880182001184644107140ac0c1d40506840311000440c2420010b0305e0018480d4660035120000c20604078842490301c003d03c2501d501d000700142144814000240040c10642400d52040a40300c4901000c0e0503da0000701610390004140038900b1400c0c2040310151210444062902011490461302145140410000110b038210b00340d001c90703000e07140307a68002d2003014140d01e440d680e10003041c10b0780c001d0981040700c150340f0032840342030640011004140e1401101d81610307210840c1000e880c1401120f60b81c400640c0c090301040c00b0402c1088035109030101c0c0c4030901821500a1b0000c100201040b2012030090007182e034000b075014400c00002d8103a075803150183c001780f2412940000181110f0205200b0007880c88080502e0405210389038429040d10b602084000c591008424241c40010380350100f000f4040041051140d40100b20484941c050310000c03445440e8042c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970258884 1250 970257634 970257637
    0xa0f050d0608061b0c15250309050601060f14130801020304200d02010e040506130629130302061803010f050609090622050106030b09010e1005060d020f06 68
    0x30180c18162030814045075088000800380d00c1148a01308100e24041c6040388602d07280500c83c4a00342c00e5100c0f007020040710000301ea0541d4008680f40701043c4060344440d4503280400e0300165440441d80e00c0b580c01c01400802c1c040305000d4002800c210102a100f0303000200206001940c1802e540004692106069508040c0000600c2440002c0d9103074280b90030007074050b554a42c10200780c0001408020540e0030301c242e60801c00ca030161240010040ea0905000c0540001810300d94840c040b134403960900455486904054490480080b4454680c09002e0303828942c02540900f040c40d0a225241a01c29441c80300404d0305d41c161000c58031440c0d00b030b6105d4841d09100c62000d5065081200700c08010705a0b6001c14800c190450700c2d00e126850345180315459242c2665650007501202240b1144003924280204800b4456000054031541c1c9444d00410188241d80b040010b03515074229900c4c0c920308010141880511180070005400d08400240141803000c40003802114006541c04d500d584920 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970260134 1250 970258884 970258897
    0xc03100b0d0f0309170d09090b041e0606030c1806050f04080607080a11071112100218040b030d0807080403031811010311090901091505030f01051e09030a0f05 70
    0x500410702ca2266160140003080d0301d014003000e00c5081041303a05c18510001300700d6111840350b12000d101d942002903141c0034005400c0d095400c0303601d826141c1540702010a155018400d560340000d400c604000008003500c1000745810301f048800ca509020744001076044c0402c0f55102d043c0359a0f10b0064a17040c1005001e96070042c08607000341d0007081a10340c0c00c00122031150510303510030411901010140440d90140080c0581565242106905c43d804c26980c104004018401280c0401e520181d030482a81c2c02102248003155003a40d51105606190148850b03c400440142000003264680209a240003c0520082002850200f82450300035403100d0000c1c8454070001d44140043d00341415103640e1a500ea0340020f00d0a448000700311a441d0640303100c03140041094440e42d103081580805880b05041050034207120810014561780e040080380120070481c800420149070001401c0006400903d9110f00e40b1921003c1004101009c02100e03016040e078144001c48803202d03281100c040c0940e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970261384 1250 970260134 970260143
    0x20711120a050706030c0f090b030a05040309080f010204171c0c1110020610080105091e15010f15030b13020a0c050f0a05010e1623090420030c03100b0d 67
    0x300000c0744250381900006c11082c06a142c03c00002c010b101c044034845424800e82851032020700119040ba055074000ea50018000e20f041c89401d500c0e440f4650a01000c10310307180d090b039070000d010000c0c06001284250300b4181040501700346180c1400d01c024102c03484c0c00c03940c03c000c41d80500c4020842c21007502079410708060300120441c0e02c1c109019540341000d50704a01c108418990002e411481401001d01c40c030078401c09130100409050503548810300b4501c2c090003500980680da0004d00340c446101e8000e009440c12171a1036450f0a0000403461444038410301018140440c2c50156221021020803103000d48400503030fa0f14011200302c9010384400401072040c040e01d0301d5058201c0000400c44940350041c00200036070300140b06002d58903c0c46001d5205c044600c18410040303048858541900848146080380342010070f280002d00c0000b08881c00c40e05c61524280b0030044141d55400c18180460640060072110028800a40d543c01d40152100b489501d13002001040d407a034110003031126a20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970262634 1250 970261384 970261393
    0x10c02090403031113060201151a0a02250315060509070e0301090210030e07080c0a15050f070602070b060f0f06030c070203030706090b0c03040305030a27030918020711120a05 77
    0x2240c85d981650450344074400042d0700b41050340c10386401c81001c0c1c0b412a84032812100c0780070480b01c8052807039048082c4080a5000f951000741030782c3d80d000340a5048100c0400d1900a8134154608011800c01c4c540c007502c41c0620b4490f0a1100d03480f0103a105810035000e003495a440c644106c00603015128140b1700940104041c60700910351034054101c100310f6500803054811050300e80e4841e5036034140c008803180e0300021054042201c40c4079040010031050f86031421501c1c104042c00d500e0942d60140404a0b0f60b00d5000400500b480b85403000c094003c5002c135072442c1c41044100c00500c1030f1883c42c0185100c1e030800000b25061016050403035070b0040d1302034141d944403429030030709100400400600340c401582903000501d10000b940c007200e101d42d41c1a202d082c1551160340b1b40c40014a00200712400c0e0040d045242000f020082d1460301045102ea564010342500b444252035001e20100041b08040d0300611078200011003070b081d1b08244440a84d45405100c0401454614240354038202a00f41e005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970263884 1250 970262634 970262647
    0x1230a03090605060f030601051203042714060919020415030e070803120c0310030b0a05041104020901022e0608030301030507150912020f0907020c0a090b010c020904030311 76
    0x101030300104081409080704000940e203134030034801c40c014200b0720705a260b084100140b24500d01038554a80e000901c4084a040c6038031030b40102d581160750118201031a204c0c110284c556080ca0080c0100504240025000b07401c18101196a1030741c06442c039032040120301806c010710656a416180240308ad0544140040284d8201900074031680203208118084c007400410088000411aa0310f04035400242169035914039004800e81c1001d440b11519009462000001c0380c907502c5401d0040e540b442c00091b1030305092521150b803e40000200d4010b80c0140f0107040c25030b070081551081500c0703440031034085c1100084c158200d00d244c8504419440d01c0c1c900c1c0415000c8000020718184c034400c008840d00d0684441a01602d20b54440300f04000078030100d810300640d100f0803900101203202038071044c1201e03910000140c40c4401102d140005074001c550341e001c02c2c58082d00724801003807100010010308004e40c000a102c41d0f140c0c00080d00951045000c40c040510030f507c01041c20500707645041c0c0702d65 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970265134 1250 970263884 970263887
    0x6210f0516080114090d1d060d05090c19050d0303020405040203040507030c0b1c0e1524060304050604080a0c17030a05010519061d040509061806011401230a 69
    0xa0700a003840c0390b20f4200704c0100510112041d50041d100c0200070007401022040850301d81d09040005038181900d0000c031109500c40e03001a08914607a14008140d0746402c440c07403403030801c885040703520034080b07103c0600301400801052070540350203841c21542c840083c1010307006403185500080c0c10a10000821090000228104060340c3c481d40c074090140381d444c450714249024158482030042030b2180c207504826819800300c440c5000ca101070f255107024001d540c8408034000c40300c1d17010518110100142044050380c5100c610b60048405604508041d103403a89c0e6050020001403051b00005014050f007030040c4010b0000690040c6e01e880d1991080900d600503070015900118081d0820002007040c1c07400480140300c0600c2c07642e84079a16841c28000b1624410021103090629000c1c04042010ba152805094800d40041000300072070304002402e031030031100702e601000392a08070760018001c001c8440381c1c096103c03600340b030401c4031103ca80f901075400e20030a60b50094000d00000e410220301c1e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970266384 1250 970265134 970265173
    0x907080a20070203010e030a05030114120a0b061c170c0a02090109060e06060405010f12290a090c0507030f26071e020d08100506070b090d0306210f05 66
    0x30f10a40080c0480c0000c46001e80d60380c01410400808214284014019000d41d100601050314006180c0c0a0700b0324035411041c02d005a400082d038002c0012000c021175030429202407040c01c03401d0340350300e80780c90295100c8540e9040d650302d6249203040c001640c111503c0c4100f080e482101d8009000625035603458541c3c4000384035900c07940d010201202d00041c03e0b4500001564111101a1100800295204001c450071019a810403860954548407803485019140c4041c0091f41244044146080c0a108000700400c565024007449400e040000c00603075400307400d585489505007801301e2890003040007510f040d102250641c24002040380035050b20314031900118011100350300d40b10444442c1401d0006504010b50f03503240903074440180191001d1282c41e10580c00074004000c0421140c4540029426a008a4040e5042e2640000384003640030107001c024644001420100441454281c0031801d003590600b440f0f65547c035881c1c002c4103204012104080b0298402d050f5a10312017100080c5141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970267634 1250 970266384 970266397
    0x10060803070302070f05090a0e070b0d140903070c180b031006141801060e120709270b0c0f0d061e06050f04050d141903030e0c0907080a20 61
    0x144034582c400a494061400401e003038071b1010300100c500ba900c02103060044d024070b0b4000f090910621000003a0b446414000d8104010300302c40100344886d442c081401280d0020744070481c540c000300120310005940114507002c90714603141043c01c0180d68000840100303400b01070780d43c060080080548803503585034840b00903145c0d5200d0109105840c01c0a100354040c640c002c20301c01c00c0d0101c00500685015421080b038070705004049422117115580540d0074155154000c41d01c84d9160b0b003101c0f1000400c1c040d003480700c445103c4007445260664840f052121400f40c0295010072000a01d2a0b0064070b103c2201d414511002c82030020a503a00a03444059142036441820402120808204a80b09100301c0e4003043c041203246052a040c141004299012080b04031800341c21480d000704081c0003400740000c0144090220b50302c03003080c0d00340034068032444095035401ea000905030300ca00e603407062100c0340c00080d103181440440d50b5052220000300584181304d08054540301d5a080841e0419004001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970268884 1250 970267634 970267637
    0x3005041a071101110a150608060c13030809130207050604060b01050a0203031b071410060605040501050a031e02040f140105160803191b03110301120311100608030703 73
    0x84400c0d0800840001c0c010301c440201001c2d0480340c1810715611440840c1d250311410410345100a0700c540c0d07000d4030018015910407540340c480d102005030a00900c800740c8c1c401c0814a40500d014040030710340345d2131407240c00000e140c5880422040c00b55110611143c503c1011000f0456840740340c0e08190b03030b80f40000c4400301c400c581000700391303030341544541d09861030000300e90010360640d04c8100c800500003c00816182e0452820700808020403000c1018503034060181e8060700a0030000c00b0814140e980f40d8020100b8000104000c001c1c0381d03406401c9540c1d0b0601441c002a981c1d1a40000702601c42003100400c2d50302d0b0001c1004900410302441050840c1e0040031242400d0a50100542d441e0044524900440000c2001c081c0410030040007154403044c14414150b41c04655955241110903050a110002c0300303440c40c5050294041c816009000c1550614605640c0350201c411461101a680102040011a05203d11a10402141e0011901e50740248901ca44600903c1c3d620b0b007090b40103a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970270134 1250 970268884 970268909
    0x910030209090c042306070203010c110f0a020a0902031302060a09061b0b040308090a0b0708041a1515070b011508011e06030c02100c0504050a170a300504 68
    0x60b2148000f6080318201c50b0180c42d4011544030725282d4001d0014200b0034030750086020800540146d03030a03c194803c5031001c0e140c0b64109060649000d2070b01481803110581a807200112201503aa0b43c056103040715018400036a4030b0340d0300c8140030011081c03c070000350010800b00b000824150854045404d0350320541da81d24186a44c08040010088043d50242441c0d0b00807011802091003400030561094442e421980e085100d0b950710850f4840481d52000001e1440041c00104580f0a002540c21000c04006002d1410820b05899000724108130301886114041d08880c105d259590681d0070b104d4108555034120b40c0d42e0300c101d0b21418214050f880000d100e00d03001140c00d002c03210304404060404a4a411020308100d019001003038071000d2041584102d0040c0c2050510714002c81e01c070100785950f036540325803400c0c0c103012a03000310f41c001103244c841d41c9a038198920310001d0131441072351308044910f803115040640c3c5c683d80c11228110850380c13141600840065600400140f0844420000c4034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970271384 1250 970270134 970270141
    0x3060c110c0a05190b04091e02270f06070b0a1d070b07020a0806040f03020c12150c1207030606170915040c080709050933040305091003020909 63
    0x5640760804058181c1d881080c00300e040c002820b00c903070f50380c0140c1d20000386455100d80300d5505644c150450b51000f803040b5114005100340d020765503501d4040d070030916025401d000c5c03c0050721450000741c100340b50300161410f12034005a031b50551503209280b4058149130340ca200d503041c10301c48000c00f114080760141c1842254401d10b03501403e4031140d4080303103020704005410700c1e00401041e0300403a0300380c0e444128140d0205a061b824054103015070312034208000310540b140790290500e001008110b04c00ca10880c007020412402090105902194847d40d0390250307100c8203a4400c6004840441030741d0003604042091030f580541c00b07201524030940b100104101c030700145846c510f03411142c1f0701307954000c2c0c0030030385240c21112400c07030f0028801e080c2d042000c2d032601d482c0b9240040d558000c10980d519601440300c0041d050040a24200301c194410724901c0d900031111504824401c5141a090460700c0011b00b414400c5041d00e680e41c4e4000e06c3c1217518905100f008019400c21008903210f00c2186010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970272634 1250 970271384 970271417
    0xd09050c090f010305030a0f0e041416050f041802070602070c0f0b07081b0c0402190e10020703021309020d030503040203160501080601030c05071e0b09012003071803060c 75
    0x242c41c103d81d40b00f4010b5140040c92141160004044020318050021205003000c10765502d00030504030001d8035082124900d8290180c10703d2030701c2800d4420034040d040041080c1c000c1200c00715401c1d40c070b00c03c41c2d00e040098058031520080c8100314000c0d103258030100d10302081180b440d90020884042141001180d61150080d007290320840c032000340f805408001e1030680400440c4900c13041c80710001956400124030005c1426079202e40702c5210302c0c81d82103000c2c80e122508040e003c200c0010507650132161960740c5002030340d03454217408040d11032805c11040030540702c0b490300102d468503400b8150b4507410b8064a4064500c0c0c1081d241223219005258440c0c800042400042007142c005030350f1601203886500041d0020599030800c1002c01900b048540080b031110b5030307440c070407a410407500504900c440c00c100c0201840903005034810790424008190306402e4900803c040340921442c6640c036241d6040903500c010b5445c044640f42c9100346000018001d0740d46c840e0900034120340f0f0b00b41c000d400070901e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970273884 1250 970272634 970272661
    0x8010608070c110f030706030606020f190f1b0306050105090a1505011b050f0303090706020a0510020f04080d030e1e10051e0a0c0e06121b0d09050c09 66
    0x428030700054010312080041510040e0320540d1600c094402c010710324154001c00c2c100401a084000480d440f21020400b00703038100500380c9080351107000b500f00b070540c1b111051030b00d84020802800c100000440401448200a0344003440d201381c88601d048140d4928202c0c014007024821141310754080800174550300b105000302002d82d079501ca035840455003040019a469007802103000074011020050384006841000b180704460301e8400155144e20304540100d240c280c007604402d0440d00a0050340c2d000034400105103421548200300035845000b1605515120700aa9005106500c40c0c034200c4030103542c060340704e42c065003207000683d501300e403030529850729440d114214200c20703901c000c207082030361a002e0b400700703400c0b003084040b03130740040313980d40000b4483c000544080c0d016540d40d007010500541c11204001580e801900ca850806101a1140b0f90310759005040e81c00062101060301421000c500803145e2080e0096400c001e00341190902da55150841000d0078050700c003c801003504100d50305c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970275134 1250 970273884 970273891
    0x100c0314030603101d07120b1303021009030201020f0316090902090d0b06040f11211b0c0a0803180c030114160c0506011211010f140c070302090a0501030308010608 72
    0x10010000000b13014401001050080605180554148490300c200c00d424840c00000702240e00000701c00da0b110782001604040c0242070414040714030070221002030340115180d0144590500c00003007a051b84e0805030302900c10a418200c42950005c2005240c7d079a610511050f080150365250040e500c2e40344450480c46082200c650020303414170048006542c000015500400181021401c1c8500700058002d403000312410403c401c1d40443c000810000c50403030270007806421383c0c0d503410030705200140c080c0000104a403a4030514001494a20f400420800145107660010040b90b42c2c0c60031380d2125500c42070141080c5500c1c01a03410781d80c1c0750f25050051b0550700c046400c810700b554441c0010508080c05410080040c0046000000042001485100e000f4402185d24003544920751500b418615002c1c400340341440481500f160507554840802484c80544240c5079540c0c0c4014200d01d4603044260340000c2d4048002e2041141c1d00c9080c0d000641224800d0b2910420381e40c0712481500c40700d00c100e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970276384 1250 970275134 970275139
    0x1e0608061e13020d02040b0c0f1903050f12190b0114030604021b150f160801170f0111120702060123213301091109100c03140306 57
    0x48074015400e2a05005681020b241d0250051401c0d5a101c0a0000d0784c0140e031090000c0c443c0496075681c82581808600743c200100740c06000c00300054000203044c40c0c85040702030100140071070490f441a462000700c0d1060388080030000398924081281c031000b1030074130840c0d00d4562704109144c0074a50084a02c400365130400c03142103003035650311403e2100a42084ca005024008142e24403402c51909110b0310385807042c40c92142c0060312b02060848904000540030700316424603d5424826590320140c0c8505546000440d460f103542030090003032500700c040303558281d25407070440b401d485850424000c22034030310301c9030341030009598582e010ba0b2640030034031410310001004503404500b2204804080c0c01d5600003000702542106880c22400c40c840300c2c2e0101c0825600400100c15000601644c08199044400804655100100c1003013a0b052040c03040c90500c80c0c0360344003641d031390300d0300015a6440c00c400742891101d003100c0800100034440c900821741c081042e8004020b550b80c0d00104a07845288007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970277634 1250 970276384 970276429
    0x1b0d03080105090a0912030207020103060f050f01360806010e1014040f0c030506030f01060b0906090a03020d1505010e0c07110a0504060b0d050a09020a0512071e060806 74
    0x30038041c002d0600d002070016199917030356100c1300b000815032000501d02240c580d80c010b07224603451001604603142c9801c030614103030491404008580d5104134459000c002841c00100d02d03141c441c13040e88000008244140b00040400c1c10f070384a8078102d2044d0080b200c010044501c1c41c0d0b650f1004c4201010305032401c0701403c1288006200700601c008204081030000b82c000100031281c0c01000e021900415201e900280c4c940050041c10f1904104030900d0949010007041100c3c501011302c0480e00ca0b03000c0300c0d802420046581226076581180000085170040c10300091f03c500ba14003104c03030f4a01505c0072440b1a240600100300180c1c030400142c490243c01a10034a040b0064460b90038100020740380980c0311005140100d802d49403401054000c01c4010299515860210040c2050b540b000f084002060300c0d1910070009a40c0e2154140e04440c81942d00800490104510070704002c6a40c000a1075603c404144c900c04250809003c030444034940e95860a43d00e0310300c00c11050b0140d20400c407844592 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970278884 1250 970277634 970277639
    0xe0c0d1205071a1006030b040506091518010909031b0302120711130c03060b2809030b0412260103060b0a08010e030a02120f0f1e07051b0d030801 64
    0x6940100074490260389442c0280010f1202140d806030101d0764940e0185210710100b00994150196400380e000c2141c050000e464401d0100d01c3e000401441482041c14442d52a042a150031302d40581d0320703010385c48103240c0d585c6900d0048080c010001040700002c65021010014a81003c0c0c56400c0541c036501400c0050001444030049400099085d07030541c401c0324400d56a03a0311810342104619102c01c0100c0c056020b804054115070a641c444900298100b1017503410009135041100c4484180403500c3d040e80070080c08882540c0180c01c000c011082c1402030206111011058100c05421179036544000400b035440e0907032040401c2e03143d0803000b4050005000184803a000010300403400341016600681e02c103081425200d5075103016200740c1001035005002941405880c040041400d4140d10b00b10561a5101c241d1140c51810702420101048040303009154403411f1808410682c41240c0790612402c16a40740c800103407199200b04d50460a0700c0766410518081014250991a41d00c0280e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970280134 1250 970278884 970278887
    0xa080403020618041a0112060e0117211305010309050a030f1112070b0c040f090e07050a0b030f220308180106031a06042a09030606090e0c0d12 63
    0x1c00075150780403050303110480080c09440e14495464142401c10201c5490500c517400540102e280d89140050b00381801c0040c072100d80100241d60440c0d05220188001d1003071035564500300441602c401812401c8a00b91481d40c10703061002d00042c0442490300084107035100e0045d41101e2412074018540c0c0c1105042c01c0200303000d020924206075881c1810030381d0100240f07806040415146040752079040120383e00d001d0001000c203807035100020305a02860141402080c1c078803410b00c0d209004d101c80d00c9901d540f10001c018000c0324001e00f006802d1200f229201c04600b5003a4204441030044101c2102c001000781d00304081200001c110000110020340c01500c00b02d402d4240100480101d0100d980ca0150105003445408009c6016500003030520380d840140414080003d010b9074821402c0118000003245030a03502d00205007603c910081e404002d0300d00343c075800d10315400030702518505200041d601c442504082e950903c00404d07180e481150000304480ba00c805900a440718594082d000d0324607 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 970281384 1250 970280134 970280137
    0x1270e012c0d09120f0c081b031605060706020409020a0f032d020a020102091002070f0602030403030206010e13020d0503030a14010b0909070c12021c032906090a03061d0a0804030206 80
    0x4600545174080d001d007980e200c04400340100e9010480c1c90b07020910300112030804400c000e60100f021800f418440919003205ea100c8580d60180c4c5125940c0000c15404021031396040718001c1011500a544900c0110000f81c60703603106500d6a00400d080880d0030031200c460b420550a00706c08400c0141c01c12480d200520300a40045111105641d8200071800e12030b0b40f001c0e002d04840d0759039801801000c0c1450302000c42411141d02c80c9040d507100f800148002500402e803141910a031021643d090f80d2601c0a041c000f003010400a900f0204000c00c01080c0000840218032451000106005c21540c1c1c0008a20b1107030244940d90060301d050100345024503080b2096030b00013902e0b00c2c01040e6982c0b9610360740004040380b800000980e00144c000c404001c0c6103034090001c4441d0703003010004000299140c5040b840c84403004c60f903462030341001c40b41941d190b501760f50700c142c4098803c04400d40c503490584001c5c030002d101082c3c602d8102c04480007901c00041d12316103840e440845035091500d15824441c030b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 970282634 1250 970281384 970281419
    0x80103080a0918060906081b0607030e0603041208060d030512060303120a0f0612030f0e061e0414030f030403152a03050f01270e012c0d09 61
    0x410040d02d10000701c1070040404901d01a140000018101d03107402d801c101103c441d03034010f41703050304403506d201d0302c101c00ca40c0c81e80f20150041c3c84040ea2680d49103003c55082c003441c030195901c00004400d000c2400881e00f0701c40701102a030740700c00d002601c4034002c118500e444894006e0004000b00140d035140700d944442180c12441c00b6003140d0408644884071980180100c2e004044690748000d211f640d01c615018400040510242400b412249618002d241da40004595000c2c40080a840380c0780d1b4540c401210030042d00b20146403401e0070300501030f060711750081c4202d0100300f4100c03018040b68078001c00d80300a600c01490003189094a1581d40b0306808040307804030080542e58846680d10b001e6070800e803140420790b007820185282416031002d801c580000c3c1c5078450100310036005009070300e406021004001044d800ba601040d41000303c210151071001c080b1400d55007486d080004c0d0000d4074503440441015582403c07154103080c4240e40d580d11001c0d44810029480c0c810404c0041c03002083c5602 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 970283884 1250 970282634 970282637
    0x4050c040902180d050a0506061c0b0402150a1709070e042402070804061205010e01061d03150906011203020303150102030c121b0a0506011403160e0a0606020d080103080a 75
    0x1071074002d0008400c04c0b1561410b441c2900705128010030820240102076004c401140e2120032140e80307031101121203c512000a1083c1741643c0860290342e551189000c0c0007042036181503444036880002400b10300392840041d0a1211000420b6050300c1c003107603460039222a6480c28075542e0752a00c410a5040c0c0340c0700c541c1d009508030310203000103c00b10300003072180901843c452645c5926020700101400f0005002110301441d0000600000aa41c182c540c111495854a140c6098108076442042213100d014641d0510560116840481c0c030040580d10901220b020f90308075a90b40d041010f8644a65000100140c0007000000c20062909091006004040c412a03081444117103405140c10241c02001c1400e050206130f11065405083d07a8103100b51307026001d0702c100c203034039554150780c3c84040c092036119642040600c001a00c0412003249400009040a80003d41e01c02c1144103501058071600841c0d0301f003400100300c00f03000041c68004d80c8810741d5811800e030700c0d40c0c035406070581015450783c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 970285134 1250 970283884 970283917
    0x1909150302070c030c090219020d1d281d0c07020d0c031a01090b0406050114030c130303080703050c04360c02030c070e060a060e0312070308090c04050c040902 70
    0x210b0300c2a0700c5c0c0005802d4850005070b130b40607038003c0b145100082c0c400301d008551000141044844e0f1020401200341408024001403295540c00118200001c001040386000402c04002c103070841141d110086540030003110701900402500c6d8000a101101c0022800b030041000800500303050420070a1940112080000d140e203076581c10704a9400c3d0300d41c0410074820600140000c0310580700700200400112410071000b0b03e4140080d081d10121016034448140120000d0340100048084446022019444c1803044c2d07100d240142585600741c8500c00003a180c000094040624a000c5a06940103200074150820a403840400d0301c100e00019041040c0c68211701e00080e98441c0610b4200c44d006401440d110503106006c9890280f49901c01400d0320841001c1c010b003903d403058000b0955200d0700e0500c85103800ca9011901e800c429a81d142240080004c81c082410382c4100c08074000d4030004155002c410130001004281c81c426643d01014260401c0200720180b420390013400c0340840200141c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 970286384 1250 970285134 970285139
    0x5090f060a030b040b0f090c0a0e130f15200904020c1e0708120a0509090a0905100c1215050f01020a140703120f0507120e1003021909150302070c 64
    0x88500041500c045490074049410306c140c0c44406e1080503401171649004005242c00e91b4009265410f40e446640e103640412030120703c0040301400d048c50b48940059088400412624101c41c04040344ea000c0029540381c401802703508424000301942005d815500c0506103030000003044029807010030201407500c1540540b00d046202a07400b80c0b8030407042c0300549405031801d610641010f898103c12484001c0421441124980010540300703002d02c10740d0030364000c1d59031607941c070004c210384000070f46903100e080e40c400e00503c6030b9000300d84518141c0e5036843c1b50a540c400101b003a2194403010051000340d40301c05110358204031000d50600e041c144110b07017000e4529207030341d1410100c40242580642001034107005000805d0460030b0318450501d41080701010195000304240030b03c81d4000c018030810340e0319582062003203a0111164130014240e90040a0421010700254048a419120800241d8582034403074040d507031010403900101500040711409210480083d4400700d8115990368168402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 970287634 1250 970286384 970286393
    0x905040309180f060b03162a0311010608031c0905120f090a0308040503120406080718080d02011a0409050705061308070305030310211506150e0907030605090f060a03 73
    0x1040000d007600070102e50340c4c0c07c2c803031011800d030008885131900b8081c41c855403500b080d00f0006081e0716140310049001010720503190403a11003000c1155251198200070740400d0f40c0c08084000d00c114640c03040c00e0030101417003007254810340b080c000c0003a000b80c00c1004010b04035200080204070b074409170800a4a0440168005011340d4410740003603568400104060166080030040e0f564000b001c00e0a850a252419000420f242001020001040800081c2d690a0415011068058041e031015200310603616400240201007052210303080d000d900f04d200503207085c076110f000240c1d42c0040140c405582898240282640705100d140e5405480f0311000410010901c0b2810207107108801840e40d9081a0f20300040620031600b110240b040b2407250030059407982c8540460303041c4d0044058030f080e6040b40748000145040d9010010401c0c002c41708903011980503140800f0307101e0450f003042450b01c400000318200d9006000703007038010300c00c2ea0206407040d441000040d40030078014912a101516a980c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 970288884 1250 970287634 970287641
    0x14120a17041a09030c121b04021204030c020f01050a320a0c151a130603020405100f080c010203040b0f04080a060204050f0108060319050f0d08010f0905040309180f 72
    0x6400b048041c020940061600d4144000811504102d6100101c0d100c00d24120382c03100784800b039681002d050300e40e0014080d111038042e15070103064540c00100e01d15180c1030141c40091041c100b00c2c400e680402c0d000080e58002c0c0705a403101d01242ea150301e469051010000d03d60042c40840d40d00c0302e03010602d45031415481c8001444000203c0d80e0310703080164180742100f1090350b910080010b80b410001107202c1c04a590041e880d5042040751039408246441c48880000c141d07540010750800d044c10108200b40440c2e61800d07040b41c0c801d901c0616a00d550b004425200e0001011080c0183c001f00010080c407105d01c000fa003c050f888009040c5025501da481c6807400181c02c204840340c0d6008a42040213141881036000c410f070342824540141d107003050019440307400107854144d06003503961004051001c20400c0c2c000011050041b5043c401041c04047d1840100744540152106101000304032079001340901c0e03025135819100e403414107040c04100604248802800c0309500e55070340905120b07000c0d500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 970290134 1250 970288884 970288919
    0x40c110604061521020603060d020405180d030204030b0f04230a0210030b030c0111030d09050a061b020312150303031501030506030313030f050304180614120a1704 72
    0x1200003e80451800421440f01c0041d8054241c202d0311034110002400b00c01c01340b0998a134101c0e940d5030369a80300c0001401d140044140a13410a01d408108017900b0980d10764094041c0340d10301110348017507841404030161f200d82d0000030b051000b00c4002c5410360002440e201e400601c950320314000320a09032904a00035015140c00211a409800d540d000c0d41410312441c4c4815015203414400510707582c0100c1e65405106000c103040104000c0c3c10128541c0c144190343d012000040b0611602004d400c011359941c40d1942e064600074680500315141001030200362102c2c804076000b4600300180c0e810340500f0300340d0041200d00c200c60a0806016103a40a20082d40306180e0300c419104214040700c0010101c80000f04064000d1f442008030000350008191810100ca521025007460121249041ca0a50003a0750220416010003012099210f41c990000001e40c1e071b4164401d01e032900c24500304001410010203e95243d00104d50010208012a481003100080398694034a0142d071641a0300d041d54088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 970291384 1250 970290134 970290143
    0x601050910180b0424090801020a05070b0a1b05090d0c0b0a120528060504060314060903160206030604061e0e0114150717030408042c06040c110604 65
    0x2002611111950300c0b45000d0300d044400242400d041002032640e203000b00348260225198031070200011031103506440042c1c007481c8029900c402070681c024046070440c2e1412100000e5000c002001c54105106281441500c413034240f400d04890a000e9400ea44064407480c1c106901000c010040707420980424001d001c1c4030340290352a008480d005209010302408a00614100700900c0142c0014800008001c6280319600000000780b02e000c60040c4021340c441074101c1c0c02d04c0740000900545207540d03207515034140e0554081c2e03a250302c41d0f192640724000c0c502405281210750403001d803c1c00c2001c0c5501ca07402610005441d07451703044c1490042c41c0b00d4914203d00e500d0790818003060644681007030040c40301c0108042281c00b02400140d803070303910f541000c900702c030045000d05c00e00c4071066452050480590048c1d07564203160510002c1c5900c24040c0c45070300503216612070b0b00c0d8484505034400214400410040075101c01007080080c000011501007000310803525495030f107005102e03076030040d0b100c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 970292634 1250 970291384 970291397
    0x50c0712060b0a05030d0e0409050d03050412090e042901090e0f0c0d030c03051c0903030e0312041b0801110301030c05100906051c14040308101a030601050910 70
    0x32450301c10180c402c1d1900d0365001e80b14403c0c0420054500240c401c0c0c00240030300b401c082e03142012010600400107400050098802c44440d80201c91301076011074060382c0203134104400311030404801c1d100300e031262041d11003201a200011300403840d19002610303013003024880040807055800e8004030201082c5c100d0000320350b4403a02501407203000c000348003a120700304002e0301c03580721804005151800b00010207410f1114010881c810184a502160301c1c4105074066050603001c0040010010302228000f00c0c00b0038035202078041c05003c0041580d82509104004401556440e940c01030340030b2000c01c48107a07101d02224007094069085c0680a0302010620b4596103961450a0004000019a0040340115a140900360f80580d0000b0388009a4046041c12a96144ac811054101881d2840d0b00e10700da03032409468941c03000c640b508440c0100c0c0642c0c0c0c3d160007900c412610342c80901551141004007030100070310800112130a400740d613000405062140c104100b4001107941e81e4451003004002238003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 970293884 1250 970292634 970292669
    0x210f040308120f0604270807050703050d0201110c0604120e0d0305030402090a1404080a090509010e0a0b1e040f0605090c030103051c27031b14180402010f050c07 71
    0x10080d90781d940c40030301190144405079401000010740801100d10540c0c003001c01c04041b050211641c12a500e043c2e1010450380f80c3c0707a80f03040c900d03201c03008a1f0132240103508245030500860008000c1d1000c0c600000058441a182c641d01d0301240c060b20714025060003000031100c2083d544030141a01301ca0300a03100d4999a00e0b00744104500315100419621b001440d20083c801001c3d03903560410f80c020761003440155182c5407541c0940b40d4599643c8080d5008401c00c001041c2c100e1400171322406100b5980c000d2000e541014100540c1895845007005001c108001010142c0b50607044a922241d0151002540c55261804964a0f102c00c89090790305c2413000004100708041005181303901030140340c500311280c0a000b802080044140300704d5500014035941504400c0325090136400965010a0601401c040c900300b014860710a4444e03c028101c0c1c0007403440c102d081101191001d40820a109003042c1da44d035005548604202441d0020040d05110000c0b01d0341042020b20003608060350403828045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 970295134 1250 970293884 970293901
    0x3010b0a1803030207030b091f1a09060105340501150e0c09060a1b1101140c0304032414040b011d060105091c0b0414210f04030812 58
    0x280807519044010400c20301007020a5010602200f80c03980b220f0f0180903a10b94262440c60b000115018a0482500700c04016101401e07911290703141c104488090f210074141820003802090442d10940400c4080050000c8003441c500c0300c0000403400045028580c4481c0300704501030000c81400c44e00d80e036503038006440a080301189000208144064503040d46413200807072480d401207002c080d001e03080105515441d54050000c81800c80b10384401c4001c41415804e0940c0001c00010305180800d25030100180c1c4511460100c130a04c50707944000b9841c2525564680e55000d01c24141e00c2d500c4880c0412201900c6024001e2001351511030071142000d00f81810b000140c1a01070b400342c2d410f00e16010442860b400343c42c2405074440000d003002030b2540441000b0588000d04000c1460020013024400310800c1150f55500b40114081c940c41c1c85140500705185036200e009009040c4240b481c1d56001c0300300c41c3e10800500b1400246000541000d03500c1e034651103039401204a84c00b10280807000c110070340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 970296384 1250 970295134 970295147
    0xd0f050f1e0907031209210c050109050306061e030607020f0d1d12070504021c050606090901121a010303020f010f11040b0304060b1f0210091e0311010203010b0a 71
    0x340401c11141000b00c2c0d0380e42e41d40400c0c80001c0a8120140200d150180079000c440020a4140358020ba500e201c1800d00c1c40450038500708403102400c91901060300c0d445031070340200b070f20704c041cbc020445901d0312410440802101d2004400107c1080d00b00c20458800b0f01080e80200603a40040100052618000d0b0900150351044810401004041079144054845100e50091300751030450700c41400e0101542000c03c01e80005130801d000241c0b105800000c400254a003d12619081080e41c0b00c8804106580c4a00c1010388c2e0301845480040c000707075000000d41041144030303d407002d0f1030781d10182c1e06481c060401d900035409600880501e0521003804e0151a080c1c1d0041d400c104600e100420695005010b503019072001d01001200040070800a94803001011070010221003102d0200c10641c040b042c801d00d5040014040c0580301c0c4056882400303820036203603104846841d140700008599242031040a019010820118190001e02100b807005501a04950f00b401d561011005000b9011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 970297634 1250 970296384 970296421
    0x503160506010806150108070e09070c02090f010303140a02010b19080d1404180b12031909080604060b0414160f05030c0f0a050d020301062003070f06020d0f050f 71
    0x903500241c0c20031200c010300ea1700035500340100f4203103007600f44c079001d108555102d08403845540112002c4180a0102d8001d0b40e20000644200c0f1800c049944049030000200028800180840c0b0b150311960f05025141e0b019140b00c03070390781c40002880f95410001942814942ca800244424110014004050140860030128000e4140a08001e5140c0f1254032684142d10403000b04006c224010211070715150031410505030010074005140031904101601c0354441d0304903002c242144ae44a15165010f2801c22086861f000041c01c05a40c8a8513200060001c0300307110b03580302da03a1b403d00c03c0c8411142c8a13003902591040c00c1c0b41050098104018182181e00301090051250901c104010035a881003103812017000101480e880303511200c0d00b40c2c2c05010f00d201c113519244c0003100102d28039901001c4503805194007540410f41540d00c00360380d6207030302c00e00401070321200034030210030082034844e0001e00c42d0410070720b030000d49031318200f80440032503030203030350300c2c991601d0140030301c040803041e440407490 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 970298884 1250 970297634 970297649
    0x303030601020c0f0102070e16020d02061303030902180f0f0c0702091302010203040b0d0209010318110d020a080a0501091208130f05030403080f0a0921021903050316050601 76
    0x51400d11800103559001d000f05040c0c40b900300a00104100d034030070700482000b084400340400140c10000c200107000020042c8000040c440c2410303e520703541c40050b42502911205503030b00034545161f10101c002c0c1044c2081642c21450b401c1d402e245042c440841a40710700d11060f030021450070f012604901c0b2140181c010050700c6000d00c642c0000d80e6440c1300da40d81180c4a000c640b0803403a16403005030b045000d240d010402266010800b0380c2c03462516001080000c800344da0070403642d01d83d030070365000c000020308001c0c00d241c030548007c00c0541051803101e1b0700580020100194150790724a12881d01951400c02c9802e0394694000d40200000361208040441540c204004149840344903450541c0c00d4200180007814840c21502c1070110a100b25805941c20541c442c0d5149820401d8582c00d91240740400001600e50740002002409100c4042a803100321a6440400703036181c0030048403a1701846035180008882c41c0000000d40c040004243c10b161030002d8014000842c101142020300c141c5c071506 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 970300134 1250 970298884 970298887
    0x30a0314011809060605030f07090605030616030e0a061b02011a100c06020c0307120e0103060f0b0a111c08220f0f050d09151e2a0605010e060303 64
    0x1125a44006002810009030360b8001683c982a0030080c010744000d5008030340600921608101c480f40100d482001e1b11181881801865520000d05036540c800322108500799a50383c1001202d58441c0d006104614807100c101c54140600c0e490350011141881c150b002016180c1030704520303881d0203000d02201440765501980d218410300b00494220a25041040300300142d01040a04014041e4140d071800f14103401240e440b95441e24016044880e0240f2100214101c5020760b05158070038000e42054912403072124810310b2070a40d06e4411501304001d40414041d401c00140c0c4c015204004910070b00311030820043c00c0080480b00a0945013000d0910b01065200901031100011880e103180c0a040e841841320300750a05c01d08213080c02401c085030003407040c019400e61105581d44610004140d68540703a900c580c0a500003001e803100c20101050010000b4541a1524401c0c0118492240c02100354030030344000b040444506c54005010070f045488940c0d030703401442002e0b596505a40d10010035002107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 970301384 1250 970300134 970300139
    0x1003030f0e03150a05070e0d0213052a1201170715020703050102030c190c03170705120a0c02011b0917070f0e04060c05040b0d24030b0603012022050a0305030a031401 73
    0x502580a4248500032b09616070300803a4152020445040c1e107116a120120710030000c001c4a000e580d444403200b11002d510000c00420304000344403851805070b501c40300034005a451712000b03812000b13042864400303600408200201144d0203000542c851503640207529507442c09140000348c05c6080050800030800c5080c4004000b030f42164170700041440070071041c50181e031014411105c3d403089589008800b140d02d414880c1c100042e400042d4141c80315002030114088a84042682031480a8044c000540411042002100041080920074024001d551401e40c4800c0c0c8400f0f10000c42e44103102051800e8200428803115110f004c0c80702e1041c1c640a442d0a15082c010041030141190f103002c02a51100790380030300e42318202c2e003c040c11480e903c2c084c54542c4d02d080002c45840100c0c0c8950180d400e110501d0607001901030200640c0c050103c90a00340030303000980504681c16414402c031024520384010400e591a041c01c180290304c2080116603035004903a004040da0183d00d4200f070b4101010340107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 970302634 1250 970301384 970301389
    0x80609160605031504090311061f1403030c01050906011e060e1011010e0115090612030c0807200112060e0a0e0712060b091003030f0e03150a05070e0d02 67
    0x2948215807891030541c0d1203031103080c2c4400d5840c1c030b6803d10b039900a1414005204042e00840d1010000a242c1d05880e100e07626556410460000d09e1000d00014a00142c10302890040500314001100041c0131031742840e0149492508403001a6507100441d401840100085d03195104041429407810221030480d5150150240030702d011001c040d88111402081141e2481c45034200c60800c554000081c4542020410380c207008001c803815412400c540605c000c0b48418490107400100d030300080d000c1081d035025807000c950014450301704a550038820030005020480744205080807020485008003001e25160014001e404190070380c07248541081020400b0f00980c0d05807035406245003034041111080d00c880740c0c0c00c104481d0840c900d030018800b00c00080c0304281c0d001c8550f26400b920941c1c140d444800d07165281603541e12000300004c48008085601a1040010303003007000700070742111007082590700314010450044512180c0300d46e840007000115944030303918004100080d034070958814801d802 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 970303884 1250 970302634 970302673
    0xc020303070c050a170c0714060906090d0803010e0f06040c021e0703211814010c11041a040f09230309090405030a0e1503150a0b13080609 61
    0x6444180103110b00a2800c1c04014400d46640310f80c050b8021061410ba032180c28525044443e02006501c1000d40100d6034841061110101003c010071690600104404102d240d610601d230058107c542030f40745000160011000d18060310581c8940002e514200c1022081200014440741c0310741d040c07144a184850300828103034074a40d154450104020902d0705000c4c43e0400c294801044040700101d1450300c0d05003034a00b00040b14150b96400743c03195408110262880c014080d0f070011300c040c5100320046600401c010340c015413281ca82c021210346540d000804485081c035420301c18030008181d43e500740c40e05108552411704009410403440196840700783d8451100360700c0703202070443c1804840703109200f0401e490750340000030228170b4640b420b4541191290000d0220101203401043c900c106498101e103600c3c5020350510046080d40d64280c064481c0350400010b1a0304500f481001007260034440c00244a20642a103407041540e151030038485ca0400014440b00705c0380c00c00010710164448525 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 970305134 1250 970303884 970303891
    0xc0e0114032a0c0a0c0f0e0f061801080618012721090326070206090d02040609061706060d14010e060403030c18050604050409030c081303020a08010c020303 69
    0x540b411040b00b008691124204186001c02d82d241c101140000d442e250000d40d82403414420075100600c81d9652503610b03214489030048039100c0c0c4aa10001e4030740c0740300b8040c003a40801d009050300406558442030345031b141d000f81c0004d40d49801035010081c0400d0000990b40000d49000d008000d80e003502002041c107211005400e002480c88401c0001c24400c003400701c071030311440f980040c425001e02d00b400a04031240500c404c0710341d04950403414612101c01d00c0c03a5031801d01070b201c04a02d88002d560811a5690248042c994440c6404003076002680f50b500c0744030003408440a00003491030a111703400020000034443c20049500400420000340c80d400204e00b41194040680388405550b034021601520748040d00c09100c1c8280402c20040c158142c00c440154140e0740c031804000e42110500301c1106a0701e005064200008000811860405500400016000303240c03041020307070300d03543c0c1c210030760b114005203901910311700003d10651402d410400014490710008018000e1004406034a900009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 970306384 1250 970305134 970305151
    0x121202160608070518121e0d0e06070206120705030603070509150103050402060f07061506180501050c0c090a06080118031209020609040e06040605010501090f0e07051c0c0e011403 79
    0x410860300415105d00c00745c011882c02003a100301301d6404060f540d03881c0c07950381d60081600110071411019100205010a04081e0340d61101281204082448250ba00200c82241c01403030803c03680b00c1943c605008203005010540e01c00d942da050002c20103290402d25040948030391210340034440042090110b03228521403c0c03c0105650380e0f140000381040c0200c03190f5400000c00020001d040003404d5001c6041c15901c0901c154003941c032081c08445501980b05d00e0340c040ea00c000c1c0300313008035805000a80124480042181c6110040c40082a034000f416070780c1080c0e554440d8030038002c1e0407082c0900600f240b62921001840c0b0141c4e203004040c81241002c04120507a540041030654444204841c500c4201920903c60041c03c0b4100e640d81d40d40490f0240c801a25050001ca8550f20802d16070044039468480d850800b418624010b01c8502c0181003a01800400c00c45101c07407070498251a20a11020400003a0107044a600600710f440d8030801c01e410080175082c0c2c8038001243c04252904403c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 970307634 1250 970306384 970306387
    0x1e06061507050d02060a1d060615091e040f021207051804060e04060b060915160b070504080f0106060516051e010e011a030703020108101212021606080705 68
    0x49000440398821540c01a1050185590114560b41c0020b0740034004d1012250400c0412014040e0031215030020344026420742207140401c00300e00e070004140040c5842078410b14545046a0700007020b0313114180e0380f841004c0110240c0806803810b0b00c110441500403100943c6412000d00022811910040800b418002e000c15004400f522204500c070741100058800c1140a44072200b059410134100c0d401c444007810081da14100e41860301c1500e00586000e0304000c1804510000c07010560451150190f5070008800c800e00407901c2000002d0041030580c0b90782d6590b83c24200154184540041d08071040ea040c41800c0160651103012a022210005c1e055200b00c030300c915185040c840784214641c40700e2001041400c001c4c0041d0f102d81005001d6500801108009c100c1100c5c1355000d08100e59810f80024200304095400b03201c0c0198010400000440e42c0b039202d240b40110416540000d8802103170b0b02ea4880865034040001e054908550441d9401051800c0001098400000c10b4841080300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 970308884 1250 970307634 970307659
    0x5090607050f130b04140d0b070516060911090a09020a0303032a1e0905090a0e03120708010906051207031e0c0b0306042007290f04051e0606 62
    0xe5510643c0d00001d8050490b4600a6441c0030307092041e04640a500c0e1603001030b000003909468400c0151f41e03110b50244041d81c00b66207500381a80d154010f00c2c10501000d291411480000c2d406100d1001c14511410881026048100a0040540000b0000005c1e0380c58842c0328000759907090601c40c01c80368541390209101904490510030f42c02503007002d4160f0441c070300042d4541070b007004100501a910104200c00011001c1d07040711404018459250444c1266020607089141904003110003214002164680800505a038071140402c4801d40c0c0000c0a04005100c2c001c0b10740075400040000b00e9110040c0c5028694044d00c42603a44401091000754030b0400e01400c003003d40d403080d925001078815401039500c00c80346100e607100b1942c0c0e500c254034040c400c451044124500c84845d44011841d503082000782c0e034078a00f0f03010111800d11003c400680000a40c502c01c08c407584c1c811940d4842c10b05071810700d40760862410300301850003455482428009a440f0070006441503000c10100c0b940b100d10382 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 970310134 1250 970308884 970308907
    0x10f03080301210203011805101e020a35010501050a0509040b0a050d061d0102070c030321060b0a0e013207020d05070f05030109020d0b071806020a14010509060705 72
    0x3c8000039019400d01b01040703032200d500040c80030b4060203401900d80e642002801007040b910700064030068503000380c0c0050100d29103517002e4490000300d4100807441e410816042c03201e06401c8035240d07004c0c00e81c0400101c00340ca2000c903410b004003001c0c203005091503c5c210001d0918000c1c81041d07401240c1ea1803250740ca59075101c0340d0303400602c4054040e60303c1003d00c2c01e002c0003030050109030400c26041c40c01301086102c8144200c8031420381180c1001403140c107650b41100d101603005100892900c0c28421480190074600c2000020054181c60541c1c0c1c0b000c2b0100604040705440308030b4107001d000301150829040c3ca030304a48204200302d01040d004000126800541d00076a04042d42151060300310b9400c003c00083e01b1419540d9001201011554460806080e181010b070000d411140180c2a0b400290030600826042110340c02c00b8501c5600d02c82c0740c911012041c0d800070340140e01801e49001407001040c0e14180c40301d07200000340442d00c0d10f001e03078607541c190141c03100c0104800050f0725000388 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 970311384 1250 970310134 970310189
    0xe010f0b0705070f0b12090a0b0408130b0a0906020d08010501050f074106060105190333061706010f05072913030905040c090b0d02040608010f03080301 67
    0x700200c140d68005135407202070520154100441443c4502c0d84c210104001c0b003c00a601340b042d581c460010707185a45d940d9661081034000c2810903e40a017070380804100c4002c210060203502032640d55000e45145410f4000f46017521000701c490a118010005000c00d99101048a600480d00360406680d4035003403800c400b50744045a03201d04240e2100b00614a00003140c46004580b981e100482d15089041c030401c15200c042c150381c2c4ac2e02241c0f042003401080e41d40c401c40110700c070a150030006082c410414905561130041c450901004d14a424005585c40b9414081c0c4080c0c40c4034a0007200c25a59500c50a9040350040e020a0511001c034000d0207015104002f2035001c1d03988602c1d100000000603070a0110b1800b44215031040d80d06400001d40c60202410240343c40d650160340790101c01c0c0c81c1009000c0185810a0720074100003d00c0c2c0049807009c40742005200140d560f007001659070f8a00f007001403045106801c41407018840e001c04101080900003a603040d2080184600340c642c1da48010611380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 970312634 1250 970311384 970311389
    0x100f1503120912080c16062a0b070306060f09081f06052e050702010e0405090f0f06090705041415040b10020c090c2b02120f010801060e010f0b070507 66
    0x18841d0003c00e0007000302c0f207000342c001034011100700e610541a10060011031400c41c0205000160007084507194040d114010f00911518614085800b207016100c2c410700d60400c5402a012907122102000303007581c05440c1103d007102c2864218641820024441d80300c403407210044124040000024004407815401080100401001d0751000568561401c030a800d8032000b640d0350301c190b11107100303090f40210101c3d1901d47e8140d440c13030040d50300d040801000b080c000c0c05c00c0c8402d11403424010450340c020459114603040110080805140c050202c0346419416080300340520f041071540b0500c0e40010383c0d8030f81c00440c05158142480500000b0600418180030485c2d800380344100d02ca90440c4e0040b070000c45001007540e06558559402e601102c3c240700d418604955140700d80e101d07401c00e0010f140c04104c20f0040c4407000d454400394402c100060101660342100c85010600101329401f024400c40c1c004100c2209489199890800c05198000c80c0f80300d01c1540400008129040000600c03a1030701 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 970313884 1250 970312634 970312649
    0x3110d02070c0303020709090f0f0f061112060f03150a0e100606030b01030e0c04090302030c151603061404020d0e0d030b120712080c0a060905100f15031209 69
    0x490304558140b4080780051840190090700030b8502c00304403c08a0b002d24030710250001d010300d20490241d5286040e04403400410384803c10032514035800104079008101e40024490070007034071941c0c1070011109441010302081d100b240c0821b85240c0340d890100f82000e0004606011500c15564604c100c00506114064503c680c007030003104000ca10103d82c4a1001c1d68004c1d61304001d98406140190210b03200780020081681c8001a07108461038107402102e02030b40b203407050b00d042c0150a080ca92804051000944a02c1101020032007020700e6445400083d0314146424051586042090041d5090760008240901e800060749443c2c1c45d4140c00410458a81d041159514611030358000c000f07164040c11644101011003020a10700e90004d940c0d4103076141a2071541e000c0034540d1b1006140c0e8020070307182015004000c424404101c09100c3e041030b641c0101d028102e816140d6401d20304071408500103e11540c501041003100d080003c2c0c0c00720a49502c6020540211302480054641e04895400842c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 970315134 1250 970313884 970313887
    0x20a0c031506080d02070b220e06010212072018103f030c0515161b020906040e3a080c07080409330b0a03110d02 50
    0x308000c1a00c038102040c03000c01404012494540e4183c076162030110001c07500580c0404070501c0540d01c4c440091503900400308007040c030000d54144540c040300a540c405110488004100405560140405c035500141040450700d402c0c41943c0d0702c9014406e110030b50800503c021900d8455440340c03140c03d4950080006d9040c4140342021490030a418980248210208810b00e01e400c2036a513500c1e0340c840075460390244008200c0b0380980791104010018107508214144151001107101403000c2110107000b180800d1691400d40b11030014440c8807031041080040b012a46020300c56002011420390b82d049035280c3c51600c6000020b4080c020504681440d8081c0e0086a000b0544e1507041c2c10040303800c1000d1500910072001540d03880e17503800000c9400b16940c540080c140c540400000d0800c2c51090800f5070805031950404421280c444030706016902030020881000b08108058850803d5050300d40c8800d5420403000c656240513482d000310908d61100c01d5003000b424000d003940d864048280046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 970316384 1250 970315134 970315139
    0x6020d0212090d1e0c14030d1d070e0c09010521130302120c0c091b0a0e041b0f030b0a03060c02030423030303060d020103020903100608100501150807020a0c 69
    0x25a22524500d2100c00071840400622021481c0c3c2c040411070200700740c07a42099402c0365151b414090107041102c42d502d01003003011880c1220385204144951003041071940041e44002e09035460099207403c03058407041e040040209142411003101d1020b0782c00e00e000e40d140d000b10600301c000c58581200d44101ca028840400415000056205030014000d9003164100c13000d028440d074042c4141640400d5507001003403120090708260f41d001e034014081c2c0007000084018441d403039215400141d03042380007a1039060040340c507190a01a03684e0358200807211942075000140301501525916400b201403544a8409040d00ea842541d188002d54102d03000f805420707050302009480382d202d03010707900b0203a05100c004100e072610b500032140c8408020b80210300d5900c41000700a03803214111001c038101502007110401d60348081c01421800316141c000032442d01d04110350103003003c2e0003000b00340003a0328141c0104190508504062403c18035400e10030410f444082d002ca041079420a0094501d2100d50b400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 970317634 1250 970316384 970316401
    0x6032009210d030f050f0609040302030c0105040c140303090904170c030403080702090c04080d0e0607051506011d0d0b1003080a0e0108010e0c090111010e010906090c0e0402010c06020d0212 83
    0x140d002d09409940c041103051004800d810403100203840022070084400001003207030070520704044d0030a02a004403400d2020014a01e401c0d11303412101201e0001f03008104108409020f8000040454100c3c003850800c101e0002050583d400103001410ba0b00890009901e11281c1c102100e441c2c00920b03080e280e540b0b03142d080050850f031210b10704078000c959520016500e02141e00907107098a0a920142460101402d41291030b544460302c44c6e40d00c404200038050000c0e00400500900b508040c0300c84069160420024280a6a030040c2488a8004c0c541e844080e680b1400b50151a540c0526410b4081d201c0b984a100301c03c6490304001c2100500240141089400492500c4882002d80c1e8084030790380c8071803622088010a0380c6021140e070040c03003540c10135070042d85550303d80803a03840006095900b45540d01e09403803101905490341aa64040907003070161081000002c0c0201c10300c0403141c0d081c164002015405c480e40c014241e2540842c00d00d1030682ca60301141c50440c0039691111840c00c19490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 970318884 1250 970317634 970317643
    0x1d1605040b040e010e0a021c0b01140409050709080f0c06160c0308131a0301030f02180112170c0601060507060920040e0604021003020705070b0d02040e010603200921 73
    0x5c2e0600c942c43c0c003800605035500c01c1c000c0f144002c40707074410b81906201c6e0701d003e01c015015111031141804210507007540d0403190031010b0710081c01d000030b010640e424202005030003d82a43c22900d49604840c00907001d041002a90505001c030594005a540c4400b04000304038070348002c00100741600c020000418070403414042d154840c441600c10090641d00c0510081c2202c10801161600100380300410124003122000c08506001402055429103280100c10a04909800030101d07003140c4c00d080020712121441020b03003024100405446c200741e414685681d680140301711010844005003480802115402409445920454a043d02035002000c042010b1085048a005524102954900c08400070304a030003030380c001d0b0550040ba041c0c02030490195200c6003058480340300b072001c0050f1882001c00189040044010016152030600c0b00002903164181d020b08105810f020400c45603103003007080e01034000140b100c0c00f0740d07540308240810301c5130700e51000f01d5090b07001c00e01d0b1701c8400d0400460b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 970320134 1250 970318884 970318889
    0x360b1306020f0f060106050a030b0d030302041701020310150909021219020a14450111070504200a0f08070906140906070819091d1605040b040e01 64
    0xc00396096800041482c580d80c02040000316107681c4104010002c86000302c00400241549140c0070560000710808602941d041040480009600040420180704400721551040c05268000d502d035081a0705480d41844445c0200ca4058044803d80c1e000140540100310050451010a64641281000c1e90795940c404541003403c46464090401d05566035200b2a03020400c1e5807240400500c0001c14061150400c001c2c80c08500b61010700c1400100c803510108510032105080c115580304508030800340011100c0c8210b042c0034000341f41046a20000c512034003941d85c140e800040c040d580d151640349407135580035903000880b400a203c410a9600042500090031962208802a00d6040045403010034922a880000380c0703094882c00448400801031005810091040b81040010b442d420703000da01011006900030658030215a2550f045480a0001c00c0b4503030481958030030f4231405c21079202c4024000114001000c070401191801802514090030ba42091161103e8441e0f0415110020a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 970321384 1250 970320134 970320137
    0x20f010507050f0c0f0105040e13080903070e150402070804061b170703090e0610050903011b050c070617130302070b1c0605040207050d0f050904020d050601030c360b1306 75
    0xd0b080e917400d500a0003203401319040c980d130f0701c909603032200b0811031120084502181c0c4074400b0041c1c50380716a02008480f029080b142d41d08905410090402c06001a01801460055005020f0030001c1110314083d17608907501070a0030388465040c079514265401d0b03c00f1004104400d40184d0048403017a0402500c00c01e4800c0c0c8440c0440394403441000292a0200e46095203e010003940713050607486507015051007440a400492011020007041d001030481c03180c0c41001880205220720804030800c410f000801c518200307a95010003100e504400d00303000600c10340c40c144108069030209882080002d0003440b1901001d502c5104240b01e0310105210040e81c160043d091000c042103071703d050703c201e0368000c1d8020f0080031100e070741c61400d548070400004032a040c17180520809009032254002006110220310000a2300e00c0d0003c0090100c1d8402e003c01c108000005d807044841c641c1041e51951544056541d0b0540303019250b0b2a5400e480c0e280d0050301803480c000c500c40f088040e00741281030588941c1d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 970322634 1250 970321384 970321399
    0xe1512010e07020d03050f0126070e061008010303050f0f0c0a05100e070506040e040c09050106020d081317030a06050310050907121703130501020a0c0b060d020d020f010507050f0c 79
    0x1001040317054900540d100d6990000100040041760002c080114452001045008200003041c0103035041c405a6070200000e180600c0806c00701c0c1c40c005c14080601002810640e600b035045480080850041110350b42000e1000550315003540000300c00d840c1c2d440c07100d100305d9901d041c051400307a4031500441d2064001c1410711413901129800801c0c424161640540150309084c0340c85000c0ca02c0c0340000d4800c1c3c03010030b142c042c003299500701e40c00740d903029180c2c1da001840110391484005020780c0740240b07104040408994540005103440d004d18580b5009480c540707440f9140c50f68041c00a004d907511445d4588130305008544209215000700e8171549002050b074014a9442c0541d5420701e08113040104921040051500c1c0010004081c5400001c8000750340148181030b0f860030b007280d0010007a031000c9120307000710008016914102a03404107040d144084001400da002c00d6428095130705c000d04c50320b9068880c652503403150094601c140c5e0003104807203001c1c14140d41030b6103a02c02e200180d4041e80302d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 970323741 1107 970322634 970322653
    0xb0904050d02060c09030a0f081603080906100b0f0d090c1707060504180902030a1a0415110a0c02030c0405070f0e040605010e1512010e0702 62
    0x1110340300505455401c9440a460480300811604207090704124040307558030b0104184080c140e10201c410880116890305988900903003113031f940c0c400c0b15841400141644206418080d68000043e0b41c4d003500c0726440e2140e50412070069444020302000014025485000140030030320406c80001385040c00c56840a036944032550018150915544802c2e40100c81885814010105418802e20b40340c90188480701d4200e000d0100401d042d038a615060542d10180581d0f121640e21030340041c4043d2407101200c07038a42090301e09071540c1c1121444081c2c00c91301031140312030310648a21101c0c10881c0d40742c81220300142d0000d00300e03014007d01d10994901d499078002c1d2402480140c13166118039845410091030080401e91107486035040c50810401d0b070b600201410175105054500c0310a107208401a002d89204c2e031920505903070400000061a211842c680500503400f1f070342910641003 = true := by decide +kernel

theorem cover : BRFrame.Cov 970143884 970323741 := by
  have h0 := BRFrame.cov_init 970143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 970143884 ≤ n) (h2 : n < 970323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
