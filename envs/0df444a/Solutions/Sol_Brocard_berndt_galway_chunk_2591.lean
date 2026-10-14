-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2591
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:09:39.375976+00:00
-- url     : https://prove2.me/submissions/4d35424a-b8d5-4f94-a823-888cb3dfe6ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 465827338 ≤ n < 466007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 465828588 1250 465827338 465827407
    0x151603080108017505030c040501030f020d1b0207080115091503050303100e0612150901140103031106070801061d0f06070c0810020403030816020115090e070b04050303 74
    0x31160442c0192040d031007480e03c4001003a44e4840c1100d2001021044140303040c0b411b44c2400b25100c0894400c0d842071604041d101d908003003c210031941201c0c00c480c859a010800d541100d42400134180000c80c2d020b016004c0c0c000c0004218006000320035801c05502da0140c0d604d4100151500100407202d80d40300804401d1b030000c00001c40400085004440320b0690b1070701c1618204201e07004000c0200031a01071504406050a032540016800c01901199002c9040c035170390340440580103041195184012058000c000003d05810502010040747c00070b080e00c1c01a03564038000c0e203d4030000c1c030a202c00640143c406400c0c8501d00d424803088058003d00e80000007140c000011a29046001c06a407d01c000703c1007000118000c1010200d00005400c0640c10300f880c549018103050341c01012501e0a603a422114501e092007988540b5841650320060a41d694455000400a0034400301814007441144000301d0442001c0c010f84088a00c01002503141c1058220842c0c9a081e038040b46100788a10f0700d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 465829838 1250 465828588 465828731
    0x50108040f02130b12010e211303061b0203120106050901030608030301090501050f010206041a0c040e070c020f0d050a0f0809060301060203070c050405010b070215160308010801 78
    0x20b0f900d40884040c2c08110b1410304000c000340d014500c0c5501502d60300d402030244c0500e001080c7d0b460f00b01d1032039444052100e13020820500b180b10b0788080904240c1c0304880403040160390760125001855440200c101c00c43c01600580c5d0700e1083c1c40800103034400801c0100f115500c01c034003c000d0004185408a4160f60302c4030154a075410a80240e00800e8994005010500b400c1f00e009013120030034401010f503400d003a00d030380c03070007040c0d404803e1680c0c040100000e50058402045500602c4680c5400143c3c3c0740c098401000c03041501e00883c0710308404410043d003890540040d2407200c0d0403001900701d484069982116100185508990a40381800320180e01d1f903480000d10700800c16600915900c011902c1c3c501d00c11112034100c82c1c800e42ca01001803110b618054145c0300c0300b9606440c034840121030300350442246e02070301d40b1f03200d4650001c40500c401c055018003c24100c50099009001d040c0c100800c049200b0500c102c4100c00c0030030440200320340b82010006035580ca0b804400d9170740000928 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 465831088 1250 465829838 465829849
    0x40f02030f1509121e07030504030c26010b030c13180b01031506212d060501050604320303030106030212060109030c120204110304060c09140604050108040f02 70
    0x1406071203101c68a0310400101d4070040c400c1e540c10800013628035181a01c81004104458a000314444031090041012810140a070301260040d5800c0b002d0b8140081c0c0d149400c5282400856180d0b40d529443c505194485d0814040c0c9030002900402030000650b21000780108030300c5825159441c0b989a8088070310041110714000d0551b8024240c004483d811030038000d0340b0108515514050070325040e010851109a4201c606403a46800010b0350505494180800c0c086049216007002c0c98191076030094810652103000e0046202d12028003070360382e941d01002001e001f00e1007080f038007c030122640c9150480101c5a900c41426910040a00310166030109245810913000000400d0b400120340c00d601c81c1e010b04050b84608246880740c402400c6581c1c0161084e080c1c400c1d040c613280e214006004550703d680025901d0800702c8200c0d9181e180c070f41850400b800d540080c2202181802d8400704411001b500b100760392410107001d0b11b14141c50980110f6204c0c0008000b40c64162102e1090801a905d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 465832338 1250 465831088 465831103
    0x1209020a15020a050d0206070206041101111f0b04090803010314030f18040e0a030e10051e090a0f1211060706051306060f030f0803070504150302041e0b03040f02030f 73
    0x320381c0180314400d80c84c60168035104054019030207651141c13041202039603001035000c0e405984940b11107a6040581c0c016180400c420101013410700498005140141030030200e44441244804284858200542404101c03a40301c140a00f0002c0104011300101390800c14916000c42504200c0789024070241c1585642c0e0000d081c1d01c2d0110380e4500d0488100e14041c0190305c034020102016200701c000a035000341910a24075080e41c041c07028210300c00101c03030249040c9c5d0112210a021081c6000311008040e040d0303409a611704d4466030962a010032000a400e550340d050b01c05800c071481e00010306071150941d407801d05030303240d5006604100f1480020300e203014140c001d400c400c4055200114510b002029551103800c03480c50042c6e125001c0021480f400701d1003581d50b81200041c3d40d25118180e00300c0f440c0c480c50b00300100007605261403250680d810340c020f00c2121002980180f8440000da240c000001d124801c00001640c1407001c0f4000c1103240c04d407800740307510060441d5001c2044100e1103041c00714 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 465833588 1250 465832338 465832379
    0x50303040309050f040509150c040906080703122309041518060b0f0a050306192c060a09020a032a030b0603040317070c150507030b030d1209020a 64
    0xc0707529041046013040901d45222400454003840a443c0038640d841c2e40302200b480c02a0005070080c041441c102030a0200d4018003180c10060018544540c03003a03580d00302c1440202da151104881c0c050a0900c14106220300e01c161540c3c01e100000324020040751504803060381070340715684074881d1055000f02060b800091801c40303941a079145880102d4000c84403698000421a03108004216040d4448011240c03100c1c02ea00f009034a079101d110100750301c03c81601915440810f41c0001144034003010081c000304c0034070b509416008840903108810f9058081d00c1440d007000c000902401050b1441c0c001c0c000c269054640020070710409030114580812205c031031100640e11036281e00c46168140200c160481e820783e0b14a16600382a82c0040a09a40700e8001181910b80720204207128458500d513a900360308566041c4140c1e1900150308014103060366224042482c01c25007030498180822100300b200d420342c42e030748207a1005040d880040c00c0064000c0342c0c0860441004500001c0c104070a135603810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 465834838 1250 465833588 465833597
    0xb0106081e012607050105031f03020307030b0402090106020f0601050d080d0f0b040f0204180203090712050304061b0302060a15081c180f0302042c0a0b070306030503030a0c09030503030403 83
    0x8100c0d80c400b100124070f440ba9601583c100000c2484140d0b004000c603600120f24800410110782c901c1c801b0007000c04950002541802038410000a01188409040c004d038000ca4102040d030f681d4680030b0365100c184054408441d0440d00c01001207160550b1101801405590518a02402019900100e9149551058502c2d40c1c90900518a00f40b503c14290000d04c0820118600741c14183c140000084803402109003940020014501c0307101800444001c0c0b01006210340d0098641c03070015220340041c0901400a010460001202d240f8441880452a055005040c5581324100101c2c01351081c60309050f00740700c44001c0003a00d28010001d100d200100100310320511000e2210007025400c08505d411a2039403c1041070020a0703030004000b04a90341102c00141040b00031000840c41c00100c1c85080b070003119062035518084003c0345408d0444d10629003110340c1ea460144c00e908907101070102410980c014400909140c3c00c0c0d920241c049201820040704151352513864514540c4201e80840020303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 465836088 1250 465834838 465834869
    0xe0a061725090810020906030103060e0a0c031a0a0207030e210d0504080d022e0b0904080d1b09090506030307050d180f030f0201050a1403090114130b0106081e01 71
    0x5010030f025113000e0010746041903203440445400548140410f0001078074a55960100c40c0480301e0410440490300e41c080300030810130f0356900744500120002140904401c440340c00103200d60000d4401c6074142640341d11060682075800f4244801207850403104101000e4040c40041140400c01145a14074403582e2400d6a40e801c2c10f4229052041c030304000415035000000e88045810011031006d500401d40d1040c614030410144288040c041c49a52590059150030a2100f88110350b00181000300d090781050040366a40c28680604880e16000c000c0084c2010006000181c5a82c1005030440c00c004d00701cac0e09120180c0c640c9814501502d9025010a00c403035602c2e03000141100021000b40341903400000c0b56440c0d6110141c080c040304200030304001002540074a12030240441c20b5512144540b526140c0c80e01d8a11030b4020001e0000c1e00000150100010300c018406144283c0782075800650b9411692030700f041520300e1003024160000d821140b0100408907200d00016500a10f00d46c00d80c240344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 465837338 1250 465836088 465836099
    0x516091e05070c0b0702010b0402030a02091008041113020405060c0a0512040605040605030c21091513030302031806160e190501180b040305060402010e0a06172509 72
    0x16400010100c40c0c0782028200000c990708000400c0001c1c0c0c2001c82c803510741d43c59010403070040800000f441c1d4420b01c04000c0c4401d2070495400f07020700e0300f81504d0380da10501041c4801c0c0c581c2c0703004850080c5840701100f9032030410304114000b13408154503100054200b41c0c0341c0001034455000765500ca00f0a07402544841d050090801c003095103140e00c0740d621403509082000c014568072442c010841800400001309800e003007520210388481c00c210b98221f00b02e00c0907043c20720b048401a1010605031003083c05a02c03020700384000c140e000310724003141142c9051166400740c0c060b4000600c101e07402d03443d810fa1550000018460306102d030201784100c2010741001c2c0005807405400e10400c82c0500e60041b01c0d00c081c00504108030040d50b5003401c09030700206518080040b2541107800c038500c5140f0210f800810041d00080c4140210320036256029200d588a043c000d52421502c20b80000800440381d01e4014201c0aa982e50004909050070084005c1016030301e01c400500b40110340002d4246100700b11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 465838588 1250 465837338 465837371
    0xa0204110705061305100213051003050f0705180d020f09010915150219080c010617070b09031f021905071101080114370303120209060403030507051609 67
    0x1408020880300c4e04c2c152600d900c9440e070380c0103039900001000e540012450028010381040c20001e2100038a88140c040400c10001e005d000191004001c0940400208040500500a5400202c540c0c08070072401c1e0440070820070002c891010590300403807852100125600c4011089018111002b400310380302208010304d11030b101d1075a10051161482c410001001c51740480d40d00c141007c4141e1f0641d0a1101d802c1803200e612540504c06000d619110700092445a0f103007540c2c100320f10702c03004cad20031043e0303186007031922403241e9442942d01d40c1018480034201d1207035040d0f1035259581481c00500300500001c0c249010200000080042040400c62204010026854260b05002071178082e04951520110310400344403004801d10801c5800c050100f01c4031852401a60700303841c840d20002d10401c1e44075800e03100e403050006500081c003402e000c840c0d03244140200c80c2d28000240c0190700d818655101190340750401c42c800c890500038a07003c04650507020f0500b41c0038119201c400241c85559050291 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 465839838 1250 465838588 465838591
    0xa0608010504140c0d02150711040213050f2709030f0403060501080613080d020903030c013207020d1412070306090605030c060307141611010801061716020a020411070506 75
    0x5105c4e540d50084040146ca0f40c1d580c0d100d00a00f0404e5091300c801d402e14040401010526001350002d01c0840d541840d031181d10b032000d04a89081c2e8900d03151180040c00d2180101405011000c2c0e810300c0808000e2401c04021a194822444001d6a04200050f168940d0700da0042d44103403401a00c420060203400e80c184600780d0003d2030140030041840301b40c1d44031204d502a010072b0300c444c1c5a0124001ca1180c4043c004c07a4200803c180082108451003803c00d40141003a4070180b82caa10055151500610344010090082d2615001459815003601c82210741e514a000c01041d804802c0c004058800307014a803441c051002a1404202d00e42028401003c4807210360200344a82d000ca02c2400c80782e2150170480360042080d2074000c0000c2a48041d0a44521034540b10644200309031480d0401c3c0149500d40100c101000da0f2103040990341c841045402041500060341740319612000305002c2d41c1107203c00081581140140c8001400d40d40015048503001c1031400e00d000720006130702007082030900500303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 465841088 1250 465839838 465839863
    0x62713030e0306070c031407060f2a022805150106030b0301090b0a02090d0c060224011d0403110f070305010c030213121a07053402090a060801050414 66
    0xf0141c910300300000601d510120b070300160520030000406548010307044103d5621710740000c001d00c030b0141030821600042ca810b01088941820002a50030303200405c0d003902c165a8415402452111030301400701410301401c015448448804a03006000140140202040034486a200c400c0d40d6143c40400f400f62a125081d031880b0b40d140c00700f0000050081c00d095500086128401030310780e410781d004a444c2c40c00c4034034040c00182c40c0c0314001403a0340e8002100038000110380e0001403080f181c1060202d40c10020b00615000c102c0c0e190070800c040894000040d446400381c50110710307001c40c0300940c90602c1034500e030340c6806403c101070500c1445400d003d000380c483d01910781140f5040003105211400c02d0140100c2842203005a800401e02c078501c0082010420001280c0b0340e21b05280e10098610351004c0c1c903901c44001d81050108442d10040001201c40d1450001d145201046034200a0000c40042028030741687e41c810209504c4024451079200c9d40c4640145150b5240a01e241480d00803040000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 465842338 1250 465841088 465841093
    0x306060a050d030e0406030c0b04140402031b03040f0204021914070804051002010908031e15011e1e02071d0c190201020910090f140306062713030e03 66
    0x820503500d8200e056002e054061805030300c42100c400c0060090b2105031300141084540a03c041800c1031210020300498803104003c200341c41c0440107000607404210348465030244020403450322400c4042c000e541c403511410000007100080d500103000c0b6040110517064050b286540b00346519000694510741c0c498001001d41445145d5488c00010f225038080c140c0501960390701d01caa914000d401048503075a02401c190313204e25180100d030701d80070700e0381c082062824001c40101e1a1140c0740050880b16080c1030395595031140040c444e5070070301c0c00802254800c104403a82e44003500159603181e5000050942c0c0601000c1c1d14040384204c1015101c100c0c0220002c1803800d0000c003203e035a04651101694401c05040203075249400d900901481d072901e0b401040c02451032240030341c41460b83c015111418000c0a55588880301c4000c0c0203010550190980d000a003c1002403400c1d4015140a41a60102c60720005092030f80682d010b10540c0c00100c1c4011b2a0111750800da0002d40d010700780003080c1c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 465843588 1250 465842338 465842359
    0x90718090e0c0409020a140319081201150816120905030c0f06070c030e0604080f011e02070507050910030c0305010207060f110912030f0c070810150b0c0a0609050309030606 76
    0x41c0044401d031081071f4490038424000c01d900d4405200c0c04445429420400c06040010309106070268003014814040080700000424044ca960440d03c028285d142d80b10041682c54440d290807240c00340c1110401e121f418030002003200341b01d0242c01d465500c00c101842d11481a40c001c0d6107000c03000904d9a049170095020050b00503440507081c0c8046415151486c0800d01d48004141d091050360440d44083c043c258100390407a0054200d00101d19070004600d4003940082060801ca0040300c00007021500103032020455032504550a0750031400007190750220701e64943c1d8600d45002a6481140c89940200314541440032620903044080c2c0700304814000408030048800c02807040c642c3d96031141103003e5804048860070010b80307002f03500c0707201c1c03480c1e036600204c8025a42d01c1851055090328030603c26041800351103030040188411601710100d82207418400c1c1040c0940109041c00040d02c21501d46001058081c010262490b0190300034581d40c850710b00c1070500346000240f00078045c1250740d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 465844838 1250 465843588 465843593
    0x39040f0b090d081809041a06010f051b0304210c05030a030c030305090f0111040504060b040b19030f1d0c04052701060f1706070e030705090718090e0c0409 68
    0x1400c80702c0e10303800110305070b480c254850914844044262101d812020308070801041103032a443c0140b481600662089450342c8401c01190341e0f4003c1c105030301c00690203000d61007000018881034440310740c02d0400d0f41e00b02901c0340c26181900c080501ca00c61200c004101c103000380f00d445030040d0060001500604007601d000e4501038420f0010305801801c0560b00e5001403c0d03c1d0052121000e1600248000c0c40084900207807000c1e40d412078000c003845245000700c005400340d856802c68041710700b40200da41c140b2a01041c3c50b414440013207a4641455280d07030176141400c031540300b8200004c1502100240300c0c0c3c0c0c0220503528009002c0c00d194041d514001c1440246000b0820900e49818a80045160344403080b004034003404c060340c80b141d040c6000c40408502e000500922910095281c402c50341e046d52034100444183e52010421030f0150003e0310300740030701c0c244180429401031041c10580c50040c00e03a0580a4141c20b181c2c0520911aa510f900b800b16507020b0040c14141c200403101481308514a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 465846088 1250 465844838 465844849
    0xe07050703080c25050714090105030c01140c031c0b18040b100302130209011b0816061d01090311010c051621050c0c0604030b39040f0b09 61
    0x250a070f61000002040d2800c075440c082c0d91881c1d81d648006442440d40c0c0040c45c0c000d40d2107050740681d000350f81d03510a03408414100401214100c507002030003030160b403282c9001580d00d00c0107030444217101d52080081000c514020002050701810490340c0d2401c0270013082c07140084885a075405072090301d540c0440c6280c00c0c000e1034550b400c55000014525562281000d5181419240c0c0c002504030b502c002c242d503142030f0380ba40503005190080c1c03621800d0003184101103401d4250b0303020061030070109102d0b01e2040d2008100c440002403190400284280407018103800d1802c400c04001b610b82c0d140d240d20f008041d408100e080c014044c04000744804c0c000700c14050103d000300b0484a0640155030720b440240802c0c0f02d61110740b103100b442110681c14000800034813a90111001d2700765032280300920781c1c04d401d01104641c01c4a030000272100c101d0702d5800780440c0500c0180d40544420001d0f00d41c074030242c206500c03d0108140c0e5004d0840d511403a10540641000c1550b001524406062103003074055143c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 465847338 1250 465846088 465846091
    0xb030916030b040b06100206270d0917030f1806270109081c12020906030f0103050111090603060d030212040f0303030e0d0207050607030525020301290d050a12090e0705070308 77
    0x5642c00100d01d0880c0e40550050340109d29644001441516440c50340325412210800680741c076502c8004c91103102000c802e07500e101d010520096900308100080c0525003000b1501309181005141520304561a00c6003450841402c076407a1004864102c520746a41c0c008012800921114025140b5400d154486031001e5006203a0711041c07080303103c46901c102c40182c1c1142c80c0803000808882c0c032420b00c1c1103015028642400120b84643c40d11010f0038508001406480e40c07500e00401b010710759961981401500d00c8064001c50540c031503006894100d0301941d01a1000d0f144403040011041c0c0b440c14010b043d6034940c60040b0264110304008a001a40801c0b40e40548000740c4e4540da0b25004c43c6801c031030910884508101001c040e40000c80c82c1e00d00400070004190080b03009105100000852050003200d500000c040d0341100b5185141606103e4000007605018009031042c403070035a01e42d25200034121403000006080054148a001d5078042042d4104140d40703481d0f401c062442d500a05141c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 465848588 1250 465847338 465847351
    0x31d0d020a051005040801110c07060c0203060a18020405010b0904060e100920030a02130b0a12050c0d05040b0105091e0c1b2407180b030916030b040b06100206 70
    0x54101c00c001c2191302420440300245000740c0200101340c140c00313400c0415000404000441d006a20000075400e205501124500b50010301a0041c1e03152146080000d00384d01c2c11014400300b1800820b0302503980d41c4603080c02841d5a0319051303034400b44101003100310b4415800c0000c2c0050004180a400380115030f01c01c090380e00c5030000040400e00c0c6106104540c00802c901d051544002017000410341d1281c015056900584d4000f207010f5403128004d1015005040c40310300054010203100c09890304d00c1c0c002c9034225405406081c81e000c00c142c07542c070544070708607802d0b01c0c2c80040000410445c2043c07500c4036404030100d100c8046001246100c0104500060510140c480780440c0c0f86110100441c21070b05049041001c4440f0700411440c2c401f01c94680b50b210884000d038000028143d60b0180780030501990001d5040c12249081c02180400340c0c101400742c00d95171264103001044200e8103041d001c0514000c01008000d032605182c0041030140c010089406040700424046c3c5281e000240140c0090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 465849838 1250 465848588 465848599
    0x6040c02031c1b052206080406110c030703090807240e030c100242100504051e0a09030e121006090b0a05310216031d0d020a05 56
    0xd07051003803800542421041e40021004a06105801070f4104008050820081760b408882d0b2031205860807100c50f4034842c04021031182c0001500040f150760000428425012042e802e10054001301d80ca15000303020301314040b81c0903000612505104002c00b000500b10810642e1520110304007689100b00100c1c01703030b01031000c00c11041c0c1c080d80c0e043c1300d440450400138100c3c07184202e0402c0d00940d02e090b440c2070f5050b4103520302c1225902960b41c207402c005505440c614407424000001486414140051007080e291220000109542e903484c09914054500c2101d02642126000b031540e0304840080c02c00101c01d4030300450b64000039004403400481090031070381410300c03103101d0011604001c1a22218410a03180c0356003c2110703107441e80103201042d41940d00400071034490017800140411030354140c58032340c400c052480654085402c1c40c200c110104be4058240110381846003203500c01c4c0c1e03a08401054110381c0462551600603140ca0b0200002c4608603540344054000c9260001d050245c0ca0054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 465851088 1250 465849838 465849877
    0xe0c0714060115141c1b020d05161e03030b011806090e040809030a0510060b0c070b030603031c09031202090d03051b03071a07080103050c01030207021305040c030b06040c0203 77
    0x180a01c181c8240c10a01d4140654041581d1515001010341846da90b03841010215031403206440060b03080c2c1c1684a03a120301d4641b070100910b148000c160340d402101ca120000c000606000302c1061a03680c500d10a440119020042c9000501030601c11321600c603039055505003c012513540300c1054011510b00c21002080b5031070301d081041c4148140140b65805102d9844818100030300054000c2d0200c2a5403c01c0001507190040080f0070311840465800c5507101c1d1700d0600681c200c0000450f00100c000b0220380c0f0380006500301e59003031042000341c0c40300c0b1992070503403c0c00d145e00641d0881c0c0c44110203c0840c80c04801c000000c1301d1503030058002c0d0801601044510080905c9101d8030b25140080045984807412803410445074098a031142c00d09004140105070440c0c000d420047c1642d9000018100324000900118000d401841003070381d00240d182d0000c0700d01d0346588a140c0c0507d00607071001e00c0c0d0342d0840c100342583c04005010680200d180139081094a6030100a41c0d11007459121043d444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 465852338 1250 465851088 465851117
    0xb0106140f0702151204060e0f250e040b04050105010e0402010219080d090f1e03050724141b0a0906030b0406050303030f01060809010501030c030b07090e0c0714060115 74
    0xf20340b0a545003a03000007403820005c01075001e9a84600e105850034818010b070f0110454440300c08000d03001d1683d205c4051007425414107100520b00b05507048600141c642c0d2004113403100d00d400d98007915001140e07420300c400e00c002800317441c9c05007070042c42c031035a241402d9000135603030024801000d11311456035103664100700c1c4500441d6003100f08a1420721601c149030900d2001e00700c40d207004842c201aa641940a1600c070f00d0268801d05d074058650900b480302d1a1195100489140f0b4001150344014420164011040c0b04800f80c0b9000b103131007205145404840c250a40c03240385410700c06600107128030b84555a01680d11010740e141ca103000b068040c00100850090082900b1007a1300d40000300400c1010302c1c480d16814100c0300c20755901496038464010203400c80e80b0070301000e0940b102c208804d00204000115103a0807107020b03c0c081d01c141e0390b41d2052140114042e2584c449184000600205100c69003508d80306040d40c24010701a00e51401080210006011a0282c01d0101d6907210780c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 465853588 1250 465852338 465852349
    0x1920100e1e10050c0c030c0d020d330c170c0f04030807051f20070f060c030e070911090f06040e070f1e08010501050c1908070b0106140f0702 62
    0x1001c4805450480303081c0182001812503048050844c0c0c903032107044100845454005050948060042d0440342d02a10076001c1c041043e2503a0740550b41800040300340300034042011042d020070140d9030000c40a1914440108080e030f00520b80d10800c100390405030030080000192065000000100043e9845001030300007c02d42c0201d60001c1d011601c00703c0c0c03078000c0c041c0c04509442c900c203410340c600c0c2414804103940d20440342d80c1c8614038003e04206801e00b054000550062004500540460000400320707500c6105907914030074000b00281d22250040d1a101c0204520005800c00034000d103c07243d4190b8503250782d4056a130704078ac4078915401d5400c2c000d03220760040710050401303184110114a00076101500d003410744c11320b21000075540c2c0341c0640001c1d80d8854850a1035540d9440501c01d034648401110b258110b400405094051240c3c2465084208005028640d124010380381e100c10f494204290654030592150f4184400e081c031441c400d03e810411113401072100c0310565110229400480c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 465854838 1250 465853588 465853639
    0x3050f0a181e0308010e0123010c020603090f1b06120c0c0703060c090b0a05070605060a0801020409200306090f0a09080a03201611031920100e 63
    0x2401540c1096416045012090328071021034001d13203490003181d03038800341d010f1170300001d2150649007040303038241c40d01c4ea80d804035010307008010501d04400801c0682d0005407541e070066034008200d50040940950140c02446001d074407200f012020000c900600d004940c113446803140980808845200103880c2020203001e841c40e00a1401c111805e0720349a2a1200c014816008610041801034078001105940c00049404540a5950b6281806003a64845000c3c1c031010301200e13441084440007140c40082440a800107200b901408503e050b409401c00c000301c3c001c00144400ba00c07080080101c2c9440f948111500000d0031040b81c05940d035a00d0cc0c050042c8040200184408000030f048081d55626800c4044002840d9900130040268240e540d201480765041d0400c041e821030344088045142d80310401c51507003004c1c080c1c800e50390188160032040c004001045420001c0d2400300c000b90b445480641c0c600500542d05c0c40c1009001d4a409400c000b240c0ba03406100e04404a80956840c1c5d1301e00051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 465856088 1250 465854838 465854843
    0x308030901180b0a051609030b1b0c03040315200d0f0c09050306090d080a020d0b0d1b08010c0206160c05060106110111090d29150a0603050f0a18 64
    0x3aa031078100d618101c2c0080f036050740c0788100f4030300b00f4021403040001504100b0a021968841002041c60740d920702c090040000c00d54070105000300842c2440d030350750380020040388100d580990f80e59411441c1404403000c2c8119010f040b1403421801502440e8503002001051003545202512518071005020280840307810400380c160800c598910450b4115000405440d002c400303551840da14180620b682d008400c22070400514020041004112554010710a1a0720b0110118640c400e14011072070342085110119800307014680482040081101090043c05046009100e07000d00b0141c000e69401001e072142c0b00025480c82d4200362103000300d0600050640c8142500c00940e900e03907019200000b011580e011a500b80a00300c441d80d40d0180403036516100080c0006485c584907100c141e00700311000c02d0044503d0610408604002144044521a003000c24604440b680c0440c1070000700111341c0c0c03241d000d00d400c2c80d040c0300300c0e90504041e10382d00c0f0025840004000414075641e841705100848003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 465857338 1250 465856088 465856121
    0x609040207080d020d0209011e080a0513140601050102010b0d03020601031e12030614010e0a0b0a0923030c0d0809010e0f10030203040b0f09030706020705030d020f0c010e010c090308030901 83
    0x6050058403646c0140c45400826240c00f40c04140d81422700421003000782c4000001100c06000a00010007a800f80c1d800030242d00100480d4161a0b43d080007031300c10810b541c002640310b140104065a030901030052040400d44003000700290503a40070f961010180030080c01a4841c1a006001c6025036a19181207500116034a646070002d82c1e0140c010141805800b030040b10313009000079294040e051f00721006202401007403001d0301e0040c920b0b9044d0000f0300071030100144510700203540100707141201e08510060351000c00100222042600c2d00010350070503401071014028000101d180f4505941600c0d02c01c0c24a100442860740019208444140c14a580302ca032045502d0080c039815406507110741c2c801e155403091503c91101070132004004548116150b80b040102900088541c1c000c0c0c40180e20038000c0300e0805004c2c2c1c0102007643c0280e2580e0f02101c101090032040c00900b40690740e0103201c00c45c002c0194062071800104407401d58000540a185c0c0000400d07031b14042544403015000e200d140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 465858588 1250 465857338 465857347
    0x30e030307170c010b0a0b0a05070206070c031208060108010e0a020307022b0815031f0204030f030c0210140d090201051c021201140f120a21090e060609040207080d02 73
    0x2d000ca0541002103414043d43ca421201000c1d414094030310303810307900140041030510500c0316046134149e0020740102d8002e4070901542c00010000e034180406188190303408600c58081703590080004000410750350402080e400100003182214000c2a0010020b00000d81d484c0d80c0e00000346d05d03080c0012101e0481c10320403204c80c402c004e9000829400051700790788240c0b060b2243c80a08038141101400e8030b070306401c9000c1041211591480b09031010145000141c14590b40b034031448a003c41c028029004070b400440c01c0011454082c116007074845460804003413120090115030760313030700401d4035100c103565035402d090f400c0d68080e03003d481d007105c4100e6196031100c6c00c64840401941200812045130101400041960a40f041030540c10140240c5a28202c052050420152441d00c40800c0054050001d14001080540e0740c894001403011065071042050f0050003070220195500000700d0311006400d218040e0b962408480045000b11405a204c0c4001d0403d21124810b41c5a6003180520004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 465859838 1250 465858588 465858623
    0xa05120c0f1209060a0903080409140601020610031511040f060f020f0d03091a04050c03060901062123071a03192a05270d030e030307 59
    0x90082250864000540300c614140c030740326a50303031210070300c0100c9051001c3c0300e01c2c0300c81e040c10805030500c00281c0c680b29405aa4a48802040b5030154008040c500d1301c60000801d060741c0c4205482d0000800e200030162494030f80405540761019020041c0a0001103100b1b107849100f035004804060200d8a4441d40d4555840050080c0d41080c428140840d030310203c100041030001c00d03641e040310240c0e40580325100466908030001e202d040350860301b0021985252440311044603069204510400061006c84920001c061034014000c0080301c3c180e052900900c895a0005c8081c1c3c0c1122034007880000c00ca0b418600000c0207003110a505452843d00301c0c0f0210702050000e50042142c4030400301180c00508120280702e288030032181d042c1d500105d2a400c0385620021f510421009420508982d04a002d00d800d80a4a010070515030000600100301400480704501746503400e400c00e0280303101803050030004a201d152900300003405100040c0450101520107000f119145584802c80c0004252a030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 465861088 1250 465859838 465859873
    0x3031b07030b01090203040b010e0c0d06060203032a0409021b010c170c0a05270a230f09042a0f031a15060c0a150e06220605090a05 58
    0x41c03000340c40d00d9032850000250500c3c03034800c136030046800c00030040716a820001040d01b0740c500038000d00c0301c00404000d410580601482520060612a40559501c2c100202c030381b120401c501d407000040018030100000c0f8810550b0480b8101c0300701c0000580c50328100303000714640c043e035944980b000394244080314072590f520000200c0ea11030380c048200071359110034005074540d01410290202143c0c04018843c1e507803910030003000b880003031191044014101d410218401601d2903101c108a1340c14000140f41e02010101c040d108007100740c61080214202c1000100b502d8401b0f8009048d054015803a801001020041110b44440036116419004d5a40c05040255646840144c40c542510000202821560300344072340242025980d010003491400c1c100240b981c00390151002c0740c820741c0060000200f000b01d00030011100c59000240881d00a107000d800c009004054403600c40c0014a100180c0c191028208006074002c80e00007519510300a0322803621002040180ca544198000c040d4555141d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 465862338 1250 465861088 465861103
    0x19120501090c0206090607090e0a020705120a02070603050f06010806210a11040e0a03200f100c02120f0708090306160e0604030203030d050702030f1602040b0916080603031b 76
    0x10b500b16036141d40e0704034205d6141d4009940c5000081c500200402c03d03440c003400d243c0d03001101c2c1d5000521704000350381e032a80303000c0c021180c000c1050f90100700d0042480c1c051241d90001c00b0f443c101231049282c00800003084880090025042c01000340110345035072070b4040000d1000c5044000310000c99003030101c80b0780d540180081160038030980d101c0d0760410f0401d03010709846400c601004010207507455406490700c030011000000b00c400703070981c03509110070208108205220500080c00119410300e6643c03040c3d0310b0781c401e40c03400d541c00704004080580f0042c04452182d85814041512011149000b8105110300c640b074507803512601c020b10104c1004031400d0102403905840b80001c0101c07100034806580158071000e503040d002808142c2d94000c40741c10059108000c0c0c8142c80c64822416200708681c0c120311900c04400ea0340900c0c3c2000c600b482e1083e2401003100f258012001d241c0309405644040354010740e4803c01c1500408182c1c0380d10100240c940c582c081510180030740b16120007113aa1041c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 465863588 1250 465862338 465862361
    0x513060e01120302060601030519060f0e07020c030604120903020604030b15030105061c11090c0409060b09060f0a120501080f01050a050403020606091003050714011806051912050109 80
    0x2802000041c0014080c84004042e0b0f503da005400f56503070f1040190010a8028408a60140c0800c40725142e4081031144402903d0004140d5566506045915403422001002c0c1025503014030348403081e56400041280e0700580c0704000302c1074071880f18021111030300194002074104402007004010080c28000f035510840320b00f040640301000350400c06003071322020f076451078101030590075495200042c00c480c1c40300140201010308244c1c42060200d0203504084490400f200070106003401003035210300a450092030440ca00c141090045400950710b4482da100a0503003900004056415900561440030018803901c4100401d40e0340d40c80d50354442035050100aa1075107017100040e900c901c94854180030304e0f01039000b40300a81d00c4900b8409a20301c080e040041d1a03e000c00c00100041d400c10441d40640460404403000d0324030743c00090000c1c41c070340741000541b40b2410380c140300b070075441400e80d540142c10511500c8200f46168050300c03d40c4d8011070300303081103040000100d80f003401c68011603542e86 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 465864838 1250 465863588 465863609
    0x5040e0106050d0c0c0c050f060f0a0809061303090909050c030115140a0b03040204050705071509031d0102121c0e010605190308070308060103140403080702160f05100306051306 78
    0x104d15410880d00110306000040c4002e012840601c0241000d980c0d4081c000c00250005103032403440b0380500b455800055029001510702c20402401e40c45c01d01505401c40301c48401c3d010100810380c1c2c05015410300740200110715903216440c50510008100400c00305034040c00802680b0340400007481131451a003e41d5000c14a2100d84c040c4c1c03410421510000c650307007000000d055884690030070000e07020240104040080174411034000c50181e8a13807072282d201c4660000307030704603161802601e501008060b0f82a2400701d02000e00b40d590b00480c0740b5515000c071400340f6941c0c51002074a18609483c070309a2200c4c9614080700303402d21510540c07100c42070703e40444550440d1000e48a441c640101c071400000c00110080c802e620001e40a10981900104141004280b109210142e001d07140e104407400c0d03000440b0001800070094040c000403010700c07101d03800203500ea81050b00e00001a000c41c4103083c05400b420131384c11000742c400c0e440310010f80745c001d00300011100042d80c0c4401400170341c0602d0b4200c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 465866088 1250 465864838 465864851
    0x31012050c090903041202060f070506010924050102030a0320070303060e1302151e0c011508060c12061513081903082409010906030303050f04030e1005040e0106050d 73
    0xc000000341c03001c4440003103070407104550603401d22008e41c1000700b00c00e69541703003032002c1000202d06000c001d018010300000020580005980004403007c1c402c100d14608880c01c0e420310545e64080f040780c2d804d0b813650602003502d03c403a01d000000540410302d03204910704049250701c20180e0540150040792114901c00b09541c940d90900c5001c00f41c0d5100c001e41c007884900320007804401c00c101400810703880000042c400304182e50040c18941c130404035800c2381d9550300f80b081c01a9502d044148050540c0c00000e003454501603a44010512a14030010703600004500003039101e60b40c82c0d000f20702003100b443ca41610b503c1d003103c0c0100c041e0801d010f440361900400d051240310400c1004850a03181c3c06641c0c1c040d8507121043c4011203582684000003114090302c440c0421603c3d42c0503698020290b01d1800038455140d424010304a0f10043d040200505d40030081c0000300e54800c101250150003100c88103c6840414410b0b80c5038030030740c3c1c02810a403a01d040000b9141d50088050040054881402c1c04403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 465867338 1250 465866088 465866101
    0x3031608090105070516050c040501060e1903020603010909170c060f010803070302060c090d0f11010f030908030604020f160c0510020109050d050c210904180f08031012050c09 77
    0x280c4004a0f1088000341c421b20108500c40000404d040059000ea0259405500e000c00464140d07202604042d0100e881000d50395800e00302044040140e0012070f10400b003550455001603464841881018405629041018140107842420411211728503030555902d040000b1695160402103589240004038480001940200801101c43c02a0b01d54003510380d9075110340d00380d592900700807842d03500314000090003400680c1036004882a180075840900004040d00001001000d00300c0344c00040604221000c000030b003102083e40d401c010207c034090307110380186451602a00079036440a6443c0400d1100b01c00b40300728070500506903041a140c6502c80d40340024240d00340d80782a017005010f5070000588056240c814405041e084d04294169080302c1c91503036040c012400103c0d40340024460018005072140b41034410170b800404100c03a10810145039440301c0034000312803078010380540400400115011a81c040110141220303441400c080d02175402c2159450202c0741e6041d00581c1110b022502c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 465868588 1250 465867338 465867341
    0x20408030412121e030504110306100305060907030c0302122d1b010e0910090e030904060504060609030303090309031a060301050901020408120c030f0f0d061d0703021b030316080901 80
    0x1404854240109919965813200314018840100180d900344174090210040e650b00340515070140e180740c21061503050441c2030060415401400300c0e0f200d50300107041040000e12235044141141c0d0110350401600503203100860500340c0c0340312446000700d010000e40d0740f24044010305110480310300302200c2e040d800200c034100c0c0d101040d200303450100b0000c1084c5000b5140003003000b54442c24401c3d501c00c41c1c50340e507110101a14903101c10b210141c0c201217190440741c01c2c20300c1000c0044c4011034042c0007942c98414090304074080790102608150f1245055010715016060440055a00c905641c40250415505424054040c1c400610950904010814a05c414000d540a8a03504000381801c00210184280d00e64440c8600c00301c2400f092203143c0d942600c0e000a802d000c0d01d02c9c2c48a982d690b80c21503040040b10380a811500710303883c0c0326610f0445040825201c0d61720682c182001a6030b00d60241103030b250072007202440b00c0184400400c00201d200200140f00011046454000e0f068440924450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 465869838 1250 465868588 465868607
    0x312090b040605180615040e03030c0f0a03060515030103060b0103090206090409020f1c05070602070b0306010309060f0903030b2b170c0609060103300f0302040803041212 75
    0xc004910000215010070b501d58482c3e0b401c281060300d402c6200c044041594100311040b036040c107140000384400300250801d4001d81d20f0540140c0d000d18a1494240b814101e20f02820312400390806d408607007002003500a500070006051700902248141d107801d84021407540c02400202c4406080c4929401c0e25400313800303681d034040ea000b0700d01d03424604140d0501c8020f194130401a41c0c04108840c046500761240d4a031401c0c0c12040d500200c2d01c070001410174505c0d00e000d99200340e08550008004221040009080ea50009c40920300803e4210301d904048000e401ca030142100102d190107100400c1581540c0100e00d861002e5446d00d2144408107422803c1c1140102100440c1003e0301078080012001c10185001c1915000d00c1420007080f11422445c0800441f40c44d120395004400610501c900d6142814044d4040880d1401d85050b4034210915151400365040900c5694240c21860300d01980549010301040f00440c0e450310796914002001c9031000205031800800b032040003004600c110f1014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 465871088 1250 465869838 465869843
    0x702030a0b360d03020901090b07060e06090a030f08150306090c040c11060a230103050106061b120f0306081207060e071a070f061b0927050901021201030f031209 71
    0x181000f00030b11100398044d5002c083c1a0781000a582000304014032038001500030700380a040002031541c0b98412031850640c02401580301c1c0c5e27104002c940e00180e405041c0d1480c0c020540f07408501a150001201c0a0326038401800c0d505019003c20044c01c108009007440034040f040f1014008a4903a01c0c090b250302c612081c030100c1c60f800000015000c0e441d240c204826040c500806600308101d03504585950745020f030001c03100e80e51248000c002540d4000c0c500c060350306d0b03005108a044050b9985100b80300348000c0310182803101104035880c03454000e5200000504a0809851945450891030781d440e50100c1004c41e0f03e00d1415404903141d0340002040c07001d844400305449000407000c112100160444541140c10030103400c1a0b0001440b640168142602040d040e42a204007401010701907000170740014440400a6840b07101c0806161181294003a090000040329155455000c5c06440f03260040039004c0c1310303c2c2c00001000580c0c8012100d640c081c0e40d60032030540b42d191201094581d1100003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 465872338 1250 465871088 465871093
    0xd0c0e0609010207090e0f0304061e030501050a060e28030b101a0715060608010527130302070510020303180708100b1206010e090c03150703020702030a0b36 69
    0x184007400241c1e1108000d035040b10700f00d851107d5140c40c414619405030700010001900e902c040b00c038802500d84c50b40c4034460703241014015503050101141c555241442144100b04030300b41d0032100d50b11041da504100c3e6802d6070360000c4c1001c1ca5010341d200d070725480c842112200703200000036468622503400c070411b07110700c07240e020f447c04110788010880380c1040009540481070a50744000407111440350800600403905c03944002c1d8034190401481449403a2412300116514407062985403000840541c49000c40c20f40403418200c5040c201e00e440440d40106070008185994036001d1900007002e1440b4800c4a0000c42d03015480c0b441c110b455032100d2141680300d40c040710940c82c0c4d0701040d07048044040005403c3d004020364100349940742c07400c00e038807468008059406220354082e040c01500080030f000e40c000d00a0490b00f40c080d06c42100010a10004c0640c046030034421558140700840c0d5094104100000c9070801a14082c030007426488110711500820350307821858030503484000e440c41e040002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 465873588 1250 465872338 465872353
    0xb060307031515170c070b0c0a050427050601110a1509060c0801060306090e070512030903061503061302030a02041515030b03060a0506090a0e0307080d0c0e06090102 73
    0xc06038082c242040801070032503511440490035840042110610800c80d030340b000200070300c1c880c05054800014181904808042200c000132821107113040d0380103900341c14074076610f41409104440c0781c0250b820078030b080c004d600115005482000007000d401440c0d00010416178480c10015200c4c00c03007003420083e150304042c40100124180c0b140d41c100141b01d080003c1469401540c1d02d40883c0c0002e21b801003c02c4584c40140101945440b500e030240a4070b14042080c0c2030400c030a660303103c21911500f8402c0400c2c01d6440744020080c4103940f8608800740071034107a820601e1040101e900e980100c98002d101f0400043c100010030511516803c0d00600542a0009150203200180280004e6503035566200c00780001e001c5010044107001d00010356000403901d25520816040c00000341141c0d64090501741403050540c0c03940c00b056000b0004000020b4940c0c600f44105085d07000b80d12002e8031f980c00110f40c2030000d8065400038441c09255a4809082a0b260420404e9a0294607101401a401020b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 465874838 1250 465873588 465873601
    0x1804051303051608040e0f0108010e0c09060d0503040815061008160c02100e03160f060c0f02040c080618040528051c12090206090904020105071a060a05040b0603 71
    0x4200c14601004055001c10043e101c140f074179449540041d421090100400805142581d8518090200c200003403001c101d5030045107503105182d140ba40c0c42a60340f500440c280d03503103115107000c070382da0f000c8141d0b03844030b68035180c03942c5030340c09842056050650f85000400e1850f000c40c640440c00901d840e080b145445d40064511a044075607401c10501503210004e1025945807181d10007425000c0ea1000c4844a000307003458200000394243d40c1715803098100a0000c2e210180844090b54564500300b10080414104170b40422040366010790820300c0e00d4000c01ea01907110101511900c400d840c07030b0b000c1c00c0c554081201c0d03030201194003500e0f64010040b103c440c0c00e84040302e1036407400d6101c41c0b130340050107903110705003400000c802071000300400440d070241c110780088058012662110003003007000c1e26600411a1803084030810b600c2003c40100080c11a80140240c68040c0c2e0000004100301000310087e91007103070243c828038454003243d0302c0050035107080c0c01040303072821000d84918250703184c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 465876088 1250 465874838 465874847
    0xf170102042111030604050105090d030203100302010f0210060e01030c0b2b0617030306100c030807080a180606050a050307050d08130506070c1d04050a140c0a030501021804051303 79
    0x40340b084605410b022050b4110b0341c4c08010a0307004600174000041c20703040007142a803620000c04421410700d030049c000c200722108501c2c06c1d841160f8081c00c01506007195240100d04150601d0503c492191400b500415084040e0b000941078030b116072a000c0025031121092640e0b8010000308280c800b142d6001c19070003031241180f02c04449120440400c545456200080b0382c048065410045c544c030120411800d4508602e003480d005010f030803c02c0195449440013002c00100408600c00c2c8408840440c0c80803100b07034000350103908502c07030504098445103001ca01070b1440344195442030f04101c0c00400da500d00801c5032421a40c0040c00341c1600718295030303410003035041440b194520305a941e0001a003500c86000404840c0d20809031041c00908045041c81c840707171494110131400c8410340070440020742c0000c500c00ba003500700d10343e40c030180d8246001038036080080c42c526030030060062000080003015000340c0f81210480f10341030744083c4640280001c50710101c94041c281d40641041034007083c005d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 465877338 1250 465876088 465876149
    0x24140435090411040807080a150b06030a0c051608280e1903050601030b160503010b1c0902030d09030302060f06030a021507060219112d07030b010f17010204 69
    0x140480d003418141e54141e05ca0810829500c80c03031a50f0000e0a00070100000250200c1c081c40060000304140c1c2c6620f40494990b010044c00303007000540d00c000760340149004005071000e802d4809000044400d49150a03041500040002907503c09844507e032036564080982d00248081640c80454208906c010170945020321107601504196443c4003001062080c003d480c0a9802072a6406290a11644140c507840079081400c040000510043c0640c408400c115030840c103044041071030b0f10400c020024014000307010020340c50f2203030607804107203030340c0200a40e000c0320302940940d15a991a0215490103940485072654560031080d610b500602d0a91580c0440c23135076a803015820301e04642d80d4401282e101121100513240200c0e842c2d2111640401140c0d0600c402c1800380004070001810118203800cac0d101c651000c0c5000042045d2402c00402103074004680028000d001544e40700352510707203055a401040031400c0081c52003268070005008403001c44942000c003040c0490480401144d1000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 465878588 1250 465877338 465877361
    0xd09030330050f04140a0b0c0306041407201902040c110607170718050402160510090209070807050a0e01110d030b0a0909241404350904 60
    0x654000454084007622906201d49542e2854110f07a0400e07040c000c5000740c00c25810042179100030380d000000b81409641c0d64000f00c800042a460340c403460b001401a00b0b400c3c600800001070701c0308001c00240d2148000b240a004004d2032684000030f690b445841e48005449d1096242d01c1c00d08d09001424658014030002c0000e1a180088031098140740c3e01f0001d080d100a400070b00e80b00d04019041c01600c15844d001030403828000101e1080074501c0201209500c519840f40340e0115410003030043d070b030b001d8080d09503210003a0340c002c1404488100041c4541d4509074001d100803000540c2050041c021280148a5925507504100c40303044103c0720303100c4002a060401c1088856015224001c0002c4426800300b40c401040c83c260714000d01c1300400350b6501070300350141400850f60205501107801d0310081d40d060b5241c0c8103d030301c010b0818090901400109014481282003005000d8030b012006144110829082d43c5180303aaa540303807008801040529650a0030410a512032500d503119503003410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 465879838 1250 465878588 465878657
    0x121110409050d05041503020301080a06150b120a0c020c0d0f030e0d061a03123f010f050906090a0b0111010e0c040509010c0918020d02040b0702030d090303 69
    0x300d159601402c050704203c0d240b011403408241881841c501c000000865001c03454218210361416003995aa08040d400141003144d80f402c42c100c0b11070842d14030802400c4240300390303a0b603a81101c41c8503940080440d1032261a83c80c000000201a201050800308040e000b00b0a02c081c83d0300b922049003501c03100d08100c0c14440c5001070031403d0703101c0401c07080301e8502a090014009072045000f5a600b191405428480c0d08a68191100d161082042d140c42d01e145420300c4010f9039070b111302610342a004c04140c00d14940d44445110030700302e194408074140c400000910030800d9503001440081c0a0684d00c0651041c0b442e400584608450340c06208460070514211200c15446c14034582100c11009044056400442d2062124181401155082100500200f10003d401000204003501c2805140e41904032a89a03030240300054058808225984408655655666411b00b2981d485510124002d000b9440c55030f01007405100c0020840307806440b40748003009100546c61250344000c074200c1112 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 465881088 1250 465879838 465879851
    0xe01080303041b09140a050601020601271d030405030f030a090e0c12040302240f070305060604080708010c080f0f010312051b011508060106050a0819090b060901211104 74
    0xc110383c001c0d403545e441e517801c80712443d08009208205440d802401c09042d584500010495084542c882801e4401009609107a00d480300c1c2c0e907080500303117581c141c0500200308030320300c41842e00200081007242c00c00c07011526054590120f2540328011039020b403000c52800031080100c511300c4c500d0564440766402c516031a280110403154400c2d94107907800d6005030710900e140c1120100a80d807403603282003152103c51061808880c440e12400004210703208140e101c5012440c1a00e80070141c40c007030b01d00c00d400d0351807140c2c031850040d0081604400e01d8001800c0d1030302088286c81100000c501072540301c038011140740c0c2036441b0400c4030704840c0050f0b401c01c5401c00c06000d5802d4403240c50440140c082002082104001d21100340c0c00000743c00961041d003101004100c000e400c001114200c56460424503503070340d100e42014405215060f070300d4071428140b0701403504200ea8540051b215034011100403a150b40c94482c4220021507480300c44c1d070b03140e0b020340303890000c10102c502c0c40006150040010880 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 465882338 1250 465881088 465881099
    0x150c0c08010f0504120504030803220c0602060718051c05030405040f0e210a0f0216080d1e0905090408040308041d0601030b0d02060304050106081b0301060e01080303041b 75
    0x3125201101c0071401c5a960b400e01c802c00642c04c030401283d642da460401d080600310b840e5500180700252000e41c450bc211001140c0b086c00c2c032100d5003e15500038007039847c0d40d69142c2e4081e441703000488000f40040c540c400c200c8805e81d020366440c81507603005091030385514241d21004180041407402519a8401032000044942e2180142ca1445407082004686002001c19075850b00c88491020491100390984074210001403d01707540343e2072030619000c0b0501002c030000340c1c201510305a090101d0440c2c41400720fa921400030b81941d40f1456940c4e01c140a54042c1070807004002d0b04030307641000403d4040300700110b10b40418099000360080342954030f4103a0307940d50805544d12640c401003a03c505941e21031600449103c0380da5001e003080c01c0510025a1034400140c42402500d4000e2244002001050074000c0940c002c801034150740c81200c41a1111400d0032038800c5000f142c00d0701c290f0801c0303070114001d10106082c0e030485402a00450541d1a80c0c0d407890f088503101d0751482b006802a013000240d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 465883588 1250 465882338 465882341
    0x10306051b0c0304180501050f061b0d0509030c010f020601060509060c0a0303150b03060f010309060f05040b09100e0706050a120207030906030e0a020a0308090102010905010504050c09010807150c0c0801 89
    0x724800400110742d105c1c50b01c062150b03e00398150074444440e00d0b0034010011606e4800d08045907140c100d55113691586c904038248079805056051501c14440c5150864a00340c0010040188250482c2100c0d840b940100044881c0d0882c17614020058100300c00401c1514003030301c05071074804802440103040c4070820031024986030036034000340d0000c1e44421031003000041451903000031b82001c40c41c0e240356140c840040345506c0c603101d1241d81055a9031040c101440001d510000103c06030340030134025800c00e410030040c00c01007550224098002c410482060900a1140a694107034500c060441d8520f0706030140c5581d0008131a82d014070092102c0e0042c000e0807032000b09002c6203e0f8850303091031824094001c0c101da04015803a420b96120400b0040583d0b0b0b000039500c120390f4040d001c01d94444c0324600407409404004002071156003054184001c0001c04900d40d2095902504c0c0c0a81c60703030b40e8400e055900c01c8548141d00d0407035000d200310804036200d4141003c9543c06411041070080d650100c0030b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 465884838 1250 465883588 465883597
    0x6240d060329011208180f18092415010c0c35060f0a1104060804060e57012709090203161503060f0e010306051b 50
    0x120300c0100d18040d070b01514101c02039180541140300101940780056074440d4014406e9280389240707045c05e503440b640d0700d58452501401440340a0108042038555924a105243c0242c031070741500d00880400ca140300c95860310b0a041011595401d40940e10b035072002d10b01c140c8192440504002300b0030200b10101d10210010002010750702132a18403800c00a200030800b546050031003040000601d07804060780e10002d10103420010840e1070840f20340320075580390000d1000c880200c03c2c208020400040321900301540070700c1140901c109100600c41c0c19240c0e40c49141c0411b04c032060010010010401401740110207008054074880401c64101c5c00201c0741406000c1d40d088104103107900803985065a2207080c400b01500d05048058540b40f404004e80c0307042c0028005c0d51512a9120ba150055607410003030840d011a1124011101036280c483c00c00f03850701c21603d404042800d203000000c50f0251103290b40222400e85602c0440d80e42035903140f00c0900340c080c003401a8074002a0302042c400e4070f00070091 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 465886088 1250 465884838 465884873
    0x60c13030807020301090f0524130303020c0109020310020a090b0f0a0807020309030601030605070e010c0327050d0f0201081806040303050a022208300a1707120506240d0603 76
    0x30a00c2501d000305030b140d52a074004c0c0036940c2e142c0c06401d200202b20008042c074141ca5143c1009030f120103a603240300340108001030000e0350511601008204442807940100448111503940102c0b094649520011510500803821502c0c04204a000d4a01e44600600c40c0c00030910b1054914181c503240010b0703c2c10030281c0094450713503914020300002c580c2207480c0710311008082c01d003585030030441c0d1005040e8000c10480300b40d49c68803985808420244880018015003070042c0800700401050514034842015004102d010803031000101e04002d080103103028003035516030300a0685a4a0303a4048020304405000d040d501030302030121540c103008000c2e8040500c0303845403540d40c2851400300018606216500f00705420662100803c41403000d0009002040e10041d1480365100f035801011100004440c5204007590a0142400050340d400007070003807020310910003400940c42e14810485460303119600c0d0052a004059014400e61b008005401c04002c1e140b80080c0f003a0340e0ba11114101940d2038001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 465887338 1250 465886088 465886093
    0xf0f0d08040914090607020d0e010203070503070c0906080a050304030201140904020c0a06050a0c02122206022407170a0b031f06140102070909080405040608030903060c13030807020301090f05 84
    0x9403daa42200b0795942c0c0c0720301060002c1c0039a04202401070746828401e01d40c4001c2000380600c403030840e4020000c88004540c4807003202d65440352411b005100384614013441d02428241940050381c028009035502e50160000050340c03405166500540d40003010040d0088000414000300c0000e81d00ca1024028201c00c107805080c111059142005c00c0701c3c001001e040000f480c062030040d65903800a01184003240410020769142d54a980072601690300100304558109542c0300450016400705104020100ca42500c080c80d15602c000c4614056048982c040000c110306011801803440070b40d0540c1012071142e0006803442e100000c41d0034008a12000d810020410348124042e141d58400c14000302511407a4544943c00c0e200001e4449002c1e21420100d5074a40075548240074500040f00c0c010013005008100642e034500000d900d91700140d804510a010301d02c0007480041290044400000f8901d0b5460312450459550070555005244266003540d620322002300069540c0d00c4441e43c0c1c9008500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 465888588 1250 465887338 465887351
    0xf08190f0e1204080a11040f050106170903040b1206040e100b010e090606041829131b20060c0316021f020a030e120a030606020105060f0f0d080409 65
    0x2d25103081400100c48201041200308081a404502401c02c503a020400c4a0380c031518000280240418581200e2020f1605000140c00e6800070100d1660030b00300c121102c00741d9182030303000c0d459004a216554210408000c2c80e10304d41102c03800143d1008009000082e110341801809103041d03044e80d03a1040e038a0b52000e807080150382120889824090840b10942140350103c01b2800c0b900440c450709108107120302c031a0f424403810360002c00d1f8051071074050131103400030128116480e070001301c5914000e03400619114040c5816020380d50310480078115032407a121a03c4070407280401000356001c0c0e60300b00103120344c0c49800c0c18030078036000e002c50301106512410001800c1e00202c9003600f030101035603c502c88550484503205c844905508c80701c07500685070010184250090142a150040070f40240400e001080d007480d0f02800d4188500d58040048a8035410241c1c201d03407081c1e59683e40b19980445180070b51810340001c503610340029012101c403025907600d88105410039008020010389071407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 465889838 1250 465888588 465888611
    0x51e010b22050f040504021201090807031412010509100f0806100602030705070605160b0703050a0f0b150706060b1605010c030c1e0207080f03031f060f08190f 70
    0xa00d07000780d2448100d03405028a1900c1d00103401c411000348014000ca484000140c20740da91044c2100128410200a00c007070f90880c44c03c0301c0d40380d2080000728003140c135445c80802210310000c203440740c034001900404040d07402c1004020a05c2c40052140e000410589070208803041e042149000405003d07008200303c0c00c05074021600490244c0003401158018003806000c030f58001840e2044603114181550303140007420240202c400e003a0006058080e0300300602148943c1581700c584540070441e07042055801c00101282030350155981c0300d50101b2561071521080300c14900412405114040000d1010303900c0512480325000025001c1c142600025100c0900100303000c0d4405000f40f510341007084042c034500142504020348400131194007014803a010050007045494041c0c186e480440b6200420301c2855641c0340c4c82103940701850360b080800e034812151002c410302c0031344440340c403000306142040c1012905050010016039117202188044a03440d40300d0300c18814030440150303000c209050b081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 465891088 1250 465889838 465889867
    0x2708030a060e0112140330090114010603020d0b10050a0908010b030a0318030614090601060e0d060903020a15020c0c030304050913050a0b010303030e010e0a03050a0c0201030b0406090902010f0f0c06051e010b 91
    0x3400440035034140540c40d4a0010404910be043d2107141c10016103902030640214020141004000c2d001059034608484c0c0e90707001406450403150070f542e801c49403a2514221421307102404012505503011003400030000e03000d4010005d4604107a038130146016030fa41c4a11044d6020400c1b0607245101130014048ca426041c8001805041141003c0c0c0c2d8a040800105040e11441040600307035a9aa1146208141c0309000802e1640d0704198440c086040c401d9000009502c89080080180b29901016001e404c021050b242101d0340100003000c1c6c0d41d00d8999040c81c44880c0f400c200d07880e0080300c81c42000200301000e998041c5020342e0b000110344601c000501d013110400d25080805034045010710300040d0348203088032030080d42440d05075941e02951005070050503040c0e900585c4a4100b55011500b40000d610840300c090007641d504a1a9180020a440b200c000d228030500103041401004017103001b80d04a141c00a22807020310501103561140010003800a03001504401000034402c801d86280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 465892338 1250 465891088 465891091
    0x5010504060903171012020409050f0303011e120f0c0905070206070f030e1f1103040f0611120105061e0d0c02011a132708030a060e0112140330 63
    0x3401c2c5540d929003030440340080017030828400c5101c13400d0030052130000c6480303d401c0107010f03d034084216000400140d21b86502c3e50024000c041e030001e08100300b6058242c103482440304a03018090380e4180588a80ca9944000c4141e1a091350744c0e051304140001c99030490301c1201c0c413a012907401341020b401c2c400001048000b001009104043c00e1140f414013283c0045152100a84d001c034004400803c80800c24001d4a840448038041803404000c01090103200c0e68448581031040e8003c100000a203501910030740141040340d010001d4050041c072580c280303200100200358101d1040e1075800a041e00f5603280b9130040c1542e08200d0303140e24441400a8090180e01801450079640003803081b02e980110b0960364009407880419526a078a4054440303d03c04812012090424035003c0a180e9050180070742e841034484546240c90880c000950814101c1d01d00e05a40a0f2180104030081d2900c9031581c249807911101c40c640410052840b0158404492003a84c1810407000100420307540c0382940103010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 465893588 1250 465892338 465892367
    0xb040201080a0c05121012030206090d090807030807050c09130c0515272707031104030209060f0a0810050c191409090f190903020c060d0905010504060903 68
    0x2802a0301c1d403c1908002550000080c400a4406583d00d880d091003000341150311000055442e0070044060644c04920702e4410210700c0100c60b000c543c1402c046503c00c03042d110b070354443d410030314007031000861040c0288502801141282d0354946d0140c0002c04801050b183c40d007058410519100411142c0c081540c01000b084034044051200860030640302c3c442c51010204140c4003481043c100ca02c00c2c5903082607520007401c2132025002c10f00780c90700109540c15415050151060008452a20034054000c012901d1122142010318613400d001c40844041c2c6020303840619940c2d41c003031544517460030790b0090440740010440402d01c00b07038000844030040d0171202d000c40704104a002c2d2000e01c03107a00d500c0e030409181c2124082c0950403e4000c5004401c4401c0c3e012a0150600181403a11280036000b09503014501c4208070300800c40b0000c03138810000003009070f08840243c0d0310354074041001d0503008007400340100b4130b91941e545250171190100c6003150000c0e95088928140742c1c0c4090384008142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 465894838 1250 465893588 465893591
    0xc03042c09030d0f09050105090114010e04080d0923031c02040b030f04081902030909010b090a03030806131d1608060f0604020f0304030903030806010201110d270b040201080a 77
    0x40000e10a900c0f44500e048002080d82c07134031020f041101481d404024500d800400030421804d0031040d040c00f0b032811148842c108038105001040544c450302105001d82d500118507840c000f4510300c0903001d0204c0103020384101c40b00300616180c602d00520040c0508102c100515501c49152108240d1410b031a00707004c00207071042c0020b129103203040007100d0f0003503600000000301d99a285480c644610440035020680100003402c03c01040d0000007400c065002210300391520707070b00c580403800140142c04076940c1c001c0e640312082010030300880cc03050b000704016103c018030070041c60108050720070004d2030440c144441141200e03691400e1101c2c505801200d40500b080602c1c0c40500756484070302604c0f01020310b04d082c0100329244e80359030440e02842000010305490340b8080c1009403200714584420f4001c1284040051010b6106105450324070b540c0e0040117091000342d0318002c0c001e0000310040c100780303003030b2640c440b5014241050b400001482545040414038040c8001800340720050402001203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 465896088 1250 465894838 465894841
    0x40f151a040b0409080a0806130b030d110f1f0b0a0f140f040e060f0718030f14011b02010b031603110a0302060307121503030f140c03042c 61
    0x15a9000e6503a0310414048030003050619200300003a00500c01ca2100511100c00001d00c000c5968200e40c0c0c1178070415085401d02e0150442c4074801e400d841e101c054581c3c1c190031140b0744420744d9000d00500030500c100f400445085006d10301c0c0c0d9a162032010b1200c14017003d09000c181d080301600c2d004070300440b10151090701c90039141860148010300203025421301e5194201c11136a40b0340310030305841d0300540003c000303003c0b2100701e0004585800741541c0e20a901c080c1d610000b90150b001e510b031110110344402482041c0c4e071964540c000f0413084040d08440c411260607083ca151003090180c1015411844000d00d0829017103031019084a54070101c4038020b40210f6505036110401038031600449401102d40040302104400050610303d1680009500060101c144400c00303500031011271080b86140c4041001194100e00c0903402402803100400040240c182000145d200d10851002026003040650800c50152140750440c2c00c29080300c940c640154280c038240c10604a042c8900c1d50400039122401d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 465897338 1250 465896088 465896111
    0xc030c190509070509031c020615150d1407020606010207150f080712060608150f0a03061107050706020a0201170f0a05060607050a0803041713090f02040905040f15 72
    0x12100a11581c1e10500b003a400242025006004540d0000703001070543d800800150000400c28201c070510000502c58100051110507403540410131000e4024050200b100000080b104c283e40070b28100c3e206075460341001c4010740b01410b8050300402458010702400c0c0360102c00249065030950011003402111200c1c4603000d40c00c81d64841070f41c0c41629007a1580e036140002075601400850070055028644030f00010800e502c10340090051454140c28142c2c5400d40c820404186501d405003030348241034134010000641150701c101001c07001e210945040c9440c50300c0362400d04c004c992041c0c000d6001000944115039005402da0000c0002203045511801c0c24554600980300080001c01e0055888001c58505e9441c1010794200940c400c0071034440180500d0040c96035002900c08a4145801e0060440b515944d0390035281e00c043c140f10241c074500c1c40c0c105080080c0489483c0505070950804c0301041000c490300031117105501540b003e07110141e1620303004200d00070120707852840038500f8050403034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 465898588 1250 465897338 465897379
    0x8011a04180b1507120c0309030f143d14010306140c0a05030a090302070512010e070f0503060a11090607030f1403150f0303130807060e1c0807060b060c0c030c 70
    0x1407070f1701d245850f440e461071078502503400d0380941d00043c00d815107100d41d5004210760340b0610103072801c5400c1543c2d03000103540203404400805c0810150b50101c4040096400101c8000d1300f1408140303801c0100e14900c00d511401400d8000780c0040d00d215446405144400c10941c10031070704600350f407040c01d292001c103103001800ca002c00b1f4000038000da1240c08070003c1c980f08004540140c140142031005413100c0701c94150003880c00060007c850b0050040001e00494000c0c181403c40317401901515642e610030b05920000d140d82e84451000c0f54084c000000d940d110b002c090011319110751030380300106d81c14050241a007900c01c00340c07100c800030820800440d019940c0a8000c011401e0340c441a440e0b50410009040d800f5a4001c03100c89a000000003c00c1c040004170881107072615140c145032500850240100300000c01c190030825810390f80441d00260f07040b00280b00c0140284000100f51105400040d00355104030004c061b06e0380301c51503000d02440c060213041c07a800c40842e510210b20110342010070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465899838 1250 465898588 465898613
    0x11040b04090f0f11070308060f03062703070309051809071202011b03080402100c0c0b1b011401210c15110708160e060108011a04180b1507 61
    0x901c16846140d0b005019036143c1102d5560800400700f0700c001040c000410416800c40601500042e07410300201c1c0840c00d08000300105030310040e015144540d507800071803401e055024280e1001000c848500c5d0b08204090001c0c0420743d100356039406403585000104079030b0001040304203001032980418420700810008860088898507001d18401d10160300060703c50101100b090041c2d03803020201141059408000341c0e100341d00c2110305e107078800c450902c2283c1240300c9060040c400c00d1100c43c00d200350551107002c0d0100c480d03054425068060340048071740c04d58818a0f00c00c0100b0290900510030300e043d502011500c0c610094600d204d00110f03480d41c00c00e0740f4180c419130348001c295103818610381d8424000c541086400c1c20443e04550b58801031140e0300c1f021040445e600200c64040400c1001c60898014041c41b03059590351300726401d101175080441ca030007040d03444000382000001000512142c1c0094440c1034864000b55038030426084c00307503180c92480c41240b180820031404c1c00040e40c480340c44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465901088 1250 465899838 465899849
    0x6050609061e010e1c05010c08151903050307110a050618060d0209060403030c03031404120809100e06010f05060301030305040b0705013b010c020a0803090c041d0111040b04 76
    0xc0b054403408500603141198203002c00c0d41c00007070805110300303000c417403002d03c18030107105400070860144019400c0f5103c923802d4403000740032555022820240e2824000d044030740101807001c001402c2e601c0d591517245500982044515010800c0d80c1036103032a1030411040144025100c2d24030b0241c424061f00018808012194170624020031800c560340c1d11503050b41d501030809441165650740320705000d42404150f1008400080c24109072050042d402c02c0010f0003143d2041501089010540081d00d10100041c15000a4458400c1c54400b58080740542c0f8070b9220180d018019a5041c01d03c042000c5040c0d800840c0500e00c10001000042d50040c1228121425119003a03101c01080c07a1084c058541c0345020722440e1202d03502146120300b400c0d440c81a41c50811000548510703a00066400c0e0b03000021b075000540c025100540110311000c00440d8032a0b84407042d00c41c1207550000050031244c10100b2911035412000886500301000d1107421a460760074400c40b801c05162000f914517034801d60182 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465902338 1250 465901088 465901129
    0x61e15040f143d051011010b1801050409170a0f08010806040b06060310050406272d0e0706090312030e060103021002031911120711040203090a080310030605060906 72
    0x30f0420b03407031001c00308041e14006000c1d42e0541c13510304005104003d02c84402d2100d52900c4003400c01403814011300c0744a052100c0c00b85000d81c5c0382004010003001c040d44141e075602d43e4500c900c0c00242c00c0380003d00916410b61620a0244040c040c018107295050300b02180700e50003001400041883d410031b1301d9100f9011221076549a86102c07062035040220b50000d5001410301c400462010b25036021504e84601f141003000d082c807850200320059820608030543c11b00c07000f0074443c03001800d10f07008038400f0b07058000120b1000d00190780c56182c940300b540300d40001443d62000344108060861380620000d00c034501403207600f1400d0301d0f40752122418800248074412510b14210218024000d50380f076017802c1c80007104c3c1d513000c000018044000300c0744a4a614083d02c8020b0114544980070f55202942024000350185202810300000b5807016054901d2881500031302400a09404002c2d8410b10191954030080c0b890b5240120035640c0203040e06129090882c1001125155511181000e50103540b5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465903588 1250 465902338 465902431
    0x10b011103030f0702030408010603050106050f010219330c020105060102071a160b0702060601181202061e04060309060515060d050403120905031209061e15040f14 72
    0x4c01d0349980300ea540075280a500340b05000003481019884141181d40a54160118142c0403004980b80c42d00703c50401e094039901101800480c07c0b501ca809080c1d03105029030f104005103242e2065140c1c42070000c07480c803903403501d5418020b1942801800d400000038001061114101141569005091010300801c0300010500c12079181210070a880c68075088186d155160905000c0292030306070441d90389000c40c04031558000341c0302c108501e40c003c0300c0c0340e100c00c034403070803103d900b082550340c02240c9013000f2122058000005014010080c00144903e440002d2a0065441d0450507664018a5241d07401080c4607070700b89941340e00c01118480b00d100a4001600d83d5185007e4070480c55a049880b45a482c0800c178000300100003004010300d040713450000ca01d0360b803400d182c03030380e1401c08a40294110051048014611131f1050400780c0060b40c89803010340700c4192102040407541400c3d60310007016180d107610130383c1c078102c0c1426070f4110040c86c0074041d8a826140300b6100d0000f50840410360024000b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465904838 1250 465903588 465903601
    0xb1302071115070b22060b030705060307120b1807020706031a130c02101113080d021c030b0904030518090601020c0609031c1821021309140609010b011103030f 70
    0xc4d1021240400440840b17154401e081042c01051820402d6000f441001c40204181c5004801e84c0d00c02c20040e680c440c0d02d0421040700710042c0162100041e00a1400fa039101812014039600d5881526944e004200d86c80c50000c0c01026600080c00111448010740440390087c3c44814110290f6030580501042c02045008105e1030702d28029203103480603140003068444039480d04002d001100b89000b5882d801034613481505d8850020405403030150380801c0c05c1109900c8140381e21452200c0a0800041072103c1202240852004850450001c0c01c00600c1c2115480459540e00d15820706803914011440c207600080d5842150345400707803184801003a0104030b5503081041054001600344003121461954602800c070040c0b03a442501c401040c4000880e82c5002015944603411880f0610383c034440740c0d030702403116030300200c4a6208040d407a241c40d00b001c10200402c4d01541003110000b0000c0345010f00050f400c40701f10200d20390400010742000e84c41d1880000541e600414074840c81501c40e01ca02c23 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465906088 1250 465904838 465904861
    0xb0f010b07110d030e03011a01120e072d0b0d0c08040c06030518010e0c1c03080c07080f0315040c0c2402040323010501051f0e040b1302071115070b 65
    0x74058251b00d58240013070303601d03240003aa0300c800241c5401e8840001070780700c445000d02640c643c2c8502d0462584220307000c2003030000d00550f551215020741011918104d0707589070304403030b440f0f10703003104079000d10000c8d0130301c5c12030850f1041c00c50038109490124481d06080c1d4401c641090f50384906010903480344007090040701c15050004480d101103000b00420303412914500c0e12542d4912035144291203404181c030a000d001083d4000c0c0342c0d45541c81501541d1070401c058480d400c4810155804c25050080b000510306001c0118081e000b80f00c0f11034a480240c0040100792003a0086c410700f0000d18043c0180051a2608041d440c4440c0c9440c288203c1c01c5410700300000e0085070b00141c5400030308840f4184241c400403515400c1d410042c02400b090303803601c00384200032556040d0b40352a82449091200450311441d600d12170700c013004101080c9070410b20f0008181c080701c0d50307424250a0340007840408010320410f40b00b24020003030383e240466442c503030a41c600301d00445101030100c00304200000c401d90b0b42c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465907338 1250 465906088 465906107
    0x19150c0501060b12041502040303050a080705040e191a0a0311030c060a1706030a110103050a090c08030a020f0607020a02010f0207050616050d0c2001020a020405040b0f010b07110d03 80
    0x43c10304403600e500c82d29016004921058405883c141e200e84a2500d200d41c641c022181620b4142e01c80c2458242c801c04200c4094400514080802c10144408035000d2410140a402203004070000c480c00c4443d0f0407090200c452085981c0c055a5100b17440c0002ea4503000e1900c000c894100d07181350144040746000c00e08200300c1d04640b0390300c500c0c0010b007804c040da00080d040341a003a404a10040320ba8400041c50b5840c0001c0001904c0c02c042e21280c0040d542c803d07005140d10061541c000b14540d481a6281460101d10341c02c203070300c0c5410106401c14265410001c61008a440000501041c01c0148000c2c1d11490b640c40301030f040200c25035260700000e00802032240140310142c0426034442403910a4125044c10b0001240c20740200850b01807424400c50759600381030b0304021528004400c04a526585041802c40c0c07a0641c0204a01ea4000d6a250310030503126a0151030542042d2408942201c50307007105800506035000107021003004036050146e0000300c61021707154400c42c41e403541825680c1610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465908588 1250 465907338 465907349
    0x30408010c02010e0d05040513111209010e0f120a08180f0d0f03050609060f04060914040201080c0408071a04210507052b020d020d03020c19150c050106 67
    0x20809440586603055120104450300714090305d510b1560300100301c82912807440744036801414103c100c44041c000d98420324003250300c000d440b4640402221142003841f01218000c049940da03600c083c801140c1840810f24031190070010740030070002100d00595a0180000b000c04205151f8000f50a03040b800c08032440d803180b810102e800355203641016a40e554051a0040d0000c2c2d865036141c050503010b402154080c94004244403010760f1100240704c0e402400d0341086500c95101c0d04002401c01c0144103001c940d10f0401c3c05202c65140500014054a45c05401105100820031041000d031801007500c1c016204c040000300f1404c61804092449401107804c030b1000400018080c80b1051030140510070301d00d208805840c01c4039070b55000c2144c1480c0760003d1000b8032007852422980e40070342c0f01c8408940b52005082c000000c01e90f03004200b6544a246084000d03034019000c0a00c1441c2c101c0d0480d01c0d00c80f902c01c0c19103074282083c0000e40509081503003c410702c040c207000001000000c4d00204d01908 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465909838 1250 465908588 465908591
    0x80f070c08030a0f0311070f0302010b0a06030906060501080915041a07020303070905040605062506050108070306140402010507020103090201021f2408070b13031a040b060102010506031b0303040801 87
    0x98a4401e202d03102e43c4100c0c0c100b000b045200c071003c90b40c107000e80559154698040540c904001e07040d1501c11300284401421001c40d540c03088102026039a505141c13024040310342e8000303000402451f01008980c159000705050085002c1000161800010051a40070a01d10038842940701c038646242200c6e0702c40c0c03402501c214a0f20070045000e6001000c2c5120b141c146d5281c43c0c02d11b90fa04144400c07941c9900415400000800c400d00d208000d5800a00b400315203080039400010007520348108480003a0082402c03608950020410b00001d8042c3c40d000350388034401505d0324101507001034020300c41c500c5d00a041c180c4904415041d617009000c1d568642c205912800400c0700d20307c409c4002824623000301064100c6072038140440440380041c000607900c5500c01011824142111040c0d15001142c03010300c80102c017000480081c902400c288540b000c06030721410142003500d082a070402c1e000301036a04581c94141080810783e000108403854103010501082200c5801c0d000c03900314407581d0001009903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465911088 1250 465909838 465909863
    0x1d0a1a09030d1101050a050c030705180409080c0f1b0f0d020d030306170304030f1106130902030709060c0b0a2c06040c0510051804090501090b0f01050607020d080f07 73
    0xf03030400d19100b02d01c0d02c50301c0200440d036100c59000b0112507096802c2080c4030410300000b41030074007a400510b4414469100f4880a904e05400101566294142140d004902240f0201184420030035072608056000140ca41501c2d4400d04030014450540200d1290303550500d40315880d20744401d03d65074a40c001d0014845038406080280c0034001703621a0a40c6c2d41c600382842c404000b0f000c004e440903070743c2c0708020441c554401d840d511504244c41c4911640441e04200d04031781c0c2c03818008920b001b054024070240e207a1802010241280d11703181e1000d41801060703647c0600150460072450792001c4248000101e2014050341204441d44001c0c81d4542c41c40c2c0250340b20352941002441612592003940101e01c00307074941e0140103c0d6500c06040f10040340b805d00410a02000c1d0787c1c030780c405181002d040014402c0301c0303807985030945100346000c1c0d541410420a01142c140011041c0740500f00580d052484c1c07150543c0400e400c10000c08020b400c003803021540408a00f41581260340c2641c10001045a0b03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465912338 1250 465911088 465911113
    0xa141e0316060b040f0216050d050903031206030c030d08150402161511070819030e19020118170f030a0914120106031a10060905010e0a08070f061d0a1a0903 69
    0xc841ca1000942e07040c4a41000000c27180c1c4154211030704070074041c02450420b00d00c03490000324940c000d01010b626001d000001452511b00700710340300f18145140e0321b0800c1e41c24030107002c4076141210701d0410701650040002030304002580c0700307040041c0c0d80008049035103041b00d107003e002800a00d201444150001860500340180c90f805415101c080c070000c0003203a030541c2030581c11a062004031a415400c4054a0a01803034240303400c5c00c40a00604000607140070180550044000030303046081010071440007801e45881c100140c04060700600011490700900b00005018104540300791080748407564803203e0179440c3c0020072500804c44000034003039161a0320305181800350010402c17a0308980100080e000801007050201107030207036150409400c0c201001101c0550101e100301e80c0000309844001003150003049842c0050841036400d988441c2403100040444044110b040280444140c51201958800d000301046a00d06020302d00904c900320f969060601031840c8141c2d00d4040c2c241e6001e107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465913588 1250 465912338 465912367
    0xc061b0e09010b040303091806030506040c1d0123010c02060f0c061506030c0a0c140601170303090c060a020703080f04090b031c0e01020a141e0316060b040f02 70
    0x406a004507410100e80c1e032240b4815100e406940302c040c00284d0b0110b0100501c14450440c075500303440031080070035600d0712600e80900d0071405603401c03200740c0b040700c0e001c00c01803030168120300d4150007c0310842c5603545042c1011070f4031038100d102c49200300f13181e101c43c0c4041d81c0215990361080c1d902800141e145e0424044031045604204034440042c014100040da000702d200c10b0400c06c00c01c0080c5141d0854940c280c2c11440c540283d18001c0c24071410503404e0020601c1003135044101c28074000103107007035030400380203846501182d00010096482802403042504010a0b521200041070b200c280e10b90321400d1040703183c03810a80c4041c0c12403000043c01a00119110021700076544001c00501520400106050307231211403121040400030b651456030b0b030b114030494013003481c0041407040f2005084281ca481d4108010491203403200d500c0490098034002208102128600d0113002950404038142c20100e520400280028070711555408801f9460751107070711034401c0d90503803201191030340c24500381c40c1c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465914838 1250 465913588 465913607
    0xe09010c08010509100303030f180c03030221090f06091509030c0d030e041d19110405040c140607061803020c060415050d060306020a0512060d0b06010c061b 69
    0xc0040c14090002c103080c140300540d01e00807116552011289480e6880450080911605064880380c4072406108004030100711948803a01680c00c4204281c42c5150192400030078807298019000794000004d409984141074035850f4006840e064160b408050005070184035000900c1e40c891110720b2880003101c40800908141072041d81101d0b88a910b0800304100b0f610801d4000b03000600c001307141b02041c00c040d0001c015680e070869a1040f0f2900141140d030401c00300d209105007540040c4d0f0207200f401040464824510b6040d40c0c100220306150b02d07003a00c00042070051203d084012000d40c0741c04d4946404903240c9941004007002400c06a40301686614444e18040e8011301c1460352801d024039181e41160100c950234002c0e0030303240c0072612054801d5084440f01d01c4180d9074072800003001c14214001031018000c10380d10380baa150130700301000207901130142006000b000e40406003000200c14095040d001030003400c040c4194101454480c01403c2143d88540620580c0f070351908500b600720749200f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465916088 1250 465914838 465914861
    0x13021c06060912031209060c0c17090f010c080d0911091b0412081306020d140a02060c07140715110c0a14150a09030b0c0319020903070e0901 62
    0x1030260903034400046958012a01070481d00d42140000900000d02032103840d019407002c00000302e100d07426034981c1c600301c0b01041c0d40d600220b10030301c4400d01000684004140b454110303420303036070501000c00040390340c098005440c14180f01c10407101c81d0a00c41060b0940f01c00101d0b035081480a8142d0b860010001d440b41c002050040700041c01054000300041c28141710406034070b8a803800d042c9040c041140115980000b81c400038810005194040307041c190800c05070450b038000300815031019100400060321200d00c514040c0e030a00812010170760108040350042402103003251518101d0500504005003460303680c0f6144204640050348200c084050b410800f20340c0c80e00c5400860f84421140c031038905c24451980446003e0f014817813404843e090400c0400060210880500d00040c200303040e0303110354041d20200e2401002001004200241c0c5a400b075031182c011421424068001194002e800ca03d0072805900820b0000d80303a00c040120300d00802040b0050651404d0440842e0700801440000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465917338 1250 465916088 465916091
    0x1091409070c1b170c031b0d06112d090103151d0712020705071511030301080f1b010507060b040e0706030b180c04060804030203040504020f0a1106010b090d0213021c 73
    0x185001101d0201d4659160400070307000c3c010120401148001c005d030303d142929401040c80c50303248041002403288990580340031500a07512849800c042070702f0880103081c000d030041e810154a0f030b041d44880a0354030000382800c0105103408a130702450707003642440c1c001801c0c41848003014801d00203846092401840e4a440d009581120301044000703a201300540500181d2011004118091003500b500d40c42c510246800f4249920000342642150702c00c0e40305101d00d034804685c00d10300380c505015031030310051070146010a51101c41d0010b041c6000b45240501003540d14070302c00c1c900d61035540024940e4060b080c15107600d00e44416014005060b06185540600041807114604000844019010307440540200d07040600d0900c08640c8001e00a0084045010a010000307150300c540c0060728080201169042c0c070b40c86115001003049100c208841d142d076010308010040050348908466080c00700f6100000c881d26580003040b8880014180030303044e035100081c0c1c0d1481000d0307408841c1400203081030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465918588 1250 465917338 465917369
    0xf07080a0f030203010f030201080c0c010e0703030816090b210106021f060e040210110d0503072d0c05150103030c02030f0d02030307081e09011a01091409070c1b 71
    0x7021400c901007400f80d5000100241c8041c070156014540c6103501441c908111881c0c1140811082d00351040e400004a20b5400b4078400e204240d000340c80564455250f40d02a0741040b8165002046887c070303449a1802d810001410604c0c60a10540f410707000400c5020b22851540e40e11402542c5810211240400c5951903000607100302560080000701c4d40f0f1a484030126444503001c00004074803d9103054180615500802c16800c410700580c12042240d41b586a128a8450800742801c40d10280c860011107064182c0e4410030f0380583c0e583c0b0159001d1801c200d6410305890810710f403008421111420030311003c000401c056000c0c240482e1030303100350192501c614000503c1c2d0350300c40e407002004002d80c20500000d11003a100742034242d44031403080c20303180180c0700c45041d061040d6410744090b0a180d44418034401300683d4207140400034902860269441c40c5040c0c221180f10480e00c0e100b0388a03440d40408030300a18424044031102d2398110000d0041e0041032100a00c03104001d12401020103500c50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465919838 1250 465918588 465918617
    0x608071722030f0f0c02060a140706090b15030102120103110d05010e0304090c0503070c0b130b0a1a01020a0b04060c021203070c0c0b0306130e030c030d090614040f06110f07080a 78
    0x1c171762010703502910160031310a85240544103c0e02200c0d40c00581d003000d020b0707140418420f0250101442c01401c10400506044800300a202a5401814040d17070042040741000194440606d0440360000d8500f840704941e0400149051001c00010340503608207002090329100100c002d0041751111802000380d10345228040d24035000481e01e820202c4d0354600b05902095150081d80d07403140401c0603152035a02c482e40c0c2e40c065180d050f505011565034600801f8040f4200741400b00c5480e009000a081520440d5220400d83d00300030402024207840d4119440240e0007045039030154102070014036124646104011b0106040900c15103061400ba45d00051040700a8222030003034001038a031054070060003200602410302411032014a120400404006030340a1014000789a81c0a40101d000c2c0a02d003000b1003680e50841c04681c0b02d082030024880001d10110305171074041d0380410082040c924101c41e000003402140300c40f2401a00001d0600c04024084000308110045d903151880540d0184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465921088 1250 465919838 465919847
    0x537020d1a0d03080c131a0a0e04060803040501110106090e03210c04060e0f0901060908160e13030318030338190b0f03010f0608071722030f0f 63
    0x94000b60110341682c0c0407612010006000340341d26042d004480500d10b40c1d80c40580d01f0f4003d201803a07559604c001c143d4a00031039002c0314400c0035800c00c070703400d000180c2400381042c0c0700e01c41c41c401c15050081e5400003590031a03003900090010504107100708020200c0720704c096200d61145080e8441144480071030000318181c054441c1c003a502401441c0e0825040c0081628031403041c401071a44000e41c1c0301e00703509940d1021040350103401e42c1c2d1350f2084241d00c2c1004031807405c644540b4140391013109610510101824821080e80004000c00750040542207040613001407451a14141c100c080d0010403400740b6415410038001010f5200d19040040c8841090ba044e070360110740040d406400365183d2508500e07219540d00410540303111a0204a42e03104650303c501c2d441041008000c003c0400104400005051014000d000c9810401914074201c3c40c01440b1111029800015025640110300c000050100c60309040c01f0841299800020f14100034028645010f00b181c0060200c0711245a0540704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465922338 1250 465921088 465921109
    0x230a02010f050c060f070201090b150114030c1206061207031b08090604082113020108060315010302040c050d02070506040b07050412060203091f1b030537020d1a 71
    0x620b0184c44a622010006001400d002e000f030f004542d02e8000b124041400d07203034050f02520307607442d810403044c0890001601040708100002c0190005104219840d01d54000300da085490b902d80054007036a80e032001500c1400303421040076541c070f003034030400260a4040d4008203c41510000c0448a0010080102c0d40380200f10303900b80c542e80160003c039000810b40406402c10002d880f83d5800001030344205451540c604032000040ea0884085c2034040d07582040560350424400e8001e03125a402035070040360f8281041c030000780229a20680306202d14440c1080d00c500d1800048259903039107241c20300555890040c0c0b820343d01f00464501081d04a40510101d80407035600c4101d20419641c5612054025040202143c0b82405192480e03441a078103c1071600f000b541203c800140611031192a444691045400c50285842d0209101407550344001c80c201c001d0400c840403000e0b49101c0090950303400c000d043c85501c41e001040010042a041d0041c140c0506115201c0c1102c1006c1c0e42003162920b038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465923588 1250 465922338 465922357
    0xa11030103031b111221030105030a11241305011e0c1103061810020403030c02221b02060906041214040b0f0c010c0905010206070309230a02010f05 65
    0xc20494081540c0640d0080d08040390207940c8418804800030f000c0380c0345c408880005405a0070241c0483c07244d00380406410341410446081c1ca0656040c880271036030300c0c036408001a11001c01980402520742e112901e01c020222515601e4001e48030000c9010980c0c0c00950b88900398040244010941c0e511131500d03000798203c003014010b80e03201611070560340d14040c1c7c030003941c01e11f5403400004a5600c0810015000d85c03464031403410f610b4100c0e40c10904103566150b01d03884050040100f080440d138800700300d407280c03a01143d107100e071000c030b922401c4514414403d01000440c04c1c007460701d13106402d01909000340121502922144d41e6552170254031894100e40c014001c58500c1d546101152080401d26603841820004928281d2104241021500301240da0b00d1400070018001c41c03080420f0103490081030355403c3c807001260501c00040e440759001001c103010103030b80d00410b1040c0048210701000300e12294812000f0098200311140d1201c21408050340402c204d5a80040803901c184c0072659100d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465924838 1250 465923588 465923597
    0xc150f050702012003310f050f01090c0308390d020a020a0b0306010516210c0c0e1308220e09060106120b030d080403020607050705070905040c1502060a1103010303 72
    0x241c0d4861446e8002c1e0b0141080c8800020180102d64005816039011203130601405911800da00070b49061450b041101c5c0b84d0020f56410202c0303520014070419a2102a40d80c802041c5890380c5540071500c00d02d050ba00b442603a11195514601190306080c41c1004400106405440702412501c10981e079a021000c0025000b1503451802c012000b145d0024503004201454080d142c800400f00b010a0280118015035280f070301140350750b00b14500319004140c03078a0941450350602d1032030380703c802d690041441034107407698118000410480c0c125504540e000d0340840c0136501c5024201220340000b03103030099410f2407200e0b42c1c2c2c0407c104140700f070014403628410300113164980c240300b001c481c02c0c110000d690404940300c0c0d5a600e00c039501070041d00b444a06d19907502801e8540303801e0083c42c01c2000350002c401e00400f080140c0109034003040900580300c0c000c1001ca030381d440e2032409854040c0192700c6400b043c1d2105015031042540802c000380204104181809200e81d100c101030b407548028480100800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465926088 1250 465924838 465924841
    0x9090102090109150c1a160f050d0e1c1707053a06080a020a170706080c09030a0302060708330d061a030609010e060402010c150f050702012003 63
    0x340348202542608004c145411140040542d890268006410481d2480342c1040740410100229202c400f603100407441c580171400c6002e9202c081c0080c4181c0940c50182604c4560304605020104070140340041000d41ca464a440900c200503c080d4040502ca52081e07201c40125441610030410b40b40c1c020500d811651f0300c00d0032000052409041124000700700c0314a484e11001101e840c1c41800003c00c50000600013242d8107104001d01c115403508140e6070401a510007a165603000503011003034508c0c508090039152981c950901642c0900116643e0510441c03100f003041681c007040440c05910303140c50389821602d81c008a400054400c010101041714011440c01012050b4080102514009040c00714268400d40350401515071030441441d04540c1d28040c90410f00b8100f091503400403d690080049801c14082c89071900405800a410425810700072018400400709515590141403810000c00c1103008a050140404440140165207801c603000d03200001000d0b00d8004020284886255 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465927338 1250 465926088 465926099
    0xc0d030207120c050904060209040c03140a0c0c080a05040e0907060807200a050106051302251b060c1416060f050c060405012705030d020304110d030e09090102090109 73
    0x7400000300b00380e811400040d000142c07904c601c0c4074280680c4c000e01c0003690b694028070511060b5a20103028200f014942615074032402440030205070000102c43c3c01080c01060320004030f90800c680c40f4050100700000403a0305006030008001e0003124403516404005c0d94480b003006840b003105106142c041a04580007840d124495206a805819802200721140740c0020003586003000c03c040071203680e035403a00c091200f4070701054403400001c4061029490038081c6030a008400c6040a508200402d021000360100700c8101300320ba80000402e0500b0bd50955181001004400c200405403822000640702c100c107110085105520707142104c0303054041c685070540c02c4680d00da40c81004000c02c07a081c031902100300c00c1481514044c60050002056040603060324402c110401c0c8100c2101d0203048500900040300803041e542002da0100c4016103d59075414100348280401c0b560b25030001001c6c0952082682081c1c41103034190003900c00034020b90b900d0380301a0803031103101c0b405d502146d00310104100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465928588 1250 465927338 465927359
    0x70f09050a110f092e03051b2109010b0d12140c1b06191d03010b090a090303140a090b07050307020c0f0a080303070f030c090e060f0a0503070602010b01020c0d030207 73
    0x401c5025410310080341049000001d00c440036a1052000107903d41c0b0030f00200001c4202300880d0108012862403801042949120f550240843c1a000240100d8001209410203500c50780d1018030280404e8100210352525440a10141e20103001160640060902c01d401400568403246010741c000e00c0c10b145080781c60b203001c500102c4410303407008d010084808080114080c000181145844022240040365030121107491910039280c0030760b01d03160021041d81d51b507280168220321000c41c0083c00001d05d0404070007400d0480c0020170303403040140038070101e01e0b001c2c0c3c809150b050160500c2801611541012075103403209917104001a44041e00c82c04040c5014100c03a46510340003040b21140030398511909003036810485081000c2849098061140303500b50080201030141c500d0160900b0342081c909850503500030f0034450103148488101840e0f80c4890341c100014102c0101255651595500000d000c0d1200c60605030050084134002402e42c03d050b034140c2c260a5040c4c002d00b091908026080303d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465929838 1250 465928588 465928609
    0x90803030f0a02070609060c030608120a02060103120c0c140117040c06051b07030309030b10030507170c150301060e030a05190816030c3e03070f09050a110f09 70
    0x55407543da0b0041b4000192031032003941c80b1041c003a02c01003070492030710301c10a08124503804d004180175004c22000314042d40c045100c0c2e0543c0c2c0e0240c2c15020038084136208481004c1c2d4110001c022104959001c02c540300d1240c0000c09084003641c509243c0e003034580340c5148110041c2d5006007540106241801698007400141000b14000c2c0c107210600210708200380c3c50882c0b80ea00c02d074003103100d885043c001c1c480d10010381d81d8448901c08040301c1c00c1d071030340d983c080c0e9800151058100303081f800c204c403588241d030510130340c1075035140108020b01e034400131203008545500a02c580703804103400d000b4001403810080b41381034910b900300010b443c1e52900c070480107031140d154000071200140208030a2103070b0a000a0090042c42c06503498001035102c2d45480c603003075081080c21002c000010322507150000c20004c85a4040110007403440c111025850210b46000c10a400c9140100c2c820507011481c1100342c1d00981c0308503514502480302c0500107081910034400c0360301c5022030100411000256040c03005108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465931088 1250 465929838 465929843
    0x30b07030f2f21040b07080c07150b12060718050114121e04290112030f03111815092107091e06060201060f06320703090803030f0a0207 60
    0x1041200f40c106140b030045001c039000c0319032030080c0701802440c6901404082e071020780d00c080c040c0f5209040e102e1004060084400d015519124a80a000c1c0d4907031001003503515101c0c00031901d0358240030b00082c0105900703486040ba06261700c02c001449600c2508021140b82d03030548541c3c60046010141b1003400e10007440178864222440d68402c1d1302c0b20680000744964040d200081e400e1543c0c0d4581c0140d5040c0500e0b80045d000d542006115000e1401d1040c0b107000c0c1d0504004898980c001400e80284c151800310b00c0f460741011404190b01494a5103812411800b240c176040341307032001d50444000c0d0003081500e6411090380750001701401d007448080e030000c030004000ca0784000d0b5580342d100191408114401300340a803103045640000018084c55000e40010f00080c02803d00308240a0400348503481154204500c403c1d0819604030408109103851800c04140e0000c10f40740841c0c1c4070198000700f01100007075aa1080054402004010381e07015202e40200c10203584c9071007080c50069003081109 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465932338 1250 465931088 465931117
    0xb090307030f0803040303050c03100e0402011e1d04020309061f09020a090302040f0603050c06090a0806010f0609140906040207050115030b09070603021c15030b07030f2f 75
    0x440403907002e010000c0080e1007056116544d15107854004d040c0c400140c00d40032038140a0050001c41d4001c2040b0000307480c605174103c03d2660352800100c1e43e020079031030032501030101070044844240c1c2c0041c800c4442c140014241034103c80c444140070072403004940710061a0052800b0a40400c07400382d80741c0480e0141001702d0f01227500c0360f0020003282d000b04043c0d008188810020070441c1010702600d082c40360007480400c0340616545407161902240b1030b0040c071801c00081c569210f0340d1400144d9001e800c00c001121469a1552051034100d55107014080100340966800101c4040201049610b0b0602421692182e1680c07400d010103074000b24402c03101e079502c50030701c031105001242a0360015809500001401d051201800742801900d400480400d8010050200403c030700140f0346070011103044000410318003030028100125001c1c1c0008003030006000030302c07000550541040d0011040b92404007c0b1000801e60304402e0000c80140e54031068246001108106500d03000d4034100c1c070340380e80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465933588 1250 465932338 465932353
    0x121005041a1006030506041a040c0512040c080f0712080a03110c0d030c0e0603060f150703110c040e0a0b04051009051c020703020d060c0c0f0b041403040605040b0903 73
    0x55051040202c90404000000c20002c20525500d802015048841501c04000e8041709410204040f143c000e0b10714011074498191a06441c07046040b20b880004070f515402490030207107800c1007480140d104014072445168501002c40c0700220b951011644201c0381d4022001c026502d0024940291113480c0616596004041280071400d000784120040c441c080d003148440558040d08035501c061107003040003a040c0c0c11810703076200c841c2220380080b0112000c03808141400d00040c4002c480b000c42c5090108045070103420550001d0301d03140c0400221017500d1741c2e400c0c54000d1000301d460201c0100c00b20b511007080c00e0041000c2c161050f41041c007030b08c29600c032004c4001e02403081c2e03040300b0700031100d541c0411040d031168a1002c4080d48000450b1028107620383c5103030001011007050200c0038110b103a580c510490394a000d94920100690b00c0180814006e40b181400922242d040b079050360702e9900244000b08110000c4111400d445003501d07003a08007401c2c10350005680d00040021a010b228000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465934838 1250 465933588 465933623
    0x112031704050d090611030f0d0e0a0b04030306080a0807080307090825152109060c0e09061f050a0e030304081e070609120609060e01020d0b12100504 66
    0x26001c0c8514000c00003404800c80204000f88403070b4007030344003034100903400348016600d81012048480340400009a9500c40303c01004940051980c01407299240c4074101c0c0710b0003004040b0001300c0c4158041d480400c001d507520041681c444810b002c0051502c1c0b020041c100001e03070f28001035a00555186001015107032101c415514054041014404603034100040a28540700402445e02611844140180000c0c15523005400c590181014402c0003580040c1d000100c0d60507400505102d42042003403056049524003c0e05e88000c11001034080d01e0302c000000d003941000740400300903408400500b00041e0224900321500d0b082074241b1802c01c05d00c040c2e21050307541c04201400c047c02000700601006940c6040200c00044003612945440e00070820070810035410200f207108403a09546070170022081031805c0340040041c1c0000809007843d01c40c4001c10300c803055000d0030304024030360740c208100005001000200c0e004000c0e0403501e0390052000014052054010580162088000700403c01341003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465936088 1250 465934838 465934877
    0xd0c03030b030a030503011a1e0313051504020f01030c0c020415030b090d020d090b0702060d0b1f030c091a0a02031207030203070e0d022d0406030c05090a06050603011203 75
    0x94002c1d00000c40100041c00800116003a4a00d400c0301082562729140502c042180500c0d01d9035104105210040005580080c41024848940341d000c0191600c4030041c41c000c64040780c0c2502c00768000c01445005038650f50180c440c3c60b50b255001d80326001d01c003400d68200030151080e040c101d903284c5185000040010390707c5042901410041002d89845a482e20000b407800b6100e0171114104441031008105c1c005241c1c048800703264050724013580d121840031050b0043c04062000d070b81c1284a2000300c594400c0c112120300300c102500e075424014004103c90880d840c2c606405041020705510025080004004c0c1c0104203a6190b80107580c14074414001802e4504000c85821002c03036000010000c0c0c483c0e001c0c0c044c010840e0120340e020150f030304907008214101e00035003045842000d14003107000c0541490380d14014641000b40140320060700c81ca003010707401005115850203650501c01085821010b80618400d4500240007141140c1c44c000c0629050000f2900a4080c011140050116200760 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465937338 1250 465936088 465936103
    0x80a0c201b04050c03070f0915020a12020f1e100504140609070b0307080601030e0610030506010b09011e090b040909020f04051009110417011d0309030d0c03030b03 72
    0xc0d0406000380911690304291101c01c035485240c8a50b1a101c02c00c00c0c554411030503240c112016181000090581c540306440600d20394100c0110b5140c4480301518150380001c41d904540d1040110101803004180140d03136580a4485104031394001040780c0603044030641145003420080382c02c545003004210017400403100d050f501a2034040c00a861005042c0041000c1c1c0d41084d2840000d228007032903d203012100303002c00342c070307480802040a0209009a00c41e42003018070f486030805968107030400c00410b00d20b00c10544411202d90080f40c00020b400c880400603210030f401d044c0c5852244c0e07580e004030400301040142d00407080c001d07420000b003003045041d4042e1019100a04d40000e81c0c4a83d07004000c0001011000144a1400c1c442000b002000d07062040c6c1c00c55085120110b15001030240c907441e20300594000b01c80c2900100c85048000ba015003008490340b507034a120920006000c10140d890344107114681b078041e844002e0a041e041d10074800020790502900d800503210b45440c1c0080c3c10060b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465938588 1250 465937338 465937397
    0x3020c0f0a170105160c0b060909010b1305090d03090c0b0318071d0a020304020f1306080307080301030201090f030b1b0c0f0c04050c04050d020f0301091e12030c080a0c 74
    0x10b680c03003048080803a100040350302c0065404c080c2d440120399031f6144814100103044501480307200700451f114050940209842c0390f03004003c40c0d0002e1940700c2d4030004100c116482034442c490f96000d1404c03c2c0c080e21950090607004907640e00020b060810f0081180e001418808103040d8511000441460902050010b41004400c04040005100700e801c010f080181c000382409204005120050351907107004c280200043e1101c400b450030703605e0b81d2030040c52240c0c814507440c080041d0301410860030030019410391b8401d0300c0d0040c84940301c00c4c1e10b03c41414540402081a60520085150b1800c0d80325031441401103064a14a41481801007505000c80001d2103c010b42c0084e40725a03c0d031410b401420f50000341280b1450500e45001c0018101c81c001c5003002e4041c0d44c5100b916840c03070300c2c207400641c1d03c036410200188003107402908407021a4000f800c16104102d80000d00d002843c4240255604100150740d1b00410b0313222a07039244003c1c1440000d400c10b0040015400c2c1102801c1d8051150520 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465939838 1250 465938588 465938591
    0x3022107020a060e0112092604050301050a05010e13110a0b030a05060402160209092e050604050705030f060f090106030c120207020d080a11070b2503020c0f0a1701 72
    0x45641c8184100c440d4981c00000a20444d44c00016043c0d038080201000700b039240001190700320407401c02603440070411801110581482c002c00250600749001002100c1050b4020060741d50340e1710903042103400a00990a010100030041103810304000d410392a482d02401c403200600c3d0580e0f002901c42d8130b10380d000070382401c03011040002c0000b992040c0e941c420415507085d4a444440e041600320b41032070f81c03402846042c0b000301007080040d00300080b114001e030900b4007542d0100c0d4400743e055691450318401c60010f01300400621181414041c941c001c44103616200c0c02c5032070f04200211285030040056411041e15508034006507201645c2074000c14140c1c41c0003482c128540c50051150520403c0c0058042c0100462401078035050b1810380800c0d0030000403522048140c201321103903010095500b00c14803503480d010031000d20340001440c05006408800b19103108540c24100c01c0c0716007100190140c0c100742864900c80c00c1800900c0c41d100300040400703040340e84420321110340c1000b21114030b82c83d0703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465941088 1250 465939838 465939847
    0x706060801021606050610080c0f12010602010e07150912110306040606080114010803222301030b040b0315090c0a0320061e070611030403030b1906120504030221 71
    0x1c1c52145d250065001d50700518010a07102000d01400c5020f40760031140b02002509000c20f58090042d51142300c078290401420b9656210028042c100300110a2140c1c0203c160000d0300c602110091094100a501d400038000e24042c07104224007a941d100b980c990600321802c040540e014007182d0700c03440c4603660000721135090800d4a42180d100c2aa9141c0300c088490040c042110b0000c00e660502c080050088841c403c01d183d20704410440780d02c4000281301100c2017580c82440b03071a2001582c2001e90b002c1080301d101004000c10b4071154092150541c102000e0030400d80e41107040c01d64005900c0080b03541210050010404a0302c0c194802e0380d501108801254054100e640401c045610450b07096051a0202541c04584107080d20801d104417400128401040711641210070202d1110304403584a2502c1c0c1000790140c40c02c840c955100e6041ca01d4203405251402c5054002e49820390b503260100140d0340000c1c0001c0002410030303025849501550025008021202052500310002c8103465 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465942338 1250 465941088 465941093
    0x30318030602071a0a1e0b0d02030a1518031d03010b0d0b0f0702011512110a080c09090304060504090b0607020402030408041d0402090f0720030c070509090309010507060608010216 79
    0x41c400117401103000c10308040f0406000240d411181c0512444100000b078011403610024001e801c400b00c00030740502171300007104140300c0202680136680070846410f0100d206000c50314980d15440507030050118104030001c80c01984030b00c8580c4100c480140001450508040004880e03604c0384c00101c1d855140301c0e0801140d16910a00c10360010350300d0001780640d019005007204420814060361000c802246140410301100802d00c00b05d420002d0000b004494485488070340f1440383d03c00781401443c2450214020356400001c6804032003540e0b035018286410012003002818401042e1607000405200c00c50269545100441c0268480e0605d15a40da1810302c0e11504840c4031000b1090440c0c07001c080001607111698060351000c07080c02201030568503040c080d5004c402c1c080300b01c41c264010308110b1440c02000002071081180d214101d03000c1c02d0f41c0d40704002c98418100c034100110380080c083c1c10002c0d4041c1014100c550f100314404113403151030301101030890300020b0f03c0f21414040700305110103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465943588 1250 465942338 465942383
    0xf08011502012a2a080c01110d05070f02060105030607030b030a02031203101a030a0506010c140f070905010f05041d060a020d050c0702010807120b040510171603031803060207 77
    0x1482d44508113011000700702c58441148141c00c00c0400f0709080c00024114000c0002903018003011824201301c651143d0224031104018038080380d66002060988250380540340c000100030f4100c0d00010001c00e405d58a14400b00d010303000c411445501031149001040050b6402d05c0303c1442841680b02554991401d90f1010800312075a03031140e22503104480c02c2940100d43c4100322503220807030b0180400d031381d200d010040390848480d11000d8180385811008c104440804106000d03d44040c1013120b4000c0e03110341000d01298428442c2c0b00c10113000075410405030410750000316000c1d403035404040451503071402071401d102e42200d4410755aa40004e100c107a03602c00348120341d0840c0300300481c1418903000740e0010f054158042d156906200381e0040305032010445400ca1840a1400341c402c0c00f07a42454524254401600e0051144480c285c41d003030359081d0b10001c0e48010031006800516885403854a094172900d070200040304175204190310210211b0403900041ca10305100c0e011420500e41d03041e01214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465944838 1250 465943588 465943607
    0x90506040806042312090d02060309010b04060504020f1e0405060409200702030d0309081e03160804020a1404020d0c0e030f0106080d03050603010b03150f06010f08011502012a 77
    0x200100048004c00f2020000036401d00c4000030080c0c000e6941e01e1700300005002036081d00000354051400010018a03440642010030702d07000070780c1d0500480351548101300517400303a2410407900f2503080c801114007918111000e5410200b0880061815031618041080f55103c2d4005074003541e22201e89034040550f1501e8a50780103524007a16080c0651507000a850714000b803040810161500640014040450112005030400b28060003a14805444891241e04200c0e00c2100c401850701151001a00945405201701d40c020951044242030402d0100c20b00b00f1100c0250f0429401c0c0907003454091103108800e8503050b40d46030101900c503c43c08051070040392000303030003081e4181807080007002000204d590164800b070501080aa45140c00b2074010a4280303c81e40d414803420090300c00300c01070201c0c000c0c010004000c211a05540302c10055904145421040300000d031a600100522400409001c04c1031106100214034007165146480c1d0b402080b410500b4050210001002c172190003c8466 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465946088 1250 465944838 465944873
    0x807020607020d050a08060102010609020c0c0306010504150506211015110304050f0d08070c0614090105160f170901120b0a050411040b030f180c150a09050604080604 73
    0x400303031603c102d0030041c4035000d600320340401d011041000c191942c0c000c2d040341001d4529030000b10b45401c42c0b85415943c1d650000582c1d4001c3c0207560000c500c9082c5401104020341407200e40b19803440c41d0030140f051950107500800001850242c100d06c9940d11140072501400b02c5800c2c1d0b6503d50300746000680d40006443c82e00e0240300f20000c20f03d00a907004020754040f6981241c90125000c800c0c00071034403050303241e00d0041c001e4100150700c4041000d02d1240310256801690742002c4109010004403141c890154001d000c10000d0003000d2130055920050101c9521504444815103030694401c00351080c00400b0b156180c0d4042541c60b010b5901280e07800790044040380c107001420600012a940110902038030303000710b0b11040903811540c4d801040314018112929490354034a0950340e198075556081e94a940d600d00c8502886102c03070400120610000320082030b501014805d100140c00c0c41e0f00080c200e40600c81e1500e0000f92035500c2c84041c1009003000350141c80c2e50b01e8039140104100c0c1052003134 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465947338 1250 465946088 465946093
    0x60303300c070b1b070f08030109061208070b07090504020a2a0309180e1911040203070512100803120919050303010303082a0d050702010b0f040f0b10080702060702 72
    0x1010b01103801c2600407600445407042005040003841540841882006005031854030703071442d400200300008000b14100c030301d404410820306440c0d090030740d1043c1c0c0510740038020943c00e0001d08042078100c0303205038210919080c80710110380c2d41c2c1c012030141d810503114600460260f9a14691088009104684528022183d8070060886580180095005002c0c445522140c640c1800389004070303501401d01954940120b8500821881d40302c032041d8003d5504840c060640a41d074070140c11301d8000e5074040c6160703444182c141403070581000103c01d40140320340d80c3c0c040421030004802c0030900c01031844100300c0244842925000d08140d2500031200c2d0b1000d498000c0991440c003003200402580d055940c145028402d03504d59107113103140c80e1b4038406c0303910040030305022040a43e0520002801d41096030842031001780d448031801e80c00c0703d2426491a802a1401307a68409901d0254441418942c0d640d1000450711b0100300421a000c000e0841c140c0030030308103c284404103030100136460703120707040303200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465948588 1250 465947338 465947347
    0x2031006080603030d0e0a060227061903051315020403110a0302030d0f0201060f120510060e18010e0115030b130f060b01230a03060501050c15060303300c 68
    0x803e6507031041c24010f60800d50350307060292081100b8031a1505154008802755200c410f002540c11b0300d250b13400c41055000745070140e03107801400c0000c1500c603817001003083c0b201003440020040d80135060050800744403441e25100d400006100750b8039540c00e0498901c0c010388403411032800c240c00003002c45195204202c1080100f006903000229a0112007240ca010141d00c0c2d00341e03a042e405400150040100c1458110002c500b6101604100c8020f0740104201c42c08000f5900f245000ca030018020422403507903a0000494801428080c22a6400d4079070001421100c2c8200b85800c550002c0f07a403188440510380c080003440b1140103101e4012030150300c1d001114851355140d855490487c2c500820140e1164801d0040d80c0c010300b080440a040412a440c408030003421088050784101c2d40400070138500007010030b19502c80c40503200128286001012015116000c14003246002006e040d4144010403014622a00c4c480381d0250b24802c2016217245603001c010780c0c462a030f100404501e9112418031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465949838 1250 465948588 465948601
    0x203070c060509010f05120109111c091101030903093b06010906020d2705091e0a060e0a092406060f0c0f0f2d06050702070605030c09010e12010203100608 68
    0x29280c0d4110352279944000f500b0001e213004465180140c4502801c03400c590b141034810050b01c1c0c2c20160000380702e50028482c1c0c41140b070065086402042d17000e0001403117101d0a101d8046040c00084842d50007100e00e460000050940306005d4080024440c82400c240083c4112542c008541a010340410300140a000001c0c072002445110084001d050b001c200e400980b40000d01c0c405a200500303c09421848d09240c510400243c0406c905c210b0040c8286032000a00410600e00c1018242d45000f58503201302d03110070410030040d0120305016202d801407408200341c0c81c0070b4084e40e0882d4090300300f40810580d2a02e03a0141043c294200b0150a11800030302075000517030700401c1c1581159014100103400d406505001c4541c8414900c06184908207008000c038052000301c50109071441148140566a20144100d844049521500002c20b40c1440440c0040100d24040d0903001011b15085030350307400c600005403902d01e0f1900c0350078a0b65400002d000020000311107050103000c0a091070703101800c0c1034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465951088 1250 465949838 465949867
    0x20f1803060f09100c140403050d0e03010b0d060b06220906060f09030807170307030204080105010f050f0108090f030415020105091f0e010207020d0615060c0b0402010f0203070c060509010f05 84
    0x40c01070107907403030f030701c10f12030594900411b801100c85500014407901e80c2e4980c50401e5890070b400101d18085220112020b8161038140204803000001500000d080841c3d540c6d1940540003a041050b030000061002401c2884032190440302007206201d41000a86000c3c007000031911135822007400c0207002c0703445c4d040c3d26811800400480c0d81c02001256078240500300001a0318040c4012a58072400109000e44680d06401802c1618640ca00800c1142d0740c4141010b8025440c7c4603a41c1c0240303516a1900b41907004001150f4041d40349401c5c1d51800f40c0d201040c504660003a00100c45c0c4401032070324480c01780e03424071400358403a41c40c0c1c0080210a0103c1e420710703803c0300040140602640c40314002242524290180ca5051380e02810385c054040c00ba15009010700414261290b4002268000142c400d2042d880c02c000d880e040070b0030401c03c0d15960011243d0000012080095200030003500c1e00041f41140000010708047d9102a1221030801c0010005681c3c140c0c0c0804000d4140062420210358 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465952338 1250 465951088 465951103
    0x80703020309150703090b010807060f020705030601050111160303211e020a09120c061e0507300909110408032215021f02030108150a020f1803060f09 66
    0x1860350902d680da4074000205c000d1700c841d0400400c410f01c2040005009070780021100d05440490f200c0800c013548207281280c0d280314902c581c60749688581c0c01003289500600c8000f050360640e100361012f244084841050500c4990b1080b8005040c500d50385040040c018101d484143d64100f091180f040c9415641c841801c0020a050020b80c0c0058524652401209408010b02402004c1d4022400908001028460910030580803c5060040a843e201810350042808070951255828a849511100d9100003086508501e0810769410103141143e00b00403003035100c003282d41741d009050406006d4410758032040642c060b001d90502c01481401d0000c03050790040507803144510456a03044450b240c55a1035075000110310000380c440443c0032640880e0f0880d8403880880c0601603040702c0345c1e01800f20f101c00d2007102000c3c1c00c198202c3c07942641c40300900340c00c410804030160400e100c00030703a15120b50285108a1030010031700d10080003424180805a40040300c0f0414400310700c0d015940e551511003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465953588 1250 465952338 465952363
    0x7021807021c1107030c03120e01020307080706060b0d0b041a180907030b0c0c070602070612090203150c07020f092a0d0501061119080901120603120f080703020309 72
    0x10144940c450711803040070843d000001d15011a80038a540e0700b45040d80a500b80820750341600c2240110110700d025095034040b092041e0300651416009494659194102c004203c841c4c0351034010000d803c0440b01e0141514240c08400040d4401840c81000111400444940032500c84c030000c086103640d0741d120345561000c03036a12036040e41c0c1c1c4514070f05040c00030300c0c0c00040c0700d00c06460502c45440300207009800e08a00301070446070025202c0c4001c1e41d50712a680b02d5600020300107200d0f4a008070140e04410800c4c1d1000d000c540501100c4800350000c034004440c00c59450030041400b20640c585407290101d40d500a441d510402c3c104010911404185440010304001c40401c00451002c030281c1106c180c1d00e080d4804000c696100d28000788100c18514611105200d001c40403c518054800d40040c02907000b0b8503240b800488200540d00040707580004607400f95034400c0080440c06d03282e100d2000784a01d540e010410350b180d00002d804080040c08880c200740c4180108198900c000441250484 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465954838 1250 465953588 465953623
    0x30209281121010f060507050717010b13050610050f090d120207061803110a0e0c0a0e19060e01030209031002030a2d0b040f020d090c052d060705030a02030702180702 73
    0x1280c3e00b007991030402a4ae0006150030000500d030b4410301410750040c4012141107590441da01542001c81069850549400f0317841440c034031211203001e01581c020408101181100c2c0c4c14003007141c002650300401c4a20984007104603020300c500860f414001c1c100501464144103003401c50440568004888901004001000f011a42e20b03131540c642e40e0280007080316860080c0d491401134090b50349500b10749201404a88441d1104013207103402010790381c41c51a0900340c1c100592904400721b070000c2000800700d06140e030170001e00710b5a403000c0c80f60324085440d4170000760340c031f0405510100032200c1c110301c030410703901ca440040e400305202168080725548081c0d5010a20b0440440020000c1c01e101070342500103031001600800b10b102c2038002408081c028111411410b0382c803024407404840c401d09400d0380300e08018003640001c0020450704002e02004c1c0c4043d05008a52307580c1c0d89140e00581c2c1c040b000d40d01c0482d2450441c60480303090101d01d154003401c043d89082000010755039040d0481c1014108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465956088 1250 465954838 465954847
    0x618140a0807060e03010b010302041409040623160305040201050409050c12130212030a17150d0b100504090308060f010e03030406050403050f0106030209281121010f0605 75
    0x40da24000810007901e1800c0990710015034030040a4800104c00da00c650003035003841c0754591958064800d44040b545136040c01c11944145004100c421703013004000701d8406980b4441c0d954050700c06445005004144003854150b41090409c40c02518002c200d40403c0509000c00c001c01070340d106041d10100c511400c0089100e450300131003032003e030059000c42c1301c0c40c051110421004202d2845140c0b4118001c0e94070012100b130503c80c01b602d900c1140c40102c04101001c03c5850320001481c80d00341d0060715007050f80c58010014001522010003000256013034070090f4140300091107900d03910001414100d608001008080c5da000c0e1080100400e2907210315040007001c04a80d02812a1400e00c42005081c1e0340d17140c0d110040600b0a40090101382c0300c0d881081c0c244c040ca03044c140b103040140c98000300704182d0340e034407141015450104200700d0f100000000e1040c100d480030a02408800c91040c15941e500e6400d4503007501c02401811604500441d1400010840c00e411520741c042580c40034075145549 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465957338 1250 465956088 465956129
    0x10f050a0509030307080909131718090a0209010f0c0b0403080a090c090501090b1e1203121e070804110f01030605030601120204180302061314060708100618 69
    0x90068400c2c05030540000a006020406458002d080d140011100490591291182c00010011010001b07180840c0304020048400c000c1d000f034401c0350024103110322030480d00750101c0c0f46810150b404000894000c521814035603000b110245000d00680f600d0350240d031207600c40306410741c0b0252000d0103010b0400085001d08003107130440400c1c0d40d01303e002d901e03c866135081b0380300c02800c00b4400c402400d460580078001600d02407a42c00d180c140e4070645881140d43c22002c000d0070441c5d0100e41e10f01d40c801008110501d04844040f82e10908800d000d034081b10b906e801c0c010000701801403051303081041031810400003903e81034489180d44420758401040302108001a4010b100741d802c040da052140b000002006039106001030000c5d0302c05d46052011417202034090200070801c1400a015030445400134200e42c100d9030041207228040c0d20341030800e48103041d00c83c0c04c08009880e8180016000000c00c010a0141150040100404d251466510f544003c00034007020581c06a440701d00205440000c0d0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465958588 1250 465957338 465957347
    0x30c020118030b090a0c06050408030403060509071a0a091d0f0606092808150a0507030209060a0809161203050702060c0706090609050f130e2107020f0f010f050a 71
    0x340d03500c00800e443d9420a01d483c59600c0a00c03d20496004055810110b01c07517200710700f03450440d50407034011403c0905595a41002d494024040c0401d031007980000111828024807100c0035450706240c2556549032004000c0080040742c00c07015030000501e50f0785e00080d4200b0b060079441481303120b000000c1c4d10b6000c001400c512031342d0744007684000c0610030002003c0a10b61201201030408072481c0d1000d5440c0f03402907c4925050740e405540e5174920000e00200c003a500010703449101403038018600ba4400d03001a0b542c0c1c010300702c0000010b080c0307000c2161181d002c2005124122410303180c0300000e854590350204c160309480e401410000c0101d0b040d000c40d1510b00580d440766520005070303031242e40c0f00c402c0206005500c0c03181c50300103007081c5000109410192001440288058a844100c51031041d050000d0142001d44001600c100e0295502584203000e0001c3d0000e440c45400b952282c45004001011b9483c40200d44558050303520f80c01d0030b81c0c0000d44119401d080c6d040032915580107660a80c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465959838 1250 465958588 465958637
    0x10212030705090103140601080103241d1605030304050f0409080a2a0c060c110a0303120e01050105031c02100e0c120f07060509040213090501090c020604030c0201 72
    0x89809408800d102449801001810340c0c02820398080200c0d80142c5480594140c041d2985408207450340c00500218a01d003990a1036042903403488a00c5001c901080c0c0200e560815860780a6001000480d00d055428041141d1041e800c40d001c20603241040d0000340c0341d110381e00c51030b072080006010108040c2c45503002202c0f000d800040ea60740b50f40f0408070150110360072856810f61000801c3c0c2030031a81405200c0344181e1500228103c0c0303c2400e1500c15240c080302030005807031801c580d10000390203035101c54004015511a0341d600007800707501e2007031038181d542141090015905240040c0820740340040e000840c0c110581000e2002112070500f03034107049910443d40c40c11400c04060074160180001c0300508800184d4440300840002c000c1c541d20b9091810301409a600b044804000352845400503180004008000615100340700701260b1002e0135541c04071070b110303848000400404030180304203151101c0900151805141940d4001d001c40c1a40310000e040c80312400490201c00c5c1c02e0440744 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465961088 1250 465959838 465959863
    0xf0f040b0a080a1406071d1c110111010204080c10110a050102030105092d091c0806041d070303030f1508010203092506050c010e01051f0b04050a0306020304020102 72
    0x8030700c66511120099214280c02005a448a840022010f140b583c0003450720722620081c5e07502d445408040fa1034024443d01036240070790040140984850000d41480c0a6042910540b1b10000d90030080d0005008803250301c04021603a4414001040b07410400f148503200894202c4440c1c1090300c1c0c0940c00c3d00d40000c0048550a00d20030101d811080082c15401103040e00c0c0115090303105075075422594602003a20351990080c0406650b660798203800340a2a842c1c002a9010940f0b2041c0c01d024185030700c1820234080b00740050100401d00c540341c140f41c070a5142d800f41c0c40c0c0d030856500501d00b6600f551500300d44401402c0566440600414105940c4014041400b6401c030f05203071030343c0c0d05825000c2c0d04281d42c00c0e0040c0c000c05100c41c0e02030b05400c00c8000142c6590032002040c610b48402990755402929440380b20395200c541400c0b51440a114003441510705000f00c1a002003090f404000b0f02d1038036003040080150401040c48566200e14402e01180d90081c805641d0355683c1c80100c0c1005c24010710f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465962338 1250 465961088 465961099
    0x31409220f0e070612091a071218150603120f0203040306020415121415030f0d020a1406070c020f04200318011e092105030f060607020f0f040b 63
    0x8803090792000f040d201e04407030b101d94612491030701030003440c002c984a6a80017081c200785004008202402c41c08840d6001d905400c20006210b00d0429a80940b2103c0c1d92a081c0080c40f0035240c42004003110800003046030b444020407429003143d46181c1c01c050614145828413401504601c1c24a00c00c00880e030265510500c00d540b10b41e541c543c03070707000da1140e01903000219031060745040c0e0503910707807069518500c240340d0031100c0f80c3c032a1003c2851345441400c206030140030f074690503100450104000340b1a8002640280901d228504080c030004041c0702d0380c0109504910103100e111580000184101a0126820342100303009000081c004c1800c1d600300c000401007040c11402c203600e10303400b8500ca0003501c201000b454400d101c02030b08039072524407103640d180030910b250411a500d0307a00a001d000e100d500418854480781d600510410b5440300e8007000954000b00f000030351200c14100b181c0020069a41c00d00f40805540024200e0824021a5001d0031054a40441702e5440d40c00119202001900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465963588 1250 465962338 465962351
    0xc051b0303071b050406060302130504110f070803090607090f05010503060a0918120c0c090203060a03080708090120030915041205150f061302070f060e010504031409220f 75
    0x40202107183c06214041c4a10316088000510300e0080c000c0301d1100404044440a5505080411000781509002d8405011040c030407a548001c190000301182c602443c8a140c0b240392100c10300f4a4410002d00c28002c104403107204014445401403900243c50007401c203141c4030790351781e004900340d1b0949a1210048500b8100c3e0300120900482c4a51107081c01107100e5071405124007410356984401a20042600c0d020b4581000096036690241d504001d0040c407200c0307807035a65140c4a160350440304050354045000a41031100c1d41c0c00229656000501d1341c40b00f801c681801d0380440e101d02610300d07421301542c088840e0554040451040398003800160300e46111281c028103000343c1d82c8a03007460000c1444843c1000c100c01030395226400c0d116040c010f0480501101c0c2d0001480a5049200704a64282131342c184080011124001c80e09a907804400003e103919003420028074500c1e440c4e002d1705040b5420850b20b0b4654480100103c00d03101901042880403120b40d15040080040b4800340162914010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465964838 1250 465963588 465963623
    0x8011d122113020901080d0234230904110108090a1e020909010e030301050d0f0507230d02060a05130b03010b130602010606021e0a1704150c051b030307 67
    0x107107025079036802500d0b04005686c860426a41d41c9406071888405648a03460800d20509031240881c41d80c40000761034020503002c511400024909600710b0030528105400c03101c01c103003025809501da5001186c121269013460380303443c2480c5c4044600c042c1000000d41c00540913410800118110307070360002800c103d80700e851104003480841071504901c01e1744840c0c0482e0140d0414003c0703141c0c03d0752920103145141d181c4010170444010101d4202d441d403046405d0480032a42c2801164020b10240c00005004442e0000442212040081c039603c200d4048000502680b50340040d508040d4550a0041c2d4900410101c4c11800140780e201c520784e08000400803030802105d0010744003681412034484a0503031103903002c1e401c1c2c4840d8000d00e0016070190441000250303c0c07805141000703010300150f50240341d141d100d01d081c83d0a100080020785200080400c4400bd680340d9200e400000b40c07901c4041c0d107041e56251611040840006008007049404400b0b2565050040720602a03010580341c0109030000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465966088 1250 465964838 465964861
    0x310020307030e060402100507020d0b0109020414010201090b0712060305120d0b030a1a0705090d03030c0909020a1e2f0105010b07021f0e030d030608011d1221 70
    0x7201c8000000e0300b03203016140c6940001030030a004e1640117004a0011010a9049446400a94059034800d40050a8401069004803a40e000c0c04150001503a52820214881780c000c0802709101d045a1408510030040f600c060202c54014000e0726000c240721aa015086000d4191a0009855402240307801c40d13030262410000d02c0c038030760707611800d22000f0f0a60b010152101b145400c003a00c07020f181800c4040e07280000a0160744020541021030a040d00403008c16400e0202d560200e0201e0ba566401d02c2902e5003280d441002000d904509614215041e0001032450080981000d6000360380100c0034903150213030120120001604d01d540d650700c920640d560300c40c2080b0203500c0d43c0da9460100081407505042040743d515030303006407050b032441a1844e410700003030716440c0d405c1007000403c0c184400e2568041c4800107420203e980c0c045442c0e814810300307508498400840c2c400c03400119401c40e580c6003000c22032001c0c100802c0303200740c0c0305d9010250803404074501e41c07030b00da02c0302c2180307801c07c01d170711440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465967338 1250 465966088 465966091
    0x606040b0d050603580c02060d050415140610030213050301051e01090507080601050711121605040e0712150213060f080c09041a040e0c2409060a0302070203100203 72
    0x580c4044442d17401c03807801d901c03004a1551102208403201d50700e04240e008641800310a032015080c4c43c501280301260f10101c900507074040b20740040101d041d0b040043c0c0340c001d030840340b40c844903102c1003802d101e03000400b180d10058200c01071580106081c488051035100600080401500a1046103807001144810885400e40e0120a021032000072038005203034030410348111800d440e5648203403141c070010341c0e06800c0402d0845142e00440c12200c21910382e00803142091161b4402480c1411000c44201c1b00d8809981009005514040141104210004219048a426142c6000d10741d60703d0826150909641040703064150001a100d4085081c51f00c1c0709040305d026035a03040711070b1010007048820800640b003030529400c0038044078085260550218100744255000d010880c0d9980010400f070b40c0702072901e000248c110040340b03041400d0210184d0040d040ea001c0f08444102c500b00c0b940c40c940a1305405034025000403e107200490302070b030304803601142c008044403114140c1c032114a029510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465968588 1250 465967338 465967423
    0x7050d0e03070e040c06050c160305010506040b010206160302030c0c0a260307140a0306120b09010e030c030406050319090b01030203100e0a0204020c0313060c0b0606040b0d050603 79
    0xb0b040000582d000040300481e0140d580f0200304074110340340030021200381e0003a00c883c0c80d050060070140c1d0054907410400000440c800c01c004a40703807401a04000c02c407004003184a05641100042058a001103a0343d9074070320b200ca06005881b1b440b00d86010700c0c64021401503046501c00c00100700144105015030810190a002c540200d0384140300201e1140d020549006020404a40c280712440c5202c0c40580041e242c140b50014543d680c40038010803000540000b550401303211001c0c84032030042030040d00d542c03d203000300540ca016204e169007503981c480d038032944040060100c08914005c000b500340b4000034800c65020b005803207007401c0c00c45400b0802c2c03100702c0c868802c0704611155103032680180c04c44256004040c0c801054113070240006940020705071103040c00100131100b18020b0340201000940030740d0b80c071030183d0265464203001562005d055948120002c1c4402c00c4101d02c4001141d80c00c2c001c07030101160640b40d580100f0315180c280c14a131566070100350000401d450004004041c4141e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465969838 1250 465968588 465968593
    0x105090a061404110d0207060f0e01020c0316020f1815010f05070201031a12150121030e0307080f03090a050f011b0c030b0a05011502010c091203030207050d0e03 71
    0x12900492442122458440c1c0540c00e45442402e0308035103800d900c0303003a20800d18002e061402000302c20082c1203178015041160310550703c0c030301c4c0300302500940300e2122825400c80085240c00d1698820a41e0390213001d60940307003043d40d110034008545030b0241c0741d1007440020b484890511418140381c4030354203044030b80600320680202c003801190310400c0c207104281039a488291900c2c880d6001140949031002030b406041c0d03962007400c00345450710303a030303500050360071801330408191500100500104180c0c000c07094003261201e440314500c054001d42071201d5041c1080c0042004481c00309061100962201f46180544003d584259402100800c001c10b411a074180303456441c0c8003000f840b50b1101c0b0f203940c0002c040e5030603080c0c1c4c40301c541480740d4090f00804121070442c0d80c030380c0c0fa00000042100c1074040302e5111401000000e0340202e1009550140340001e00c220000031500070020102c0344240446420380103805028503002c0e80c115800d041d081402d03075a12442a20000d008610444003090091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465971088 1250 465969838 465969841
    0x40c0e01030b0f01141e1932070201020c0d0507081e0303010b160f12030507030b03060f060f090a0902120708070e04080d090506040201030605040c09120c0f0e010509 73
    0x1890141c5071601c0040d416185c0c084020807002d00a14150001c0e011000ba00240d03d0941003000e101e48007508100d44049402c0301e40e801003401c005d12040e405c0800f001c80d25001301844c1d02c19501409611240403074050625214681400101e141100c108642c64028032179026020038440080f6200c2c05485945013114008926060010040c904140303018482c0d81045c0018070540300c0c80b80080c40203500c010004140105140c90f61705403100b070100e04880c61100d80510342e581542601900c1d6000c219401d0810041399082c01094480300024172034bc40c6051072400003100d5641c2c0700b00c0518681c0380506a0340d51860201e040100501c0704820030303403066914a08802810780005445016149154040c3c00d03640d292203a10401800c000d0421640c04205100007031521020b0703c00c12911501510081900303042c903000241c11644150030841c083e41c180800c001049030044c0707030001104d030f10b811b04880144d00780c2050301050440d9001a1192a40074000050386802c407610941615011103c440c0c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465972338 1250 465971088 465971111
    0x91a0f121510020a021915050301030501060e011212031107080705251203200c09100614130902070c0303110105070c0f020111010f020a11010506010804021c02040c0e0103 75
    0x7150125400c2d000143d21011008006040203078000600c403981005101405403100404008465844206c4000880200042050040034080d560041c4044d000704000c039410300700b240d42c00c40c2403400c000c7d00381041541c41d111400c0c869071100859414032450f0f56114181480d10100a6009003420384440c4a945602e804250f16120b40c12000c01c1c0388100202401d1514950700c2c1c0d100b20707401c1c095086c0035982250a9500b04011111048a61880080c0881d2100c003801c00c0740c8140050a03c108100c001d980a104041c1c1082d038600025600c24810707034071810b89000b400813841d4a5046220905e001043c1d04041002c1e074041003003074130701c6601c0e00c0aa80030f4075200e40d030807580201e03031000001c0d000f00301c1000032581c1454500c8406006150818a001004d0811825100500300505c1581d5002507154000c0d50301920b410700410b1004003e0000b401e03c3d4000031b24420010300040d01c1480074070702002c0182100e44508030450b0340980184016030000001500c4482401a81400300e410310880004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465973588 1250 465972338 465972349
    0xa03060504050f01050907020c0907051b07260c031b090705031005010c14061807091b08070207090e01060914040c03080903010609090f02040606050a091a0f1215 71
    0xc640710041c290f50541c2c2c41c050801c41c2c20308002d09103200750301464540020a464582c5224455442600c2e0142d9911740030b1703140c15030115824112240d41d00300040500c60303650400d447d039403c2e00420a5140e8180905402581010743c025003950789485905590810503050248030310f800c607001c48000000382d44122040c1e03003a20040f1289103a0784c038108000d010540c09006410a500d0085c501049010480e0000914000c01030350401011016507907055038204040000d4006010007450911240703c550015210001030044d0a5003030080100000b422a8070801403c0018150f40c0c0703003800024000e42d160b0b4000c196502035820120306003103260046030111580302d4080c030b9020382400030040c91501c41c405c00d03421501d40c4035030554a406000414200383d000c3c00c000d680c064114441d5240b4184100030480d480c80d8080c00a10800340300025074150090014000ca07061801117002296044000c0320061081241e6401760420200d29010314200e4002203e00c9811a03808610b80911304204101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465974838 1250 465973588 465973591
    0x60603140d0207050103020f0f1612020f0c100c080301140a06030b10030f060b3115121d0120030c2502040603080a08071704081804110a0306050405 65
    0x41c05a80400c4082043d94030940c010614040e42000081c2440f0610301d40c405550300c400b6113040309941c503040501c14044080030307038400d003a40d5000800306d02e0000500c42c2e40750b44545841e9032151801ca00c0c0c800065006d044e0b03040d0030300ea00044440da01e42e120180740003980791103160340f8041c1c039040e900814601d0103481282c00c83d6500400d090b400345800482100580281d84400b2a19a111000050119410700c0503201140b44044103060503001c502c00221107110103840d0b180350b02c458140410a84160141e2503c2650041c81c060302140300d40d000040c0038003016190300c00034803e2000181546c010660240a4000040d080302c144680c98690800140c002074a82d0b4480b00010000e000078011603140300c0004080e507000580f1030040680014048581c142e00a0354054000102047c07055481025140c2c40b0709642000b011140383c150b40d48802090050001340b0074000011180000d20740c050030b83c45d41c500014002d000f403240300c014a0740070350031140000c00030900303203c0c0c08107251419005c2d59 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465976088 1250 465974838 465974863
    0x601051c0605090a05030a1223060d050a050610060f090b0409020c071a0a1e090b0702010509150c100519180c09060e0c1e09030c03060406060314 64
    0x203089902540c6a59005181c0600100410300c180050600050350034400f401251841d51070783d0744031600e06000d541c152000304c640d04400700c0072110100f8507051a4031001e60802001c0c0c4640c400440d940c41c02c81d10b011004440039250f0301c141810000c1250810301e01005848840d45c85001704682c1d9034040d5840f003928001c02401c11020301081c4180d060b140d000c1e10511845808a0395840c0e0f80d011400010f090118442e0760b09140003e900042a40080c11490f080142c0c10130800c00c00b011800c0113214a2a40c0503074005c00c0b000244003419a0300c5030382501c6d0b000c5401050044074100c0c103000c1c058030364003100b81c00e0705502641200c0c0048510750b1180d07038071500101c0f514003011011202e400d0010301e040325000030464150000ba41c0030410f450009400b0740b1481c1c400080407420001c03100c000c900020b103240b51070714082141c01d070f80700002d6050003c40040100a99207a1990b50b000034201491041360351f07018411003003004140302841c0c001c2d1040300c0c06600c055903601241c06256440d6448900038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465977338 1250 465976088 465976129
    0x50a0f0528151505060304080a020c0a0803030c071104050f06040c0207060c0803040c0f090203010f090911130209101205060f06072409050a0302010b0f0a09020702031e030c060105 79
    0x960510340b0302a0007180000da804a00e04420f07640313a40c00120701d80c00076202921000030203c0c1e180d400c0340d0100100f5400f20b80884c1e5080c8444c0c549081039950340300003030010203982004610b180400c0241e0814500c0110000e00034410791520083c058020709003182c100d44120700301780a62022900200e40141a1403040d9108400741503280c40b4a2b0450313001400c01c4030140a03054000070081c85850b00d070ba001d01680d080141c3c1d2035261078800060104103030808280319103800c015000284460b03030b21442c0402e0503223170070794603540344e06400c4004d000700e249440d0045100c044140d140e80e03008000000c0841c0c200420056601ca52062200c541c100449554110008026540c0440c1c0344059000440d60b19141022550600816100540301d01003000c550a601c200c07a44000c040e0280669100980141c402c003210a1781503000030b0f2050298443c044403503900013400ea040d910244207800c0c3c004000401d040c0c02500000c0c000703a40c0c3d03002143c5910b05005001c00820030b0b1410240e116500c1d00359844 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465978588 1250 465977338 465977363
    0x60609090a0303110903070303110f032109010f0f02040f09020c030f030c3702010b13020f0705011802100905060a2f160905060a12050a0f0528 63
    0x28250010304980864015004e014002c2014030794081051401941c400c0e0354203101da450a080c110b181c03000c20f882c0505181c2003071008290041c5541411110700c0009001c0520944540107820b0042190051300307a60107042520404200219400500850b20850304071000e41d44c2d00e1005c40c00700d0180e800e680c409070700104110b00c054400400078540088610380c3c542e01c0c1540310003c61060380880301101192120b19444100810b02c1c0441032407480610380000e201d1300354a640040d0109a86041d10030b10281e01113040494504c100060310740207903024000f04a460103005215080141546080344074200112405140d9445032902034116a406007415051405a00e803e4510703000600340b1420160070401e9050003c1e08070800110204100300207080d58009100c5e034849982c2458100b86000c90400d03007400701c1a10752074242030807503000c902e80d0441d0019914003141441a154000350004824615235010300501140b080c00c082d0307011a048651903a06402205e00d0308510002030300107a900d11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465979838 1250 465978588 465978593
    0x60b030408030622092018101d15060a05030606030c07150c02010c02010902010c06050411090115080709180c020f0307060e06010f030f12090f030b0702060609090a 72
    0x1406590001d01c000e01c6144403c980c1802e038001e14140e00182d03d1410386810803c8203001c40011180e120003040c41428041654450101c4d2003644a2a5140c40b843d50100c00239115017040348120303005d468210341e0300c1849c41a640310070741030050584566401d075201050178409854075008031801c180042e01c51605582d1490204901e90708000e056103950f980412503180000c09840076880038207108040000e103200702d801c0c02421510060344220175a0b150107264000360383c00089413040d0039170150307000c0380d0740d55146041c001c0254011031140c1c105c5c40060001c40d0209448002d071503000440d59a6103504c0c1d40e1110220303400d182621600743d00e0100c3c041b04001507405500180c002c0d14050045403040d01030840c0880c42c60b03000f000c003540c0050340e84681851070032040c03212a00500c80f41120028490543c3c413403c14006e0920380040501241c030020082c1d59004418000041807181c11041c0481e80d641084080344034222280300c014000c0c140000d4061500c1c5803820701500c0c4410003010141c42ca42d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465981088 1250 465979838 465979853
    0x1052d0f090703020a1e0801060b161a0405060405101a060a180b07140601080d050c190b0a0c090b04090e03070204110712050702030a06050c0d110a0e0301060b0304 72
    0x2620741d2409008490300400940c503080c0105c00140988800340c48183d4009200c40d40c030034038036007105409034100303001000306003140d4069500c8008030610030703560780e50180381c5408100c00005c0040d140380e00c40420082449004500d544c41580201d0503150301c2c15107000c0e900c08481c00e19003841c03043c00c1300550900b49400d00c0c4014115011180c140080c0a010000317900080c51050350200340b408200003103020800c46500e080c8600c1d504040300910407075041502d2661242109042602003003004544034400003000c0041c070803482407000d220b40300c0b08180e0914009525045400c0201c203030034000f540035000e10800c2c909007258644c0d440c1d141002d041c950000060705540340f0141d114403040c0051009603855205400b80628541c0c1002c4e0b5616840c0f82a10000c428203a01c0300a020040c84a000561008107070751040503070010000850390303a22a51000f640c081c0316400c02403145000e003181c0c5204640c000a00303074112682c8074840140340003002c1501703a0b04180201d4072420700c1440403e001071540c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465982338 1250 465981088 465981091
    0x516110102160f171e030c07081c140706050106050a08070e090613060b03010b070314040b04090510121109100f090b03030c0f0304030204050f0f070809011d01052d0f 73
    0x113180c19101c0c010500e442c8891640400303080080c0581000a10a207602c104101030002031494a029240382c0c800460200d41e45208a8032050911030395105011a03142500c084901565225070200860350f110f49005000360807001e04407020401040205001a0090043d0748628200401030700c003980e00e40e4148a05d27503c0b030309041803500b921003038003007070464013440954041c3c0000c03c8410313180c1030541001407042105005104480350b0030041030242820510485081d075140a401164a85810820405100051f03000d0b40c4a180b24080c1d40081203810040d41e00d0201045940388110f0310341034410000550031384102c814020020504000704d210540100704030140040c00d5034200800c480b002410901100e0b40c05c0c64a810014040c0300b14a054032506030002807040f0600c0091030040c5480e000342c94064060801d0045602c00038003004800d411030081c0087cae07000700810803026a00500d01810381034640301d214003520380619844000880320b00c1c080b04181001d280c041c1c1c49240c17030b20b92480b10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465983588 1250 465982338 465982379
    0x60903060a27051c0509151305061b0705011b140c1903200130020d14060d050715050c0a080301090b0d0b0a020a0516110102160f 57
    0x10b52002241001601400c501c44083c050030151100c410b0000d5000280d030340003192401801014050360005d5100c41000382000100422080d90382c000c440041d035405800d0340c0c003203603100030b002404a1080070503510ba400d0075072a0600301c4142588031001500c500c0c82a0995401741581854140007080d02d4100f6081d0701030f98101550703c41591280410180074984414103801480c00380c00300200001e460461007001c2c601007000d41d80ca003950b40000c0c1000712101d42400c041903051821502d41c410707128003030b207007403911102196505030000c0c0240181540d01032005250320414001091401c001d20035910250788100a081420700f41843c1c003134603905000c981010018280141c0e440800c00304076808013240500c8060b9183d40c500a01441501d00725120a40103032094001d101c001410032003a503406c41c80a210241c1c56150b201000c0b122401540d0b1400004060018488180640d25002481c07514003a82503459807020300401c500d60580e5403240303240700408e283c020441d003940b42d004040000c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465984838 1250 465983588 465983621
    0x31603050d030b13020d050f100e01030308090f0601060e030f01051302100c1a0103060e0a05120c0109020301090f030318050a020f22060626010b1305090901050114060903060a 77
    0x184010240c0e049030804091000341a5503034091010a06000323041c15481405060240340203820281c800d4403030401031200505000d00b000128862070818441070300d00c000000700303d444a6940c0d0400070030241d045a04107000e3f0043c1250162158418020984502c03800040340303500d011503500b4001c8000e455034205c0700300312426090390300140d088001d015140070346040d0201c0b95415804c0082c1242e24582005481d5400961810000f031804108881c0900807491038548918001c10080d0241c0300740c41e002540355181c028001e080109040c02d80300700c0c41c041d542c00c1110b09483d400028240a074070102a000d03906c0824580d006103404e204070701c043e00002d404540342002400c5202d500c3e8905400080040d40c40c2d039814006d0b40e51268040c00700405100c0c520070540888402c008821406019100d01d03031100207070081c00a280b603e8400010103002e451204036180c51001c15009240078082d51412183c0440b141c2800d01e042c030705842000c100103001c0c00140e00c0781e044002c02040107000881201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465986088 1250 465984838 465984859
    0xe0307170c0a180b09040f02040509160308120109110d1518020703080a11070201080c0f04030b100b0f04091d030a091e0e060d15020a0c02031603050d030b 68
    0x540390000071034001c2c029107015419520b83d1540d603405032a0901c9180d0301940191003040045403014115440a5405680028040d10354408890034840c0e9044001d0885501840000801014400409041c80d8a0640d501c40340d80b203170b89100c00d54011004420300c41d502808040e80c0c501c51a400805804440c0703180100c00b039580c1499440c0c490703000113003244542d400303d5040c0515801864040d8018000c5600300310703610025980451a0160000c060b0402c5104000a000801442d007158544441400f0f11603c07503950340b9000a20309412958004041070318900040c2071030340c250950318500784450700e19060038200b005402c01000c1d0840042c902414056140031591018402044101c0007942e60552490814107c180b203203041c07540303010a0381401c410401803981c2e0050301a4100c50122071440303a820060402900b4814182c5411082c00c1c800108503d4068000b540004a03030300c2070702034440403411556820baa4004511003d08603400288000280c00c1c400da00080c02c8034402002624003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465987338 1250 465986088 465986113
    0x61d0616020f100228120b060d050a0207120e15180d05010606030b12060112080f03090114070f0206010b030a0f1506080f04050705010c0c050415030605070e030717 72
    0x41c0f000000d8545a0a030b07001038561081040c003c40301e80b070908200080048644a1720009180901600da2611482e68a440499145e500e0004507803a01030041000c4c412410a100500000e5002c854100c400d10084034090460300d00512141d402c00310010030300c40d81c0b041d50202d52104c992111680b00e0b603002540482d140c142e03455000118145000b0800081d00300d0425101500301c400c407060582c0b05000a4030b25003c40d907000904981591021071424103280c24902e00700e03c0705e014400540c404040044100258003005502c41d000030b0b040c110103545903480f014000e4500d00440325a0100513003180d001400751111810085400c207500c0c2a0000c3c00700132540c1c058086440c490004146c0d240c100c4010807000d5440100e0540041041400c001c06003015901e030b99076410144600c60500000c07032107410034405124400801494040c0003030180c0c01c043d0314901041101030100300d440a14100100709054071806018001002c082c008010b801e0510102c402180c070b60300032207003040c130545259400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465988588 1250 465987338 465987343
    0x30507021c140109110a050a140102010b0a14090c0f070f0201020709020f030a0e0312010e04020109170f010e07270905030a0206070f0507080711040f020313061d0616020f 75
    0x141000e103080000303018a06450110176020100078001d00c100525002841259103030003108007122103055130403141c40c0c03000300140d024042e5002e10560000c044c810001e5542c2d18110a0038400c101100e1400701ca40c3e50045c2000280100049840b8110080c003404000031143c95500c0707a010700500456234031903030f900140c00c05c0c0e81c0304c070005040d0041c000c410320007103401900406d083e00309001c000e5400d18003c0122a80e42000500c40d0400c000744120218083d6409181008007401084624200c154200b038001c0c0c0d0b9580c1d54044181d034a40c40c0011200b00c000000c20548150f8141c0c1c100b031154101020020080500d0805003141980c0d9140e8103140040d104000a10840c6000e4001d1f141525080c18050200300303454007823001b40002009035400281c1101c08035040f580e0320802c1d6980340c4014401040c0206400b4040d19842d9200205010450740421410306685216600070710800745401040014519100e0903409154444008254095240074590a0002d0948100d40060128807007452 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465989838 1250 465988588 465988613
    0x6090f06030a090c080607080705030a1b0905010e041401050409170a0c0c09110a0f020a0515011715010317130e07091d0406112221030507021c 63
    0x280103566a07031800204031168544c0402804014090026480c08403030280040000a000200700840000041d229403204c1d440f518009990340400c80d000c03c0c0d030300340140040d00a805942e01055840b09810300c54a098012800055601d07441c00780964a0201031102401d41400200c4a00e1000c02080502006040140403c590783d81c3d1504400140d90610309a02182500150406400c124450a00320345040444444140340e2404071419000444100c0c00c05448140003800d40c02001e1000c41441c1121007024180d0381d10180c1d01c04401c41d050002c6e03559801070b03440c12070f44004032801000410b51301e00321a0324421a01e02d1580ca00300f003e240003030012000713800008200088406100042e54040d2000000d40022425002054a0181d20f011b0075180180300405103078907040c00300240c0381c400d8150740d081c0c1e800304e4400c18540e07075986401c10b00102c20301828042c1404480761812210342c6601d003040326509030310b8003490328040d0740a2081e448030300001d000d4015010034141e40080d0583d0708a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465991088 1250 465989838 465989851
    0x203160b0f01080a051b0a09020a0f1404030302060a0f0204050d0308040611160f14190212010213031401110d15080c060f070c0503010501030f030e01020307030e06090f0603 76
    0xc5040d2400410840d182001a00f010b012540010072440000f80001025084201e600040041b200c004e14009035130f440940e08582c500a0010400003482600a00d6102c0651219105c81084606d01035111003140038901c0050b006a00540104040252580c45400980f00754400945080e031141d0224509003001c440803400941c01208210510034a40724000c038940240106600d171000c0d074480c48002c80d040510140c41e004c58148003104000407101c2502144841e842a14400104604503407040800824140e018100c85031101d4074541040c802c841c2c03144442d440d04403040f41940c070341c030380d8000040d030a0410543d0303036068803801001600090a58582540c00126a6804203248031400c942030740d00010890380808928038a81c0d540c80190703100301929030041500c568050810450894079603200d00c1d01540390000101c10b004600400744c0500780261900038003688070000490380d030306c20000c003d400180070010600051500300d00030318001200518074a08190f81c900056450351091790300c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465992338 1250 465991088 465991103
    0xb1c030809030d090c150c0f02040e16062303040b07181a0405210616030f0e0a0b07050a0c1203020d2a022b1112030a06050d021807020316 61
    0x421816146e1104080000f040d0728084048208030342e260007d0004681700284070701e440302000000b500c010041d95000a5000c00300892456880c1405800048800310002848151300d111441002c0c1203030469001c0c0e070f404106c00c22a684c2d176a404403001000d048030105400c66140001521351007c1d140c1002e60414041c046650794035180c200700ca2511024401080c9941e83c03142c0d400e4002c8003003095644444090502c15024152903001c500410082c2c0e501d411f82880c0c450f691031494000903803e04d0952103440780686d65100c4a2090380c2600410b1035400000b42d0082041c000a014440e40703d04d00b24150501504062205611805681c40c541d4030514044140c44040c003454180612200d4490240c005020400310004101d41000058400e28002030f88404900300030a21602c0160380709490b040580b82c552000c00b45646055100359000e074000350030000c4c0829035240981c81407072241e80c01420700c10908119a0903107920f8200800800a600090041207000d030440da103070302c800b07078407600c503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465993588 1250 465992338 465992363
    0xf060203010914282c01020d0c020703051207060e060f0a060b210603031b030a020601051c060905160305010b030d030c080411040204050d05030304060b1c030809030d09 74
    0x182042d4507000403c180c03036089000f00075500400740702c41d00c2040b00c184130f81c0100b86140004400e42d02c00e14004918050a8900c240c1c1ca1494501036001e040f520704401018080c1c0d1440303a004a0343d03403029000180407600b202101981a146c490b008141c81c903c518000700b5000c66101403682040d000720303240d2160800c0c4801700b0200414500c9204003425480d40341a0030012040d410003500e4120511443c440282030010a60a50b030420664071502c0c5c5021200350025980070070b254503600720304184030240c89079100204003840c0c05542c0403c102400108248a03101c0c1e6298000903010800c41039880d401031100c6102c07105601c030aaa00954022000400c4143e81401810f24003410883c1d103030201440c102051200a901071603003034201d504030303825200524031900014002c1c031a6501c4aa4400317074405402e41008008805184503502a16040100f19180014070030040e00c4400440021440b0031502800640140442c64020261104072410481509035071b804850342a0400c0d07885201248 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465994838 1250 465993588 465993611
    0x1205100203090a0b011502030a050d020d29060702010c061a0a060906020601080d0e1005090301020304210c0203031c0e06042411040308070305120115020c0402030c04120f0602030109 80
    0x103681c014041683c80121b007050a882c02501c2e40030f51b401c0e07402005400981070300320013900c3e019100200c0e80380348100105a09000c200000c1c84040580c00259005071030141c050b07141c008141c80201d50180c60f200d41e0010b050740c41c040200740c480c0b845050000381035180b44007902c820b04103101401460701c6002030300d401c14001a141c010141e21100301c5038006a41c82d0070341c503480640194840c8042d10074a00c45225a681034669004440e621500f4ad803010003007006224500210640000b000101c911280103039080c2100c0b100d00f01c00c8065059030003080080111705038401d81038600091140c00068aa50b462203581c10030200740c2c3c0c1504c05540012010840815003401c013201c43c40e0701d800c1001841ca803828040d400d80030360f1002038200d00020802c4030505000e00d04442d1400001c08800c14103603100c2e03038402c020b0403c07902e03500c2c01882860502c02480c10729100303d0f4010a291103d96080c9442c03c60138030780030a82c1d404203c038151302d000341c220002511400618068030040f140400d8503034008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465996088 1250 465994838 465994853
    0x108010203071b02030d140c060c03011706061e040b06030a1a01110c042013150e01051611030f1c0e281203080615070803011205100203090a 62
    0x481010064107065a1070f6006030303000203188900402504000d010000d11a1505085008000c040541d50094070100101030032881c00a505890306100310000c051400c9400a40d00e55084516940001c00360a003989400c0c0c0f03400c01c80418410007040420322210f080e02040032900156800c82d01a82c0783c1e21682c0c05a070000d4030b0070900369400c0c0381100c02400c8040e240356480c0c1e0565070340c900550780c54401a2920803c8003014401d4416130103440d07510240215040903207102d074070034000d499444645e040c502078824200c034095804140d46070381c140003140c82094614089080b007254122804803150000f030300c09000b0541042a110054a0a101c0e400d0709101c034800e0140440d0104510310ba02a0801d0b514030068403050601310341c1602400900d206031502101c029007001e402d01981140740c104242c0c1c0581000c1c80794a082d1100098014400a10a103d00a1600081400b01d00b0310041c0402d00805800c2583c181c010806c032140300b082e40700f040701281d00c02c0d150010940c201e07610074014080803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465997338 1250 465996088 465996107
    0x303051803090102071502070f0e0702060f06030a03030f0605030114040623040602030a0b060d1a040204060504060513030804091a0108310209070201060515091012090605010801020307 81
    0x6501442c80c000340c03940001e4035440f06000e003c0b80610502c01986c0001d200304480ea024000c9410001855616141180d107010003ca418800510415000442c1448909021405420040c0080c02113068582e41613000d0800c04402c440900d5403004001030396a824006e010341d805c10f00340041c032181083d003002d1b420340710b0340900c40c002c0c0c054440c0d404145007030f0922202e03801508000c0050320381c1c85140148020b02440c69202d5808031012409640d0344080754003501403c414141d152404401c210103100682c007440c132940000c210305020030810103006100800c0c025a8003988089002d03240d80e90200e45800580110000e641d44001a8040c030880300600c40f0301502c2400c110013185000c0b04c1c1c0b0b90140300204140c0c6030f20803000107040464030003290b20134065503000700490301614050000070b0007007032144501482031101c00708105004110100b25480100302030f1903d03031500303000402036512000d0407c92090103640e031150301c00400e07124821a4041d14940c000541d0703a0401d02002000c1407007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465998588 1250 465997338 465997381
    0x10b0715020a020304060302160f030216080105060916050c0102070503120106021b040e01020c0f0a0b010f060906030c05310b0f0405130213030f0c0e0c030a090618030305 75
    0x704000c402d80080c2c00205071000c0700c017a481c0140e0345031081c0c1c1020040c1c61102800a150f00ca03400005800c150f0003280382c9449801d41d80c03041c42110b0355800010701f030b10001d4a0064200715400c0218514000846400448960358140b051501c41105e04071401ca80c0520000c2e2910340021510204860820702403c1c0101081c0c801481c030b031015801307200900f0509000300c41c4181d0359201081417055003074040e07031040701a01d4280e0304c40842c03008007075486401601c01200da02910300000304440200c008403405071203941c0d50700b0346024140380098004101500300e81e02440000d0155500d90508400c801c104a0b02400490722001855000d0460340c0840d5048800701c25000e1000780031900c00b0009887c00c40d41c045803804c400901c00510f60b8000e1040708500c0f503602c2c21807000030050041c0100c954440510074003000c0d00c001c0d47d401e2050200c0c00150766011136414100042100b150403600400d034964000e4000007601c00703241c08201440c400308041240800d4480080203404024260342c50070382d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465999838 1250 465998588 465998591
    0x9151e05030121060f110d0c09030302030d020c0111070503120a05010b0702090408070204110408060609040b13050708030310081c050720040203070302121f14010512010b0715 77
    0x5040542c0c0711000b1024880240b291003102102c00f080c841c4035008685140d10100702004102003200011089a00ca1002140f607203042802c100c03410761180700c22104a80d0568055800c03d003a512110010354005034401110b503494003151f10034292100d0080003c1440348c4015644e8810340e00d0300d40c0381e85c1d00080001802600d001d0040025104c20000c581c09194111b0301c8140e940d80d14600071407940100d00020b9001031401281080351038801c4000d1082d554801d003180e0066946100700160101d045078000c100e1448040441c80d1001003c003050300d01d5100d14180c0d04c0719600c40164034a550000c03500390170360700860070341004005000d010140e2840406509560009102c1e107002d0924802d0750001040d400710001a0541000c0891034055000402482503540b801c12910041c0a90003108152445540c5030004c0b601c0e0380701ea10700c002c0403400750101141a4500d415002d8012240e80d00030581801000c100c8021100586074905010344075094455450b110743c0d0070b0008581484240d000c80c0c0c2c0c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466001088 1250 465999838 465999841
    0x7060506010212032703030a0c1707050904091109040b07110a05030a050c030d060305010f051f140303090303210609011a0f04170105180d0909050709151e0503 70
    0x8400f59400c482c1e0003641510003c5004030400b0300141da00804004c0c03441d1901010041c0a418505038028003190312441d910130807039009c400c031b4940c0011410f40320000850703c10010030225042c82d4000031001401003003d070f4404020a00816601082100d0071980400b840f0100245140c102014804d80911b0380d004020380075170390780c5042ea81e11071030032218107000c004149940140c40404c200c8051b00301601042c86416602d01c1c107035010b4550030600315812030030080085d0070109444d111106801549240740c402030b00d00b84041050980300044160180000c0240359a5510700300014280301900481c0480c52020303010400901c0c84000c3c11042c070424018004001005241e01d84102d100c915420040d5500308400d0700740c84070303ca03582c46105586814030f00303224801410340c07040348a1003903040700c0501395154590307042c3c1314208001e4040120304144010b1040b500b607584460b03401b055908141e94080e03115040214040251151400090748182d220b42c0110302185003131600400a06259086 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466002338 1250 466001088 466001113
    0x40f1a030607110303060904060917030106031a0f04050403030b041d06160c110321120a0e0a11040908030c0a110a030f08070c1b051c02150c0a080f070605060102 71
    0x5170b21004e0701c054810151000410180402c42d44003501095001003e5230102001c40f1000d0500c1e0424445d40f40881e183c50341c600240f10440304030800240d03009051103201d401141c00c120080c0000b820640c1050354601c0c1c50340490b2528440c210140740111031100c64054417000c0301c0d01d801700040a03840e46070803200c003410340107400c2038007242040c3d888890012080040008240b03014040807100211440300c0c000184403034000300040c800b03101c0500031008a60b95420b40ca034145d4120303c007074100f01c0e84400f02036004606040f00340c4582090083c40460513100356140c000341c90700180c071401500c2c1800100085030780e4110044200300071040303011700281401d5890180c4541800400031060003400300014091610401d0030301a1158085032140d0040386030003000300c10b4049030043c42d0080d081c50400e9066800d4041d401d0103456402442c01c42c80000c00030100b81d4a42140512810501c40c2031341100005d05c50001038200107500e400d0841c0c0b14002d9050260681304043d1801d0706640100c41505d80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466003588 1250 466002338 466002343
    0x3020a0e190f1d13031e09031a040201020601090f02090a080d120e0a120309150c0e0a030c0603090c03050f0a0204050112030c030f0908121b0d09050f040f1a03060711 73
    0x2d01c0455100c4c4642103030600d0406035607540110b2044040c4180c002c0415410a411040c0306080d41d0103011052400ca0503203680600c0060300b03460180c096401200104040140b54101d81c50a031311404025041c2048200429512801600540e026410020304108002d5105084007550074420746c0a000d094004c0e000b00d901c0310301c103001c081c00c0c02300580600c44a83c2c0c000d4000d4000564080c82503002c9402000c502c600401e404840200029480c604644552502000b010152500702d00d01e403000300d04c0e0503401d07001010140000c4454900315030000000c50300604c09002106602c0010b004140b84a20400049510580140d0068516042d915000c84c1d03008003d403441c1a0b141c1468800049080000c2d520b040c200d0b03000368440d11603020206001950000035042c9021450140711101407a03514880e1950500322031400080c403604000c01151400d8480e9600310344d005000050299094071608055804608450708080003503000c098203401c0801896512030000e1602e8000029448450354 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466004838 1250 466003588 466003591
    0x70629010f05040b160203010c111b030c0d0303050a0507050c0a02100e031e01270b06060d0f0504050d0203180d05030f220503060601080703020a0e190f1d 68
    0x1410400300400c0307420264007501c110b501410001c1107003602d4022607078460021240088049020b5403e000c1320f45074103401070f40c18402e00c030550030250070301000410070036074007082c007001c0c040d41481440300c618a0350700ca00300c800351614000c4d980420300740344c00c414070b0050721005404582042020460400d441e1808a1008102030f8100c0c1c05030710700000400101c1308003c5c1002440d1307240c01030085d445010164040410001003101009001c0d00346c001500304036030400d42404c20244020407021100090101544a6210038020945424101d81820f840c0845140d821007040b0241c1c1d071070601084c05070800154038010101c2c4011132600e89080d0203896080f400449043c01a60040040010400c0910556540401000300941c0f141c0b0000c2000340c90740e00720810400d203010780d0342c0081918100030912a200b210180c45040054540e164110020340c061411a41000000007041200350b5801401030078208544244280c15810a2020003800491758840708010081070241291160340c2d0102070f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466006088 1250 466004838 466004921
    0x30f0406050a09080111070302060f0103110d0f05030409090201020c090c04051e1002160e010501020604020d02310f0e0c0103020a051201090504061a0d02040c02150c0706 75
    0x3161910840341e81600c010f072803500041919401c01032460075400c200e4025041c004c0c0203074216035240d1034ae8418212011400e0002600d400307000460942c250030005a1021641d2040100043c1c84001f600ca090440c0c01c40d0700708941140d00c6410000966074108115400c0e01403c0380c090700c0d507040144030300384035100300d105080c016080360194601d003006000044c81c1602018149a503c0101c64200a481d108034074551540c29a5000d8045000114000898107a800c10780040c0700c3e03612107400300082d1400403203049a1080c511300c0003100000710b07805d4200460b40341500d892118030341a071a84050750321078a4a003104900c0c00c12400304000000942144040080c200165030b1900580200c8092190003110800c1c3c140d8900001000000c40c3d0200344105d01400e01041900003545901490740e101000c5998400c804044072009440d0940c804840038a60740120744c134181c060076407424581800c46d050f007451500072a991060000314000d910709a1502203103071881045e003003150443c00300d004010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466007194 1106 466006088 466006097
    0x2c0a08030405041805060403051303020301090b040209150306130f120e0f0618011809140411010c03081303180306020903100209010e1309170307020f030f0406 70
    0x1401c2903136501101608003505d460310112540e0704005030f1a181c02c8202500000141c0c2c0c00d03c156500b0b02e1241c1c403001600e141600400c40701d544010101c02580841c2e500990741541e0109440d98889205408406041d50074100300c4900000388600401100a0894640705650050040814008202c5061701c3c0404603c083c03001c0c5004121201240b08681c189106056008a00002802a14000071580f440d03894503400c0c00d540c0c0403410102e221a07085d06110510200e030f28150801c1c142824202041c00b12079800401000d0028982c84850146200010400d0704c501d08d0b5141c070300074010040380f80a840341083e9000b98400b2203403910a114005820346103400c1d80c000d407800e40605071180c00c4004081000d1110700c200032507070700300800c0d5900001000122800804030501c0380100840e502d91510400107460440300140d010b505910a0011040394020b810031501501c0076842c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 465827338 466007194 := by
  have h0 := BRFrame.cov_init 465827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 465827338 ≤ n) (h2 : n < 466007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
