-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:20:26.230341+00:00
-- url     : https://prove2.me/submissions/59c2361e-07ad-4e16-b954-a7842ee00a05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62050362 ≤ n < 62230218 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62051612 1250 62050362 62050367
    0x3060b04141509030d0507060213060801151707050f090301050f061201060605040b07031107151b0809040b0105120a0204050103141303030b0a1809120908031206180403020616 77
    0x143ea007410b0b4065020910f074003003462041006005a0340a042e006041c070340302401c0a05540340a5210704001040280107000496100c54200500784090403c68a228411651840f030010001e013a0f030300b032000111344000c100310900704507208000b009008200b90701c2c1202d40c1903c8008192080b90151000d0300340003030b4069052184006484c12a11003a040c5890010308180f0741d8070040c0110104040307590140d01415003003051034080c0c0f00301c00d402c09041c003a4100003024039020007000030040a0104120000c105148126005101d040d10042000307240000181e40c0751180c124035007078529812040044520155005c0c2080c5c5400740d03800d00098014040f00b1540140c20780d0b94a500840715210131001074001d520460320590b01030400c41c1e115a440349600203032003201c1503030255291034003941300070401000d4a4070507001c3e10741810503000341003842c0da41d60390040151b00040203d6440100b055a507031180707502c2000150340183e04051402d440c001303482c2d100c10399000200c0d10210140042c0b060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62052862 1250 62051612 62051617
    0x2706060e0103030e2106091e01020a0504030609050f06010902070c0501050403080d0911030307030801090b12030d020307020709020c010212010b03060303180604030f030f0e060a0804060b0103060b041415 89
    0x25019030318101101c110a08202075140d10310310301c617262002181108080d100a1044510403205c49004d854510f825a03014410002d401e41180b21a074810404d00f07146a8003c002d072030030380340c0100700010106081c2c6803151900400001440091040c1c1e0000074002e1140d800500b0781c548079001c03c0c03400c04d94a070015612130059010080c1038000c00d004641107130350598000043c0f640070340c41540540c0c1488020038150390103400c040c1c0001e0036550061021075030307600911344d80c41c106039880d0f44001c0f03000b401a52a4003c01c0c40340e03102d441d00000895122842000308601800500b4421581c0e0703145115103500070360091200c5d1800e9401782c000043c503040c55105407841400d024000d103140c1107220910703606d544420a00564070000500c404030100c0d4040d19a107100c54030a44503240c0010180002904803e011255a8841d440030004010358590204185030015170260002c100d84100100590182456401001d175041c804240004d00c00300024142860314000c0d102c0c0d41980181031101b10451 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62054112 1250 62052862 62052869
    0x6150305070f0302060405040b0406090f0b0a0807030b040308090c0301050c070b060901030b010b0f1c02091c0c0314100c020d200a02060304030c0f0b04020a0503150601050307032706060e01 83
    0x14001b4401044a8186600210022200104001025911050000116482c1504004003199260507000440c100350b2000005052100c0c02444032500c0c59441c5003290000800c0141003100080c080340002108210101404000a000b4030580c94101c202c5445034007c15419688003440a0104046040c608841ca0580750000300b00003041e8200f5100101d80c4c0d00030080700f0f100040070440640c1c0422418143e904e0300a886101680e28291032003001184030300d4042c004103042c81c100304240058096040391085035880103400100050201c60302d4203040b24602041c03541400c00d030881c04002e03408140c2d102c00340e8068842c0c140d1404010001e42801c09290812817180d030040841340007616060020759807142c801c4c542003010107419a20044130356a10b8204a4040a0203404e00c002c40c5099035511010b00019030040605107445032541e4041d91010b82014180000003002c02d5840d032094003c0b40440034000102c0c00000e09019412540fa5000c00044d00c009107400400b040300002140c1d450b049 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62055362 1250 62054112 62054119
    0xb061e100e01020a020301061202031c020a0312141801060611070e15060c0303010905130f030f27081204060203030f100e0a050601020f01020301060f0c0206040306150305070f0302 79
    0x12889240030030703152012106140c50540c420003a031a07005070b030240512405007140e0f1b030408503c008d11340305140ca400014101400c206600483c135400b06d0b80d00017680d0078080d03010316204410850181048000301000540d08900d802180200000554894a0444103810901c02003100d640e0b070318002c4500008407402c07600b16070401ea82c01c01090784407440c116081265500d800e02c40f20113500004244d41d010307200134a261707000400100301150faa84296503000032026030000c0046c5490751241a2140700410040501c022268404941807140f502842454210840c1003514204030301c240d844201207200301c04182c4039004241d13401601a40503201140d003e90010b5046480d4400b0362402200024007201d0740b1650341d000040c40d40202205075000d072144020008882c20080002810014413120f540754aa0042004002c0c0d10350210103906680003c0c9080c4000040d140300040c0340307204503030014040c40e082415820b0215004854002207034032500480d0a400d903182d50920580f021440040d50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62056612 1250 62055362 62055379
    0x306050f060706020408010203010f0806070503071b0c08010e0109111207060f02010b0312071208042102030f0315120708070b0d0f0603030e040f140112021c0b061e 72
    0x202400c010001e071070524443c05000d4105910341aa4a0072a00241d00403032520700703c0401003110103001e2003203640200c002d10f852451441d100c038004e484000c1c43d81d4902582c80084402d502480742421418014250140c02408602050200540640754800c03007903984030a102105a2203141c103a8204480c4a0104060a451490084140e416900c00c503202d4056540351000d40c2c0580d6000d002288121a01000c100c2e110507042c00d249440d25603001481090012a900380004105004107864820b0700700d0324001c95400084404900b94041d10241514444000c03040c010b01c0071009907242070011041c0d079151050111148030b16a14541c3d0b10600b10b168200740018441805040000c01d2818003120340403c0d445580005402159130a500940001b100c0c211007040038070301409403040014032218107110041c01c584004c2c000100c10b03c60002e151a8100d525070854484694803500b0142d01035441c0440422410100441001141c10921a81d41d00c0c0115124182a0704d149090503c06004c00d031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62057862 1250 62056612 62056639
    0x30606010809120a03050106080a0e0a02100516050714030a0b01091a1305010807171507030b10020f0d0c230106080d0201090c0b070503121b030a0516030605 69
    0x11000714001c0c10b401d407a40141440350758038880340300043c1028155503030001007540c50072400814103203014088a581d00e0502c2104081030000144400020781c0440703080c5141100000181e46601c12a803500007140e002d03c0340c00c401d2010210700742044030300ea00031400020a07450f007015107502010350001c020100ea135005200c14011680803052003550380c54140003011014001801d6000807512604d402c41c3c8400062100ba2010b00c41c410040424200500180e55458a441d0300d61103041d845100e200080070000d12a41c0c1702e80c1016040c07d00140144008003120000203464190000401040d0b200e800d40300040248110880030030150051040b0703e014401c40c03a02850320b5001007641c2d56564036000d011074054070600103c121500705400010303100d082032524040c800c445a00103540c0200c20703c060350110300c001c41210740c00315001640a41503603914100e98111910301c0050311140784c021040281c42c54480d40000c1c01110326804c0341069040b02103040342a40c5250003115000086c040841 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62059112 1250 62057862 62057867
    0x60813020102030f0309010b0a0b0309030403110409230601140a0302040e100608010903140408060c0f1201030b1f03021e010201020714070f0b030c03072111090f0109030203060601 79
    0x4801441441540d150110741002c40c0c607141c0050700c1161541c2d41d5401c04819a142c101005002002c49030421406c5184c030b030300c0c080d440340105d02c0040c0840e4665012640d00d9651580550f55699200c1201104800d400070400310050610b00c0d0004e585c030940d0000f0076140000045e118890364010640e41589045900313020180c0f030b007901034824030f12491540100c0300c00940205c001804c03441000080d4101642030007403545601807042c61480070b04000502008034040341d4140d00848011199a03241811100110305110300e0b1a10b100c006812400802081210081103005802483c1c1e08006a2410700c1c8149004143e840700961204401005440c1d40c0c105410707000c02c445050000504003009a201d40c0701080041c8034079081c1e6080a83c040c4687c90740d0342080b8004d480390a00c840e040d460b14210300d022910028003031506001141c964a2400d80c45011a400c1d82016000c003403064042989034a0142d411144805104015075890004603501c10a002000c43c0c0d0020002e00481d104c18006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62060362 1250 62059112 62059141
    0x3070f02120403063b0d0806061210030609081c14040213020c01020711090705031302151909150201090201020703140f0a0b09010b090609070311190210050a0203010608 74
    0x4103850030841c030030031051810a542c842400c401d4000b00291843d2105e00c41601702404480e0b160f003403050030010b200d11a203850003556007050203103000132000c0c0c8070360204090440460f4801000e041c103000d4403808128004010f0640e440ca00701c0c604042c0118030900c0c00507200c80d03d801e0ba1f03010090000040240c03914a81245000342c00150061400a68a00381400e81c0d01c01d007010b0303442c5441003c1d5800300d4103000c0303841e540c01801c1d850b00908505060000d40c1d0075a4610102074407454100351011120f90f90f070002c545a802088402e0745008585503c0a88084074a1040b50080701034002d2240d482c50060141d07920707007541603001d0683c80d82195200d0003030484c00000c2a046201e0f05842c2da101e13440030046000d405014a010100d5843c100e102d69007541d120100c414080c10b10300040c0b00c03c0351256503440d60403154500300481c00b5114213030740c0d401c01d00500c05003a88141461242c1e81429402148001c075100f4514004e100e03558407600000300341d200a100d250006414040001c010a409140303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62061612 1250 62060362 62060381
    0x507030831050606030606060313060f020f0301060c0201120c020d080901020d060e10050a0b161103060112051e0d11010207151b0801060806010c020a08030301030803070f0212040306 80
    0x16118084001c07018814400400c040845841d4829014000c45203810021180e00c00720072120b40d40303940b50040c2603440603c914000104080d1312075414080844081d015501c8a0502241c420780381d40c0d4500c0c008010350022281a408114140c003115159110f9004804001c1c0e96600200748002a10780d0840b010385008190100c2c80d54244070403807000d500d50107a04010b00960110300d015003003000e203a00c00c0001d658481d61207070340820020440c017602d000603a030a2940c05015603c0b582540d091045640035400c2107107a15005403000405c1e180c46610000035a40e015170225621004065021045c00500003c14070859000c0c89200c100c0c2d81c812a16074086006400016040030420b43d0b40c1d02101c140d16504c03000094440901402c1800c0943e003426944ca01403034440425407500c075000d080d102014144c1c0d410011581550400d640780c00b18004020f00c1c40a044955079030b03503400c1002c0190000d840140026105140c0081e0785071000402c16019107a007200c1c03614017403031039440c030004096484 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62062862 1250 62061612 62061661
    0x40206250c030606050a090e070b0a0513170c03010b0a0e0903040305010501090c0e0301020913020d0204080319020601080607080f1b072004090803040b0c070203030a0f03060605070308 81
    0x30912000030745a800d000000d622406000c04c4c05400d240030881460901d400103550180b5041d2070a107100c60024124048640f40320b900c0e07076035041581c01107a052083e41e240482104030f00d800001d81c40074080e800c03807490420105850800d58050201404c0c2d0322020700890340010103c0d4103000b401100545150040c06130306c100da2805660f560b8036801c1da14264482068507584402940c041e0b50402c07107181e03046004400031032800c2c00403400201e005900308040201191f0104507020022030590440d80505481012282c8500010440b030448040b001440c070014069040001400304001980d540500308507110307100d25a071041e0081415040c000c01c020105481c0d1840e002e06060450002c000343d601524400c9a12028040c035801c86000b0148600c4c00390749892032030b00114a898098a0304140d0098100c8510b46841c800d40c0c1e480d00446901940c0b50100150f280300ca04c0d00008180c0303001007292406d01c0032560b203103020f444078081d1080c0a0041011000060102280c10060721099410823 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62064112 1250 62062862 62062927
    0xc0a030b090a1a0a0305060a050403110f07170d1b060213080309040c020304081f020403020306101707030b0a09030212031e060d0203030403030c030306090504060507030b09040206 79
    0x18001894040e800e542e005115a568185200200d94071400079012200903540f0080036459555116582c000081003001d4055891012500701344c85404034081404190080760340071b19a61440c0c0d51280164031505d41e07009070381b40c001c1c00b10900100f400c1400340e05680b15a04000c56103a158884100600c03000c5510a508026146581c43c0c00301c0c81202420040d402582c44100f40000e010464a0841d044015580184000c00c02841c00003040e6204c143c0c1c4501c1011105011a54078010303000e9604005c0d414011001080b849890b059404000c032a241c41050200451840c001c0e0348590341804040c1c030111241000681d503010a4004100040c420310448003c0300f1186a400d0660308180ca10ad07040c40070300104c01c610900c4030071200b0303005101242e68150740c08240c5d0002c1c0e036a1203a0b1000905100381c1c12101802d05000b980120000d100c1d50400f0302c11803400340341241c001e00049441300c0c00719182c070031323035401714206445902c1c070071030380945040e20b0180c01c04000c0c400207440c00300703031810420036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62065362 1250 62064112 62064131
    0x60915090402120906070c0b060f0d0b0106020c01120207031b02130507020c0a080c131e0f0605011209030c0b06060d140a050c03070203030705090103020705030714010c030b03060c0a03 81
    0x7148010030010800c4a0f844105003410942a400d051019000c0d804101c03c0003190400308550494a42e0050000c031250740d0108101d0000c51000024001d000e0701182820000280154000c90b0b806174104003640c8403048a900820448100d000d85440a400030303401d080e4600c1003a41d440c1c03020303a00f10300042007241103210400305041504c50484d403a80058105021008803400d04c883c0ca200540300e540060800700d6081d41c003158511404202800c019a1038140c2a414804150710746040c60307107409003d01003e2407070003107480604201d00c5803d00140e582e40807403044018611070002c00c5540f5564956054001ea16000300e19403014001c076920440800160a800400707100e071b04c001180c03081071104c5600d40014031000b1110014020f82d058101001004010340c0e0201c202c96000081d400c1c1070fa03c03030688200480084c000c5c0100288544070011b00f4000744010790343e8036548400c2e100020f2103450341d000001c9040d01d0741c1c050340a4160b80004003043e21a00c2c0c220103070440c20304030320f800946440d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62066612 1250 62065362 62065369
    0x90806070c020d0b0405010f060801140a0c030912020319140d0b04020c1504150b03030f130e04080d05070906020304050906060d06030f060c02190605070212040801060f05030c06091509 81
    0x10180c030103c0d0031f81c0d074131aa03040049815014400c02403e010008010158010102500c52000140ba0744403190303440350001c0c0640c0c069804010800d800c50807810b2081050780002c0e41d2580035042022100004049503134450348614070400200003c00740203030900909540070f102074400440c42540c000d030240170a2001c9542080b40444d803ca0001c0d05c8441030510382800c5101800d0080c1c0480c01d54141340124200c1d07100007080f980300702d42d5040c0072541d4541600c450803a8901c1c0383c01c0502c00009003400c0c04140242000546259100840c040101c0e45070010155016000c41c800c1c000580c01c140400c22036031514816055100385c015011b41d02d8010101290411680c85800480e03100e801c071101401407114600c98111129118002041d45800d0b0105d0904c1e4401002030060a082c0c0726000625014428050000d00a240a00e50b42c1c9a0362500d041030702820090060016203070b0754142c0003c2e1490001541902c3c100050b000520f82100700042c40124051280c00c003809203820828001d0544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62067862 1250 62066612 62066633
    0x1060305010c0207050111030703020303190605040606170a0b0102060109020a090b030a02071401090c090c020a1403090102120913022506020d05010501050c060c1605010f050103030f090806070c020d 87
    0x1411075001e401605e09000c00500003020250a03221a90b00a204c8032000076000001c603138110b40e800c0300318003843d0344a8004d90042e1441e0b03040b864005007403020025255801401500c58440301c1100f42c90b0359600c206004040360b2845451a0040c0e101000400030902103900820308416149043d101c01e81c0c550b90029840d42c0142d641c1100c5903400245202400b20358602840b140061000a000180e15612480003d050a010311386e200c556858070341091500030001d04c1c1c89030354040c108814400040c0c0107191250080c0410501502032a0304907010703894803204544858800810581042610700070040080d081100f040d000c0030b8610303c00c100400c9a82600e4003295108003c00742e43c400080850105541e81039100303505000d0203000f41000c02c0c9011500b10341c4414250a00e13a1580c507100241100e400456401802e40c1d4644040020856015001581624065102c11402c41000c4004848000c082d1007121620782008003c41e91041c45140340144460000300f240c0e4850645487c0c00c007000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62069112 1250 62067862 62067881
    0x9080a0f03050306010c02090f0615030f01140121050105030606100203180a0f08060405010f020316030902030c060d0207121803032708030c1b0d02011209050a0305030f0a0614120106030501 83
    0x6140c1002000b2650bd00511540d0004122007406400e50070009606140d5190600840420071071003440d0710581d91181000e20641d1000c4a07082000c001000f03103000060800703005441c00303805400001001c505054a40d82001c50641c9e0040d86270585000c081d1019019120400d90700c039800d10b00010b8440c0c01213a4190150894101618050810b4505203084413015402003d141e401402040f034203c1401c0000d45000310541000b0901e100148006811f0000200c03609a0140000c0384403015040d8503405004594403d0130031003071a80d00c80f00d09491228402c003214504200380070051001a10852000c2d200884080d4a841011031034203480000d81981e800012309540b011883d2800d0003000c006854460032240014031107034400c1c0022541490505070040e0500504120314110b020427940081000340d0804152180c058403840d005100764000c0c5e845100020604020610030b948030721648084800441e02c41826000d003401384040d60be004040780d03105568903031000000c91000e020b5441c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62070362 1250 62069112 62069131
    0x4060e06070b09160f031e03110d050a0207080106030206030c0c010905010c0f02010b0111071a09060705070f0603020f04050112090f0b060109120c05040902030f010f0c09080a0f03050306010c0209 86
    0x130100c41c50700160b4100301c280d018409000d820002080800e0701e03003101c556503138144440a01489420304054038100d0400da100710142c4100e400721701510354010302420b80070700c480c1e00360791404e507690201c54243c883c103000c041d5106100300081191054100c005109282e5a180049600c80b0251034260869008920220100380b0080c0b01d410341c25030a02c21072521010908069000386c401c001400c0c0da41750742d40201c0050f02c2d2aa078205140000c1130381a5040404002c08895171240f503403800700d4035904c0910984643c3c8103608008101d5600034000d81d141c04c1824202181000d20b0100110340210110014002d015682e0340004040745642403100d1683c0d0081c10700104d02e00301800010902401540000315141028690600207800c8041c19411101d086801040480d5140002400d01084040350203413503182c450454003d403106c1e040903151040399181d6080d41941c5112040d00d0f4403000000910102c540b011480000340194007454000ca8180b400307206d0031509902245074040c098540404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62071612 1250 62070362 62070373
    0xf03010504060b0c06060405071701090f060b1e1c0f0504030e0607020d060902060903031c0c0f02030d0c030b0a060806090a0b0d080d09201203090604060e06070b09 72
    0x41e09050241d00d0041004850003442c0850484d107440d1550800307001075106603124404102564417400e546198121107252068117940d480700c44000910b05681e00341c40c0d09080000c00601c0036031520035151054541104194a0070900d540031546a011501c0400310301c07004c2d018a40100224030900340525045c90001509040c10b08001e01180320b42c0d620240315140401c503290040c0c50715040241019802740c00810705070b2103840054114020000915014030002c00c888451070b00d10307641e0625400180904000c40035003d81c04850f000700144090000d6070080180c0030000c24203034041130f41307001c4910380001c151000e10002414450f00381d026200152204050008070b02e00314907000c0d009a803000c1c5c20042211008003040c814110418080c000d008080342440a0b11666040f905540e503120890307401c1c41c02a00e14802d80e040518500034010704600c07034680c01031180001116203600c001804207041605c0d1000480704886111322054200009000351000202c0028100740a184a0703c040c06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62072862 1250 62071612 62071619
    0x4080a0819021809091f020f0705030a0c0614010608070e0d05010204080703050601050a2103050903010513050d140301170c060f0403021f1403070315030302030c0f0624150f0301 78
    0x3000c0707005c0d0202c212900034100c0e038035810290159400e00c516124002580380d1030705d0b854031205070060a402500a0000003100c506040e4081c4201d00100d01c22101001100162400a04110001d02848011880c0d5401140f0780c54041c00201c5590007006107051400210340c0d90740707421782e080f40d444800d059019000920401205106640c09001c06580d09021180750907464988011400c0d880c201304400c4030401800c2c54031030003c40e8a03003280074000703000c18100b500c80082c54500f10001901c0034001c000320300041c5442480701c00b1000d8001407905046900b84550800354045501409041d0b20a11500c0a590f45902000d4041c0c40c1c49842c0254a41c2c0ca10b00611819055030400d15070407410240d40001ca9641081c0b40160031454100c4030b944a0703540190aa000340200c81401d1402d403c0c020001040640c00401017001048020585402c20740503043c1c04d5482c1021303121100015a950810354000310300a40300c2c00000c50080c41070f4000d84d003c01c010030140d0700c840c3c0713807510780e820000061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62074112 1250 62072862 62072869
    0x10501060e0103020304050a0303200309030403060e010c091a071506050a0611031905091908010b03070f0308090301060b030108070f060c030507110303041503020d1404080a08190218 80
    0x2440d06070020709055185141513600d81d904c81100d40002001e056442c61482c02691403000c00b202c1c08603032110110340e031782000c1240941d260070030b100440c2c00500300404401d1007401030107244507a041540760032542a042048004040540441000603c0e005102c00d101180d41c0c1c00740500040703414400081c8142c14030090227990002c035001a4240403000c0a800e4001c4000030489011040000c081200526644403c550030310601f250b151348940061a0702d42c6200e45941c01e40100c48010000300601c1c0c1d911410700d51610b070713188144048806c1d00c030020804518600001d058002c0014000501d00d0b84504201e001c80d08283c0008101c0c0e40484414401191400f0000000d44442c2c00c1222003040b099400424512a190004004030714020303001041d0f85007041580d000e4150490003900c1c1241c071984c000c000350040c1000321000ca040410701d1116940e4401024001c40c0c20005082c90105580410b5440360409000c085140003842e11064042c0c0551004e0411488804c11640b028880b00080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62075362 1250 62074112 62074127
    0xe1005160903020102060c03090c1005090f040635030a08010e130c051003060801060902210f0402060304110a0e04050d03110a0c080d05071106010e04020d02010c0501091401050106 79
    0x3010300c04084014070150380c0004240e548004a18059030342c0e591390188941c104500c0c0034290381c004600d070440ca50341c290004080c101c1801d0903a00d03152481010400c00064404610611400910b10703010510130382c41701e0ba0000301e4411603100b8680450030200f00245103901c40300d400c40015a240c4010b218030000c403120709401c0308c0380d03401075080c01c0410344071045c0860017446014410303404258091030860003500200010040f034002080003507070324004007010354040306010740d5440030403004074240910b45428600510070441d0140c3d00d69555401c0c08616031010b40181c80e0034581c0009501103035106100c8001038620000c0809440c280341c41c3c524640038030200140709142c1032403413182d442d46000c400d4942d045180d24200d480c0c100d190501e841c07103210b29001c14422038200b030100a00f003900001c28008806440c0d0485009a0380d40303080c24502602901c000b9807110b04818140302540c815401400664010400000c8880f40759a440c0d0003d06024103034002651103400403c0103a81080c038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62076612 1250 62075362 62075401
    0x11070c03030210020a0f0f20071502071503110c0f070303031a1018230307170c0d1a040f060c0e030a1b0f090f0506060405010818010e1005 61
    0x401e40c200b03000c0c0345c03000c2c11a40100c0003d40030404070645401c3c00c2840f91049254003544a95114824070700802e103203440e0511030080d030441e04039201c030f107041551001a0340b008882508608100a000621003100071b0128003000f049207481c01e1100070344915040c09104200c1c0101001803525910b036240c080d007552610b100048039070700b038441c00012980b80d41c0f0183d03480b84990b140c074010840e0f0201c064400d10020383c0080314a2ba40070754410700307041030042800102c0e0a080b000c941c201580c0700c0c0080c6c0c1241041e2203101894104107480c54035802c0140c54001720314402d98180d4a84101044c00440c0b81c14115000d5800894180100052004138407401c00d60b0851031034900005084440400d40d00c8008001c01006040070b403003012030000c455210440a01050f0030040c441c0e40d0758035240000350000340401c446881c41c000100b609450036800701d074111413040e104c1c488207070389155506404800081d00b820760b654a03101c080541d20018424940300c0049600c0004217401c02c0390358052011684c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62077862 1250 62076612 62076643
    0x605010801050f040f15080a1103030a05040b0c120d02070615230609030d050301080f01140a091106040b0c01050105030d080f07090503060403030e010e0615010f0311070c030302 78
    0x3401030000e5140d04801c40c0c0d41e114143c8003c1102c00d5081c500700300901c030303048900d0003c20741034001151905010814002c0c00740620f41c801000a80003080580b00d11440d5400804504200310420503000c40d1005800d01d90f441500340c0d01078882000b00c046160780210344040e40b10703500048000420460f481940c1503150040c040f4250141401604400503a40314007600c000b000f082c3c0b2a6005941b04000c5403c4010041c0070b4821300c0349440c002030025042030094031014040c1c03c000d0b04007103a051041c40e507095407001100c000c80d100c02080324020030204c0c0c02a150811130420808203a2a1000280000d1121458541d90703000c002004600f16001a00b08034031a07080104540340881e8040e003c81e821420041d10080c56848001041d2a070041c1d0380d004641500840e8200030505805074800000519843c0080c001d540440302c48a4990f4000c5036074001203c030301003145403694407588090b030591000b403c00050800b10301c490340a05800c48241120062400642442016070600424981c40001c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62079112 1250 62077862 62077877
    0x31807030b010b0904150803091c030206040308040204020c0f03031006050301030503030612070905160f031b08090f0a080901030608030313060b040f0207030206011a0f040e0903130f0603060501 85
    0x650701d1112000042c41104100e407000b041c8140391350b803268800b84586030f01d0076546850f41d0b170340c500030390b12034001d0541c141c418103c0f45403d240c0b00c0e50000540202c01e81c0b60f03020300481c0d030715a80c050300c3e6264003800a0342c0095091103420703640001040340c40002c90b4080010b44e00c91400004410011071590010740400006000410000d00000181c9030000c2007180c0042d0041014544245071454543c800c480075414a0113108286a5508545444400301d5a5450074014080340c00d80944010344070390041808201d03d520101442010742c0b0740c201d001c24003a2415217000c0d8817403601e4403c5c000010b6850400000f81c18070306607023511524004201d0500603500350300d895160001c0083c1145c40240200390ac40e00c1001c0d41c0c1e690b50f0f0011700c02c040d50007021034460b2943d080003945c8520034010b84403100c40c1318071400d09681c40d01080d1078401701400b003001c0c40c050801c0882104070102801040f11840280010480d149500b105040586041011505c88a1034400018190349141e40f110b418070040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62080362 1250 62079112 62079119
    0x40c080c012a0f0f0303020301060e0a050303070b041103010e060a0510080601090b04180f020301061a1c090c081605091603090302070e100302090612031605070b0f031807 75
    0x40d140c49003400164410a070706100e40b81d00700702400f0306040d00d00400c1c003560390807107400300740d0150b0146059031a2030f035a129184d0301c18400d000032440c0c0e600601d50306500c144840000501c0205400e030740b00e0f1050002881d0780003540042402d6600d1104c500266130040002c00050a02c0392150039800083d2000d120355941c9000742094550006018100c403290711089500107907200c681280c668a00d0640c43c400a0382c5d40c034281103006d5425114128829401e1060004034038110b01c082e4a45035000e1101c02e442d00c101e044075015840c83d42054012002d4a40ca0120b012490407445d2200510141024120842d00c840c41c0e080c401c040d07504400d11a03803010051107000301415407904d035013041d2424001440505410107a240008076440340c03100804000401ca01d103070003403141f4401c981c826100c050440c0c82e98402c00251b8a516803002075142e10a11409205403065400f211109000d141600d025607101e00e0f1103c01a0700c0810402002c100010074410f0482020b410301e030203c2402800b404140b801d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62081612 1250 62080362 62080397
    0x3060b03062203020f0303130203010e010b09060105160b010909020a060311031602030904050c04060f03020f071e06020d02090901050916030509030906160506071b06090317040c080c01 81
    0x52014141202d4405082e00042500070441d00e0a4020500d0440c0d40ba890705080d2003804a1014601300e000e5401c00d40d84040b4584140500e80c40c81000410101e040e42d80c100c0111004e400c07640b460005904280c001d60046822888414080c04000801152100303403801807108486c000d90102003018544880382c810703820b2000035250441c81110140310300f0318036240d003240356004000790741d0b40c4103160006206403442c151000344210780d030a03140d10b0000c12a00c4000d400300d004240028058110411a540000e0414203030069030030015004c503c1c440d01c1c0340e1240422600800426070820380e00180300161440d0180110f03004010032502c0c0013080c41c00c10b400020640440043c10b050580741c0000c07500c0c02c07100b4025196081c1b40580903d480c0c0702100542e04076030400940955050003000080303440703a44200106203000850301d00c0040f00e10b1003681d07440014808800298108022410341c42000c080c01c11203180102c0c0946c5180748a00d0400d40d903076050100f0002214140a81c03241c00b00c0c174076034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62082862 1250 62081612 62081641
    0x30f030301121110020d03050c0c0601031b0e0a0203090c0f10030507020c121b0114070b04020f0d0b1806130209100302040507120501050102070b0304060c12020a030603060b0306 78
    0xc01200307603400c2d05440c600d040800d1503219800d50764084480b03181d0b9214242d001070481905401c55509010540368610310141038801d0f42c3c1504d1498001030014000b03e40007510305089980084520398041307a58a100c40034140040e03442c90041900001440702005e07041100350b42d8003078211802e006400b50140016406404140200e05040d1a00b00254815000f440400c905c17102c0908403014544a05401c692503000b66030720001c00d151002481c8a843d40724681c000400541c140f00c0d80c1c54201c09850b0402c040c20010000c81e40014000c48080c02c40e1294954406520300c1416109582d082019001404080880c0c040c15194018030402c076400c000070080800d460780560ba000d0854807a810340340c00281190308069080343c1803400b0310004683c009525084102c41c520708004903622032004a840310414810071440d410140301040110344a0303482071403403e550f420010181805516480c00343e070019200800440c0c0e880d0001c000b84030741801201c44404003100030708403500c0d2004066200d030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62084112 1250 62082862 62082869
    0x3030608030306060a1d0310140f0f010b0738061912080903011103090607080f07110c0a06030608120301030209010308090d141e010c080106110309040609050114030f030301 76
    0x308499468118020800040068401c0038040d1452023942e403012074041c000048007941d404100c4400565120030039045240550085030f000c030b401d17901c1d01c03e44188582004a0a03514a00411042c1c200082003096494800c03030b00e8007092140c03600307809055004280060016014a171400280c080c6030254400080c1a5102d4a0945402d080c003410031090324003610340740c0341d090340c6421182c0c0c00f096402d0f4061442103152804407003095448100032651418245d4a803044005a400407601c0710b4016510b804030340d05200c0859060160390710004042004507808040482d5440300103001c003000c240a40580a881240014071715490b50740803440520051102400c41440411540d541c0ea840180030382809401090070050481100516900c0700c400a090820240e400703000031420200c18003c8440d400e03407648a0590503860214240e400b401132081101072030000308912400b5030380b9445803001030020700500142c01d43c1003203444418403101c0750a04d4800d910125142c4008440001100d064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62085362 1250 62084112 62084117
    0x20c0c0613050603010e040c0609030812070e2106060103060b07020906040902090109020414100e120c0406081e0102160f030302090402070b040308070503100608091e0a03030608030306060a 83
    0x803200e900d008407045050036000346601c01000000007540b590381004440c0a2030242030355041003655058142e415050a10008042140601c000199458564041d0307900c810340d800c05600560130200014040d4884071180c3e0596103501d503644504483c200f2201d50301280170f0134100195414050b40c05854007031044001e01c150b0702c56001a0a5445a8001c00103565010b480d5880c656190100407001e50828054031000d50168074200d07510740780078a18029444c801c0d449001e11300d900902405168a14400c8506451092220182c5180c07201d1040e407005216010141045001007054043c9008146240c81c1c40c50b801440000348007070196241a1020b13501c01400c110b5030301149400d42c00313800344440d588d502c1403000c1040da0034005065001c3e4451446559207000b140c1e50703940141d403107000c19918813005028011081c42001d000f0b043d0315400c410500304072a0803d80c1c105415411070301151000015400a0900108054060241c00d01a00150016500f1458101c000c254607015900440d401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62086612 1250 62085362 62085367
    0xb090402070813030c030605070f17091f0209010306120c0b0c16060c0b0609010305120c030706090507030c06080c1602120703030906180311090702070f06170703020c0c06 75
    0x100081c80b000c548000102c003000380c103140e07981d05110300c1483d41484152825824100020700701c3e4443d41c9511002c2c0d440e074540c400c02d2003200780204040c44004180d0713010780c81403000c403407081c00840c452003020440004000d41d464824100040641e2003030b5000c40001d403054000000062000b51302c0c4800e0b1140c1c94003a0740c8510381401c00900c0c00c0940401d211a2012501e8082161540a040a40c040d40130300e10b6500c0c45e44030b00f01130050034042440003800c1030304890401c0103a280b01d28000c1c03551081d80e1048a040c080141c42d48001c840404000300c0c1d00e903000701d85c03c00400482c4002000100082d0608074614540740040c3e040c5842200030607800c2e0319952060500f103545091806144e840024200c0780b00c2d940381d140103004190300340a0080403c032000d004206c6100d01003818400d0b282d006e541d00d464485c044041c0060b00700040c110500798000e01101149480b40358000c880241880c0d81ca0040b202c0c21190b03030503201078000d007580040500402c850209080c1c000390403802c2c140c041e02c1d0300d035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62087862 1250 62086612 62086627
    0x3050604060504051203090d030b101202030a060f080d0801080f0a03030504140a0b07080a020a0903060b0a0b030703090b0f01051e041104060206040c09020a080403030b0d0609030503090d08010b090402 88
    0x141070101809428041c45d101205120298500081c941a103a0480d2410484c0c450b900c42000941441740008200248086403402e000c0c0000d5005990010588207002c40d210b07440d10380d52a07542655411004960307100b140c04000303082d0300001c1c050043c94840c020740351014007801460389400307052001405040d10743c130124041003819488100c80b84801420348000c59014600302440c0d51050b2900340001e200000481d080902c1842164013461054440c15901031456807100043c150b00c4800726402070154100159020a600066204076a15640000c2041c040e1420740b1088030054504400000808011300c02503c0d01041c201904040300c9500a0300045140000c01501a560481403034800114000a5a80d00004d026002e0703031048548400312034075003540104174055128008005074150010501090090348030140301c0b031020300060040681d40c1c40d0f42c025501c0c696000c4001071000400c2280904042c4904c0d40c0c01c4643d07281c407528a5241110484982c001c240c0c4c2c46108690008421 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62089112 1250 62087862 62087873
    0x1415060f0a0905130f0b01090f03110a05040c0203040801060b040506040608090a05010c0e030f0d05090112020c060c03010303031a030d030209031501080f120423030a020d06020c0706030603050604060504 89
    0xb50082c000102400e540d5440450248064000d80841034801414068032008541c0540e80310401e4451684040a88914540f26080b182108100c201d0700f0000c0f505001c00d45854a00804542e207030320360000c0d0380e42da00e4900307200d0031074400703510a126800341031000740020b51341e400440d42102c0140c81c160302e143d2948030300e050038a00c4400f4000c1035503180980300e201c100d401c50001d2005010031020f40780c2500d19110002d071105d803451880b000041c2d04100c00091580036240c2c440e40101524001070403e40615000344c43c00c5400e942210f0381041c0172004100b00741d8940140360710307040d08290f44c0b02c20b66940e0740401e07500e9210402060501da0040f80000503030303d04006540c05410396410030340070381d60346007403640e2560319000151020340030300c0701c119901c0300b030310801c40301224881c1d262014034400c6c91484c13544450081410551502400f0031070005a50741c8a200c1000d507015803401a582d00600c220a445c002140c0d00c03031004e05007000d41c100f01040000c6103288e0f0044d00311070081915540c51501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62090362 1250 62089112 62089127
    0x20903030d061401170f04020904030504031a1b0a0215130b13020907020a0b010510050705031206131109060f04050a0602030903100908030a0f0b0604091415060f0a 72
    0xc0742601072900600041d207028031007109070000002e03200e0718801c03015011407180740101180c6004800b41800040b800505086500030b5002d1b0003494078a0a01d81c0305c1d5100114654428085615000e50300b051050801120000005003800c1e14101031a004092102a480c0c012801028070b0080c000f10005000c80840c0101c40c2559900200f802182c2c903140038210204008802c05034020040080010310702400011580856900709076030040a83c46c000802290910060255017006414004900010002c00240807907d40f00c4640340210314018090000a50726111010742840c1800485070030343c90700704116400b02c481512a540e8a001040040d001840b0b103501441e00004051070010312241d020014200d0100d0880646814034400b0038400c054520608010b0413a850030004101c07154080e034460086681300d200c0100c0d01d0340d8a100083c100381c019038040070500380c0300d2240030440c074500141103900c09154446d0347e0950015a000c103080e801031050100b8115000110400b0141c0140341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62091612 1250 62090362 62090377
    0x30206180c190f05040605031c0c08041d0901020a20070302030a0302070e011406032e060f09090c050a0c06060504230f011503020d0b0a0e041e030e010302090303 71
    0x220300d00004000c00d48040204892184010540008030f01040600d0a0700034101261341c000e004011a00300d1110880c0c9250b40c6000f244140080155030000154451001e40000c2104c035078000711a81456050f001c0d040e80080591065910420100465a400c0b00e48011902160100442c10712980c801b6580303400c05a8102a501d88520321200007016800610003044e1500c600380004166690300440700c5043e580300b1030651040c2c0500c0042c03140a01c00c0d810a410300030b4003011024105440c2c0b01603148400e240c002d0380c00140030f040340b0f1a1858200400da0010b00c200c040801082140d158020010700800500400308090040130906016540c1c20050203000d00030020421014082d08010700c90b4030864104032065094030002d04404d00f080c15050488002881c4080c488003000303000c800035402400b6281c0810b81c2c4124901903501c1e8012060f010b800780800382c05040c1003508040898a8110302103c03001000546076000095010039201c241c0700c020308025803035500410000742140290301c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62092862 1250 62091612 62091619
    0x90601140d0c090e1204060207050105030604090b07260f01050607020109080607020d03061410120e0106030b06010905090c0d0f0e06090a02130b0603010302060a05190513050d030206180c 82
    0x10800710729882c10780e200b44140c44900c81140c0005c0710411102c041805544500c00c05a045001e04000d40d50058008550042004100180300001903030384c1d801186080e035040f0000303030711807048403e0131400c1c1d48007030503209002c0944041ca1400c034a00c03204280781402818007880c4c01042c0c2d0700459005d480a08040d00c5400c041d18858503241e0300003541d07000309901f0031001034200140090680d2001102c030700c05031005030071800c0d2880c1480090f030b02840c6d00c403c0522115902c20400e807560800b88074041c0507610545402e030f0076050034400104140c100e0b8208034458000741e414411601071410441d9005944004045410b405900d85200205001d00707500c400ca00550f001c0012010010980ca510244222a031400e0f840075178900703a044800d0809165005141000184007518108016010a9205142280c90a2503242040217207030400710004c0045100801c0d20804140d400051030042c020a580c2c80c4204145920000c3d038441000e0803104560403101d00c01c03174401c4000e202403424104080c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62094112 1250 62092862 62092883
    0x2150a050f0f0c030612030408030c150f10120206070c33020309010c060605060f040306110f0306010e0a08030f070507050406030203031b01060905010e0f0a05090601140d 75
    0x806840024180841d80c400031054040001600311940b000d0990081006030000740c1595120f6050040504802072906180c3c80b0502002810a40c10030003400041d075040040c100807910f07080150074406015000d83c010451b10401c000c42910b004400c1c800b120040025184802c0c0306001044240c40340b1500604840300c1654041003400013201e00b2040d011507200045079444844440f40481c41c110090600182c100b00320300c07501980320740950010540107250000c2c01c0350b42c1d040002e0140e0300c20384140100e1400460f081040c00454400c045410010f030044515045008644110900c030003000c0070f060048803a0b811182c0d840e03103a2600701400701e4404895a4030700e40d81200140d86c220110881d124403401c0710100352400c150240c034044a13800b800450070451311841c83c1e00c07008050402100e0030765a075600010750a2242c05400d00070810b0184103001410105201400190001d000014032400c00c0f01380080207000040c4541101e00028010700000840300000784200d007a65400f0f004000c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62095362 1250 62094112 62094121
    0x30c0611040e0609090601060c0201050c010f0b12010603080301091d01050a0b0a0819030305071e12060b070209060f060405040f06080d020f070b18040e060702011a09060d030215 78
    0xa8402001038800b150710029079555810b00308149244200c400480301c0e040740004100d00e40c091142c3c4118907205042c001e0508003103500a9084030035080d00070707203526203440d1400c03a1030400d070358203c0c03a0382c14440007449454155251490984018440d960119990301d6450b035103925060341100072017090380000c0c451802c12000c40c8001e0019481c40c2403181100d403000155047c4005101307441205040f86410f0302100c9078405038001d20b03006202e4401d2098207081c00c41c40c03007140c0300301c1c8103041180c0d250320f0714010445d2101e8080300d0503608484407040d0104000000750f9204041d055202001f260380b00c0c3c0318105107000c900e0901540c0d00094010f41007040d002d01d55681e40e00315400341c8100d40e0441d010811030350801c84c0d035001091031b07800c16078005032428482c0348072200003440c0380c41d60841e02080c0018454041012680c91100390000e540042d000d00861300c1d42070265600ca501c0c3e40300c003180f0500000c40010200200600724910914034081040c08240c0240300060754002030750380100003031a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62096612 1250 62095362 62095391
    0x504050105040b150d0b070512040305030a05150f3615010f0507060f0b0904050d020c1203040b0309190c03120302030c070209060a0305100b0a05030d0806010c030c06 73
    0x8040e82c0c101c2d4025001d200094002d02100010340750440001c00c4e41c0f45c00c104030303200e060304208050240020044208a00c1381c1c0012150f0049000c0d5100b80e80c2c40c3d43d00c0c54400c0c1c0240c201c03280580940b185005800000c0c40700e03681c040070150107450448052a52040c81c42141112078a0464402034001942d08009540e1210b40d221178882c003401c01150600e0340b40314004440c603054079801c0c1c0340416001d2250601082407039010741c0d40c3c0758404c480003031b9004842000510110084408480c250b0100549050783caa041c001503011440c00c1d81d164240004a101064503402540240030403c0c00c00310000c2c2d01c200c1d00300101030000000c0f040303269070f0b800a424009042080c80c001a21a0611800304a9400b8802e1084911402c002c5040904205803942040301c40e40c005450741e0ba0015100c00d01001240c401d0000807009491000c4c005a94410305d820b005000c41a94003d6100b9080340c2c841148158102403035aa10003024139000c20303908003600d0709490340c8515150103440c061900400315042c0c0d9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62097862 1250 62096612 62096621
    0xa0b1c050907030212071511150c0901120c05031306060b070507030c06020a08090603090f010c02010507021905030d0e120703020109020112020c0a230f01060f0f0b1c0b030105040501 80
    0x24002c0d500e281d17900b074101485907500e5966204143c2074541448004001c903118040840f9003490f050156903940509210518210341d09a52002168100040201656801440300c515050b110b4405002400c07041c0c60282c03450100a11484803014541d19150070021a503100f040a0004881c03080d403550341c542070080c0e5138020703801300720750b20840300102240d9940009051080b2030342c002005031030800c0050a100d1203800203000d080b100d1140384090032002c0800c0c000c91040c003000d0740c0005068540144000d1800c50b0410202154100400d41d142c080b1701c001c8101c0311b41c5882e601c5e005c141a00d41c40281807a20414441c500c10006001c100c8200701030381900005400b40c000d80c5d480510a0712503070301508030b1227000c4d04c0220a5005050000004500406610b4205035400f03850700c1c1c01072002039081c185030031501840c030941d654507805d0020200c0c082c540380c0a81030410800304a9803c0060061448c418001d00c251860701100c880382c800e0406400402400c807000e0000c2c00a4141b03403a2007406031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62099112 1250 62097862 62097869
    0xb0717130204060f180902040f0507110d0507020d110109080d0f02070e0105030a0605040302010213080c12010b0604060c08130e0601030b0f01050904050408090303040308120708060a0b1c050907 85
    0x960510000040180c2c030704d11500b082c0c0720b070640040c519102c400b0804000f00302000c800c81c1c109803524245402d54510f841072602ca00b0a54541c000440da10300c0540b41420510507141701072007418050000561a2200c003044034981c00101c21140c0440000143d4038614a070b8820200c2d40b16401d410700c3e00315407102c00414540403a400729a14282c894402480001c0240211600341d84003914850205202c1c2d08403e070400d000303000040c504049864941180c0c0780303640042c555039003d0b100f200240d01300711215000120b02c40c0c0080202c0c038030080009420340728034811401049035030401441400704080031107a02c56500d603c02c0c081940d5981100c021850102ca2860120303240c102001107508042c241d03607848420503958240392081c40e604001c0100170181007954507103018070000e485600e04100400c05035000701d951030b4a600d603000c00030302c40071402031140042210300402d121550b00ca8210540599911040103074031000b03100030440044c207100d0f481105590514051100c142da002c40d000058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62100362 1250 62099112 62099119
    0x61204030c03110601030314130b0a020307152003100b0703080105190501020d050a11030a080405060709050904110f0301090b10170c0402070c0b0708030118180b07171302 75
    0x6040c4084800d84c80f0b071024800a408900d10b04440250010703041d006082240740041c001109d1358440100080325000b5a100328007580c00011b4080910140c01d6020f0550015000203204480c0444034007056500d201144d621460b2000c4003258003a01c24031b0038800038218810806455042c42c0c00c1c002c5c4242020b206480c018420a81c241101c5402d181c480000d485041c2c00601d200022250100c030381b42d0200111100f0001c0c82c0100b800d114038180000c20030084184e070b508146061a060880c2400405040002400040c00013003080e6258451960390003900106050982441000414180e40a8889250b410b501c0c0010010402c0381403002140101c600c0d5221460716511441d013442c042407412110307410b541c060f20000315036203029002095114460315140d409540c0e0f8240d00c00e031301d8120030011903844001200601010304203021290134103030150814403090784064800031010f100203401078680180903000a150b90b0081d454044502c070366040d41d07204c524085060010062180c01c00700e12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 62101612 1250 62100362 62100377
    0x2151c1407050306030a2306010906030605090307050a03050706090204140a05160e0d03050415020606030c102c0a030302010b0310020a020d18030602030a0f0b06041d06061204030c03 80
    0x80c1e0381c03040d4107603485040d01800030280140d043e02d40c6980750f20303401c4401810005805d160b090079081845118024201103001050b428154039101050340d03c002c10014041d441030040101081d00012443c400c40e1301420201d680d0403440c14002d000e090b00603c00b075041030800c3c4200c84241c400003016441822407130001c20140d150160350008070b07c0542c1c007000020700d00310389031a9246040c019210f0810311a04105141c01ea42d003403106020300343d0865100150308003100300a20740c02e040c0011402c448007107a04023543d401b810700203000708482c01543c203602c01e001443c04000500c8003501c5410300c2d6000344008112541c034a0020b001e03205890078035009000c2c1a100055104e564001d403a65000143c01924810f01e0701e038030880f61100329030503504c1516060744001012680f64070056019951403040811000404101c14094900741501d050080000b040108a460700780c8055107034008132034080d6102a15020700040c254000c00c0440003022416205100402d90883c02190810b4400e0320340d001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 62102862 1250 62101612 62101621
    0x906041401080901020315040f02040503150109060b0a050a050c07080f03070501060902040f06080702030d090311160b18030c090c07020108011d04080304021804031809051302151c14 80
    0x2802c4c6d000c180c81d9000604101400c40340c944c41c0c00c0e000382c107910018810060500341d941e00042c2c03408100e540c2c00303410308000c00018041002c007030080d00050300e9901c40345880c002034054010018032500400c0d508100021034444000c24003404200011301101c0d0484c1c040c6605004800c0d02c13980094002c41d0700358070b840c00c0040d0283c168000d440403036880304050104241791983c1a80c05d2040149040c003180010840e01c03840c51580d00c141c2164034085e9644100030389005420500c1c10103258a008c902e60a82d640030042081d942048503207030142d02c843c080d5050b0641001c42d15004104c60b841c0d03030021a8800700722520740d42c0f03009014194000d07030760745103079980e0b51400d06440c1440492200020040c03900050100e11031200441c0c00c148041d01d00341200401c100000110303a0180d60450010340c40310b00d04400d00c104118448040e00c103100c1f08000c9803c1c10740800c10054540c1d2402070103504150184c0e82c01c04100000c0d02e081460100c0c1408415004c0c40050000305500c1c1c80101c803030f11403440400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 62104112 1250 62102862 62102881
    0x60206071d0a151b050610050d0c090c0504030f1b0506040b0316110f070603050a0b01020601031101090e011503060902090102031e040504020414030c030a0b01060311090604140108 79
    0x1c0d00400e4064807280d0080c0c00c00d2103c42c03d0481d111122024000704112007030302203419001411000740240c0181180341072203a0f00c030607101c2982c2d010382c0c424507022076050301199901c1c103808116800c4440009054060410544440c01694009009801400340400c103001c3e1102c00c0380c80c0e26045c03402410301251600c3c20801c0b10b000306e000d00327405450148005240d030301d802c40f0b516280f00800c0c2485000103092100141c0340020086440140f030b0843e1a040225075010300032507401900744a01404480c980500007980c842052201400f00c020045801e016a40503070751810141a4404482c0f51960f101d10070b1071440303c02e6504007000285003580010701107140d44285d45511905030301a6103003008034110200c2203a845000504894000c220004403507680344010310090040000b600038100b1010105800c00305c2c8620030703601940040b031001000510210129054504074200001c2416a4840d04c0011b800341004441d040740000501280000c003240b4080c000300380036a508210342c0d0712038011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 62105362 1250 62104112 62104157
    0x110303180901060206190506030106030c06051c0b031b1309050703142a0f0307140406080a080912011b0801030b0709140609030a0b010f08060c09030606010302031f06020607 76
    0x200010008030300506c885501c01c94000c1500018002c0000c40c442c0d480b9100d50502d90030961218000c1080016181552583c00710011450007001c0820000071000401003500d6440b01d45081301411a40070440040b0b51b40d045d00440c0c00c1348454000c104110a601e8000d0b9100e102d80001e0300c01e140803180400b845c240005500e41107071801035454400301e41603121111200860706031380e68010b07120b4081c4002520204141c800410010048214000184041c041144e589030060040c0740c1088a489000c00c410b442125089142550a00d44041d001ea528a0040c200d4410503050900c9641a00d83e5099100d054607044e46d005a10007055500d5400f01503442d0b009900c40ca100305100c040500c802803a201c006807150900103402c0d9a128039041d42e852402d090240c10546079014a203106000404080104650000540f00960700d45074405c0d000030b584d154000c15540c10141c001000501c000c2402c10007410004003100000d0803291580e0780603440c2c10003100c901c800a01c0803080443d40764100040f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 62106612 1250 62105362 62105371
    0x30f030c0c0405040f0b041b050d0803060d080d09060507030b0405060a06051c1803090b03010308040302190b0a2a020f090c19020106030303110a05030a09110303180901060206 77
    0x3090603000c250240405440010411381d0422200c4032a05d02090f1340c14a43c0b4429440f8014004541c1c2d280f00784012600050303000140944803584d4003500040030f50045a4000100310b8510301e00b0000d615140c10140f003007101c004055410401c1d480b04210440c0c210718010100c40d20305220717020314102440100c80d002c40c0c1d0503910204c800420015940240700030003c40219525003403901106440d6201030319141d440e00c100c2d801c015510031040c5a40550414080c018180000b4a554515200c0c01c416000354080070303104600c000b0030402120710000b00d11004041001d8640c0e1a000300c201c01030081a0b40907800d420019581d2442c4101510421501c0040c80e0f0061101c12600145802d10a29201c002c020031085082002045410f8490f078618040801e1583c0c00400c003e421454010140e910a010345403450105024810743c080d0400140c0c1c0d8002020b0400042e011000d04102110400020388207405001c0024a000e10341350705050741c1c0c1e40e010f003603920b80003e9030780749070032a40d4000495 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 62107862 1250 62106612 62106637
    0x4080105060d0f1502130e0907060203070819020a0c03030201020a0801090e0a0602030405070302030a15060605030106052b020409150e06150d15150e0f03030d0c030f09080306030f03 80
    0x10001000190420356000f8a181c04c03440042c1400c2d010b040c00101845203802c24580d00480d1400c2101900b8200a188064299440514205101035884860500807100591440328540c1c0c024550140b00b00550001c66130890300c502c821607038a040190003903000c500303c08000742088002080031046070149982e03055007000107003082403031034980e08003d4102401c1143c41e409507410000c0036a41c100806e000c1d003401001c05c2c00d0705100850741c42c411a44c640c2c1c005d01c1840014001000500e421406503903c902d25440303604c0c1842003400d1144c01c0b1034406220b0480313003440482e000c030348000309a1005400712000d001586c1d1090311414000030012089425a41c488003450b5491807485903000030b0078559500c01004503052410100350b0481c403409410a035880400c201c0140c0d15941e000b50381c01da00c14030aa030700f014503846510109880703110329800c203074103030344c480455002c100d200b5403000240708003042c030070490001c02d458800f500354002c2c2e440074481d1241c09040070103c0c1d400700440c1c010f0440034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 62109112 1250 62107862 62107883
    0x11a03030307030b0a030804080c090f101215050109050a0e0604080a051b0102030106030506010f0f0807050c030d110403030801051503040605040c090903080601140a1403090a02100504080105060d 86
    0x56000c801900082d00c00035040140c5443c000006255200a04060404d0744054415203414ac014814046001071011842c41803010501c03841078800c141c410240c40c40c1e068000d01000050504000032101c1644401e012840e020001031490f9903039004e68003901042000b40180261045100d40d209400d50740036140c1101040019074040c003400043c00540268085110100c20040d9201d0032600264001c00c0465200c5042120a6a000c03c81c405000e103141441070012050040007000818020b0180e070620400090300c01e0700204c10800e40305669182c040074007603241c5690041e1415045071000b01c0105840d80c00105072858018460b0170074510712423003c0e06541e00c0381c403038001411011b00300351007905810340041000d225600844031054041d4580f840c55003403e500040c0319103491070101514400c14070980131180c1d8840c0d2060a48030b40c032101300752079441341e03131106050200c9200020341c06682c140300340a5858110020f0001c50b0f040b00000c118a03a1000c1c14004004580100105042e001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 62110362 1250 62109112 62109121
    0xd05060a050102030c030909130b0103030e0a09022a0c1207030b07020106061b0206040306091109010e07020307021212030f0406050c09010c03030c03060315020c01060506160210050702040c030608011a030303 91
    0x2c2400340c1e61127100d281204d14010364a407103070030381070500381c0081d800109003848980407400c1184509008104d200c8003180790000b0010f00408503030194941c003640c1044620012071400b420824501c000707000410780300360050300c20480c1e50b650701e00c0c3c8421640210341d407000030003450040c40768904442c5580c440326407201d5180321100c41560b03240812a407040045c080800803075000d2103402d40640c46101c0469000505000700301816105910030a031890302070f002c0040b999408003c2da100650705460920703d25052807401810f01201d0794808041351000f02c00c002c82c803076050302d032640a0780c0200020000b503203545188100e01d2052000d403601080101c8019000241b1076442074001c024107103000a80a0703184e50b00e2070054000103031594a0243c0200e07010160120a21520005040803101c40c0d01e0840940f0580c1002e801891019224a00d4080395030340880c000d00454038010350003801048440104000a00201154000c1810542c6030001e525200141d20796545202e5a00400039401c43d0384 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 62111612 1250 62110362 62110369
    0x30b031b120a050106060302040914060a091808030c030f07030b030307141c21181113050702030304120804030206040b07090f0902121b0702060306150d05060a050102030c0309 77
    0x1400380006054410030b034201c0003003402803103a031000c0d00c042d86d005030340c451070700025005581d0190449030036440528180b0440395a01e0380c00e034017100e468135404241c10b10100e225910601d10580050721310070b00001003004002080c1c0080d40b00b03c0702e0317030000c01450b00c40003c1141200d03040d0103025056030041000d0000f141031520000c90070091502285c030310782c40b006858040c0e00c01e0b491194020600c5141d09a060750700c9081e0b414620360b00d0341410020384100c6801900760710500398002d010b0080421120845484804400d2a040e2169006019508020346e00942d00e9100320b0341a03c0f03e000041481746500e05c07980101d030003541c140e4010300311500c603503c4205d200280505a40b00384901b02c68001003408069401d10001e00043c140181c4a4142d0f00841c990040e008040368000700e6078040d01503599103400c0c1511716187e0140c1d1100d44a5907864040b5146c440e00c000140c02d909000f02d15541001d089401aa104001c00d0325418100b035900c0006a0307403030040c80542d100035003060003280600e09 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62112862 1250 62111612 62111629
    0xa08070602092e03110d0e0102040503160302150c0a1119030305040e0112080f0c0c0a080105061516030305040f0204091202240f0a090503040f06030b031b 68
    0x1405604018504481c1d01c0001d5018414641800320000c80040f80c81d0b00e041d800b00c14041c024a00d03040900c13884882d04403001d403a206a03074481c0e0655988498103ca90142503042d1005000041c080710003c40080c1842914807a051000302e226150002150b0700702d000007000d50b03c00c02214002000100c81300c2d0340c1d80b4000c1071a0410241c000da00008591090351008140030007c602907124180d0300c9003410b826210300b0005800054084003070000d007400003682c1904480000c100d007181661152070301221907003004e41d507400c80c6038810004900460001e01c107520490003200d040321141c0d841e000345003c200d000c0c0510b2101004502e20381d040c0c0c0c40440d000f50440c40c1c1c800d202e820035161a450a600260446e505144c0c26100300c400c2c002c2581801d6010801c02c182649804106035810100200d01c00c1c1c040f0b002002071450301b40750004140c1c0a4a66008603000c640e1080941e40c032551111520301c8074448a2262400080c1046181c401034180813500ca24080860201c0e00110841101404a840d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 62114112 1250 62112862 62112877
    0x3080609090c090a0902090603010c0c0807080c0106061d0904230c030105070203040302090903090d03030c0c02120105100b0405030303062206060c0c0e0f07030b0301141e010b03090a08 81
    0x24021071200c2401c0c3e075100c082651240343c9031800001c04400e903005100c20404010002070283c0e140a2640303205c180c01900c98482d50f58411252540d4840301d2800c1050b60040740740340d44c955030030003a010881c1c80d046142c0c0030040d0038001440c02440841c104111804800751806460b0041943c0503840701407011000031360184031401200d1503119a5000f02c0d084403011079409006802c00704040c811854401d02d200d07003200d4000d00a5007090700304030002e030300b1003619035000b014956a00c408400540c040c0c180c031b0306c030175400501030060313943d1079400580030702022603485550000e503d8011507600c1101050b60300740e40e4050011070071641c40d001400900c3d203141802048462a4100c0f0351030385440b9000380406801d42e9901c1c600400300038544100b111585030090b80c0b035070544400300300400c401c0c0b9403035a502c07144501d00071407140e00840c042401060712100c1d90400003000000c120495100d14000500904204c070640c4040e0b81e034007181035082c04203072118242c1b50443c02c0c036000410990350181100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 62115362 1250 62114112 62114131
    0x3020f04081204030605180d0305060f030d112104090e010b090405070503010507050901020a2a060e0a0f0302091311060c011a0103020a091701061502161203080609 72
    0x405468940051a10141070202e000c850b000040520811a03c0d008840e0841400e056240108002540254071401200c40b0300041640e2000086e60f503a40d60b4124129004010f000d44149691807a0014480504420429020f03c9403d900d031091305214080c402038400520b505034105424a0001c0004c2c0a04481e041d401d50348808200e04c0301d50300c0100603401603104000611449140c81c1c01d060030741d840100110705008081c0110611641c01003601c40c40281d201d820791081c00d14031403030241c2c07004000f050080c2c41e40a40c0b03c0800c44035049044110844d00448108514580d80e02019090b0802c034000250000d0001c070104880d14140c84140c4010380c0b0861110300b01c44200c1c0301054050f000005034400780d80d122041d4103200040d000303011040b90340c2841c065241401d05040070b8000303030f51485034020f000c101d84e600000c480c80a501c6280030b80300c2400140040b0082c01c8e0004e41d03c4402031049540d181032a10300140d880041580d0300c01c0b495060f2140244d59440204001c41c002c40203048594 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 62116612 1250 62115362 62115367
    0xa050f090901110c070608090109021c02030a061d0705060306010c080f070519120e09010b0702030c190305070e04030210090201050c0703051608070302030606040b03030c0706090611010b090703020f 87
    0x41e9082e0074007428100c040d80008104840c1b0f8100010241c500151840c000d992501007244007607101d00105814400301da03e504d1141005074800720785002c000e031201500441c030f04018009412900020a101030451200300d5541980350000c00c44284400c0d20343c180892400c841c1c0200091054024200582e038000066041101c25290241007245e01c40200d40802da00000c40c84c1045111f00101c0d07045807142c504005000d400c400402c034a48d42c10300406500b503602040600443d5001c12001c04038100c05400d645500002015030300400d07805010440c1c150003504004518556020340242c80341c3c1c0c16a004100103000090314500805203000b090f410044100503505005008110050041d4800c20080600e818504074940c01032180750440000341d040000c007040580d40c0096481c0d0824000c81303000071070b0f900d03510001f4990302c02da528820440c051200000b40d802d4010f100d142c01c44042380c039103c0da414000c9804601725008500950760105103000811115403080c0e02a100b00581620b1151 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 62117862 1250 62116612 62116631
    0x90a1817040e0f040c03020108060d0206070b04020414041e030507050307150b0f06030105041104051906030f0522020402041a1312050a0f06021b15060a050f090901 72
    0x1540621800209035620000140c1048031081c451001d5a00c1030300c0d000e5660260410b681d889822644611001c2e041040080c0499410380d5050340d29120360f64001c104a5580d005440d007544201c00c122000d0b88924500400794030381694107440030b84078070391018044030501e0019050726003510005505808000c814490100028070400003002c0c642d01803500944604200b03a02903081d20101c070788950103462103075807155040d1103038800d403415224111404107420010801c0011980500d50241d9070040c2501c0d04069210a0b0b4900070041d5110740e0f40500128102d034a140d400d454060742c65a8590704070101010305040c48a419400c40d82c030043c80546400d0b6201165440401c50080003042d0200015894142c0f403500c00c250801400c10100c102e85014080c1c607980d858082da56806080c0401c1070740c0540401c901c1d03504480101018104140c032104140020b142c1e600b4040c09541c481e560090701180840c581101c0306411240000c0c22040342c1703e41201400002800a01810860340d04c920b042d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 62119112 1250 62117862 62117873
    0xf030602070819020303060a1e181b0503040312150605031e0108071e030305030f04080f030a0c030b0d020907140c0105010608091506090402010f020a060c0305090c04020405090a18 79
    0xb250f0035005900546d10b0341001010041d09210075072101c0c0c02c200c0108840190030040d481c25200b114581e01600b0141d80000281307401a0110240d03112294503804003c4852982040c055401180240d940035801440c441c2c0031402c8505890b0b03503103000d00182ca420442c42d44180700540d4007554000c5862a00070000c3c40d501e02480003070700a00c0b17260300a803006110110000491a040c01c0703400b0403d41605165880142240c072010300000c055915190004052000403030440701030704500b01c03013241d507131409440b003000420366408504002800e2000b021b286103007001d1041c44042d0010000803064840160513182c040440d020b05070f180005101c407041e441c20a1041074020550303511001524680b02a0190400c00c48105081c4503030f588205010180d100e2483d5241d00c981d0a003494240c25820b520282d10b40b0440301d40c0103103100d042c1901d100803154035801c268000c900031011284425040c600f000309034043c078000c96800082c3d4030002004103402d0b4000340c0d081210340e00e14001d180026203e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 62120362 1250 62119112 62119147
    0x20a14031014071b020609010309050f060a0204090605030f0c06090d050316020316123905010207060c0b040f1407090507020c0f1c140307030e190f0306020708 70
    0x1001e1070140c0c50b10800640f80c0d000006040380c0c03050301040313203e1180d80340c0c0082c41e680507204540c2d0405a5419036902040800c0150a103903001035022a402450140d0808002c0d40c442d014041c1041d007040781c00501030a002840600080c1d2980c080c1101106035028440c0c0d82e0440c20515600c00201c1203950301180042c03004003180290150b20780c40d083c41a00605141440e00c500756010010480003c01901e0761440c50100b5090f80480d480d004040d1066001c010700482c448150a01205005030711004030120071a5821207000ba02610382c0c40b56100016603404441050142c0851251000180091680480c40b04001d210744000703d00c030300600c0c030703414036003909a00524a130950f42c00c203100300c55404100c56425280300300c403641030740c01002c1d0209900100c1420074003045400601c0600410225000010041c40b8103c00c0705d80720322060a00520303c03041101c106000345044106e003a60841e20f5500c51094551a08542c030701207265540d00d0001798003021058890303c00c1800306400c54001b41d401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 62121612 1250 62120362 62120381
    0xf07030c020c100e041107150f0b09090f06070201050903040608060301060801020408060f06040c0c0807020f041506120203010609061107050406030c050f0306040213022203050601170604020a140310 87
    0x1036500580c1031351000d200442e8807081654104000501c444000204c5814021301700c00001030740030601d000500385c081e01034030a4000741c95000420f1030410941d200f0002c1d0000252031904110760440c6c5400b40c00364221441605d0700c4007203400070002800701c14007900403540c004001400005019a03606200d41c22600260003084141c0c000c8400c1c484c40c01c410140c0039402003030880e010007550f005400301074946c24040c82c0c002c100040c0442c4210966030350a04043c07420902074000c2c014901d10780148034400710a4012800882e0404055a02968040c4240c80c165004c0d070300c517410400d00703203502034410fa51a00440d000038880d407030000c5401d0311a0b000f0304009510400008401d02d003400d042000b01150401c0b1280070707510401c20000540e44884001074250030161005a45062017100c01d07250010f42c00c1c5032100c0000c242800800c0013000640c0341d040b24840c1c030310058401403030204252115007c1e03601a500100030501403003031a06100510390101402000c41e02c80807010b07410182910300410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 62122862 1250 62121612 62121617
    0xe0708030c01020a272106050108010e16140105030408041703041a0a02060703021303020307180b010207060801090218040c110c010e0612100e09010603050c090f07030c020c10 77
    0x74100c507000360003030003001e03118519990221400c00100d0281e0715010300340c454845640381c6d01c20094035031409117030384001c0aa007080050000f981c45102c03080c0604028200c01c9151300c41c40c40200c5140454891080c1076800c00c18554140300c0541c0c004407603a800c0580203440301501000700044160047d0030a81b000c50b0540c0c055500d0302d2402d1a440c005642e0601d855503460710801200024540c041240741d4081b85a08005843d85070540745500034414a40009401d80b050a40c040b130700100761624100860401d410a01c86c0c4c10000c001281c55903414810040460140f10061000c420310360082c0503446401d420075016a10104001400c0d0340c000f540b00004105600103003c0c007500c0038402448181000c1c00c224110121344000704415110740441c031604100307800d010075080104100d86034010007004880c45601e05114512900800c158403003160715210b4203500c02020309081603038910480601030146e94580e074020f41540034000d02100c1d0800c40c040c6400400f082d40c0da140795022200c28a6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 62124112 1250 62122862 62122867
    0x160302030c07080d1206080d0c05010e030d0207060f02040605030103110616030c050708030309031608040812040e090601061205070207180606020606031204060c031404090e010506040507050d0e0708030c0102 91
    0x108005c0c1c05004203e2048403d541030070414040c140300011a00c1040140b840c02c10070401f91810801d00510500042c110b0a0000003913034650701360a50044c25110b40200400c01c5a440d00705815401c03031086100300f002050051004001080d9921501c4400a0003c2e02452510708500d00c2e0704984c0106400403404508840c0394a018030070100400006800c85100662560030400e1886a603805002035089102000305818810055030b0400d68008107021400c40d00700d500135400c80c2486c0d410501503031500c00b0906000420762140003419034102c0d1010707102c6035021280c1c0d000c6100540001010300c0198418202d0010713155040810800b0000342004c0c0008100e41040740c000d0a01c2000342c0020300c81d501481d0540b08804001003103600701c0d20785041c080740351115480c1c181c4803034120203071100036060003040c001503085882d00480c01030040000200000c0e5a21420081141c00580d8004c000a07010702c0309008022040c1e1100090400010403603034110398078691145164001d00050b1440c0c0d401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 62125362 1250 62124112 62124133
    0x80118061e061724010201061a091305070507060506042a0f020a0b06061c0c02011d0109030e090c04120c170303010b0a1209050319080105010c020303160302030c0708 73
    0x14214803a52083e00407941c550500484400d24100099210440da440c28040590281c1c001d41c0202c00403d03400701510b400d005910a4008550811501e07140030b108801071050f03d07c0518400c00b84502026180c0600300441d03610f814005200c01404281c02c582d4540ca0100b503603403505001018441e00b00b807603e51071448908002c003020030740141d030001d550050040b0303400a10184289584030800303a810b607845814035601d5840c003000c90301400d08414505141c500b1030302d40c1900501510314820010003811214020719030300301d40f00181d01400282110314070003110710b0103880382a000581c65991f207013050745400d041d0145103840b240c22900b01848080400030b10402c44101860f00b1448009903003198034004401121303204103043d130380401c1107481240341c071010075a010240454001003103a032568100d0f000e03829000c600b9145070010603019000085d1541c41582c1e80b502c800d034040d02840c144448201040040c011445044041d800705000382d2034042d500300300f1040181072203001850580d86 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 62126612 1250 62125362 62125367
    0x111b040603020301020d0519110714070f0b040609140906010e1306060302070209090d05030c03040302070f09090b01050402040f050d08071b0e06040506063709060801080d080118061e06 81
    0x760800715403d011b090a14545204270080152107001d45c001540804000003282a00d0800109400110749155130b41030114881c41e40401901c01e076142500d0b0071059545520140801c0c8860154065104181c0030000c0d000c1d502ca041302c2070700100041c0c000e180860600c03c402e42610f0003900003100007031340414000e040d03241c400780d203640120340000500000143d40d10010a40c5c40b004210740c00080c0000086800c261082160600615010075409845a2103102c000054903580405460019100001003003c1c0f400e80b0854007140c1b035603e81c0140b40d918041c01c1c010a5482240c042d11004030a10040c1d0203d00d08000c00c0000642d1070000010741810042204107201d006044280a80d16200412142e0f4031400c04032070130184210f0500c003503d4140c1e032001d07420346a500c0741e641030014085050a2803030303003121010080d02d0941d110850310b6a204d00f4803590b5052a000d0040015408500400c0082492106500c0360508001c1c04102503440304803000350b0f400b10b000c0034018032481c10f808209099 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 62127862 1250 62126612 62126641
    0x702100605040e03070b0c0f120601030f0b010e12030c0d090f0f180b060706090605150f1008060105070f08070204050a0b0a060e0f0a080a050d111b040603020301020d05 74
    0x100c01c0324200002c4100b050700513500e00421000070b0450b01103c010034083c6d04000c0c15100b08115528056545d105050b108000c0080f0a8400502090a00340e81c00c40445090287c20949541a9501d424010071041008440200040c0c0700540740130411510000700710038045e0400e504510b889401080e894050194541410b0342c3c0004980401200300b8406924042c98010400341040800720700010b121000070700750b01c41c000e0700800042c81c112840041005542000d8443c912219035048600012130500c00c82e440240f018950002c011104600d04500a2103000d40040040c5001820031950303540ba0105010124010341e0840c0c0041f40f840308502c3d0500489502c2049003c00340401014000030070401e02c0c50340520014002c5144001d452526505084401c080d0011304189071180d95604164403180144002e40d2940101c45000f40e43c14003843c116058081d822008002c440741b140515842407003103621245d0b10688984001015076424000380c544052180c0d800169401e1582a024004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 62129112 1250 62127862 62127869
    0x30708070608150103060b070b04020901050109080606090a11030106050309010605010e030c011101150f051002030702060a0e03150a05072a0609020604090c090602121801110a050607021006 83
    0x3603004400a000003940081aa82c000740034142d814151542078005030041c00003500075000c5040c0200700c1d0f809002c070780b45003580964001c0d1590451642c0f60401140d4024060044c920940d004002084403418041900c4e64401c07002c880c001000c11040490f528183d1080e4040301c002a00413041c041003a4080c0b18080040400f400d04d41d48107071448000c01c0d2542c040846150601107a41c0c51030400f841c080d0001c41c050303182642c080003101d48881040d618010f40f40240d900810a9140500825000204440549030001d00351410204186000c480d00700e4030100180e09070151208484c0180d505034041402202905000304a40ca40300710001d008500301c2c41405c54106005c4a6880740e8080740d5600250250084408210300c1543d00200d8030511895105c0040d5038600380d8401c0c8403540c809444402d4460680c00d54003610580c040c081e0117030146040c81c04002030082240803007507004025201c0084044015a0706032481d5460b200e040140896003980541c004182100b802e504503c9240d019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 62130362 1250 62129112 62129129
    0x30b190b010e010815151b030702010c080705010608030304120f020a03140c03070c15090f0b0301050405130c06021e01050108070b030709080a0503040501110c0d03120f05090a020307 80
    0x4008003000000c000c10a82041d40f414031020f1408103103030301445280361204400c05000b000c44038002c01a840704a501400c80000202c00c0f40303480c1069070902004881c10b0a405969448025032540c444a180b64084c1501f110690360310200061750b2030080c0055407007a40541403207140081640c03000b0700100c600066940c00c54008081260010b85c104c401252164142c070100c54030b55014040d101d00e544105180540010207100d00010f05454484130345d400e41046594001c0003542d10690001e03028002d0040043c525414001803200d0300f4580d000756400347c07401e88110030b11141d0791294500181c0c3c40c3c07c00f40c01a0014110200d031242d000c85841031a007001e4008115562421154544501160041962112000000c110300a10481d50070002d000e028040d60f051030800c0c07600a5490340a4403c0602040041c103c0f410001d1020800381c99203840a40001c00d401e00f55075088801008051808582503a142145003c0f400d4901c6054410424030000380b04020305801014070300040f66114410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 62131612 1250 62130362 62130371
    0xc060507031202031503070305030a02011404030c1104110316030b0102030a0801091104081e070b09010813030504080307050601090e010b0a12030c081602010f0219080706020c07030b19 81
    0x2e03400b4611000441e91280300585a480b05095250808101c08020394540705855012090050100080c8076031211a0000c018a0700c8848184003407403800c40300500421100000c150114a02114a0300c154500400c00164450048c40b0544550001c0c2d484c0c050400e440e0241082468240c490005004004d000940c148450320000600c400c9050149908070ba0b250050381e0500c44000c1d00340c2d0098040c11301940e140c079400c040c1407011441030341e010003c0c0d40701e400070004058419404407030340340d8410b035102d0750140d035074104011410030310f024100c08103d41008000390701e031018000303031850358810350140406501d0704840707000b600d0504032016480d9151144400040d42e40060f40070484d12000b44a112031192402d0603103441c2096200a481c4810000307415409000d8180f5198849100341c807540f080e0072100600703d07030b1080418103076010485640e44600200f4a160050502070748209400752604c440c1090300307400c100113a03004403154681c01c3c0c24021010f0003c0c50501008010a00410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 62132862 1250 62131612 62131627
    0xf08060411040302150f0a02030c0c010903020a06030203060a09020c01062904150e06070605010806070c03020706110c040204090507110303090a030c051c020f0114090c10050d06120c0605 82
    0x34401e00c2540f20091003102c5444200f03d01d0070040090300c00c00c6407540c50458a030300c101c480183d2264070101c0c0400640c0680002c0902c00c1d03018060840030303290050110010a0306004080d8029070000e0100c0740d005201c0c0400146d032042e14001070005490a6001140203072a1195525070101c8140a0304c00401c030700c9d11001c00300d00486040d101202d100040644010442c540f050b40d041d0404014190805000580c40c0240f0090f5001701d8108e8141000b1103401d56104001200c0d10f52072814010f0041e005014100700440c4500c201c00030000c0c4001c15240c108100340001401c0342d104d94051347d50262a5000c2200c9070750000b004480a0f44404069883c5142c0302e0341c1182c449944000003004d001e103c2042006101080064200b207100a4016054012202d0340103944c8043d00c034001603a035800e100c02064404440b40c8098080c00e1200e0040004171808070030082c40e04040383c000030801a0520400b001b502c094001d1074000c0001c0244001c8115040c10109046102d0350800d80900c68100101d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 62134112 1250 62132862 62132891
    0x312191407081e22050d020307030b0c0906030a060503010b0604030f0308040311010507020c0f01020f1504050f10050118060b0a08040203030d06181508060703020a170103030f080604 80
    0x712041607104010070b540300141c41d00e500c103881c11041d038040d00680200710500e601e852400b8506840c501c4c000b1010320165030380304103c201800c0401c001e40580083c0740400c001030107442c40c41d40003200c0b041c0e440c0c10b10390300a0200c0c100d600304a4860301400d8588004001d0b904080c401d0610b44a030903590503141070b065840322200200125002000c00000a0009041c184944841e00600c02020b00a0246040080c0c00035518040001007900c00c3c1030300801d20b0031660000078cc51122070703100b00240181c2c10031084270315488000240b05903158081c00e01050005101408007001003d14100c0000d520f5040c40c88207004902c0d030710101c180c0e2515158040c001c0c030440030140d400e4030300ca51030b07d001c8030b030303070750300c00b181c00c50007258400c00020b400c144000c240c120854010f010f109039480c03010004440344040c1c61403880c1085c8116400c3c0c2e0441c0e00840c2b08035102e50010802c10005060020700cae05003e101070b02c4090400d034011350001e2544d2040b00303d45030703000c690300d500074108132001d00101c240d4a584 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 62135362 1250 62134112 62134117
    0x1503061e031209010c06020403030c060b012f030702060a0206040c08070311040e010e070902040306050a02070206040b070303090c0605040e0f0906160c1a01030212010212060d02030c03121914 84
    0x1210b40081000c183d2000c5a8420b0f0820010294800303025510f0350f83d249000740c00110014001c0f01c0c0e590a02c5101d01403544180780d40d07030a0014100c1c2d000300780c0b01d10103410060454a00f0804456020030070100b009030b1071301d01c0100783c0d40c3c032a0b90080c80246400e04114000c0e94040d00002d10540043c50200040307900e0b61b20707822918608450006000100404050041118030b0040c035803402115400141c035001070b4090812280540c10031302c0240e590508003801c03480340180013580208140414801ba100700781c0074100f80c0c0d100b03040009544c62941c5589032202c01d1588a40c1c0080c1000030140303c0a4805012680c010301d95401503161070800144041c0c41d18002021807110032030b094042c1034803d2103030403000200d9800c000c141b080c404a000344d992441d9401d01050380118a5441c044410725070501c215203206051040005d4103844d10f1041015400c0714007420f9a140c805c1b41c482c924290703001d106403040d010380c124555a5400f910304490004001e07012520040c0a40c0c0d1003c000e051004604 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 62136612 1250 62135362 62135383
    0x120f040302040c0c020d0302011a0103020903060f04020607080313030e01020c01080c090a03080c0307050f0f0304030b1803031e070c0305070f140601080c01022a100e1503061e03 78
    0x307002c01c00f44030416040319a545264406944004400aa8000d250b01984403c40380441080d654030b00c422014019000e030f00c0344401040e00360340510b00160300c201012120a4009100906052401031180c49034a565081611420f017250002d400c0d1004140d0003030b5000307c00550078000b0b011044031030350028107120360081c142c041480d80000d01da0850381e9015000030165902c0141c1c9602c1c0c4940c000760940e20380042004036140d208100c96802d03800000070700c2440c0524040002d602e0300e0f05603600d041703407203001030f244900a60004040009104003440650320480120322032044071507102c09000e4006070050240303401e0107024401400482d41c40000c0340e031100d810a282d00c142100b11325001c000c5e000c07400c0c2051403900a1900101c0c03117040c04504401b040c41e0980c00c88840d904064200c42c02081c0c03480800900360241f0f9160041c6c0d003003026503034102e005107045c541900b00c00d0310040f503981e400e284072014014400200704a40d40c50110010444440544840003000d403281c40440e03690081c454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 62137862 1250 62136612 62136619
    0x90405030304020d1407061707021507030b040207080c0a1104050c070b040c0f030305041802040b04090f060503030d0b0307080601050d0807050a08040905041103120a141303050c03120f040302 84
    0x44da19401e01007409520600d00b00400111b1b44926070b03984c0010213580301100d4512038501d446011604e410304c009451600440f04508103482926850300c1503009000f8220360740c1e003142d028030035840401c4e811409442c1c0401c0443c0038104803041c80c500f045849980411040c840c0e46003000b44404031114506803640d1981c40076020f9415100d5003000440e00095600100c0c103543c11820110070907920802500482e007040500d14044a01c900000c0b05074042c5020780b04400c40c080c0010000301c040f0303070000701101e1005213000448039110400710f415680700c01500303d0002d440f51240e40e07881c20100440c0008100010240c451342d4180800076018140302c0d500074100c600041400c0c018800140092400c441d800303400980d8030703580c50358840e010f0301c0111001d42c0c125070805070304030180c00c010500170303485040384415600d407a07240c48080e982d592004880f03a81c095028054007016040f0a00d20002650040c8002c7c6240c1d00034208151500300030741c2009010340000d0103045000300001066805495046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 62139112 1250 62137862 62137879
    0x60a0e0d05070c0509011403060901092001031d16060305060a0902130e01031118150103020f09060711040605010903242309071203090312030b060a0905090609040503030402 76
    0x781003c1c03000520703a400a035407103000031000017860500c07030040001040058043d030303400387d581f1681e01d4200c0d43c007000040d10328140703905070084c580300404800a281805040c0011034803400c51102c4901000119011840e50000000c045000d000c0d101000003400c0c28501808070380b81c5a0041000c00c0310790b01c035000303060750081004400d150043d58084060110015200d40c1c81da03581c1088c400d04500303210590301a100c0000300902c4000910041e501c64110241c08040001d00d05004500030340c000a40394055030b02c140021121030303a51100400b5140e0040c02213803441280c40c820441254416031060381441035009041000400c500d003d10303810b0380c20703030700c8101d00c180460258030160100a0391003200c5030319028840c402440b4001c90900a0004000b1200da0746d40303801c005802c0b51043c3e480074011601512040000940103452062490014a400301700e82915002040803600300f00e60700804509030500c1400141005201d40d030f481401120019400c2c00c150300d40684911000d00007a008403030b01c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 62140362 1250 62139112 62139127
    0x1f050901060302030d0c0308010e010308030708060a090905060115020d0801180f1409010b060c0312130c0303050406020d0306050a090b030106170c0306161b1e0602030108060a0e0d05 80
    0x81d4088802103802405031400319810040050290112540860100341c02c0c10000c80c035403103150f004606032503100b904c0c0c502e1a12400010b842484004000039407106c40442c011400000743d024038100507100700002c003003e504080d43c6680312162030030f0350400c44d84648030382c1c000c0c65840b074101750440b140c41e580030150b0f026100f04040949050314000d0300b2785080200320965241d12850311481400c2c90f9000b080b4448203501001881e1003200c20300750f040e038401d011180c0d0105007805810b411010050b1824082d038015a500442012203500507408640007003401c000040d010300a031115400301c0d1804000243c102000a01001e08600801c00015075403201c500075501c2c25400708000e40300f05200f82d482c04c0d40c4104543d50310040d1441e014000c0c01698045000400d06041c20400c0340c60644802d03892810044814080302d00300340f400e440c400c4650056480035002103658850880c001d035400b40e56581031030540d9143c180040c0c07499419601d070050045c440c00f80801c0c059000c010601e05195113158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 62141612 1250 62140362 62140381
    0x6070c030302070501110414030111040603021605070603140114060304060e030903100b04061a030c0c1005040303020703030c0206042102012304020307060516111318020306091f05 79
    0x20f200c0000d00a6181050400749041340e00007510403103610b044040f40000020341894280e4140020300041c0d200203220501c00306000e0b0b006071003000c2d030540c0e07401d6140c0f41580f82c5c1490302007140e01580110740e4903200044070f84044c0b41c0e9075015010b10b2407100311110005011840300d20000707001420440d5a0401c11100c820140101e4158007001022240c504540550590082c02c0d0490524403075803401800182180e04000d4403c010300f110255141103039170382407012070b6903400724190b22154054200080e000000510403540980c0c002d640058070f96045180c0603003200d03044e07464442554414000c120024140c20501400740c0400d03890100c82500720b020503400b4080715041c078000343c0040d10b0800c2062003210f160500c40d42c001c8040ba51180d036681016076162044680d9074043c0350315a5542408581541400c107841100641034030512214880b03a001201c00102641c1e0740c403444022464250b04e420032215801600f120054003860f144910002d811040781c00b400d00013244c030748002600405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 62142862 1250 62141612 62141617
    0xb03070509060904050403020706020105010602010e030910030902030a030e030105070309020d12090f09020309072414090405161d0f240301030b1009063005030a0f020105090f06070c030302 83
    0x10f0054024080b0341070918010351a50028005c03440198030385030001034028814041d441e020f4915402035440c01d050241801180c101d220300b4402415181e0329590f0040c0c40800c00031800f980280d48500b1941140401c042c25508050003200402d41000c2c0e1920242c2d5030b080b0000302003a0300c4001c60703120152984c07017a075070051140e020b50358401c90454009104161034000750721800c0f0741d00c00c0d44c504a8807805c50b02089007480c0c54401400d4040502030b8132139809451901502d143c03001c01c2d141408101000102607a000300da01c00300c03001c01540d140c03130400d0700700d130035500740c03502d60714014000c0d10075000440d50900e00480c1c150300c0b850390030070340d603d12007105100206524900b004050347ca40e1642085640d081090350f8042c902c1c00381e01350000d41d6020343e110300d8055880e041c14001d82844c10081701448008000c40d0741c1c1e41c540130026070800090080000b0680343c049512000100c81c0b80001c042c0c21900300a0030a020764021b0405846a040d0105200b0b6210710325051080881c03009040440090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 62144112 1250 62142862 62142877
    0xe06040902120d0203092b020d030e031207060b0d030e04110c060705030708092a1c0c06030b04060503060105060a0203071a01050a0909051203060d0602040e010905060603010b0307050906 82
    0x74000c0c8501083e4155001c001400c0c4481c0030f9401d120981c9207181c030780d02c1c1815400043c5201a0b12805910014a444018208001c5c00703031400c8c1000007624000a0b00703001050341143d80792200040e40d0343c01c100940c0180481c200085400700e43d07045881c0c60252000d00f004d8100e6200e00d80d14002d10f038240e502c01058401a0f0600c04c00c564461404003c040c050364415104500071400304c900190302000000f4941d010111050210420021081e051280b15a0304001d6981e100a9900000d0072142802c1c2c003501e560b5001d49152030782185800e101908482806800394041e60074600c0c1404282c0300000d0351411120140c92645c0d4900314050700300e00710b01811400038018489140054085008161110305940c001c85000741d900d80d46403070540c00c803004d40700300800b141c000c403000e0b030028003a40700a190321030005001c00c01030b6441c82d034030407003203900c503402079800c60071000700501c0181e000c0d1007680d41c0420150740b0240b455041c40401011070000414400422500048250494840f081940d621 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 62145362 1250 62144112 62144149
    0x111070e10030b0907083c01051501030e0a110a0314010b010806040c020a0b07020c0a0303021b030a02010203070809060405040603200105160803371103010e06040902 73
    0x22400c00c45641c1614041d0361100f9282d4404040104000c0000460f040d000c84610304002d0010010079400c0b181344401c0811410156141d0307100032501201c0094056000b1440702000280c9490070740325443c80442c03003c084038105032a14007041008080003030328110543d00300348085000c100e05400140e10040170b8200800103e50b2850b404500e110540100300d8945003601c404040d5a580d03020301c421500319424003c01070b4004501d0740045110501c02640281030703403041e628854070010200311170b008180d100310010780c01034803080e942d00030308041040d0101301280030301080390715500002d42e42e008506001d090a00001010000b69072039a04840c01040083c00501020340e0701d04140f40c035508141c1695075240c842c11f1068030150301c554201c0b0841c642c400300600c1c541e10191101402500010032080c0c940410014143c80e0029020708444840f5501940c0700e425140b0314070380c8060381c02c1ca440f80c40111a0500c010700c040c6119013521350340180c05440c006190350842c00042c5101c0c2001100314003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 62146612 1250 62145362 62145389
    0xc080d020408030403050d0c0b0c0a03061a0406140c1c1e050316030623210c1201050403020c0402031f030c06090e04080a11150f010f0905060906011107 67
    0x1841d90b4040041c0c07086070300a905503410065501020b94008654500c000c2000c0c0301c140021741014101405071007900407500d000100203464018000d1a090048040031111134082010004135030710417034a05940d145010028180721410300240c3d41d40c204e100742e0a1600d520400030890041c42445072000c40300c8080342c0741c4160301e159032010701a5481074401240d43d040d882c40c00700419001c0c2c064071045440d2800072113907014019020480c610030700003090703900c1320210785241c80d8001180c07a1841641c10072005010010070140811101001c101000c03010741c0d0600080201013030700801c2120f101401540c000d03940c1d0741e40710749107260a0314040605080c9660140c010007440552441402551001c0e140c211310306440719560203c001d000c03280100804001c0050b5007005101e03106440e410407251080f03030340100040c601010701c010111490380305d208818004120802a00c01814000d000d08103081000b8104040070809440000b0103090502c88010f603003030490740080040700e0090040901400307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 62147862 1250 62146612 62146619
    0x20408030d05061f0c0c0b0c15070302070605041104293d0f09030f0f0201110a1110030902010206070c080f12040c090c0503070311040b0705010b010801080105070c030c080d0204 78
    0x2084054040320031b80744203101000210766140c8440460720180502d00c020000032001f90705521130f926000345a01e081580a00010000030401d004450041e841102d1400f203414084003440200d45038103190ba10b056500801700d02c1e1480007079184041840e416a0a4048155115075000d400f5014121303a07d100680041c1c280c83c101036402c1881000c082d20f640301c130807560045c1001c135915503042c0400b03040314210b81c22041c0080c03030a07240300c605588103041c501202c0c18140c0815007440c070a42825111030b682e000000e480c034070340186403420049540c10200a083c602d41c000139a03030a0001c0144092148503140361041c400344a040d11200d241c0900c10310780d1205040c0e02c41062001c295000c481c46900c1240c042088113250213813404040e129660381e070940c0d507004411002380403002d005501c400001c01002c40c481c501387d401044034038041e0001144011081d4001012032005034460909649403000f8096400e03445a82d41840c80e8041c601480001c88500304007109102d01003c0400c407510019000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 62149112 1250 62147862 62147867
    0x2010c14010903083d0f0e1009050f07120b0306100503070f30080711010e0f01021e0c09090d020706140706020703020a020a030804080c04020408030d05061f 69
    0x200c000b84607907101c0402e911490004d264401c0b5001c00510014001c00000b0502810b0400101a840a0a045171020750f42c45c0c40580c0c0741c511b141c21115944c1c15403400c001041042032104002483c407010b04001914250f1340100030b180015102e403041120080000c3c0d00e14a4641045514500013400c2d42d640f801c1c01c1e500100782c60b5044c4034032406805050b10000d02201c000301d822003106c00c107040403c0d000401c1c41044519030440ba0110705c91200d17030303c814004074910501500c0118071070b02180e000d0201450014001081c1a0300e4076100701d0300c2c00c00302200c03641e000c5803c3e074407078407821401404c1d800800003543c1441c0202d00d0041c2c0011250b42085007a8038000781c8051044c64540a403400c440e02c5403c00c50305a0801580298401e204000801c0052000e80c0202a811b0003441279074200c000590001e0b10300714040e0b2094074000408070381488601400c0c0204540d4040031201180f401d4600070b07215490303001c0d0302100002c01c2d175a5400500191101c1e542c0c11400034945019400000984002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 62150362 1250 62149112 62149121
    0x200406020c12070e07020f0604060218040c0e090a020702030105090721110918030c0a0c080109240e030307020d0e0909030d05070318050f0c040501030206120402010c1401 75
    0x1110018440c604500d1850304045a03401d2080042e0301c0034101240c00d1541c030301c22628014000d43d04510401c3c1c0030307900108061003580d010340c0c8198000741e40d888210509880c84400400d541e44580d203443c591706056a000200d903030403a0801e44041c0825aa101000b40003400350758800303900355081100700540c1103c0400d04e8400d40306090503000d1203501c0d80d0003004134103d0565006040d80d0352aa11401c980c82e00502503030b840b0300341c500c904015441d0781d030300981190405240c890250b400134030340004111601030a43c02070580701000300002c00303032512800340e1301580c6103240c0c000401140b03420319403085940092001e240500202c076500c1c20040d200a40e1240b0700d00da8040041d0800402040341d1500d01046401125094021420b000030b0b400c1140040c54041c001e403041c5a56940170401c050407861036030600741c0c0180042c200312840180d0310360410112100711840f60b0310f030100600c01692135100351030210020f545190f0041e80e4610058400d1500c10714050706406426105040320f0005400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 62151612 1250 62150362 62150369
    0x10204060c15060b070b040618060b010f0f0905010c1a010b0a0305010503010501060c0803070c02030111070302070b03130318051903060b03150a021614030712021c050d2004 76
    0x2140040c040100b50304122440750141460f40c0800b0071521001c01c9060317150b150084c1c001d07003000640c2460700c1450307100c28180c08402c41e406520b41c4442440d943e0010441c4074030740031504100c808580c002000400e01c0609000c1e1605106140a00e04107000c0e221040500c0c14069510740c03205561141080545034100102d0100009c2c00c00001080c0ca040c107000f070318102e821544620000042940d55a21550002042241040a844510703005030740c090264606020605401071350310315490400a00300a207a41066104400c1041445500002072030300c1106c46401d86864160800e58180e4041c00c2c2c10160320203a881281e5544081d15009000c401c41c0480b80300720010003000182d0000d140d121241000880b50031190311000813140c1038103030000c2a00894030340707291030f08218075a181803008031240c840741d946a2001c0386072010800c80b003809940840d024001803c04014180c1c1004a41d04a03101141c00c0010118004040d180903800c5a90b846045501219403101d03c10903800c00e68100d0321 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 62152862 1250 62151612 62151623
    0x901030809031002070b06060a0c06090605060f030303090a110604030516260d0e03030d02031608061905041a0607150c05040b0f0a1e0201050402040b0609030a12030e010204060c 78
    0x940b81c900350106131080719042e5502000042503540c40004018881d00030703040c0c80d824040c41c500144002041c9104820340b043c8580000202d40c20400e0a00030b022204400440c000e6004000307100941800003038440ca150b0340240466080c460b40800720350340d40196071005007644030303040d0540e250070702e80c0c0141c0c1c007520200980041d064420023429a00101c401d00180e9640c0c20242c0c400260710710800c10040408409000c892034502201441d0080f64003c6035085c50000c039048212000759800b1040350f4000380c0440d032085c02d0b205000f020415100042c41850310440e6a41c03803056148004540c1a503111a00a01e001d45a00d268207145111280e2010780a03840340c42c0c0100140020302420542e0305907a4408407060508044820300401d03030b4072910f030720010f1000d685811a0040c51506c8079078900c01560703002290f01e00f014414032040e144d4a03103056104100c00e2021591a07200002d0a140303a42d01f19403100c210622101098006000805030780100354000a008181160050354101030a403040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 62154112 1250 62152862 62152873
    0x1f0905040f15050601140a0522080f03030402090618010909061404050c030d030203070e0111010f0203010f1d0c03040b10050306090d110601030c05190e0a06060e010c02091b09090103080903 83
    0x41b003a2a16100d00f110120100740288030805101c1008c41c042203e030f0400e207112881e4070b5140c405080c40c1c0f0442c441c6803040c907803000040008504105240c03e4000406030b441080e410040d10503c40c01e00814040c1c9184199030b51005010b01003e0b41200ca10f500400410050034285420a161a66100f1004a01074032500f08060b948074840d200722881040c10f50741d07130110011032000442d5000d004500b204595900d0f000d03556000b0301e407840114001c04007440e041a80c1490136018802c600e5000c3d29a0800c59242c80400c0349002d550300031640c0c09940300010117520303910420074100c007442503008a900740c030903d001c1240d014000070704141d0941942c1c48084c40d070b1001d055410303aa19000d000c01070001c0f01c0c031f640c100168200750845445240d240304170803440340c1d01c40030802c04e0008210785101080d6255141045803940026a082c0440c1d401c0c0b800817a0300342680c02149040c1c0303002d8400301d1040d580c0c0c0f0b811746070b0703404400c19035030310300341c002c0655175956507a050109442d0460416203200f4080d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 62155362 1250 62154112 62154137
    0x4270c08040c0510090801050a0b0109120201050f0921010507180521120c0a030e031504110f120c01030516120c0504170604030201051f0905040f15050601 68
    0x1a035119110315405200c81000a0034581804040f220000650342449030001c00814043c00a02480f0721804040d00c0003e5440c07158000100f0051b5258001e03202c8803580d41010001d0703688035040311b021100ca08801565180740d400401c164110200c0c90894424660304401804641900090700a0f1800e07a5811402c401e40911054049014811240c1c081e003071030058015815110415400803031400c0c01c0d079100031031080700c440381c81d488820710900e2900716074801e40401d0341010030011b030908150001c0806003400c5002d940c1c001800303840503004005c00c10740c0b09440e41e20812509210207000d001d1a5000607101c022540e100c16017450b15011a0030540062068005004000381080030b0350740d61494400c2d80030306a4010f2121034099002c0140412020a40080500414280008010040616140c0343c2802030840f0300290000c01805003100a44103142c420303200b040140c403000c000c0010305440b60700c1c0c0403a13003031b0300d004006049201441011810900d20741c4058802c810a0301c03110000b030013 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 62156612 1250 62155362 62155367
    0xa020a15050405040c05211e0601020c0f06160c031a06010503041101031d0a0c05010201020f1c0b04050f070324090509070305010e0304081c02060112060204270c 71
    0x814801103030020301c060004205500e4035401000b145082030030701c145070066440d00c5407000410000c1c071807909124541400705032880d01c00c0c40d804250030321401c0719a5040c0380303000075210080c20213075500c03503189501d1403e0155514400c613080101c440c5c0e4100d140104519104420110b03522080c2c54000c494141c0203a015903103490ba41c880c181c140c0d02e80d4516540c650b0340f80304d003107040010241016a40c00040900f154136261110141d5081401842c0d05440d514203c2c840e0031498002e41c1c11640103001140c443c0211000340c4d820342c20302100d00040c40048400882c020410b101c4103640c05800d000c2803000c81882c2c0d0000074060a110f80d400d000440501900704541c8141420781070311013603601741c10803803110960701554101c0084819280301565980712503080d21081c220006054000207000c000a010800c101e05952007003e10b0b440c0d45816400010751035440500c01e13084040c0304840310404016540c2d048401802100c5005400a0741595142014810390400c40d8009440d151008500c80d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 62157862 1250 62156612 62156639
    0x240405030a08040c0902040b18030106030309091e0504210201090209010302060a03141801060f0b04031113020c03091318150908070f0308060603010303090e040c05120a020a 76
    0x150040000d501d0404a00401c40e100d61008105540d81401034502140404450000380003c169162400c0e40303922202c0c01d410f4000c2c01902c0e403a8840d81c0741010800c002600068210b04441641000060403600c903048282c41d04589261200c0d000d00e000f00300020040e50041d800f420600c4046411040d0500c000181d080366140040a54401c1e10390004000621b402d030002c144110f078a05e0042511000c44402140300003050b10f020003003c080300e003030702000c0300240300d408000c03c80c6000a240311440e090f140c041c50700c5503020103401a907244a01010315141e6101403010390740300000c115503030417030702e800727240c0b00e41100303805610580c07c840f01901d2450644c0540494402c02c1652010f11078641d5403068603440100c21110151903c80c0340110116000d24050300303c40b80540440b40245465240007483c4100042031203100f21000e00052011990180c1c1c44d03000d454581c690202d41d5100d6007440440a402a8072055200c01940c3d04100400408244404918400d1700d00205403030f190640011f180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 62159112 1250 62157862 62157871
    0xc0a0306270903050c37080304060c03110403030c1707110405040c09060e040606060512010311010e04020c100605030102043c0305061608010608070818010e24 70
    0xc2091091581d0804240c0c403880c0e09a2180c24800e25020511155a003480301032200a09500c2440d910a001e818685910a0100818900311016811a40e603840c000e408081c0000d044a80d94403006080ba5012360700400c0c0507440180f91769102c07a81d034517000340750480450003110500f0000c2c91740d1060080c1754050310238095201c2d00303242c0c40340031400901c13000b800b0040060b03a641c01b071070800090b07008052241710702a00c0c2050003050245080e050142c01e0326165440352080003401c00a42001803c1c403404203040d658082400040580300200488004101c0c014043d801480094889031228000484520022040c40140081d55031981054204e0040703100e44030010b9405a002c0380e64991442c10080e20440700c442c1d5079801c008044040186400a13001280c180d0b11040c10f012506030740768940088000c1d01e103014015581004402452184060001c0041c800c01c9070105400001c200c190291145001008100b030a50400c0240c1e92071103c0c0d1160751024140d03110303100c001200d010005204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 62160362 1250 62159112 62159159
    0x2307020c0f18041109010b0a0306050607030806060a02031210081507020d051303140c13020403080a030c020a0605090622081803070b070b011a0306030a020609060c060c0a0306 77
    0xe103880b030844628440040044404000d1020703182c01c10303510003690318080e2041f041c145803035991418001e81150300c80c0d004140311340410301c5050000f0f82e010103125400401134800d5625003654030401ea10314003e00020745c0c02440c6040422101c040510f54a10440303c4610850708a903040c66200b910100040c2e0744100141c1000300118a094001c80040001100071240108071035543d0b11805601155510300c0901500030300141e1800f890081a4481285d9800c40304501d8685140ea5000f0079200700708955090540300c4c610500001c0c000c1c0001050755030071500a20451624001300e0b41c0324030b400c950061454103200b484604070740c194481d200381d4561101c000303444c03c2084000c00000c0b00c8000340302c4d41d05105d01503000c500c1100c410054070015100d440350529950410f180041d111424010b112a020014002c005003a81c0009020325a41d80680328103641780000c1000c40d140381303d560303000c04241c41080c0030f010949803c00001c1004041c40e98040207100c0c0c03580a109284140f08001080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 62161612 1250 62160362 62160379
    0xc03040b070e030a0212013804051302090f0f01120209010e060312040602030406020d0e030c041a0414011505210703020d05190c020f07030305030a2307020c0f 70
    0x1000390060b0250441c451000302101c07260041580011601070380c002c0400085d9440350106040450540060805c5182070044256010084100b01910005260040340324036203450200e44c10f07030300340d22061100319005455a202860801c0d48000c268009035400701c04003401c1c000020714070910000090074a6401011580c1c0e40e40382540c0c8086a50380504115414028140303c0501c1c0d0745184014001085613401079904c49180100103421300b44d05901d14020f1001c20001000f869602158100050f48215400580382c2840c001022002283e0006242c1091034058094104d1140c1400a81207801070035203928118428081140c00b4020030783e881064101d01d01c2000c01c18442c1682280e030004030b17071800500301101c6011b42400d8070010b03554070310490003442c403080000659009540703034001301340010400300f984841100e41e00c903009e00c00541041408800b05060740c1e40d94008080b5905080306990801c080b9100c1c6100d5441c09488076005803062054108440c1400504469001c0700101041e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 62162862 1250 62161612 62161621
    0x20a0b0f0706020d06080a1a010b0a05030c0313150f050a090803180307060207060c0206090d0e01030903110d0203090910030b0103020603060d050a0506100f0e040f140a060f050c03040b 81
    0xc020b500150613980d40e5603100e000208000c40c08010003050a40689078400f60745003101005540010103800a41034841d0402c2601c2d001600309003266040700340c4803209903503590760440030032000c00e5040009005081100581c00500c941c0d400c80040a07400000c104039030707100c4411810460b055600000c09680040c000181c902d180d01d01004150070084054900e48490b590b2103404071381c44442c049400507039808441d01107560402030117601011210040c660381031a0840a1310080e00329034000d04040e100c0b50180205407140c60136030100a1901f08855506a9030b00010303490f5004245194068620389000039540c01d502c400c01012240c0014031404183d007142c082c0401c1c1d034401011181c020502c5414800040c400300001702074075008001501250400c2801c0b1403411103240c0c8004c007500c02c444002d11064400d140e501350003d42c410505000880140b41a0486040c1d1006251f024007450b4400c80a000250304400b030410030000c1c0c100016a10303100c1c2d4014500081e1800380ca80c1c03042ca000213 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 62164112 1250 62162862 62162873
    0xf010e0a05190c0902070f06060801021c05060d0602030a0204061b08030601081b03040f050d0309030206061003060b1306030605040c020606010c0c05060a030f06090501060219030e060307030207020a0b0f07 90
    0xc0c01d810f00443c40ba030101511421302d00140e034041a811140091810144028801c00c2e208900241003a14000e624080000c60040e8092481c0b4504514050f602c5003c251780e540c3e040004855150b11810079500c0b49080c03403503180250090302c9000701141903e038111404041c1a20448050381d4450404c1d030450300c030030004551084000b08050245214030401c3c4131041d072220065071145100d1054011541d00c1da103407a5090180690b205420f141c104017103500081c0e00402c0702daa00150981c1c1190740e40300288001c80141840d944080c03010400081e160f08003600280c544025500c04e620248a9141d03500240000c5466035609100140c1040010401c00c1d031049405403272182c0202c511640407525040040c000e507015160400219076542038000400c40d076405007600a0070205000c010561501d0400f135152903c2c0c41050740714a100c44110070426020b030b0009000f161020f0302c5140c0300d03d4203540203002542300c040c05034440c40e001500058005011070444081c02140c0d185d42d0304056680ea100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 62165362 1250 62164112 62164153
    0x30705070b091204080a1109010f0b07020f100206220b061210050c041a1908071e05041e0f05120309030105040b160807050f0306040e0703050f010e0a05 67
    0xc0140f40100614428508400400340000e085418082e00d60040a031600100c00c09116124600404032400108146124008440211801c45080c155568081d100051898100000b030703542c0105d40c80001e40c91180d001400c940b0400c041c40d088003450144d01108110540180d000902030402d05e030000e41581003002402c9001d505100480e00a81c046040c400c1c02d892040301c148891103070108081200d1420240c4031401c000f0f9102d5218501500040c0411416a02c0002203040c8004100841c010504c1441400500300c960142180312080d40d000c01031042c0e2140c41840f00b5240100c0e4504049080385280c0000c03141e0130610380012a140c003042c0900156141c1500020303020510180c0300c280c50a0007120320541c4150162050340c90300031036200c40010310412083c2045503e00420181680200448104411050203c1d440790340d448005005171141d00302d51596401990300010800000183d03030b1035a034585200910041e0780d4130007040c2e650703841208090501c0d0700c642254000707500304804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 62166612 1250 62165362 62165371
    0x8070201031107051c02100b090106030917030a0b011202210903070c09050412020d090302040b040e010234030c060203040c0806040f03080f060d060507031b030203040b0c030705070b 80
    0x100da007000d01c562112400c1c803060803103030039072025900d980e904106e42c107003c3c46840f0101c1c00c50070030906910b940400c0880105000704428181d4440a520a1060742c05101200b0208011b80729940d1a1640c150000783c03003c2c01c41d19021800c450001d581c811410b00a0341c000f0505d1180c012003030301c03544240d1440054044e150035401c0c0010441d8a000c80d04414140000d0111000c001c202818580303800e000c0c000c04001e0342821500b0a001d120350340750740b00c3e115504494040702e011400c03411004c0018010b1552500142240d8070002d0b00e00c07019910b2a0b010a001148461004020402c46000c0c3c00f443d540324000a000900c202c03944c41c00151180d01868005000d1a400f0002544030719202e031130140155410340328100640e50307410030181c1c040711300c076445051103000c2130040c00d260000c00c0015140c80001480c040e20f5200280403248a41e010300461501803001d00365a9501005c003a00030740c8240c60955000e01c071100003a4640400404490140384c8bc0d80c0d6503450202680c461605c900405003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 62167862 1250 62166612 62166641
    0xb10030b13020a0305060910060f05030403030f090f0201030e01051504022505060a060906050907051c050c27061204050a1b0e090708030f090f0604080d1b0807020103 73
    0x41c000440c039001d4806805007001503140000d0505054003000a080703801007558a840d00005070900c01f080d440020f03000140b0642c01c006489403a0742c80d050f005405a00d00c1e10610f1440c103480c101c1445005180050114000c0e2030800c1407035220a0054280c4a04444401c6010b00d01240c0701c52070305241e4000c041080903110700c0d10038810340f260b0780b0383c0d00d00072070760107179501e0f80030005120384040380b17200d090020320020a04018262030400450b8021100521140a1240100d6011100724541e4121905165284000c100340c2c07400c2e080c0a042074001442003c4c0c1d9602d850710844000c200d004e004900040c000341500e08150704408440342e1040020300031101400b615445500003a02d40c100c10006031192030445079801d040003528003000030024214038041d401038804000c0f810b40070049506400000c3c0344240d440c1d94050100d105402020b4503180c200c40b0024001880b900301291900601c032a070743d42c140000050410310f807076141c00c203200030300044003c102d00c00c019802580030f05d00402000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 62169112 1250 62167862 62167879
    0x70503162c06100c050f070e16170423010518030403050a08030c070510020315030c0d03050c1501081509030f0f0a030603061401060e100503010e0a020705030706060302040b040b10030b 81
    0x2d17600d5074240300c1921818011903100d290240440701c0c0203050300754003640007000d295511040d0400180340c00b013442c1036042000f85803c00f0a00b440f00803083c15100c165100d1400c5070340820400d0050082c08100e035800b006006096400710340110101c00c503400c41e5040802410703024040c0d00c5082d01c0d030384041c1c00c1c8101440104018800560140300451032012820401a141d10700540d81c5e41112800c40394051203174100100307032843c65584010300f50815425240c1140c80e141451000c9203400e1030703001c0030b08070461854000141000006803807800302809948028813611020a4a035990040c40617514220b203040c8080c16091030808041d040b80d515a103004140c00388e60362901c004488500d4500720300c04541c0b50041c0300180d00032100881d03802d4155001d007295000d8000c014210b00041c0120310703080e40c0c0d40c0d0104288070025019156034075013010549903100303103a151400c010300c0340744003c034042c83c10912034103003518042c411640030701070180020400700c003a440120010254481c04c0b80d030201d44c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 62170362 1250 62169112 62169137
    0x603020f0f0f12010e0a0b041e090606080a050f010c0527011205041407060807120e07080304080d140304030c0204090620040302010818070302010f02070503162c0610 73
    0x344494603000b0300858010b10f0290030306c488550280c03a02c0c410001d00071410054600d80f035448001800070300b0080b42e1170014000d409032800e84050801075000d403100c0c0c071901d03100b01c040c04404602e8101c01c1d036205000b084801d500d103c003580c450103000e080b50320700072041f0040728000380d0510700d019440005150000e44901d68005080881c1d00903501980c050610411a001d800000c01842c4040c1c00b19040204c1c00b4601007030000e00c5460409050000b003600c0348010344181c2030400400d40500300300010380c2e4540d40c13034941a81d500d0b0030b141d0080002400001010008440d09001c40b80255010759409604100503000d1101400c840582116055a0340d608407050415184854042c030a4040d82280e560707107980001800300c88041c0410000300760015401c0c07141d010000320802100d9080c00c0255111058503400d80c280440c59011a401d401817101c8030003c500c1500390070080c0c4042185030700f5002c40c5410541100f81840c040b400c000c0c10600082141131400032509034041c43c443c0307000d610400c103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 62171612 1250 62170362 62170387
    0x201081e010b09040c09030c050f0303040801090b100603140f07120609020d0b0301050f01140d050a030503100e091f02090a0305030a02010b090910020306010c08071b0603020f0f0f 79
    0x28264060740e00d0b8100402c0c054010302e0503024200d09003016141181e000c1382941c4584100244c94401c3c548135180d03900d114001600c05105850040007130750020040706e000381c10070346d070840412102058490417102c00030540754003a1040854117242003042c4040c90340d0380701494410000c06043c1c3c0c0b080c0950304002c2c4c1c0210410f0b00900c000b61445113809a140c0000d0241002510116085284240d041c50108500c10703001503507290442e0024648004c0c94001c110104841a0041401400c0e60081188000905030043c0085016955021000400a9484001c140200c030185e0f1080981d402c034600140c0034038505000d21b101600c400c40011303d070440c0307100020121000f55204882680010481c089065028420050450700941d1600000e02c0e100d00c3c007980b141190401c00a400e50f021000c10440d034802c040e0030401d50b40c400011a6074080504041c0540c0202c0c40308110248000800030407a10700c207000341d034068041e8040c2c0c607041522991a25030706030072016481905207000d0140ca022000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 62172862 1250 62171612 62171671
    0x913120302090d151112060f011103030705210106050904051015030e0d0c03020a060509150108030d1b0210090206090414011410090b0d0609020a050a0815030604020108 74
    0x7807113161940420706070404980103031034002148080094050144028003031101d000590b2284040700d060620015850041e03884040e59220010f49100120800c01d500d50010020705d50ba174a844001060a01e40c2202020b00560900502000807402e100320841420541c0055401200346400c9011254407803581c0203151007000004e0300000c0c3c4501c48070301045030510802c1c004408624000b85004069103019683c2c03070350301c2c1d0010501076585c0c00040000c6802c1c05492802401040c1007845940c1d02c004581c0d583c1c21041030410640e2400c4850001701c960407a00c0000c10a103a00a003030a01501c10141008100402e000e0340c0108003007018403502c0e0f489110b4410007600c032500c40440c0d5410311040140b95135072510300c02d0050f00904040d407480c80d00a150780341100e20b1b407000790307564112006400d07025040581c0900c43c024004111600d9841c1c00c44083c00f80620385948032401c0356180300c0901e82c80f4001100c8175400d42c11120110b00954402c0d03101640c4120300610741c00510600c1c412404e01c88 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 62174112 1250 62172862 62172889
    0x30207020a080f0a0b130206040b070503091003020a0e090613090f15060303020d050405030303041101020109020307080c100516031413150909020316050a02010e03180f091312030209 80
    0x1600013004e204100a00c1c01440380c1c1001402e00c01724802101940420030512540c02894141a00415480c0400200300215109410701900c000c00f4504810000340194000c452140045410400c400c0c0660600c0440c40c3c3c850301c402003269808000c00030415006003034a103030a403040300340384010502181070030300504001001440b000035a1403444c100242070441203100d000800c0300c01c10007007109582c00016a0f4101e034010003804640500d07040180d00401d40f100d002034050090400014514102060750b01003e0030a440300e1130301303031210a070450b03032881000c13801349250001c1c4c800b05010a105a0000c0e95101807056614a07281002c030007070445907265031006100c0701040f104024a142c1c010340c1600103050400d0194150b041000da44482825944100400c101c404542000454401d411204200100c2e80c140c90b80c0300c114a80c9400b501e5060340c4454002c1c03112018100803410310000c030901c85d6003041d4245092280a40d03a03e12545013200d03031350082603024000b41c1041c1d550006071a145 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 62175362 1250 62174112 62174143
    0x40f0c0c021005040915080c0108040b0f180a061a060f18031204090501050307090e3c0f06090d0206010b0f1201060201020a021b010906180f0f08010b0301020406050a030207020a08 79
    0x1b0149803141480c509030000c00c030181041030710014000080c03251003603550060010410280240d50b012540d44014641e420a00c21300d100c0c1d0b0a2a80500405902032070359030b100c619100622500741c40900542e0b00c5258100c40c00800100300c02d000c0062404001008040018141d40042c44000070b00c4403d0382098120b050b0b82c1ea5208010403403460200300150091119000510400c804030146980300d8558101c02d95095a2541003100c1d038031800d140e6200d40e4815090f90140807459401120313521145070007201c07a2845008041090303804000340207032410002d1303801021036038241242e106860f084002c1e0251940701c14800300d46011215a0001d01070240b9900058480e84003000081c80d128034804640541c41e004000e140e032507680704010708191038032b0707040c4012104c401d803a103500203044035406205002002003002c10200d07064809403040307441d034030001d11500b4030103010036080703115521031803001c10710810070068003501a0700640100d0f0b000906140141c8c2da04c0410500341520305120110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 62176612 1250 62175362 62175401
    0xc080718050901060605040513111b06060901240210090609050118020f0d0206160c0807090606080f06010c0b0a020307180302030604111903050a02040f0c0c0210050409 74
    0x440c1020384142640701000301c00a21004d440c00201401c14400c0e4000c80b400343e80d00a60f2100c8101154005180040c0345030a003581e940e4041e0041d280300c084c0108001703041d008172000710702149890300c0020b050f03070214007100c0c8601280300c0c884107900c00403080110560003540b04c0107070150500e20602c10f00e14000c9402046104081c902142118100c1d4044c40b0701c5150555200c0142c0ca80540f0205008d009a0302490400300034000101c5c136010300c5140c2c548000c0450743c0307841000f010140f940215604d1030f080324140f41c0c0311030300501540c4560040300001512000003c4c0703030180030001103410000c181040030618003076841c1c16031444002c5850305d07401d540000071311800c2c6074808510700302c80c80300d030303007508540c50660380020b0300c43c040500060a0b00d016407007544242c4c2d1b50610341c01a215030140721010229074a16001d5203980c05d0100a0b4861490108003285124042c02041c11660f055696400c0315107143d400c0285101d84005501c08008050001044400746441006070800c00c1170b14425 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 62177862 1250 62176612 62176649
    0x180314030a0e0102061605250507140102031204110d02060c01141005031911030609060109050703050f0402010c081b0318040b131a090411030c090c0405010c0c0807 72
    0x145403a1802e03180d03504540c001c104024000d02c900640c06501440780c41e03c20750f00e9040440041801942c4038101d20ba403c600b035132031020440c0002d100e0080310301c02c20403a1100c010324001a80c490140400d03000c4058040c01c0041c000400e81021044822401000c1146001507600450703025042a06404204e030b40d0740301144001c00303421810f981c1c09140d4199002ca0181403001088d00d410f021100c2c0305040c3c51300c0c58408100064101d031180070740005000c0b50083d2825454160f641c50b402e100340090079203884041400366110f0f00500344601d10605510320661201d034011248004420401e50780403200f84032104140100b4544080398002c0d01f4000c54a804101c41829a91040305080358030a500c0c000e1243c0142c2c03900c480500c1c42103c034600c00543c00000004102c000d4040c1480264410744c10800c200400112218610580c0e0741541103544441c040001d0220400007a50074000c61072050000300b00c3c561092035103e652a2045140303002c05a034500c00180307000c100d078201c0150038010900a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 62179112 1250 62177862 62177867
    0xb03070f0e030f2107051c1b080306010c050c03010c02070509010b0a08060603070c06090303020a03180c1401020703060614150f0f07060b09010603050603010c03050412180314030a 79
    0x103411614102e01504802480d102916560400190111140700310302403c468034010f44402c0d1074415070080295280c41c1c4d040d140c40e0500582e0a04a0f40102c0c1d41c0590024003058103980c0d0ba40d480c0d80c010012840c58441e10019140c2d041688421116841140c3c15039142d43c03000c2c082e0072074501039a001000c2507401e00d001c004071580160403040200710240070440f000c41c0d02040c40350b00301d83c041d9030495503601e88000c1140c40700f0007940094440f50420030070004260749940101201d881d50340c1c0030016442ea81941910062103080e000d8241ca10414003400000040000d141030314005004641025580c0c3d5601c2c02901e0640c3c0c010308034204529a0600142025001ca0700700102d0000e140b0b1600401942055440c02401a940c0365070038042551000c0101d554001c14031440c000700070304d50960b5240c9004018000441d4494000e5081400d5003804034002d0046078051079001c004a034080501142c2140d4481e240560958018040500000450716281c03c80999000303040286546128045d0003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62180362 1250 62179112 62179127
    0x41d06090c040504080304020f0d0812220f060c03020c0a060203090d020d1b0609060e010507020c100e0d02060f0a08040b0106080906130302100f1406060306150c03040b03070f 77
    0xa03540180d00f004100030001d00c078002166806a8101c2c0d828a01c01c501c40041200c40005440082040c80c0005a526406900280c0d0700d100d800b50000c03d0b64100c80b11202030b002c207450150001c052240c01402c030300010321103802c0709131b410302c107860300605109000c00d60f285002c1c0e1042e400c2d01c40b1071b4004240581c4d01020720807143d4000c500d00050401410420b0010144482511607022001d41800b44108019040d080000c00c86d4001c2c105102022040d0740d0b0f180200400e0b1506005403080080c17400c0c15003846114290344070095128003204071402020f1100c0082c0040040b6884082080101210f804040c003501d1141c0d0b1a945004040ca42440c2000511034103801040034003910b007003000a44040003070313000e60112502004803e020713441e1509901c2c21481c02c03c10462642403805210b8101019444140003004580c201d42903503c41000b484003c0c4010b9901360f410400342501802c140e0101002003400445441c2100d15103586d42c3e802900030f801c1961100001040070b4100c1064681c80600c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62181612 1250 62180362 62180383
    0x190b0d0f0611030603100905100606020c0108010905010b160c050a0b0307080c040302090a0b010306030b130501061508061903120c110a21060b0307060302071401020306060406050306041d0609 84
    0x1491404c0c0707100042d648003000c1550b60815500c52101c0010050280600551912600d00a011844d00d481001c2d4640c01603c00650000710090000179810b1114064103040b03500c6451a20b152100520b00114883d0001c0340944480402c94070020b0243c90f0312440c1c01c002c090301c5040d1622030414800c000c1420348050841011984207000910140e0f881440140c6c108900000000303454220f4401640648802d52002d810950003608002d803c030b8080d507114200f50701c928003c000d595118150740200c0100001e103007001130b00001c002602c0d800c015100c90580004030350422481544c0703548080181d00421150400203051007800c20410203082e14039002d40c40c0031950a18042d09244c442c0724500011140c0d401c403043c800d0910803e00060380d0204048007806030554045039120000500a940400d01c201c2d842d4a0a032a01e0b11800410301c2540c0c0601c0300100310340c2c40c02c0c2c0f40c00c0d01256903400c040c0105030b00580e540c696088010710b07d214030f1004459800035100d1460f2000720103003001d04014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62182862 1250 62181612 62181641
    0xe0a0209030606041e0f06080d020a210c060507020a140604030807050f0d02030f10060c0302060a0c05120411090702190803090c060d0b0306010b0f03190b0d0f06 71
    0x103045059500880d01c25400002a200010102107024450a007100d40c5803c40400c18501042201741c00c030749400c804203440d80401200c8241c2e980d02401c03680c5004039040a040d08100d1020700003249110880c6100c03201452414002d40c5005032035183c1201c40c00d441050150740403a80074020031075012006040300160801404d000e14003038401400030140104100d04004001529890a48214080c1c8004441040007192646880b02038810b100f0070540f620039003007080c00c0000601a01c1402244030b000c0d4550f014103001c2c3c8400602c01d000d030a00d80c0c0c92a0a1210a200b00c0488490174440113120342d010341710940066071074405018101c0f4001c0d0006007103400030349103046689690307c20360306003981c086289983c0303580f081900b500f403001402d026030380018005286504240c250300314100380e440131800d40b965a40d031a401868a441075054030061541d0500014007605c0040400880340e1996260100f08503407224005408103400e207904070381c110700100301e040510040d4480c2d06825020030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62184112 1250 62182862 62182867
    0x601090c0e10321b071e050f24070c03120804020406090209010905010e04020409020708040918020f0d0201020a140f060c0a0c120302040b07060603110910060f0521010e0a02 76
    0x80072a81d94501c030788192020780b5414000001a0124104894002000000840101c40c0c3c40c1c0c60039806c85007000d00c5140c0c8100011000d0900c80c0c606800911741038003c003030700394184101d100da8040164208201c00e84032000106000400f050380e4410303064030141d007951046030070302d020310412040324070301e03085091028410320a100301e03030b41c201300c8070b109840d000d09000c0c0d4402c404c180064040c0c812500701044550000c1412001c100b0084081d0082d02c0645c541441a503c8090400c21400c00000d800f80d030203520000f41d00414141818030361101c40c01881a03030210445503c40600110985010612035440222071240d900d4041c0611a0080d0322504c00921f04000301800818840d00120041c01610f0302d4044400c92034001d5044400405c45c40303a01d2910341f291400d14000802851005880548203215643c100d484d1400e00944521403202d40d456869003003100c201d911078801c40c142000d00c0010048480c80076130403411005c4001580350011080d60620b00070b00340b0002d01610340d0842d103005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62185362 1250 62184112 62184197
    0x1101050103111c1202060105030714060301060309050f0d0f11070e06060a0210060902040e07020a032a06020313060c0c050a1209180c0305060a080601090c0e10 70
    0xc203101c11000a812542c81182500380c2c0a00701203103c10000007480d142041d5007480384e203a000b04055040b110200d0a5903805640d07101100311040000040b1584113108000510000e80207510804240b80110122342c0a001004203180c907282c2006492808a0020340300b4400555100c144121600d0810010788201441c00583c018680c9002d00841e1103400040f401c450341c24070802202500001e413503800e01c4500d6451054000a60042c010050110140300004401c03034000540800c0d0542d265584440300e03214503050300d01501c0c9030b2032603444098040c004207010030a140040c60123000030451255003a0041c7c94900219a41550003805105101136003d021847c040750302942280c1041000344004003201044850103415081001c40c1d141b4000724440202151784a4062040c064408201d19180c003c100300055102d48280751590b40210300610070f4020039080f403101d80c00380b410140280501361000a401d8088100600e0018000c1d1941401e0326401c200c0c203590440c14125004019420f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62186612 1250 62185362 62185373
    0x30b0f0612060607030e030615030d030501050108071d040204030b09010f0e060c0904060e09250f120507030f0b1005041802040504020d14010f0f1a0123070f02011101050103 76
    0x100520b99071041c080807440c0c406060107082c0000c0c210400038140c1e0014540014004841980141d20034000c2c418090313295486030282c800c05058840503100c4448681d5188021100c02002a58040d20302407070350039648158481d40060005140308650028031441c019031b03500d003101c0782e0300c0b940304060381085440280d00c04d002c240c041d000b000704c1024696900e02c0c0b101240181140381c2c00450607100700030801100440c0812041d60a42c2d0000c240e0748418181c5010203120074107406a2146411030180822091017111400c4100620820170340d4501d60f42e03a2644918078040303d1042d11220101c03410480180340031400c0d0b0010300002c6a04104402c840880c80c43d050070340b4035009004580e148040f800790b549401040002c030390300c08041c2001c10482c40c00e13a4013030320300880780b542c0c01e90070164660915441070240d14111081e40c4000725100300f9040046a44a1071a00c9403d00462540c05200056004100030505c840c001c010b6001701200d1807000500600042c0890b440591610005000007039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62187862 1250 62186612 62186647
    0x70506070b090708061501021507020d030207030908030406020d1b0c09050711010c0509150c10020a120f02070b010b07050d0e060c06010f0611030301030c05041a060a030b0f06 77
    0x1500038440c201d0a65541c4085468011242c1201c052841284200520f0880d080744020030f0b10070a0b820b551103481d01724900403511a041d2005400358100c140c1e0340009074480d50240c0000780c02807411004042e40e983c0502d0035075006400c1034006800c51118002016007040312061410b8045100c4000180181c4076800030016038051101031546460100e200640301c0c8000c9010240e504008100d008a6454050101c4c1c1c801d08106004000149405024000881c20f89040d07011040c041c01154483e000d41078029032101e00250700f4040303510f05000680100d0b204145d43c07001282c4006075a01020702b0402800382c0705074404484000c00b0010940001c07404990b12039840c0313803070612150034440e0100089c1107016003100136040344240781c00050f031440550900c404842158884001c07030381d0179201844e00c0f44002d0001401d00502400d0811260505038030040740c80c010300e65801e2801410301c0004441c1d50020340b1800c0041d44070384e0189090300c0d08210309615940c0c101d40a42c9085e1364258401080b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62189112 1250 62187862 62187877
    0xb0408070311040b030312040615050102030304120c140d031107030e090c0d0908090405060f2409091e0601020c030709090c080106060507050c09130b07020109080f0c010e070506 78
    0x10b0075207602c4201c1c03a2580d40124101500c0101034941341c01000111030104d80c0d040750243c034100d00742040d18009110018038401603907410b901561855917503450f100c001e440408241d404104103610600301241c083c40d421110300641602501c0720211250b4018151041241800c04501c410880c03440069007000304041c4649041c1c8540c2c509542d0b014038a00c5a000d00c540303080358103080c500d018041004000c0106921042110100050b44811040c04000310a14035446d8000300c4107000109005260102030b52283d943c03d81c500e10300700c000400b1031800c28095550400d200c840c26119090818038003819544400300388000c0584035094000641c1d070340c207148075007011a6075503a040c034144030107940700401502c045002480f038195201d100416541c41f0080613603a41c01001e0b40d00d405450481c0d0181c0c015001d00701050607100180e00c981d10340801c0540f4100656688415410000e40140080c000c84119502c0789612421040d0300e15082d151050107021041d003003801c1c140800c4d901e41041c0d5100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62190362 1250 62189112 62189123
    0x30a17010b040e070905032d0a08040e090304030203191406071413030f05030405010f030902030318030a2010020105240d0f0b0103110405060f0411090a0e0609010b04080703 76
    0x22134480e410142c41000141d001560035001e15840c1017000200074801810b9074a0006548035188200103002da1201d045140c0141003c10402003000032190720040342d81c101e5184410b40e4070b4240e896000a20304070400300380d2040b074541402d101040c043d07507c64035080180c100c00501141e15014100402d4002e6044601b4101c4102144940c400c0b201ca410000196a008034091100403503401d00b59900e070400e10a01e070000b2030b5000c00b2200c0c5c901c2401a42e11207a800f900840c184810600f80e8884c12441d601c542e909880344210754008180c1011541c902ca103001e41c4046000307807009091141e289071910420081d60304010a00100c0080c9a4003100c880810704011090004040009000350809043c00f82040c02804c0e5040c091245ca004010304030781c412901c100100181500344070907603d084921a61000728030319142c0c20350400e9007040b040e400070300054500d04595100003401112054108003450032007001040414106403010364050710100350f4080c141458450030340da41c1d50380750100400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62191612 1250 62190362 62190389
    0x9090c090a0603140318030a080702040504032c01080718120c0302130b01020c0f0102030d09020f0d06050103060e061314071a211306021b03030702030a17010b04 71
    0x5100e10141e0110b40510751210a10780d00540311600300d5541c0c0c20140302c012802c0340e80b088004140c03400240881855078402845814403040d6003c000080c88000e0056080c040f240030b0b003012824642094000351443c4811200d02d000402c000100400c0c002803989041c0454560000c10a0241c1c150010455001c3c0008800d110720601d45012000420790000b50000d03040d0860346088070017500403007044007080c4c1c22501503008480c03c0061400106020030b01503007081100c00010005604a0b4001c0c600140c40340100f442d03c040450300c10164403200b51200e0391340d003006108201b0f81c0c0c0591701c80b0b103403400010701c0303103040c0840d40c201c035000380902c01010110f030b004820540040c1800300c40c000780001d00400450008082c42e03403003075074804d00312262145001d5203410494441440d015000382d800035007006480003035603074042c029408114210314100b0081480602c002c1c082000790303c9200c05a0146071121072908000d486104502d103070300e07412880070005004c28100c41042e58110303400700c7c03100d19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62192862 1250 62191612 62191621
    0x150603091110051e07020405090f0d020303010303050406110703020310020d050606040b270301020304030801060e0301051902070f0b01030309170601060e01030207020f0d050d09060201020315010507021810090b09090c09 96
    0x11350501c5004002034002d41044200304124101081c0d03045402603920a5518098000d0000c80c0caa10003400001c0218506000501400740301d0010710345035101040482d900f0076100d400180c40d01900007001d528143c1c0014607240300301a507015040d0061000e5400700d0031f240c100041c68046005001415010104450400d0401e941c0501c030030490b54409802195203040c18100180095400d000342c0000c00c05c41050450312b4201403107903a00c1054190b400520601c5050180130103540900301c01c0e42c04d01841e850300b1b0082035880303124500031031190310f9a03003a05213441d003001d00c10100443c1c0c0400d83d42081c0010080306070410340350344a241c02480e0050391a206480080c07409855040070b59044100c400266040000010b08010f0020940d190103400d030741d4070310b4106d017170b8801204c084c0c000500c9400003c80c0c6501680243c15103510090071341414181c82ca81c01500c0c0c0c2c4040324001c290007000f10041001c62424490b45e140b003a0141d40211251511503c103e44d0350b0412500940105001130005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62194112 1250 62192862 62192917
    0x30f03041e032018040b0403141207080603120408060f0705070c050904080403150e060603010c020c0904020d080d060f050105120403080a021306050304050c0307030b01030308070315060309111005 86
    0x191030702c1c1c07a071104c80842402e03d0b041103403c3c600700715401c82c08590501c000c1020700380c1c07400c10781d0b4002a450350015415a0350440c200e80004010342095094400c0340060280c0c5200300c809003000d0000034005000b80c4c41c002402100360310004e003070b180a100d0100010004101010301e10010b07034400765501c050648482c903200219201e107a2020b40300406d0711008d800364500ba500462071204412048401c0703600c910b070030117089600122036240903902c4104481c070141481184158490b00007405c0c10010100382c0c543c4e00701c541c05088240344642d5214811310091000307071001009000c007880c125080c80c02d0042c403801079070303800360018052084150010f8107459850301103c2c0c800b0008403100114990303494010708150419a02180d42c0e008041a40c10b15040010300c00c001c4070b0b00f26007113410b0b5034616101990b41142c090001003c0607110001d803401d4079041d0450a0040c0752940d00041e10f24214240f07040c9003108880e4082c031440145c1101000158017005075409000410703880507851522a009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62195362 1250 62194112 62194129
    0x31c02030f0409020a080708090a0b04060209030d081b121302030a02040606020106060306090506090705180a06080106030e060601020303060f010905040f0506030d02010903170411030f03041e0320 86
    0xc0d4982040e0004000c00c01c03c403141c01400500043c0c0d103400c9041c4e1070f00c1c3c40640700720804030b92103030542d400514008049071030071301030680213806600f006140140002c04030b401c080c00e00d559000461858000e02c501110221017840d640341548400034105100b86641e007030b9602c00545031103800303100c040d800411755506205040e030300c6a00410400c07816a8a00c03003e4040c280300d20400c0d021070303e043d10005100d56940038039445050000c040280503620303003e00f1b4901d43c0000ca1548018a000d43c6044529200c0c13005201c054505915124055854044028142ca54800c50700c800e07900300c3c1d030a000315a40c002054940005088078000d41101c2d0b0000100c8215881e035101990081c1441051282204103901036801454242c003503c8494007014001e0307090703e4030020002c001031000080c1d80400041c41400a13085840385440c8840700014500284c5440788020200740300340c000180c100034001212103104604050352a8884145195440d101e004d60765194255100401842d002d491581c1c40010703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62196612 1250 62195362 62195377
    0x3060a1107121205090115050105130e070507051609050c070302070308090111010f020706230103080702040204080f100f06060207050904050717030702130603110f1201091a070c02031c0203 83
    0x404121303500e0b0041d6003d0182130b102c0081c041e03024641720041804d51180d8115490000640380c1c3e210b40510b041c0d44803403825001009101000014014440014002e20081c01c00e401500329503c8118100300c130000c21240e01034510810414204507280001c0c0e0003095481c00c032034000319081e850703040c400c00586000c100c001820031103501e0b02100800b0b01c442c075406064068041c800800c40d4101101000402034481108c5482c07403544000100b00103126070700103203e190310140025051075036074580da40c0b6154a208203004681c01815136403545038494400c1a200403035084003400074624007000603499003010f0280900034814000000c2c2400f2040144d140101042440c4520007403000a001b030300c84d000100100d106002a0003001c61020f842e018810599030850151070301e42102d5004c002030800c0202c100380e0400c503100c0042c00d0059080c03041c445824003403c820030000541c40510354680310020320000a00c40009a48005600c00044160f000000a0b107407200b1991030170300c103034510f014010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62197862 1250 62196612 62196647
    0x30a12092301030e011e05011409071709010b1e010e04060b0403020409050a050a030504150206071b1a0114030c0a140d0501090b0709030308070306050321070c120203060a110712 78
    0x181004002d00d01b40d17100e14120761030030f5000d0707030080c904400300940c218058800b10001401e0002d000c00d40c1080400003604602e0080c00002d49042013004101b10f00c07041040700070070440c40030054006582080300e08440c2c40c0c0484041008604280080c82e043c040c501000c2e028654454a450801c0380401210030301036000422904428807602d002421684603000380e00402d0310219208603000d000085590049801d901c500c5080c20380034441c4183c1401a08090302ca4243c041410144190110b2145001c1c00410361161494807000b010f041c500050b51951a0007500724180401c1589040740c0e1171005e07064102c41682e01300903641001805814245005003580c0001d0080c040c116810044203400c5a00c00d40f80d01c00c00c0d544d1240280c04540761441443d8040e0130004140402c0724009412900c00408061818100700081d105c101c0c0307a68403034100286080c00c40850009514040080940c002c815181c10311000543c51412122070003140001090f00e111403030701e152440c1c0203040003c64051440c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62199112 1250 62197862 62197901
    0x509010c0606121403030403021908070c090c091a0d092108040b01090515101407060903090e1e1b030a0c030b01050c06010e1005030a12092301030e01 66
    0x2c4004104900c00380c1401c071141c44014030380404004c40802a00e1050b40c01d50090900900d500380b41c101c58909041044404e074104014005c0000e41a501100281444180000d80d11425850140ca07840300e81d0000c2000024201c144001c00910b0002c658580f6031500c0040f5071003004e49841040f410141001c5012048055000584e4039070106820780300d140580e9123160540d07a03441010b81220f1003601c1b07500d031704500040b0300c000d503003131400108030245807924010385c0c3c8030301d041e041e04100d801c440030440340d031070715030701d070101450b83c403040140140040301e059500500b4200e01080c0070322031800c0220003040c42100000e220840c2469000b03020f9002c151010f42d6450044008001401807416076030120349801c22401a03544100300366420f48041c1d01c000d0206909200c0440002074000b0034414980c14840c01c00f1942780c40900401d500240300c1e41d004422100341c0c640280030614070350440d00384200504441000580f50140c403542e0f00d802801c1c001540b42000d4209805031100004107001c0d0202d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62200362 1250 62199112 62199119
    0xa06020307111201150e240f15130305030403050114010501080a0902030111030414120c12030a0603120c05150c0d150e090c040b030d0509120307020307030b0a0e0106150509010c0606 80
    0x1c00c91043c490780c1c040f0041e01542060b04c0e8040307c250503c0c0012a04401da0201c100044d0420b00092003603685861a003505042540300140707400560382d0000c0791150000300303040040040c00d001c3c4641c501c114600d10001581000002840b8040007000051803a449071101e00954400b98030000d2103141006075141d41f841c181c140f180302c08404141406a521a0113041c14465003413006842941c54010068845100c40140d142007607000540418805e07584d5400001c0000e00a0000c00842029610380c1d0280b003009082107428044030004080b6508007110400075414501012a0002a011440007031210140240d01001c81001d412071010344814105100c4001700006651203045422a410b120420140c0f0074552a5804090b400010039401e1100048911b000200200080d9000c81224102a842d80000f40380c164241d0080d00d24401c00c00070301c1080c05280c007948012030705410091040c00d06d460b098002c800003a50b0030008028000c01d030a10303568480e0b40c0c28a6841d81200061008544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62201612 1250 62200362 62200379
    0xe120d09050d05071101110c01030e0f0105010801150f0f0303051b0703030509030c0f0a09020a02030c010219030606080912030709030f08190903080a05030a0b0603070c020a0602030711120115 84
    0x484c010b440c01c440211034000c0c82e40c0b0981320184041a458090004038445900641c050841158544c8040c0184020481840002d116141c02850070b5400412f808060340500348480d0705540112410500046003444248031454900003100e41c0b516046548981e2840300104a03030041c500b4900c640241c200000501d0f40c40406007200310000c805030780041742d181e403c0249280b0402e2a4642104085000304445403076580070f885d0102140c01620704c0c011400c00c10508a900c64000700d940a40187c40105920b030749442007002500840c1443c07130b028200010704690722580704104035460200040010300152045c02c031640110390000c05959070030300c06d14001d00140c025000c001075201001e00d070881100d1151030703000b00300c0740c112a03001d2809590103011995940000d21080b482602d0f4025940e2030307120f0750025032003100d96582d002c610b500c0070310402c0041403a91b80b01c1003c541c401d01664001c240340d20090604104206c62402d1403c4016a150b0702500d0a0781740c108512120f00340020360103a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62202862 1250 62201612 62201617
    0x9060c080c0114010e16140702041503241103060d020a05220c02010501060c03120207080c010b01030b031209040515100f0809071d060d021905090a0e120d09050d05 72
    0x40111050112560b212000c40102c2e0726112079007000070b460724401c004c0121407c0010b15020740068404502415990000d420502059108a40b0507141040454001d51305404a44081444040c2480034a480140f416228040506210311401841d01d42d401150b40d0000d8010042070050710f81c3d60b510a0201032042c000c5807060030250b0300e505101803042c1c040d02c18450381c0e059841507210200c40c540300f42c4048451444c25502001c003664200249008900b041001c2c091803802c4400124a249040000401b540c1000d002640039a0100c1d0201405580c1c240648004000a80d4001050b64500b40090032680030100c040d504401d5000d004261598000b111030341a0910fa140d400007905ea02d10380c190f4484844c8130790359006400520480f03e5a282220840c0c101000400140901c00c1c40c7d00024070f840b4440b4202c034000b4142100810071400c1c01141298000c0e4130b170000700924955003086589a40d80c034807c00102c03020002c3e2081d0300103015070280c02c4045c0c01904403a003180c0780304005001075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62204112 1250 62202862 62202869
    0x1050327030a091401090618080109120e03060105090c090301140a0204030209010608090303220c0b09180108030405060318010f0b0108280c0c060513060e0a0309060c080c011401 78
    0x39000b50b0000c55103291104c0d0195802d01d041e074588104da481c0060896100c0717551004040b40c0f6600901c002985882401243e50342400b400c580701c051540c1540242000c80c18220103400b9801c1800100100d50fa1a000140e02c00240700e021a41d59a00100007030041448800d440c001282d600b0030300c100c8103426070141080d248260345c8940e050742c03288820b460100085584810580c820800107d41c8184c2000c0c461102d810504201000840f503541c04126040e01d4004c140e48404c01300389200c5526211141785114991a08200010f504040d2103035282c0c89540034050169000102064003903010070041441c0140ca60001c02840e8508191074019000302112030b80042c01050105005113400e068221010764984401207540340410b01a1001d41540071504060106a804140120702e039405003c0c456406803104c02e0300074555140003022900d0450192116601012585000a4115200e481a1105030030061060303011031614031110300c01c03000541025408c10503c05a0002901c5489058 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62205362 1250 62204112 62204117
    0x907060f050f13090b010203180613051011070504150b03060315011202030c100e091909030206010906091107030c06091509020f101706030307300503010e0601050327030a 75
    0x384000d05c0b00481c0d580c0110002c0c43c181d190081c46c140380fa45054001082c8403e4070b1081070700302980d5070002401030761030300c2c0720300011451403000542200c000b40080000790000305c50030400c0f198103040724022110f00c3d0003800d041c1c0f00c00101040c2607560400c1581003803190303820703600031541e1500c130110000d4101d100308a0181c401c801e1481a1490038000402c0c40e1507a41e550f10b110910030004000500001030103241001c6901e0405102441c1180143c0c4000c41c041d030010511035151907203150403182e90340c0c0700101013441d20005101402e510700848007602e4151429028040b06070030440c0c018100303108001c00c03020b074966500c0d005245580010400c54021502c004640c0d4082c070610040c01d80c44401d00c80004e1040c440100b03407000301d004494110002600300c9051100355603d400300c25100406640c001198541d0041e031030801c082001c06005502e14080303080d54540014112016401703080da50512101000040185501403c40349003400c101c0d90115110341d10200c16500d0f40c2c40300003044c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62206612 1250 62205362 62205371
    0x703030e061216091a120906040218090106081005040209100e070302070303021b160f0f051003180305030711060f0103030318050610060f080907060f050f1309 70
    0x4041c40e158040c2c0365164210705092440f6500c00c00c142d000d0a01d00031008040c0401c409022503091480044044000e868580c0d95540c0e0302d1000400d07011325001851070b50190310400801005032640701d043c092912619405c4580b540315001c0c9a4003505d402c0d0403100c0c03144500d04000c42450201c1d007009020358029102c001e0640c031200c012113440a8a4000c41e00543c0404001c62000c074400e90040c80c0d074a000b80740040c141805410318441d01c145580c0406941d50110242410401031400000c00804003078800030515072403d032408030301c40c10503c6601c1c820301d01d0307029108065000703400409902060702e903051140c4030146405455604140d0700d40000800002d403001500d800042c0740b03402481060f0a0010300c0c1e19555080b005410b034942a2441e00d045100c801001840c10000b0900604440c03041211490501074000e1440303005440450400c01d100082c04100c4e070010801c0402d88103d41343c42e0415101e544003e4450348203c28100741302881c0021580c2455040c8040038041d251410030500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62207862 1250 62206612 62206637
    0x103030e01110d050c070b0d06050f0d0b0106030b0a03050f070602070503070503070b180a0305070503010b09010e04030e03010e07090203010918030f1803020406030b06030705040c02101a0301090302070303 90
    0x1214250303112202e02050780080c01194040e405540680111059030086031106a103030b11700c407017041c0c01003a80f8804064690f0020b00c030901d0a4620300102d0081510700b040013851a4840c40c003280c0f070612402c01459640d28040b085521540c0303a40000c0c541140032240f8090a90028985c3c07401c0b07620031302d0018028a60041018980422010704403100140100851424454090841d90150a074000c203005001030420554030703a110f00b0001580204050f00455140900b1b141c00d40c2c00303003040948140840c80060003203406070000180c01a0b0185085c8514100c0000420b0040024841c4040036101d65071001820700c5642d00194180e5130b21300410302108a00c0c03481d500d60500c42500c020b020900c0040919a40b42c40b44d240c0601d002840e081082140d9540d4010504407401500b00303a035107043c190b040000900302040000c0c01040251801c21120f0790059009484190800c075440045489144e541d40d440440903140c01c03207400003002000910b040d8907000c0c1da200340c0c1d0304c01200411070402c4c808 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62209112 1250 62207862 62207867
    0xc04050709080307060b0f180709090b1f1701090902130501081e01180308010302120a150231051e13110705070e1008030f07020d1e0b0103030e01 64
    0x1802101d581034000c0d07044c010607030f40d801d0107006c00c00715030342d04000207988a10180d914082c0b00242c03800d41030b0b5240620b050840d001420090742e41c001a013190f003083c200c0301e00341d00d5803010103021030b941a55508c41c80141c050201c440d0f40e00d6003228514811850f0020510031001e07840302600c1c3d44221040c0089045800904c02500d000b403140550079006401c01c03990a0380c3c0490100482868400001140c44210201a40d03084003000c1c141c0001c0c0006005100714204120101d070704483c9240106408800c543d540d40850241a103200742468011840e401c803900400b501c1e04003500d00500c000116a000d04081818400500c1010312814103000a80c002d126600901c00d032805000e00600640102e20341d014024010121642e92024010050350380801d81c01e01c800700c0900445c155801541c285180c0c400c480104a0b045034245e504100705000000c0041002c41d801c0942c10303514280c0840da6400c001001d0744a03003c0c89001e040103140755008110f901c2c804941640d02c01c0d00d41800407403110004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62210362 1250 62209112 62209127
    0x60f0c0c05030d05100b0c01020301090606030207172a0f011103250909140105120c0901051203040b0301080a050d0f020c0d060b0d060f0f02130306020d020403080304050c040507 78
    0x20341603400c20446040100b0b00c3d0340145502039084161014456a10307402d180d0164803800a4081e140d5010005029010700340c010034000b002c15207025814020f1503110020101c5044060090030080043c16103d104041d1954000b095464100d040048c82e07450506522500d8200f8080385551801c03100510296002055038001d030300c2440c86500e40c80489040000d040c40c9000648240701c45070400042d454860f0091140c000000e00340b602140d4501418020448a15180e9a04680040c0c01d50b00c09d03515910b941c04d045604c1185c600e60b120b00344000507070441c8110781000c0c075443c0700040046280000010091255841401140c55414611074111010380c0b040381c10f4401a0040282c51216107040481c4c40c1c011400b446001800da01c1560024002d400c40081c1111010b444d0340300040400894070601402081c5400d055160030209a042c180705074684c00001c04040d030200d84007110454541c15038010391783c07000f00d140c2d482c101070074450380d241c00c1000103602c150709000c0011500d902c01c0382d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62211612 1250 62210362 62210387
    0x20c01020c0717060403030e0a230c0103060b0906070f080c071703040501090e0613150302030f06130813030b040609210807050918010914010e0408160609020d060f0c 73
    0x44d107110785030351b034049002c0c00c0070310341400c2d50b4424561584041280c0078503810060883e02c0c02d142ea40c1c980f00726040d007041d10b6100660b06042c17412008108004220089503074107402150021b61300c00d07030361918010b284c1b808000a4010003000c280e5000c0504001400000c0d00e00303042104481041812460341d413032045010305400101e6400d002c110140465450b560031840090501e00d400498601040c1200c00e8208121848500c411042007582414041c1c4049140341c1409010507150412004409010000008160400002e030301c1c0c2d0800d40354501503000d1a0f100003503480d0350600341080400790251440c00d503002035540b04041031003000d203101c803a01982251100c000716646c0d60030584807070b00034402d50764120680e070181124498005490501801079420006219112540e5908039440140c0114a07407003452000e02012410078070a40311842c004440f40001c40280f4030f840d00182c081ca000094110780d061500d0030030000650060001401076000c20051407403504e00441ea9000043d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62212862 1250 62211612 62211659
    0xa06050d02040906140c1902030313030c03020a0b07200c0a060e030f100504030206090f03040513020903030c0106061404031a0a09080703050904390e04020c01020c07 73
    0x1990300006003025008800c142c1d0040b5000219803221091201410b60212440070004078001048075610800b40c40703109001c0c2c0184011403c40c0b1f0000850b034400844400003409020f800b03428142054402c00040750b455610a1851070341c0c0c1410980904400807000e04500090310360203a0303802070f81c0d00141010301c0450080c02c100013146064025203004800341152509400381010450503000e0410078580e180900500000300c618180c10300a00305000a41030a0058100802100e8001800415038080d920200c503010051451041280000d10400e03904a815000210728245240340640c440c0e01155090b13212800300008a40d0410441d102d1030000403c442401d00c01c00c50011300ca0720025a1011001c800020110360585603050541c00c507000450000d50009510983c0e800c1134052100385080031300e0900015440b400850450b1802c01c42e015007188a0116036102180c4240d29010442c60080d108569a00054465a01030b5001600c02e410380d11910f880003600399614900101d42002c03a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62214112 1250 62212862 62212879
    0x7140c06060f030f0a03051206040b0105030c0307030f09050a1205090303041701060e270d080604050615270f01090b0a0507081207031d210c12030f0a0605 68
    0x80c04000907040c0140031590144152074481c1d0341d161041004618490294560523191880c918006180490080106029500345003082089981010543c0e40140d400e148068403a0b58108044000700564980310098505040352401401808103007103500b40c6c0600c00401290351890401d4407103104445800c0d07010f07402040700708001c41140769132100708401040040b50b000c0d51003000c03020b030701c4050361807115065102100f820340380d00c41281500841c500e03101400c0f60106240000c1c040c010020802030040e5102c000180c256501c0380012a41c072601151003940b240b201100002599500350b00d800003a5104c031424134028a0702c0040d20448020580d02d01e0702c0b04d030400f000500a50452840034041c001c0c240020070005889902603c80806102d81d10045072514a10084c1528660754118030044c2c181c0307180700034458010a0111540320340001c007954100709080c21030300ca84148012600f090085c24205a60150b01b00e00560181001d083c4180060700e0b040300c080c080f240c0c188203456008002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62215362 1250 62214112 62214121
    0xb0a0e1e0d0302100606030204080f0d14070503070c030b06030c01030501050303071b09090f200d1103070b030903030402120d0210110708070f020310060506030604050606070203100507140c06 84
    0x81207007441024440d2043d1840b0b070381000c2c03900c401d440440c0c0055001ca0340204043c001004100402ca110446080c0140481d00c0e51b504083d20482040c0407001c0119800154070342809410011900c2c010ba00031b044120981c1d4030700b0510b8205e07a050728424841d02860000c501250b10a019803416150010f024618001c0346507615041c0c1c0784c01c25003100703903c0d4040c1000200c07405d00c0e1090300000b0b4081c5000f40d892a000d450800d03007250f08401040c0080c007001d026002c80f51a001c111802c1940d22010003241c0111300c2c00001d14040c4036a1121005000000420540001c04005507005510a5a0013490140003d01085d20b451a01c2c4003040141e102030903080c815100742d000050721841041d072062811440c0c2c0c403440300a0307208000944862800340720714002c50604124020741c117035020b0403c001c101c1c00c0a00060b1103110140c0f0443c440d90321760010450707685d01e840403a60b400ba401011640703031801ca0030110000d0081191043c0c041504112170381250390588044404510404018184a958 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62216612 1250 62215362 62215369
    0x30606080f1b030c030a0305030a0c110a02010e0301060b0d1a0f01020d0503040f0b0a140f060319051002040e07090503061608072f01050c07020d0b04150203010b0a0e1e 74
    0x40b20000c659040c07282401383d06854609011800c0d1107400380d929030b5074070b1919a9494003904d50b100100c004202c420001110f540901082e2446581e43c2460301000c21038084002038054091504041890f14002490294641e1198003180360076990014404065148004211901604070a000c0c05600202041d2810500c0382e40156842441400c0f1032070080480d446100101808a0b030329003c2c2a96041c030020707241000900183c0c413410b4116540001e180c100e002c60745611603041410036080c1a0000d0320108507051010480344d80940a046445039502e52358002c184000307591300c40c00310fa11603d000c103444c01e012916034400c45481e001c150310800600801c8820400040c00c0c14108003500780c10180e0000c1d017008141d00100d00c1e00ca0b0791500381050000c40c0c03c449014243c0c280001e010020840161114144495580d8018010b2103155039542440c5c006c0d4030321001c410342001e10010011450a14440c05414002501c4d50351840305e494000600500809201c16603003944c040405003411440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62217862 1250 62216612 62216653
    0x20a060b06071e060e01050103060b0108090c031f0b130207020a09061409070e04050c0306011403040210030518121305010e13020c0309091005090f010e0705090105090910030606080f 80
    0x10702c2144002038050341e2110507801c491f0203030012034026031a24654102c56900c4000c0ca42c101040304050240c220080f80080ea442d045000048003441045a80c00d600c095103500031441d441c0041c010320201c5240c0c2d2301250080d40200c0c2c0881c410013440101088050700c0c0e219001c2600c4901240041201402d41080000f010040141c2c04000c091440c40c002a01c2c0c0d405498091290300e41115160700300307200003520314030860268402000040c8108005070b507640704004040c40d0203080004440d1540940e001010305400d5001c1ca1503c00c2942d508000401031001b8541443c5242140205540340e100448040401c4607102d50310545910059200d4851540105800c80c039007012039203840703030280102d610800210344a20000c1d0310000d042206007010407c4a074081000102c50189605200c2c04020140b000303060300c1c041001c082541e001e503900510440f1500d2100070f000c56030300c0c070380500440301510075400101c600398101070340002c00300000500c064105882c44007030040c82c0140c0384c1110701d60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62219112 1250 62217862 62217923
    0x50c0a020c0616051006030c0504020a050f0c0703020a0e0a0501090e42090c031203040b0c0409060b0c0d020309011202131707060206070c11060a02070f06020a060b0607 74
    0x65a80e03803c0440001e20130801c592049825031000704c3c00701d146050286143e80d9503400240154010000c840010780d121003141c0b407200507800410f40300c11078400114030b01002c1c0c1d04025000352040b6070201c2c0c0450014076031442145c0c1c0000500c010380c0ca481c0e10005698000c0440d00b1181e100c40d041003040d07802e40000076440f865625255601d44050324502401c003111400241985614a0500c08601014001c070901e0324029001041d103607090300341117a00341c84020405840c0c0070049001c0b035400406001110020500a44107101d460b031030b0000403409600c40142d0380520b10910759444e0303946001000344c1740f600342c0c1611007198580005904102035804a01121040ca80003140807a0a1b071071403c103c9545414a00281405401c0148c0030303240031009003000701400000c1104ca400151b031074113060301c914400d43e221622003c03845411380c503254607a00302460b014841c1d03c1c00714106034001011400240915028060110f003441488403074442d0a0015000000e444130743d4003040d0840304440300c007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62220362 1250 62219112 62219137
    0x30605010c02010f030b060d0603060b0d03090e1b0a08090115081b03010e01020a020304030c090e03030a020a020a02100206060109060c12140c03030f07030b04021309110d06030c0801050c0a020c06 86
    0x891b000c440001c100303500421240c2c40555840d502070040c130002e4416060405000e85180106100c42d40f0040d01184440c420740e03801d00f08420020307408001c2c040040c3c02086641034400c0e162034100201504601045540c04140c0d803070b2460b2040d42100c0c40c608501114030700d5010740040080740d0011400b6001d00c03094203800d0740d210062648142000d1005008203a03040d80036540312403d514201c554110f4a07484002c070141040012400d2a41c040112604a5a85c0134010783d288407011040e0b04002003820040e45c82001e241c1c0c0d02d550260041401880360070241e03110300c51705465042c1075a4641c84450050103403a084003c000328107001d0a120341a442c1e040340040d080200e240d074400c1c40c65000b1201346c403840c08a40c050018440d05802130054030b000444040d41080c0c0c0c003540e030b801560680c0c800c00082d140c444010801102e984011211200c0140d0414440c450316424040700d16503591041d0700c003940c83c0000045070340c014482694076464141d409817800304181810821307540c0001d24020f81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62221612 1250 62220362 62220371
    0xa1e021608040801200a1d040b040e07150507050304150c05060103080d06060e09150406080106120203100b01080c031b04060804031404290706060308030a050601030605010c02010f03 80
    0x2080460014100509003c03001046001610020f001140d0100007a5041c1860501c115074080303400102401e001a10500c0803001c1e0f02c072060000700a091100c0069801505d0311002040580300403034428191528180584c0030034042480813282c0f4807600340702a0481d0000d00050004821130102000418120302d0f00014904850702c0c0d0b907051510a0380101c03854507002401c40419a45401010000c10142c10f0580074040340d03001003524544024a142c60583d902c5010301c00c999941d40c00f07000940101d4000b00070741d036202c1c0001032a110b80d1100691180c0704440780c111142800c0d0283c8494400117075140c03440ca4071151106001a080078150350b02540c145005042c1104000000d80010b243c9903403075410320305240c20080d058009180325041880170400051040040000095083c1c041d04d450a0071045118200f1000754058250010061070400c3c82c004107101541003d54041c0030030344010403550f195a001076041300c00610940e8041582658a03402542c019140c146141d2460b007000318 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62222862 1250 62221612 62221657
    0x1021b240f0f03040303180b18011b2102090a0b031518010510180b0901020a0b040501050402130209030606010c150608100e1204031712010303050702090a1e02 70
    0xc1d03908500810403041c24084108000c0c5540350103884d0940c1c0d40344a000c50010615151b510120740d005080702c200700683c158911644900b54041c0c1446101856203110f108051940149803e0800c004c5a140f0b040d9180341e00c01230003541c802c503071148000802020502c2d03e004008052901b000f0704803098030f06984002c1c80c0c0c6480e070b558003408081d207405044060b0f6040c10704000d0071100e06c84c1d01c8020403102071580e00307142c00e100c80f0f06002d58074062a1035464020707080c0100c1c170342841100e00510f0021081d040c0001c0000540199005a1089802d5281c890104440078120b000318030410354150700c4a0040380c450350241101401242c098094001f074001c91a81c003009903903440e840306915a010b443d0302036001c1480e100d41e41e0030085180240505050031070708442140664040500002850b440b00c25152200b1000c841c00c210300368680d40119a964100904107400900e0207078042c2c6810000581500028803400c241c40c0e410f0302400c6200c417440b0800e00002c4d0044004591015485202507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62224112 1250 62222862 62222887
    0x31c05160501060918020907031802060f03010609081b0d020409050a05060105040c0302131a041e0609091103040b0603010b06071415040c03030513050a0303050901021b24 75
    0x40c144501410001ca0400d1030701d101c030001c5400c42c0400f00342021101308904016a07030840201e40107049442c010a2003120340b1404080002c81c4a8000e61010300090088080b2100c1c40141d0304031242e640303900015503591103006032960842d4444103080007007a00140302c58900078030f500d41c10a002900018417546c41d0380c0c941c2d16180e000c003c2611336900c1080108140e140a0148001c0c48295107030a600b024000302c02d402014085000c0c801d01c81f140113414081503ca020240d40003080407603000381c04580722622135081460310307008000028500c400d001ca4010864040c001d0b04410b6580c182d8915641c94071480400d06002d44580d0b459501c4002c1100e541d941e0102400c03503a4001c242da20360b01c00484d20101d00c1d1508545000300e030b00c0c07280b00c100008a154840720500b100d0f0181480b941d0f40000070706051080100c6d8001c540d0050048401005042d80640900760044080e000c60b45c40d40071002001540440d18501c546d4420008000541c80002e015042d814040d5500000c41c01e080201016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62225362 1250 62224112 62224147
    0x3060a0507050d090602071101031a131b0908070509010e0711010b0402030a020d0e01090201050703110c0a030308061305010f14010e0402030c0304020a090e100e0c030703050d0e030309031c05 84
    0xd60717035150040384040610150300b80c1e518051200b42400c01000e40783c0d030035038000000381000c068400c6c05603010341442c1024035040580c00c4240342c5040a0844004180500300d2130072801080404c0c800c2c0c2c080880c450034541c084138180c1d6070010154560341c1e81d80d10115088100000d610b5a2552034408404031070301c46001450264008140251700c82c0c01c4074090304119840c901c0185a01d81c102201c0d400980d030044101c503040c907050b18040032505401000c0500c0d100c103841d482904421041c4002062540c405c41841c0100401c5621044080078407450800703988013800f684480b10b42c0f2030f500308102c104900c1546119441070402d80c0440d020000010120313001260850359074140042080110302d42200f00303034094030804404100178040c14050b6555102c00180503a01070f6a61030940201c0102005000c115000c01400c41d1420360301c1e45805520394282c0303071090300803488101c0c0c140564500401945c10004024000709807208020881001a40c04c0d24459014400100a60702a034640d510700e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62226612 1250 62225362 62225381
    0xe090c24120711010b0f0a03030c080c06040c03021002030903070b0915030a1a060f03010501031a12011505010219061d0703030507030807080f04060504020301020412030c020306010f0503060a0507050d 88
    0x60f541100000502e60501303552901d0300591241206c00d0103901c2c01c0c2e03140c800410641303070945080580e4402e03a1401c0c0342c05220b4440c0c410401e01c10f400420040114400f0b0310f80a0328401c3d81d10012001c0d241c803061b42c1d40d000300b01020340c0c15085180d05000003c45035000c0c0002a500600071420050424051103090703000740c2c0e400c0d000f1070b00c0321a414503401107140c3d03c80080c2c10039502c41c0c0c500702603600540c074a0300040c00740c1030405032140440035101142c1c80000c4001e41c00149152910392403c4007a500a0600c040078114001d05c0368400141c1e50b0002c100344205501c180340c0240da9040658a4100a29112203845450303c158000303030503e6507040080d400a54402d8545c3ca59580312407c02814640d00145081c0c1000780510410071500000d5a03030b0780c1c001da401800411300352101d100090190080ea0444903031480c0008050050540c040c40d2401802e0080c2c058400340e9032038855880302d6401d0360017941d40651050011901618040d44070343d0b0300221a203051402c00c2011070851301681c03030400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62227862 1250 62226612 62226617
    0x3090d111c0e0a0b0301060215040302010908030f07080a020f0d2a080405070f0b090d0201091a1b1b06030703140a0e010506030601080d0311040b0301030c0e090c241207 74
    0x10b0b9002882d080051024020301540700340241950714002d0300950b501403c0100c9265484203001240802d4000d42044051070350125006840746050580001e0002086420308000b40061020521240c458422665400308111030245416402100100036005000006441003000804410256240010b0ba0200503060703648800d2814907040092600039641c2003491b07402d25040e07082041031107030703021142c01c10070036914034001075628001aa1140401d40c00400e03091465a411080110761900a1a10b46400c0c2194411800c04801e010307654a46180900d103c1080c1900010652a2a101031544060a072602094403904044d0091324410290b61001d0500d80320240200e1401c0d00380500ca0344154150020b14240d858102d2542d616160000780c54141940c5d801c0c420103040501d82142c015080840c040d80c0d80e5650f030300d02030418000b1403040003410860038000c12407146000c50421400e903801800e500400d44580da00d4408d0f8048884052081102080007904800303018034001c2c41303040140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62229112 1250 62227862 62227877
    0xd06240c0327030c080c10031404030e2d0a120203060a05060307090e030d050a0c0905090709090504080c0f03040609030b060d060f0b03010506010507050304030b0714070804080c0603090d111c 84
    0x8000380300017050608001c0e8223140c14600000d6045180070401c0b80c2c0607405140c000c2030031080c1c1010882c122519482e01d40e02810701c0c0100c00705403c44104000b69170405031100b072215607490304d0441151012a800a5050708802e01254004002c0e4200c3c0d90000d01c003c003610b0b040d9544220800c2251700e001d00400c140c4d080406ca031a1403001c2c52040c02c0d840010304109100403058200c00402c5a01d00c1d00886200794a80b0300401c0d04503100c0d406810182100300c004218504042c1010751a5402c4030f0b00304141c0d03208020a214445070301005660444420b0388035944543e0a5565480d4108c100034401d582180940e00600c0109007640540205040b40d10b80008549140500380350940e580203040c641408000c02484002a1002040b1070441ea0010004202072300d645034210388400f02c1d40c0e8a5225907001040c00e4080c00700c22001042119640c07001c03a0b800041400a00400b800119071040b0f145d0040300a01b02e2071390040401d200d103c040c160586810303a444070b501d541e0032096481c0c01800901c03207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62230218 1106 62229112 62229133
    0x2401081005030a1a09010b0102120a021906050609060105090d030e1804030206180601030c050402070c0306110a030609050f0403140d06240c0327030c08 67
    0x201650440d044600304215524502d0040e092001303c444041000c9120500c1114071042042c1c018003081501005803182c150031003980c0e04103500505246461402e007038401e04c14064800c40000500341081d030240b080555004200a041c4081044951520f5899070103014240d81e15181c0051151440340100d80780e545004040b4800040040c244000c06801003007091240b590541c2c14a824400009000d81c1e850b03080c4005015031a20080c1030090b420540c00800b4000d00540080440076500d907987c50445441440110440c900807c00b940b0140d4107008660091140e4001403009017070102d6400311325480500020140301c0c0006000c0842c1100e50141c449041c620b42c01000b0300303640e800c0c0024950003030b80c0a440c0c2d100040d805030f54909000b20500f403401501030f9143c170904003c041148180791021030115101e0450701ea4000000717280000e004010380310120251017032006 = true := by decide +kernel

theorem cover : BRFrame.Cov 62050362 62230218 := by
  have h0 := BRFrame.cov_init 62050362
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62050362 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62050362 ≤ n) (h2 : n < 62230218) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
