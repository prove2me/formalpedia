-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:16:43.027024+00:00
-- url     : https://prove2.me/submissions/f6a7bb9d-272e-4189-82f5-015d77a6c2bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269604316 ≤ n < 269784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269605566 1250 269604316 269604337
    0x30509090105120a170909190506010801050d11030708010516090503010e030a1202090d0b1603051501050c100c0e12010203330d0b07110c1305060a030c03030302 71
    0x240da660348041008840c20490641c1c95a0800c480d000c000aa6071200080c2d070010411000d810a4500b000140c8540303405c0300c100700c184d940308140045d98485441020380c0311809003880200c550401c404520700a0381c648000381000a0480b40b26429030301084070300010301a220007800245071801074402060712501028001c20207101012481d0301e410f024184c0c0021504000b1410609a0700007101c00600546803040c0403942000441000c2d11a025451555401240e05040300d0074840b0b10f018555240d038403400c00701494642070001c03401402c803840007100b5003480c00d40d8450060343d0540f170070400c400301100025480c007042541e880703401c06c186403400c103400c4404010029910008a0a03480101d5100140c050044401400c20504003041f42004144181c0740030400242000708042006004081e120881c0c02000c110300984c0c0f00c10800c030542c01160203030030b48000c4480807688010008406646264030361000400036181d9542140c0156040112454182e41d20f00713024000b07520406059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269606816 1250 269605566 269605579
    0x8030a0c080d0606090f090e03030609060111030d0603021c0201020706050307020102040e090c031e031c06090c032f18030a0206071b06090308120a0f0f0204080c09040b0721050103030509 82
    0xe847c06c018030910404200d020041e40c40d540d80e4000b00320205800078001d43c1408404c02403004642d0301080a1719400d410b0100000e803260440c0104405e05455042d4114001c001034803030001070760301242803002c03a0782a081c210b4485d00c9a950690180c01a90405003c0c1c800d0101040540e5600140341e150900080e002d03103280100d6526401aa80c9061aa080690344100108090050b103407207040c98400003440c001070019141c1c84481c0a4078000245840003e49500080c20100c50801102c42c0d2a10081c40c1880000744124204602c2c0c007800c01001001d1035540c01030b60f810344041c4a50022030781e004045030b903100c500d494031075041c40c12002c40d25a0030411140c0800ea0500481e10001a41d80154180f400c003001400346c55079a4a0080c031890703001e40c42c4d008800c0c000e803050041e80c5008143d85030150b11241440c1450b80381c0344010a00f11300c520002d00900011403941d481c410b800403824640580b02c0010725481b00c200064007014288143c3c40d20380000181944880a00428902151030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269608066 1250 269606816 269606819
    0x111605100f020a080f070c0b2406091003050907080f0610060c020a03060e010b06130e060603040215070311120405031e030d0b0f0a08010606021608030a0c080d0606090f 74
    0x511080380564504000801e01311404038003403000d61502d1651040f02c07403074a03440c1641c4030b0b9180c440c2d840c0c0607240c0d81c0301e6202000d0a10340941513416001403c1e1402d50300d003400c1c001c1800004400b80030300e07804103041c95070380e401148909000b400120068240141100c41c144104003010760b60b00790444201c3c2c01800c8004c00412818490410014000d40050014082070b080d0b480d64401041012207221496684044800082d140c0c071029201c82e4006c580555042032403c00a40c01d54940141613500ca8030b810001c0000684d0780d91001006c411242c200c6544400f55441d040d211001c48010382c001500c10030000f42c1c1490140d000410650324143c00703540380c2540000c000f2144031000042803040790002e1040000d044074a070300100e68620014150884001814040307885050f858103c10100c5c2d4503280103202080d0100309000341d20302103180c014406458510705940324080c890408040044111094080c00307031a00075501d50f141c4524040003000d03918003010b402c81c040341c4503070028144134140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269609316 1250 269608066 269608091
    0x2032508060f01090c02011b0504060906020105090a0303110d0f050103140a0b061e09011d1305031c02041d070e040e060a05060a0e041a060a060c0611160510 69
    0x41950240000851029043c1d090860010203080f0640640d070440d0761f1081d02c00c030030100d403207130380c404900894030740300e9855041002c0101280682c3d0800000e6a040034140100d071900090b501c8402a0985400200300104080f020000c1c428178509101c49412f2131607440d808245a031003103040703922640b61303002c0d02c4410480b4551121821007001c0d06400507074000641a0400364464081501c100c403419083e0030100f40050f14521007a0002c86810281030300c070401050150b400e0b43d4011a940191b681d4000140d40c4485c7c1c1d9100c0c20311f4000e03960500d00c0d9100700020361a01907070007914040e04402d5445031604024580040115200c1e40010300b498000f4199061038441c45610140c4840980510741e5214041d20107014040d1403117400c8020050000b1b02c20701c0c1b0816003070140d03100310b90190040ea0300030a40d018004001c2c04551003090f17000820000247c0040785092079035130161000c58540c1c464082e03201e10b130050640010600101c2c10061040010110360804070160388030003040136421205 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269610566 1250 269609316 269609323
    0x61501031803120f020d060b07020934050d0509011b08100905090304030f2009010e041e06020c0309040f051e090f030d05070f02060910021602032508 66
    0x250098045a10403e0f00291041c441d04405013600b26003001500d0700e910780240c0340442e00e213503121140c0c0c110045150401c5241040d20240c010030403195074882522129100c2442d0300e03404501d240c00d0a080000491054028020b07688a2040d001c1c04004514080410901070309151801c00f5104242100009000f401010101d0084415003402c00400c0d084c00303040d40003840f000c2d00581c03a0744400c0c440003001401503e00307901c5a03407260003071101000c294130308402c16074550380d00944140398080040c81200031421180740e010b038224030380d50080038200c4106801101c81d08070140946000041520081800000520043c042990200309807e0b0504810b42114015207500d400100c800480c18001ca043c4c0c500c4c980c0020058055590a1a10729149455923000c1200c03d600d16459000300940260000016900410b641c00901003516143d80701c00c0d290f094051100801c4e607400f05118400c0c202d0092a2110950302030300b10f0f401d40203400d0b0864440c403c01c000c804113201c0c95050218040c1800b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269611816 1250 269610566 269610611
    0xc050406120c080115090b1303020307091e05280501060207050102070f0308300109060503060603101802040203010806220c050d080f0703090e061c2306150103 70
    0x183d60791062a424140c0140201010625110402500060100310f8030940c800400c0e14400606c171504009241d031040c181440341c03951103600e400b80391090f5005c070b03070711010211340c101c107050000000c10f81e2354020641c402050310490f51701440384c101b85070032000225502480c1aa039041d0201c0d0112540c4900499580c10305000e0b201c40b1480500003000054048030241180c42c04101c081d0005203042c003a50300d0106a1142074040081030b040042109862910885010384800e81c041d081c5480d01801080d0744149240b58460000d6440c0c41c22078200e130b00c140301404200d038000c4c000c0d952960343d1b242c0166640e45c10342ea040445820f4002031440e0b105140ca20303c010580c4070003203030280d914050402200213807015094a031048100022620141c00e0001002458442e8a4402c89139051200445503034500410203800b900840c00c0040c40f000610200201003075001180040044180b81001503880d050704005c0030078445c2c5418010300c0d0300c5c0c03403103209505802a81d0801c00603603120920350303900c11031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269613066 1250 269611816 269611841
    0xa0f0617300a0203040f060c03050930030403060e0a020102120c010906020c250b1605160f08060708160804050a02100309020f04020301050f0d05010b040c05040612 72
    0x2004030500c9000001c001240303105201c60703040000212111080312640e0084000c0c0005030070000707003070062113010315001e0003801c1d0501d0500720002c0980d801928900c1203001003442529024800c4540007401410700f0300103540024a8280c0c01031041200f51b5a81090004440280c00c001e03402008180014819206030340503801400311030500961540c50b61311003002c6004c15500d6142c08001b06900d40001c10149440c0c03c001d115410000000c06991140111810041d040d403500c10000c8000d401d041d00daa1103034140a40010b4060303498020715100008114a40000f0040000164200d22141c050304860100701070398810303519244120f03100c43c0216415040414803008803810540b24110302544584540c0495008640300d40001d8150341c422a12600003c1c0c5038003a59045041c01c644844002400382c50644c107550401d0700041d0a4540006580e02030f2071080c0202041c050b09410201d40c1050281040004429406000304643d010f03000301400b14202c2d02c0a0640004e03503200700c41c0302c0c10783d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269614316 1250 269613066 269613073
    0x512090906041b1b0210080a0f050408040902090303040909060207021002010b062a0109050106140a14010c080706020a1d0105072316090506010917030702011211030a0f0617 76
    0x40c8000c003602c0d004c0c80c04000e00015040c03c202500180c4405003100319080c02a01c803800649040040301d020303a03d444103003013040d030305100a000c00100b1000503601542c81140002da125107940d0046403650081d60300000301c1904104c1c01c0c07414043c1c541d000b0a4820300a40d00051000741c4031005a0030b8620481621350803140411512075842c103030400c00601da0050320014598558840301445c01d6660900054072240d41d189410015403c3c403d20701280340405803942140306191412040703030128003084c0f0382d05002880001d502088502c00440d0856980848119103031500380da4000d1024503a82d400d1302c00c0c9114007800401660180341500e81c500d0b4880e1aa800300b03420400d0900ea8000701203601c0e20b41d44a030103100c03500301100040c020090002000f00140f14600b00000400f1b10b503c66003e0001c5050030040079000c40d20204c1102d40d074540a08114802c4802c01c00c0d048001d084d43d0103243c441c40d1010050100380c40ca10b4200048520740c1c44814000f440e15003038806000c2da90103459260960 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269615566 1250 269614316 269614361
    0x90312042d110d0c030203010e070608011d0103080a020c060d060303031d0d030905032a0606090103171c02270328020415030f0b010b0301050901051309051209090604 73
    0x80c240c100c0a030751034841c913400d1000d10742c2c90740402d00b50b424036044500d05820000060010550010f541401045110764102e4820340c4583c510005075810302010301080000550103100d00e00030031a091030004080d014940d00e580e0503003404020680c6002c221b0019040c000c48001071070001d10050420350f030000103445c000405020035001060101001c542501050041205800030040f0b09017030000c3c80080a04240440c0d055039003080001401d00740b00b80300c180014008103641407002c50038080104c1c0210303910b003001400382a004a610700c1281c8064000604107005006d0346210a0740a074080000b1141c04072000c0c00c0580301e610301c00c0c075282805581420400c01040001c100fa15550000e000061640c21000c09843c900034150803c3c0d842e107050b024190304100e40c03104a28010f000140c003c5086506081c0041e00004048c0b042c0b911030349101041c071400740ca0030b07030154145c69840022a52360080701e81c242981608229405807185035060300290040c10640205020b0b141019201204131 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269616816 1250 269615566 269615569
    0x310050d05210d140c040e1003050d0f0f020106030206160c0b1b0616020a030e1207090f1103090601270e0610060e010c0605090312042d11 61
    0x21020908107440c14032403103040d0903002e00c10880c0c85070081d411403581641c80038664502e0040d161641601c02000c0503141c20444100000e01c1541d00340e40e07884900e0880ca80700c45402e00304045140d0005802d034000c0207298110143c111880070046201a00c45c0b9010036000b140c04d908850302da10019411030001c0001c40d24400c0780820503070f101c62040300d081c031006c0d4a42075440801d42200791030703c1420901c0992030302002020420543c0c014084410854004071900e802502c540c101c1d1401002c1c41101ca00c0d100701652000030200e142d55030803044550042d03507000c810000d0b000207084e49052518051030800f812442c842120f10660b01c00004200c0c607403a1208902c04c04620b0703540050140c60301083c0100410017801404000e040403001000c0508065200f01d41140a5900c007000344880000d240701c10381d13004140080d0381a04800f0000780c0d95030302c680d01825032046e2903040d142c016450041004000740c183c80100f44041c210001d01c1c04920714400d00429002c95080500030300f071043c1d10020b55 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269618066 1250 269616816 269616829
    0x91e03030503071b0c050108010e040c0501031d0a0c170a1e0809090c032202010804032f0304170c0d0809011806080603010506091b030901180b100605031005 69
    0xf4910746401a03c55484540b484440b00140380100c9114100c54810000740da400101d02e409052a40e14402c014180380d62000c10000d014802c0e141855110440d0100c2c06610aa610010f9001401a242e003034110b07140852120007240940c580917110007400c81c05400780000c848100c0d40c1d002000700c035048065644100454101d9004071006003040000706000d8540810003402040030030002512410540081e1308403002d8404190102862101a1300141c1c1c0d0216089400ca9054108940324003182e12114405032044450140350500200000742d05a00000041c0100c603041e448098000c1f100f4441d1603100e610f4202805d511030038039000c08010440300070040c40740202c141092000341d140c2907142e011808a923171001012031902410030038682028007030654010780884062100346010f42003c4c01c174042c0c440d83e180702c0c1c0e200400008e00d000c40941c088804140c509000910240c600d1801c00000d2000300e83c1451b0307401d0380440029205001e0016680203074100890540d0590501092250 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269619316 1250 269618066 269618071
    0x50621010e061e1201020a08090105060607020d030302070c1511060603011404080d140a0b040e2e060e012c0c0a05070320100606180e0601020a050607020d091e03030503 74
    0x9101e0380413510700005030000d01c01002080241e44444400d8034220521600311200181102d01941080100d5001a40e5200115400b5a8107050040e1103030001e0500c04945207003504075242507a040d074201c102540e044100c00304403206420481301d140c4c1d5044103050030b13650b0800b40070b03920329041004540040c50344000781c581180390303000000b9440e032000c40b83c007080442941c201e58500d5031140c1c248014281401040d04a88013107004110103001107455010441c2d4800710203400ea800c1d103000003000b298a4020341c1c0117018004851110396142d9140c0c1d000e1021100c8030280c0c2b480c0758460b01e020a442005881d1241e1404c00761207007011403000c4295081d5100d51b00842c1042020041420091503c0360030040d18032000006201c0c52941808040031100da54000c0703001e005442c8620b80e150b035000c0d8484810354181002150180d201d01005078644040c6401c0103142c1d020b0070082100c1194001800d0315803c1155851400140e540c144050364003c2c0c604d40c80000d20150201400424040e0b001581c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269620566 1250 269619316 269619319
    0x7060903120509011103280302070b06100908060a02280903081c0c0f0908010b0f1207210c060e0616021908030315032a010504050621010e061e 63
    0x5c450820303080c81e541998071030321014080b9903981d50107400c44910140d101c50301c103100d0f040451505c07946807070710303400c016008041078428101c61703880503801840760703686c000245000b208860076400c3c090560400f80d0031420613440301190031141c1c2040c005140000000500e1591106481c4604641312040303217600200305010f8940c0075520103400810584101030300c3e8186a5120215408000802854015617901403802681000c2d042d42c91507944401e09004601c04803103960303104400c2e1340c5a0782042281d520140c0c02a0011908065030740c08108520314880c8201c22030b048a030340f9440152410040c5a5441d60030020038010308654158403481c481785a03000070102541601e01000310039104072103411655041e0404000d1203144d081c0d911103407144030802c078058030700348071961242c805e8008462071484c00d1001001c21007500e43d01400031a00546000b600460762030b2915241000a00d40d0741c4400c40c0030000074400003800400e6460024060040245003480310303034902d85183c1100100000c45e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269621816 1250 269620566 269620577
    0x10e10050d0902060304060b091f120f05030f071203090b180708070902180d0209041709040510170109020906131404050d02060106081003030f03020705010c0306080706090312050901 80
    0x1c9003da51403c005c0c500c6544920b0b004241c203000e20003030003d582c401815841c146038207001020707110040e6210690944503101012403040001d424410003090343c45102070206d001c00038903a041101860018a2564002e41112521142012044003160000000646604099004035180c4d9080070081c0c00d03400120022280c00c0703515120080e0034403100d640442c81c1944c2c0001c00b06e05801d50284e000e10344100c201c8015042c0b80258000c03811001000b0401040400b90405c003580004800b8165014414082d1042207249000000c03114040c1e640d000d00c030401501c02603031410428050040030044d982c00b4292a889403202428406c03410344030118054410303121810f40410421011000344590b0155005181c00c080340c050107424045c040c5c01c48010058048100302d041c4001c208020202c86d450303d404070301e901d021803003100240111103004190354200907900c44601d034190450010b032018030064035a05135941d502540c01c0707011440004d151444200010082c07a01a030f0240403840c0060400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269623066 1250 269621816 269621831
    0xd0f05071a102306160507080d020a0317062d03010f0f0c050a021507090e0a050702010b0f130b030703020a0b0d0b0d111002031303030e0f010e10050d 66
    0x35816003881c1101d158089000c0c1400c01c03c200360301041910040340448410000d00010000414001d224100640d0407440b41001c15400f00803081100c08002c0c281d0310b080e03c4441080308070003511501800d40c25000100142e07108000d60302c1c0d250b481801414005d02ca804840c3d080304c0308030b40d0407041c05440001046440341e200641d0310b080c003450000e2004240c3c0094005403c111500858030140c8400c0100041070012034075141c1c00080211101c641002c00402035a00c3d1384049403a03800d0b5412a0304000901d00a000b010b51860308141e028182e103400912165401e034040c82490030003017a805a014600203104441e6078010303806410300740c80203000d40d41125140d4004c52542d842c030f07500030386080300006102e0b00300310480d2149201807041122080580150307921070b0700640c1102058144a00041c098080c1003031b0080080780d40400701940310784250759903070401824040c82d04100d140103601c2c5001c0c00800b58460b80e112010440000d0203901c074606518001c4810b0380225501e803c40550fa60380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269624316 1250 269623066 269623103
    0x190c1208091b150f19050301030506010e040f020a03140708192003010203070224010b0409020901170c040f0f050a0e090304030f4202070302010f0f06030c06020d0f0507 74
    0x108440d110b00c60f400d6030b0743c0c0145d025001070b0441403004941005811300051000400100750355045984140c110b061980b10b50070301c00c0ca04403001c00c00a52001c02d100002003001aa042218082c800a070151984941c0d9180010f480d070f0945000041801002c1c0455400210804941200c80d1300c0e420141d244441e12801090881c2c2c0b046d0f41c940003590052024911682e0400b4942d081c0b4110443c0703000d9a9458000754210b01c1c003480c000d22030072580214030f196843c3d2080306101d001214441e0b80c551a0304003000c40d0500340d80700d8003a07100011494940440c012521565100c101d41c005402c003200305192600001e8800702c007078440152404108000800709004d02d860145450142e0501c1c146080c3e884010404040090300400c1c0f50200b100c41071009180d10094540b9448e079903580540d07654003a280c128010003c0c1c5460012442c03030080c0507400d00d281a4040400d481c0b00f045100d070995181d440c2a40c0c0c0314081c0141800240c2c207004458070b0320b44254040c0108034803a6885000300c200a00317 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269625566 1250 269624316 269624359
    0x2100f0201021e0301051f020a120203120f090c060f0a08130510050f07030c020a020118170304030b06030312070c020612072d020a1205190c1208091b 66
    0x70400048424013100620003494041076030082d0982010540c0414010f0041c007940b00c01c2101005030844140e442940700c054000d2044403100d0354000340e62038540c603203501c0c01240c202064030314031805c1c880c00c000c01c5403d040c22401c481900c55030445050401d425048d00320b90000c40200200c0b91081e80725400030024004101421000891803c04a09864013112039102c0040042261003050f01707041029070746940105001c80348135020300e8205085200001901041d841c031303330700000d201c54961640e003401480204c060300980f0300c40c403554419078940e00704160b524010342050020210011000c500707800c0c0038058203180c80744060a400e00707080441c183c0f00100041101c9000c00304d8981601000d10074165000c002c8600c044000070314100f0b80c0c50b00000d40d28089100010280d883c100c4070700b40c840d4000d02c25544007c40888041d8407840c0507080080c500900b0302e40031245044940320020031680a400620300c180030b484000e018500e012081403024500c038010807500982c070b0040825000301340c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269626816 1250 269625566 269625607
    0x30a1b0219120201030c17070309140d020703060f050403050d05040c17011a0303191103040f0305100b090105180406091506080609010510050108220609031b02100f020102 75
    0x8445816081043d00000d000d50721000e140e241003040c040710305011000d21602c1c0d160061090314000802000b030b454081000c2c50b08035480741032403094169200348164001082e2050343d21544081c400503910136808001d580040c0c4004000c80d0741809800c7c01400c00c1da000d168424040e40080e4030040d9240792944030f018800ba00d56480741d4480d4400504a0501412070420344000c0c2c00a61410780a105e402c403e90520100100400a40e90002a01d6520400684020b01004000182d0f41c1d9602d251455560f298941d102028034100702990700c0d0352821641550484e0406490001500701000c0d2819007844010002c90f44030340e0720321702000410389041d165554040101d100086c000e01300010303a07107407040003800d4030320b0f581c1040d0070455a09101045501241d9003030070300c3d2500b9240c0d1130312100d400e1840b4000e0030740c1c458814041c000340101500b10500c024080d03200c1140d4220420300700d1980103080c00d4065003200c2d00288000c00e6520440017019811160b01c0018101405801c181040b105c06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269628066 1250 269626816 269626829
    0x170312040606081e0d03021e030c031608010302010c110117010b091c08070f030915020c01030b01020f0615040222050111070608010b1c05070c030908030a1b0219 71
    0x101c2d081030009280c104910140003154164505110b80103040c030070345ea0042c1d41c4842d41015008204503a8050b13943d181d21480801042030152249400d180b8032020707800442c0c05401c136004040f60824100c0c0a2504c10381600d8041e5105085251241c0700d00b858040d0841e0610f04000d05040e141440080301e0305458040d100360b1000c240e0f0758580310208080c0151515040003a54100e8000c100014440b6080318281179002040c01c0b007200182c00d095840d0704c1968406c5065204c0b8000c2e1010041e80800c0c181c030005400d8808100780c0484100499603110340d04480252640004003054080fa4001d450801c0e80701d000b40090700d4000140100b582d05007441d00682040541050700780815078100301464a42d140c030200402c000b501e0000c0003000941d0603c1041c0312903100080c46080825440030700010340210101c14081f901308110010503600680c1003ea0001c0c881d100081030921022086503c070101b1a620305030740312000402c2e4180c1c1c070b902c0b29089901411420200480040340424a0300034040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269629316 1250 269628066 269628071
    0x1c0f140d05041e0f050f2406041103070203030106030c080f0f09100603060203060306011e0608090c06070f050d0513051915080f0604020909150a030204110703020f030a08011703120406 81
    0x2405d01d409403a10445003060300701d030f400000d10350b00d5002c1415490012415240404180343d06c610000c140241300801100000810000411940c540c00000460491344155410046c410a03002d003142c5400d810f54080ba12554500081a40500107028442e040444003043d00c003500c0700c0d0701c2c58104481c420f070b20440340079030044200513843c64284070090050142c0307003003106100c50031700645c0d001240c1c038007520b01032081240200c1d025600030443c01c044400040c2541d42d031600181001c06c680e0391170800c111880c0c811341c210034140d940b1440503110080c850260f200c854604000c00c0090b4900c0031910004102c901d940b00180c41000c0608031107001c0c195031605045030030700040d00700d8030500061140707002d036004001040d081e0300c988000541c042e03044410300c01520b4484c00041e00b819203603480a940182011086840302d062000200300380e6209808842e4201c02c0e0009091302c03400344103000d101003500c4000403c14241000c81d0a400d100c21481920b1070501c0340c8007003c030180c90960301620443d0303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269630566 1250 269629316 269629343
    0x50a11030c2103040812040303091712060103090206040909030e090f07020f0d09090506131103010810090c0e13080c1f0203092107051c0f140d05041e 66
    0x200d0310400e024214601061145146811703100c410291044202c0e0300081c88016001a0078184242d001e1070810343e00c00b02002c0640c80040d10415581c1110f042c5011011000000c184158080c1c8668500d05602521150030246401d044a0040118940960030710403100302c1c2c3c051654840c49098842c014107844901c0e64244038a0007442c040524100c100613a02201c60040c480ea08964100700302d407425440420955640008282081d100d0b00482840c14188031000750200610b08c00303141610301d00d10841d0fa40c00202c000700d0084e0341c0111800740146410380390030b100300310171548160760100e491511001ca650083d561203259038840b0008043e150481050a09040360403e151844414402c00c00c0d402d5050420f0340ca52108406041040003c5085002c1c85011100d002521040c070340207c1070320b40f036810310512a90120b001d07669041c0000d49814040c0c00c05402240c00109005500041904043c41c0c0d14032640240006803054410300746020f07006d07000010710024255003c1c442d0f4084018070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269631816 1250 269630566 269630593
    0x1170103260705061501050a08010b161a04050607030603210201150f0f05060414040506030c0415180c02030f09030705100c0201020609070602030d092a080706080412050a11030c 78
    0x5505605d0300c030341000810040c0e02032403540b104801e4152400b110000307564980c83e00740d90018960a91004020614948001c0007151900e00d40500c250700a10507580c00340d5905404038100c4410703010003008455241c10409180780061541030351240e260000007140d02c500c84a801e1015420344c400c800304e2041000501c944900007011900a00c07064030802e040070305110080031403401c0031407514026607980002480720780d010422040b01c2e00d0050410061201c0c03403821100e0030416800348454440020704100000005482280440e140e654082c2d400d00c1e80c1040100700c1584820141a450b01c254200482d2983d25030407056444207007500d03154040c5681e40b0019080143c01411085182c1040104000c1c25802004591680103055400540c40c0c0b054038010169803e03101c21860140224407031010240300321400034045d07402481c222a890359031900212001001142c1c010205c800c0c141c100700300680114003a00852416041032402c854105140721b02d960403151250215034050f80c51078401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269633066 1250 269631816 269631841
    0x5010c0809123a06050108040b041223090a05060a1b061103130b0609010303140a02011515120203010f090e0c1f0e03060c3004200117010326070506 65
    0x1030101f82084c40a92826889200c5808801031001d04034803044407110043d184502c0c0700200f0600d40d088079080c40e02c2c50a01010050300310708140d0f030164001d0080803900345026005e55040c0035450f61510305803402440300d1842c000b0005005c80e04180c8850031403038070b8072044000d503204600034071000800814a05144c40c0110b0007410309400b402c0002c0051000c0f0307034004082d14400d03581c206840d42e541c004603003c03401801001040342c0c50056002000c00c040e0808560b01494084a60340d642100400100c01d8049100a200300e0481e525072000030003242d421600100341320840541680e4a0038207410200b111001d00d080380781c1d900c0c08584401c0c11041d40002c0e50b5000084103030028109482c10107900340b1144560184400c100741c0c9403182201c80262082c0c50403140010000d00c1c0602e09091038a400c0000c5001150312081c03c1038040300c040c0c1d51044501890003c41003444403140e900c1c580b2944646031000f81d20300c0d03400c000104181441e0352200c0c01084103a2262004102510340504461503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269634316 1250 269633066 269633069
    0x90307111302070f110f030601090507020a060501030f12020721020114070b071404050616020301021b1027061a03190b01050103050402090f100f030302010905010c0809123a06 77
    0x114005468011480d0303100000d2842c1500d41301240050705440d8040c2c0dd92412445039001009141440004810808030705540b0380454072030420080301c40b926030400e0341c8442c4a800f40d2000084030480f4480d54041803004002c60900604106c115200c0100c410b9003103510000007610130b03022500502034840e07804014800c0015000200d18140b0b402c1c50000307070032480344e000c082650b50300c44508002550f0303081d0704884643c0d480d040032101d8441c88030503e0f521044908191003a00b446c0450112110121905072041c1c090005503c05201c400d69443d01c00406043c01d940b40c1c9054000031903003076900c0402804031003042da2180814154a40c2ca0801d200202c140c200d00d04144c04c00c01400010b803031700c07440d960700550803810b800d0700351781c4441d0950107401296000b0a103a12501c3c60010516030103505c81002240103c009001c54040e80300291a0b925003603482001c5540001c49000c9031b50720850141a100385020900a41c480c40016161031403c00d040040007007046a00d109000070059108580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269635566 1250 269634316 269634319
    0x6061002010209010c080d0609060f1e030c06050a0c0b07110c0a0e04081b010c08150f06090103151206020a09090b06180f090405010c03060806090307111302070f11 72
    0x10300c1d05880c400001d00e00174800900a002403000300d4041c800504c59003001d0080e01316020100302c0255149841694506144603100307912040500704458801032907600010703680c11100c8080303e94034004040340c0641c40001464100204c0741c5c031440004020202d8507001d0400c607030f20405894602c1c0c402c3c506105099404920800d485a82003100b00c0709125204d9010390480070707143d01c0e00fa0510800344000707084002302c541c40d464400c25511594004010f42d015040c44034102000c100d0b01001c0c05001c00c490860300f40d00c00703820312024010790312940040c1b699407210300b24580c2840e981c20000d6201c0c40104401c8541c0d50b0042007182c00d00340d20243c548000c0145417030601603a030f8454086a41c07072080000c22000c200103400f40310310b076458840c0d8034a99544054a288001c3c41c0605005009011507403003080000d0034080002809000010543c0c098500c807800341d407a100d501d64800c3d079140e030900680d0b5044640900b0610001d04548050445a4050700c80c50b050a001d524200c416003400b40c0900c0e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269636816 1250 269635566 269635571
    0x1030203011a030402011403011206060e130605070c0b040f0210051312020105090315100f030203060a090201030902130c030b04020f071410020708090f0d0f0308040309090c020606100201 82
    0x100401603104003a8895896000240d5591362510300040742d140d1b110f20814980180700100004501444e00c0300c400c0d2032801034204012250311100382e4525001c0079180b0300008004252080007180250b40000e41140c0c640c24003075002e084035914550702110440d8161840c8586851100a500385000c20042c1119140791240c17900c0c000d6200b004400c0490b0040009180000007400e0459002b01d0450380050001022540d075280c00d001d0301c00392844100e0f507a50701480c2d0140c000851400002800c800c1e03c1d4014050301c1241d854007a440020119020260304060b110254080584c40300c01c20712a490840840126442c01030200260680d0f003902586402984100070041c1d1001c503443c11341d20001d5001689000802072119150310f420001d8540030102d500c0003c0e440304114241d4020a074000e02603490708415030040c1d04102e1040004030001d0300f00c0280720303801b1001a00c240302e115032040c441e0410034401c5880380340707480444500310313a1040580c0c0010184000c504d440855400c415000b403009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269638066 1250 269636816 269636819
    0x302030a1a0d12120e03031b0405100c0c09110c0f060717092a01140307081b0403120908061506041e03060221220201080601020a0c0f080c0103020301 66
    0x401d01d070582030000602205180800c69038403911448020640c1e5544003001d010104011784c505031030b548103890b0105012600410fa2030342c0b07420041564200c3d40001d0540f0b5050945880036580380200e51802c0750001801c103004900c45081c2c1c400c07005429000316100741c0b580c035612510392030300c26008031105156001904000d00305600400405c4081032a410361047c9480c3ca000507845d00481d01707000103a50260003881054001c0001c408640001c0903070301c1103406154641c81c501d4610090350503c00080401000030001030356500041c400c90f403c915284d00c1e150760398841c1c82083c3c4802070302d0000620022010071468400304120780c0c00809001041d130710502e6410015241d440b50f031003109a24904c403592102a107000464070001142c00810035542c880c00c0d00c91140d4103003c80c0400e445008403043c0420f0312041d110001200c0f1400881004400d0840d5400544003004020f1005045120b0040d1950002c0c00c1c0f003881034000d00e0311801c2c42040d0fa0410075050f0400c003031440c4a60406105200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269639316 1250 269638066 269638069
    0x1c0c050912030c19080705010c112401171c0503010302150c0a03120e0307050a0c121113022110060c0309032d08091309050309010e120d0302030a1a 65
    0x28154000d1031413503444480318906280c11a1030380200300002d041540b9003160f0300010b542004140c800c0380100d60940362205203000d42c514070355540d01c481e044002031002c0140320368000c19406040d829030700000c4070a218954403480344602c1d054a1940c0005101100410031410151503c4d4044502c07000d0481c00c2030000c02055036646513001c4080d04005c0c141c503182001a02d00c0d48400d010b640301c8410340c1c0d03450700c40d428255503031480791400b1140e5444050000845480910070b070607456078840c0c00d501d10710f040c680400c665041080c411590055007040f00c2e8108042005015180c0c00d0170b42110500c2c0e10b040381c01003030082e40d103910003400c2c403168070008000030354000810720980303500c2008146801040049081c154400840040c0103408505000042c400e24402400e04584100c034820303803034402504000103442041e40001c1155009100804166016100181040703074050000340b05c4c8092201c09500d031640c034514030300100c2e03030000074080c44101074000c1c0c90204172580e120600f12a260340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 269640566 1250 269639316 269639323
    0xc0603010302030a111306031103160609030f06110309010e01110f0d0f090203010510090e030a0903030509130c091d0112080a05162a03030e061c0c050912030c 70
    0x24402803050690b004085036a031b841424a4070300b0300c80c1010400015031030740741044420200d445064460701c284c22101003580400000401030358865503408203082d2840c0d0b40c201e80300c2840070b02282c503191030716604000b26210802661140102c0c40021600c004028489400c41c1c9400c039403003101060030000d24850b0000c4004448500c0302000c40004d503a01f421100c00c0c0242500310000358076509102c02c1c440c80094011028081e20b482000401403018003140c0d1540c0ca00c540100c180100303024140030230220b405440179000c11030010f44082074074200c810f804c100715480000c0c240301060003030b04181700c07410700414421044a00440400c1c455410101240f401880b4104021b1000780001908800c80e84181d055424000c401268040024554070700302411542444414105010041500200c071820030b0321310081740c1d0940c41d200c5111078081c041c00440d500403c0882c0c10301d20000080a02002c0b144580c1e010f503001551682c1d103501c80001041401d450031600c034a241d038814440c039840030740e000c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 269641816 1250 269640566 269640583
    0x118080a08151005131a1b01060e040b060103090f0b010906141807020a0c030b0a0b010201053c0a0501060f090e0a020703090902030f0906060316030209040303140a0902030c060301030203 82
    0x900300b03540c9642d02d441d85c0c05030f1024a0b410070503000c1c020040401c9030225840142017103003443d50300e0b10080820002e40354200c1d41c461140c030010140c002c0c04580440c20140c201500100185004a59000e4075100c0e40040f0240f1030040f100c1c001c004004010401c0b081c0b04403000703420a00c12014000c0010400200c0400d0700039001d804650340800821111402000a221040d910207031140081e0350700d01f44403584490444506140303a081084203885076106100303061091000d90003403408d032007a085462030000d0018954442081440296550501081c0d07220b03442403061250104241d030404d0030007420540e00c440c00406220301c980003031060094480c1c4203540f04c040c1d140c0068985001d81011250604070340e104d01c009510000074420441d1541d81b80611520740c08d0111049502c0703910506035581e50070840400c881c603020506100600c1c0128071640c00034004e107404a101c0042c02150b0001340310a460244035942e0f50090320f07007142000c0c0055030100508449140c115031454000ca0b4a50790715 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 269643066 1250 269641816 269641849
    0x20d06050718030503040801050c030f130203031c05060f09280b1e010906110304031e0507080d0e1e0415082401090c09060f020118080a0815 62
    0x80340e00084000e8461503058441c07540a21209440990b03d04180b91603038081c1c022003a040d42484005406048010202e0307024030603070b200c10580703650380c10750b443c42411100300201c3e0f060004020060611580c801200140d0120840004041c00c14004000222140850840c003400c50318040089010b0404546202a1440084101c039900f5207149a001040080440340d8000841e08000c2c0509083c651040d1641000b17884008030f43d134072854182c516000c1d4603851030700c60740204002d0001420790007110000403a0416480c282c507201e651000c1c00c104090f080003c0c0b55200b45083c4260990003480d80101d0300041d40c00c041008035640800814031000351405005603140d02204d0b202004480081d80144158419644241540c00e4011203a500c140c403c44402203500f40041151402c51050b83c2550040b40c89110942d85892703c1a5882c403040c880507425950303262402442e00081506001d0181d210b088482e0741e405482c80054a60300010b01340031074007810f0f445003051f0f64540007140307001c1448 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 269644316 1250 269643066 269643071
    0x9140a090b041b030503070c030515060a06030c0507060509030a0f18060f021911030706030b06030601080c04090c1707030203041a060301060b040b0c15040c030201031802040c0c030813020d06 84
    0x100111660700f091201d07070008105120000c1c03032106200380d41c0c5803a000d60b44035800307903002c840c90080308882c0781c201a98440d90115552030100b201d18007a0740308043d10b4106081150030200b06846410880d4012907888007a5000040c0b903a80b040d0f4042c4480d00b691110341096200380012200910b10002c181c0201014440032408032100345000304103501000e419180502000d10086ca82540c10344d5014000c01d00911a0003404903056000f8011091448409050641180c2d580c6004665103c40942000708210003000089100d425a0240240e268009e403214a28842d046180c4941c4070002014081051320500074800001d010b00501215000c201c20800e080c8e4079590700082c0180203e500010300000000f40000310110f441018080500000c01580c03c603181c002001c0031090300480d0000e00d8854150018001036010798048042019004104803964102c0e9001c18111104c080304d100c0030840c250207880402d50301c04461544128181c03000c000d412020b601040c4000400f0f4001400d058 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 269645566 1250 269644316 269644343
    0x304051914150904020a09060807020a0201021c030e030f1c020c031611060a020c130e0d0305040c0b030403210204120305070602120f0406060e01051e0301140109140a090b04 76
    0x440720b03801d603404018000d10440d074910b444103002e400110240300f030340003140034840006e0147c1d00129003400d040b90113030042c282081924101d84000340046c1440c00038165031791042c0c07492503020405054024400c0c6c4c11903507603003d03694030b402e00501408220302c029130040041d2248250040140c8454240d00c820232841c0b20814900000b010101c0c0258581041002c120102d009900003441c51080c0360540300940140d91058418054a81581522050742d02000b0000a0180b11b070b84110382c4907000362034000d09251121840d100c40d81c016a82030700000c6650b44460580701048003051000d00c0840c008614151a1403007c2102030302e00d11004d418444086411810b00005404a600c018500001c0f41204d1802d40c00902100c5801c2d40c0c2501c3e8030f8940140030517003560810b080e074184c0b8130007000e60101070300c510050511080071310b202c1c5415540322a03c00440d02c84d078800b018064050030b5000300e1f001c54100b522140d1010f00515407501c45007003c5081012503011103405801c07039000f030054103041c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 269646816 1250 269645566 269645599
    0x1080d0e060d240e0108010c050717040b0a080603010c0216090b060d06030602030106080a140f190501090b03010e010216061d030304050a0c1403100f1d0304051914 72
    0x100800c564204403081d4406440700f0740c0d0543d5214405449400d55400d0440c0d8845000d00d00b00c401843c10407020800801800010400703c8c42c202103d4500030340505d245c50380314840010705400501c0740c0750200d52403038207002040c41d080c014021052400e10041040d14001c5c107010703603242214030895404075500c1c825800192a01e00031151070303880c6110140030380c0b9641e0ac0d24130001c0d8000d1081c200050071140110360700c2c01f868000e07851900300518445034152a05203140380c0c480d030060821090313031800c2d50302010620780c6405502d000340f480e42800142d0588041c02d040c20342c6c040d440c139041c1c1e60744104138954154941e00603400c03e0381d4000400003415800464a032a054444100c04000c601c0701104200c108034002035094a01c034841e45105082c3c0d561006464014014401041d41c0f58101d091043c500c0240c1e07500100c00060308070000301d0241d500c10081681c4000001c0030486d60f400004041c0468100311850b138a0006102101c0900c10b40782045d501c0d07d100040e00b41a201d40300945221084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 269648066 1250 269646816 269646821
    0x112020a0309021f03060b04080a061a03010e07060f030e071202010219050a060f02030603060f0604180b060a0806160f030902100509090105060307050f070c0e010b070b01080d0e060d 80
    0x55581c06400d1001d005110b04d6243d00d14444030407031900080c1016408500160050700f500e08031480e400051110324800e640700f10280243c0d07180000044021844889965030074011000b0000d8550042c0c011641800320042c402c079400c4503e0414182421000f0382040c0c0009001c1d0102d441509030064401c0c92440100e05008146071b25201c03c0c1d505404540070302601056442c5414803030b0300c0030403910f06596a000103038001205c04683c0b580080000610070070308441c00550001c4001e1000030300110308286803144100d000000d4845000700f208000803424401c40d00340142c40120014111407038411784011004001050340010840075440c100c0c031700c500980020b906103a0081c03001e000c0c51004040240310b81c1245254900c0713908144000601800c080e401c80340283c0c5c641e55800d04d844034184000469900c003074401c5400007030403140043c03111036001009028241a150140c6c7d510500c0c10b040190341c0c410b8000395002c2c7c0001c04e4030300c94141c10001141c21900c0a403030060725145440b080c3c000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 269649316 1250 269648066 269648081
    0x13020d050708070e100f030b0a020703030b040606090e09070e1915090203070e010804030206060d020d0b090c12010b18090f07180f06050607020607022707031a0112020a03 75
    0x3d10662101141641c030440c030042c45041d03071815240403d03a855000c07a000c05502e11010b0610415032000c544181d80540003404164041d0901150b50b00f800404a02250072035232229000504640c002c2c00a450b203002d0b81c58100c00810000c1c65100c3c24200314103448080074041c00801007484540030042c0000b90080132603880e920250241d4113070394405920107503004458203000502e610881108a40c051420b0b607000742c5c1c150f401480b0325030b14481404030800745100181d07441041100036800080403013451138403514503180a40f000b100454140403503884807481940300d907410103200d1806921780e00c81e800c41d5100b02d5100401c0c15110307282181c3c20503404400c0d0b0850740c01046d0700400e10306142c1421060602003504d0801841b007100802c0c03000c0740c405014065015a041141002529010018104003400140b511641d55010300c5420009415800e0700d030340c508401d50801a64680602c02c00304040c1c40081c200983d10b0703801d03000801c000240a0444186079000c1205a19648260701204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 269650566 1250 269649316 269649329
    0x61b0106060c03090e0f2d0405160b0711100302070f03020c09090d0c1407050901030c051302030903090d1e061a0a2301120f0c09060813020d0507 64
    0x86549540c00207080d0b110b501003c0d000724a504130f00081c1c0d00603d0340c200384030303644140340140503032100d10880c8202c55810f0b02100d5030980096001c40026040a1200d0050b42300308010101c410381807080340c960101e503900c404001c810502040300031580c40d460400e040b00d01110150a40b502011044d0000c0c01202409003507403a20741710b03030b00826030001000d1026910407109600c039903858940081c0c5c3c1e410444811070025180c1600e98000034048544100c40103481030580d088543c071381c0c02043c8444400da006840690404800f00010300b4000815000441403007010b51652070907118260740e81c8035401d0b44030301461b140e12000d410b00c550555480441543c2031a07800307030855113003481c0024004d209003071a04841c80000110052605140354400c0380c2004c402d1703a0752814594000101da240c0542c11030b0500040c20b0614450780f4440c0314036908041514070000b10b00c031210400600c84005a0400c800f848102028080707801c00c640c07140503581b81e044941d0a0420010719000d410142c0950014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 269651816 1250 269650566 269650571
    0x201170901020a0e09090a02060f040812071704050612040c05060d0b040b040513240c050c1b010815060417060103021e01050304060f0b0d032a02030c061b01 69
    0x384500103400601428015644480aa00c000300800240d040c00341c8111189501c000d501600500700240900303c5855032140c1d80342016620841c0c6824000300e05500c48502c400003d140c81040800710000c403100142034007803800d041c28900071528038800ca0740c0e04c889040d150400a802c21a18014140103000e01410305921000342c02c2024014120718a562403140d07007801c04250184c01c15205d007601c10848100041010311103604c0302c9a0340c801c0640195050040009010511000390203074912842c5981c0d2480e0355919405222402d010b6034003000f85001c03034500b07001c7c0c580f603922640c13503a0005528904030404900050010b18540301e290b2080400e0307440d250700c44083c18001309849041340c3c001ea130800103074007890642da22102c0188090380d000c0764061004c90040380e402d40c44090748248031580000c0c01d000703110020709030340c086000480000b5085191a0816190a04801004640405140c0380000c19a00282d01d90207281c01081c0030f1500802c50f5078402c00c0740134088200d001d80300000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 269653066 1250 269651816 269651821
    0x20705100203061c0b0417070c06050306210706050c031608030a06060906021522050109060b03010b01020a020402070809150301090b15090424170f0f06070c020117 72
    0x150320107074004403282803154400f1550608480180f9a000394059400700300182156200d580b01515608045003680e040300c8140710b0400082c0e81c880c0c82c03030040e00260b120141ca81c50050204030070310100c0d6400c2c0003401010000e0500500002a0240982e0f0160400d00c2e16103191805035032031802800c8403505041e000301b800c5010b0200c907900860080c03800480c00c1c04116201d00003030b00d01031124400c900c010b07480b0301d61181001488000e09600021040380117000d25615130201a003d0441c050203030744595542209508020340e074030556111010582c02030140c2e03240d440000c0e4035240d00e0308000c0c2c050341c0c0000b4081d081101e51030460740c5840b0014070140303081c42601c240c81c0d03480d0801d00804030114504602000b040c030307007088104010049000c00c00d14140e906020700c009071110441c5040840496904080d0000581c46500050402c0c008100c8002c048511024a01b8841295039401d81c0c00514040188500114006900c030180381013094803000b00d4030040700c0c5900c2140d254079450b001c103000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 269654316 1250 269653066 269653093
    0x3230f04090203090c0f0a090207050304050a0303050d0b010815060705010e06070c050714060301050f130c020a03021504050607080712110a080709080613050115060201091506030b19020705 83
    0x10398054104c0c90100c0c3c2c5901100c0e424008299090b0040507803103082c0710f000704403002c2c00390010034146108070f00f52400c059940001c074240901c650001c50104d100802c040818070728a02c607030740e0f17030160902e84164a82800c2d990720f05241400740b80240501400078a04003031060075000300f198100c51208603185841c241030300a003e203045590403204ca0040761000503042d04411101d00c4001030041400c1e1071070346000108404c885410b2186600714040b00c1c3c41006001c5c5074070462100c1100c0d034028200a02c460f16009007400454600740385429020810f100200e1400909a07520040700d00b0706071a19158484180e40c08201a5103214030315007805900d2140c074000c41d025198080142d2120847d0391541e04041c2c4409048e80100e800b141d100d0000100c0349000110a01c800b00d0242d8000121965840c03078052000449410000250791585091300820544404602e41020309003001c122050641e69820584140030300b040c10030711041500c0441d14002c580c100da071440e03481411203180910303504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 269655566 1250 269654316 269654321
    0x121051e0c0a0602030315060a3c0c0f020f011707051312031e050405190503060f090604112e02010e0d02060a02031e0106020106081903230f0409 64
    0x501d0750040003807041c00a0303254000404e6a0280340c034820b54242a035000000c0c0084e5030003484201042050051030071408402c0d003100708802c0c09406e6550781e00c1e4455102a0f401c2c01c902e0882c46800c01c54003640c500c0114030348000b02d41d807490703044541c621044910801241c43c6842d5010808100d0560300c00e1040e0142c020780100340c0d0210000712208030035a103501501000c1140903026000c035528005072929001e07401c0054240a516040c498101511440410207001851740c4c51002080d07454028440d0389070821007240d0040f40e107084d413401e5113007081203541ca44002800c014441410440c041c5e0b01c03992001c1601c0c9a4103485080303450090002c04200039440440c2d41c0420140d460100d144003c1400410302600d00180b0350010107007902d4041c2107200940c0b0003031802da004c450b0342c0040c0b0520031103204140d000340106e40c004200c6900302a101c5007400b950f101c46004800c895401000040e030010031705410f611510002003d4402704c40c0d151545032094410007080f071000082d0100e071120013036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 269656816 1250 269655566 269655583
    0x604150605030a0c11150a0e0703030c05070801060b18130c260105062a0102040f0e24100c06050901150b031b0a09080312060f04050121051e 62
    0x42802e004c2001110400e640c140802800e010264000d5555003141d002254110f039006601443e0026422400c0c0490070b080c00d225800c00c50004611110020a0010812043d07003c3d00003000200305051810540743e03800c1c030500c030306100700c40f000105400d110754815840360004a5940b04c1440725103010300004100b100f80362002c1c0507a00201030080d0340e88411500286c1642e00c003814071860480108440c10b03d104500044400180c03440580940307601003800504018441c2c8620900118140b04075203070380980c000d10a450001c0c03074011700d03c48192610000d1441010503191854440c485910450340c03945100c03030203880c41e4188002d2002100f015440020a48400c03420520f42c2900c5041c080c410b807000b5141c041500d1140303821500e4101008005011103000b030309124400507990000f190a58205441d110124100c08c1c0810905041642c504110200200c5082000d581001d40c2082d03401c1045240b041e03e189048840402c005040004114400103070501500c4e6110b4241c0081d91161003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 269658066 1250 269656816 269656831
    0xc060608100b1c08030c090a080313030c270509010b04110408011404020907210501030804061101020a0807121e060311010203071a060625050d0c1109060415060503 72
    0xf00750201d60180600714448074943c2c07206140d490350b1a403401100b40354000120403540440c14090000e084481000101110846040904491859400c20844120243e40a800c81080402448030480c810104401902d5424000001d0b141c03600b0030201e00410110400c1034010b40f9201200c2c0a03403500f100648112015030009020070600b07484010f003c818180c4000b0b401804420218145a00034051aa000009103805104035160441c184c415150280c0c02644c0480380060240142070740040588646808507009501c2d040084900030300007032008191900b000308484070f0890066094114481c400302503c120484c1c2d030000782d003040041c03100e44030031152443c000d01c81700c41650002c429142250741041140514103024141c444038600c00a04466101d4030401101c030a41c400b003c00c1039820101003c0045240c4010720b0018a0104140b1004c0240a0030300074000014600d084c03994140d10003507924030155200c100202d0050010b011402550002d0303210040340403a032240242d4402c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 269659316 1250 269658066 269658079
    0x50903010f0e240606181513150c0311120708041e0b07080a0e04020a0c05061819060f092a051302070507051908010e0c010504060c060608100b 63
    0x112010f60103501541d56450380321a03000c0000181d06490100081c00d41c010310048a401c405a20900040c005e58510040300b440e03d070089442403886a2081d004805000010326001c800e002d030b81c42c050311183c03040b000141002044041c3c880da0340c81c144030101d00003040801640d19141e203880c00a03135540117402074407040500118048040241c1c1c001100444000e08030451514000e44c0f00d0f0003081c0c0c080602003050280f441c00076540c03501c1b18401400c0403501a6034125010000c1d1510304d04106c0080c0004450780d5001020400fa5240422650b900302c0c03080409148203251454214064910081081c40152918200300300748513480814240c0310700c038001c041d01c1074642601f030114980b45a005d0320307401c00512a11342d10b01c071006074020000e85010320704603013840d6590400110b001014a984408000c03070b84c1020041c1c22024004e03110718a81da00e0103400c82d8084200020018043c0b4443c0000700711802c0c010f60144182a4405805400201d060710300094905003039101078808030340c0c000d00489 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 269660566 1250 269659316 269659333
    0xc0803120604110702091f030b01030303051e1807080703120801060207030510050403050c012d05060f06090d0b09010606091d010e2d040203010605010912060c050903010f0e 76
    0x107443d100b818000108090725a091141e142c0a002914034001c110b050540003104908401c0340b034002c40d190046101c0c4c9810289507045140081c10fa450103020000b503000301c0c07698001e91884050540d40d000c2804100301d4818800510484c0c0750550661001900c2e00074003001200744011451888860101601c0c2c100c09640d9840c400c90fa589030500c40600540c10035644422911940d80003181c02c14007e19001d42462031122a8a00311808400713045175406403a0b20340c2e0680d29205280019200b540541003105203000c0700450110140810081e1095000007408501541ca40030041c8005803c8110400d591a1081ca064000c1005000e440b020415a00000555000c1e24064100700d9042d600a04d9181e480c02c2c0c004003900c40080e00c40403014a55103889254900c61680542c40601011750f02d45141c00d050052600319144e54001c6410003140307107014400d8090034800c1040150340000c0002c0d500310140021078540c01034161680e85542800c0100c82d000e44503400101c0c0320350f812815150b500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 269661816 1250 269660566 269660569
    0x1806060317031b0f040302030313090f090807021309080d09110a0311040504081902030301050a05060c06010e060301140705090109080106140d051618060504110f0304050a0c08031206 80
    0x50004076550003019030380d0100f4103052400c001c0540380480d00c048849051940700d9001908680000f00034802d11030503503800b0440c40046006207401403881440810540e840e94440d9091441040e101a00840c81c0e413104003030120180d40904100c640001c5a10740311003502e050700b00a0100c030740c002c0e2146000140c0000d0240342441d1b564088030303440b004042c90394500314280409030070300920030795040405000c081030002035043c08465042159029550320340c108070401c10b80c6e45c01c0ba040a1300540c0705005890040340700003560350640304013480740e02c00c55803000b000901518590081110344404a810f200b800764015000e005040400d80342c0340826900c82e65558225000d80c411045080d151806804503810404032034261030380540e0075108140e424440e0081c2911241e803012a4400103d20301c1166030049108a10250000301c5050284004852102e80f46002713040c840088044d0000105082040410221780b029a10101050100303076030390402526504158680f46d40c40134000700140c4203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 269663066 1250 269661816 269661863
    0xc010503151503042a030605040201090b0a120609020f0a051803011d01140411060d020d0509030301050a090902030c0f040b0a09050711070e0a090309080105091006081605040b01020118060603 84
    0x903d0b9018442c1785025145843d400302600c000350069060010f00c640200c1c034542c1d0000140420a801d44403c18484040b0781d0100445400c1d80c0b015503040d10501025410750b551108035050307081540fa0043c1c13100c10b00341000006148206000787d1662070100c03045a10504040003103155200320000f081131940da031114000301582100c00400b915400c1080609514147d40509042c0040c0c160050401c040302d160007048980654581c00170b41e0010004001514210309642c01524103a1307010b008000c016404280d40e803503e5011548500403d90010110b916164014141008000d021072a119516107201c0300400301920220000f4107032040480c811100001c0c02001c540c14058290f48643e03d4125240080c030041104408000c0c0240d00040c03045804d0141c2030140f04000080d044407046800c0e90401c070ba40c190b009c00d440b5000300d091440d0146401980304100e03201600c4c0030889180c0180100d004142441940064074451404402801441c1d400001a03a200355030079401c10005607000c50b907 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 269664316 1250 269663066 269663123
    0x6010e0d050a0303020c030702120f0606100504140d0b04030c021302040b0f2d09030601060f1b1401020a05040e0c07021c0501110c01020c070f080c01050315150304 72
    0x60740d4412284000060300c80e600030205103461405403400c085159002440110003800c0d00c808950245000c0481904280a40e6030001c1c01140c1e1021140d1030702a0240c810b0103144505c0e41d000ea50707044d411010b91180f11500384019801000e042451a040c50041c01101c9a04010380c062900241031066942070340c0300b12029a1200c00d0f4803400c0c003a07070b620440e80a60115a80746981007801380c607007a502184e4855041042c540c803062540b00c0b1781ca841131610b001c0059100d0002c0020a18040c0900c98200ca0300c060001619515440c80300403608110314403020320f01c103075040317584000344c20702c071980d8000040c20944242e4115500d040e01c400b040d80369176000f00031002c0d500521141ca442894045c1400101e2094030840001c9650980341b00c840907690019851120079940000d9022102241031041d0f201405400b01500901c80c107008510769a00520110503042c0040040030030756003441c0c1e50240345012001040c520340410b5584007102190001d03101282c1000c500402004540c020120401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 269665566 1250 269664316 269664323
    0xb060d0605091605220911090903040e060102010213030821010621110901110a06020d0207020f0a0308090d110409080a0f0f1e1106040804050a1e0b0a110a0b06010e0d 73
    0x10246040b191011000740030503101180e1410304007200007d1070f16540402c0b4440c0b0f0100001e191928a002c080c000f0500e0020010350443e40304011441c504545041c01d01c060701e4012451a403504646050448400d0030140000802042c9000018114ae403100030715420b100ca042c0301c1c0d003400b9079001c01e12098034194880d00c40d504405000d000520f5104910404ca1203401d1403c468103001e603500d5120403640030026030340354039130000354580c20b509040c903450050703400540300880c00925540b0b903640a8011001c60510407084042901c09021b51260390390700300391009204100074201c5203004c1d40254420074031132000c01d00b02c0e1403080303100740520441d04248a80e44c0b24400c000b61020828100152081c001c0014420030689801c0c2504041000500c503900c640181580d882c100001c0107401e60302c0c1d80c0302e455155001c00032182002d401c2411f9104482c09400019100c5075030a0003500e42c140104015170700c83c0700d880000c20034040c45010041c0164000c0e01c0d0000d81c80a25014020714010840c0041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 269666816 1250 269665566 269665609
    0x90d0602031807031b1706010b09270601030509030309070308090402040918050f03030c04060507080d02030f180c01021902010306030f050a031407080a0e01090914040507050d0c030b060d0605091605 87
    0x10004141e030318005040800d8012f0a01c0c1c00c8030400681c0881c2500c60344121003a80c07103540d040000958051044541084c2410015402d40c90800c841a035580709500005101200c0440c55181d191504d4040c1d80280c41089014080310300107100b41456401c151405a41c41c2c410900300508061001c000c07280100885e144292816003080800d480c40da20401c0101c420880401c414118401644040c6000c0e03424440812610306000c603070285180e1981034107140c1f54001203a820b440742e800050322203e000c1800050b0318124028001038000302000e9001514000c0400d100c0c108110000c80e0041c0114443d840309403240c442c80c84010390038061944002d1480380100b05400440340280d26000c1d10940514001b02d0081e1500545001d982d041406541050020802c3c0420803200380405030180c181900c140c091003550740c45180b49080c813880041d100d109010042500b0303896142d480804a9002034082c003941c100012580c1c0d071803011f080c140010b04006800840c0920306040203994a09410110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 269668066 1250 269666816 269666819
    0x902131122030f2618040b0603071205180a080d05070c0209040b0a060f06020304080118031e021009081803061006031107020310061505090d0602031807031b170601 72
    0x2101c1d0004448120301c2c095088811034981d8044c4d452004080400c03420f00248648824142804103585021404601c101010702c10418059400b203d011001200c0d4580440c850b00c1c0c121500c000620510307c40f20013802008440c0d0240300d410f10082036a103982c82401c005517507514904440b0205443c000940c40b0001c80d0110b00420340300c9581035004003464500207010380d0f136071660401c1e102d0164480809a040842c0030001c2c45800c3c4038040c0b118481462401210003259001041c1c20b10318000862440d2100c0303685010284200440080c3c0b00900c0e008101081d641e0800d020503407c0f07821410030849480d21011130340d060101d000c41c081d00648402e1036000c0e043c030009502810444560b810307400414040040076035000c1181c00388603c130303100c00090704c9400c2c1482c01d06491210041d4106009003004801c01da500c4000d0b00841e225040400140c6036110b145081c035214140714240c2409120301000441444540c110803031001d0741a10b0501e0805035180d244042c5940103a900ca000f5401c00d500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 269669316 1250 269668066 269668073
    0x41203050406020c0a050f12091f05120705120106030e10020a020a08040905070e0306070e010c0c05041509050601030b0109050f01110307030e030d090312030902131122030f 76
    0x200d401900ca41e02c00f500b4007601400c2240340030090041075996034008aa0f421003101e003400404041d0004211451401c610310340807030b08020180313144101c04281c03840f07a0048284280300340d469200486161100900303092600601320b811951000f0082c0e10400000150207002e441080d03109903801c07001e05169000f0781c13003c0c802034200c0b03144d042c154000c00c000c9000192244000300301822910100140340d040500e00100041c07956224030b80642e02940901400c990407920344d15205009281c103d00740c0d16546413404a40c4960350280760080e04140302c400d01619507441c400191400c14000f04041d9888000440039030b5610385400d804100b4615051209040034283e001d81c084042c1001100c003c11500302d6072541e8048a0154002900d055504a59203014040807081c40d50610f0b1016126056490301400518404000000d06650700c60b0301d021512401c1d247c08070042080030400c681c00380b48455203400e5010021130007403040e80b03140c00c1e0342100c42e0015503c02e0b290094030a0900721101d54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 269670566 1250 269669316 269669321
    0xa140d110a0803040b0c06150d0807051009110102060601030c05090d06060312020d03060501020a03090b0c1e151015050711031b0f18060409020d02030607030212010905041203 77
    0x6a800c260030001c0801c1c0752100700700900c010011901c0c03041da00d01104030303d0380c203009001d4541b0704008130058501d0184d503500d07842c0307410590b0010509503903202249010361404140c0802c50005508040f03602041c031800303240c4410146000c0e02601c0207640c070440110100d40e0440f6100000c6582403100345818100f407070890030b46501c43d00b0005001c076201e032152040c0d600301c161007400503441250b021032040c2c0d06006042c002d040a00081220000381d940107000600c04d806211a90360001c1820041034208002d1215110101001d4003506200d110004c0e8480a013024805a001c0d811400f113182610808282000c5480b0001c0d03050104c010020300301d8580d44112010b54285950309011010b031b0f54180311003004a00c610411034103103121002030155140000c3c8401e44140e5810001a02c080010000e45900c10b03021074000464040920010700802540c050280d01449000100855540c242d401040070811064881156a03602d001c413109a420445005112100c4846402c03901400303038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 269671816 1250 269670566 269670593
    0x50418021002070e07050703170c2101121202190b1005030703150924051506090906120709020d020c0601150203120709090c1d120a080f0c070902090a140d 68
    0x919100c1c1d127080c08070072800d40e5007800361090701c1c00ba500003461080c5042c1c0b4141c2c901d504031402c034800000e9854905038841d098103001000d49120340c220b0152840318400d01c42d49420001504042504242e203040c00c8510b864101c604aa00c00406d8002181526000500710210784d0310080804041202a1404000d424102c0041300c110558000715038540402c04e401c0f803442282a48001514a8004a03100200446200c42e074010b01040103414400c1c5c898489240d440601503c9042140100307590b20f0749800359542c000101d207480419131084403051a00145650b80840b000c6407090398855002c0144103050340c0141d03005d42d00c00c002000140485614059100d0f0080c240495043c0d030b200c00704026110040405000100c14481800c406071190a071020284070980b400384000c1e0656007034503550003224801900641000c500c420550300154103d034100400503069403444d0740d407220440065001000050301c2100c08079008100001134014030001144014902c0c0300007035241e22100348a1210 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 269673066 1250 269671816 269671823
    0xe030904020a031b0c0b0f010e0f0c0d0e0a0203010b0109083007060e0601141003181407141005030a0b01020c1c140c0609100504050418021002070e070507 68
    0x115049200498803113039500c409400e05407501204042c051a0030030300544010008802580400014843c80076013107101507008036114400301c072035140d0080b084c3d4107004240100c640c4508141d00da5038000008108002a980300360001e0040605050040d9662020350085100f198090305190f4200320030200c1a038900d084660304c24030308034640010440d143d17020004c155070030751300c420050440041c100201e07030040200075450480c111b40d61000880401190754500b00309030302e032040381c10910100c0400344400c51380000c442000b200d01d64035668542440f4441c0b5101d00d000c8108858641c100740a01d0001c452289d51a05c0c80c5603614418800140f149909060441c42031042c215803603111021860700c01d444081d9040a848a1480c1004900b80c5180040e01a9004180f0314140350325404c2c16038000030021148420300c144100700c111001e0280354031080d031007800c1200301d503488101285a00f480b5070080c1c2e001d10415420b4a01030b6aa003141d0320034024590849400611002d1140002d400000e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 269674316 1250 269673066 269673071
    0x91524050f19030f1406161e030b0405090d0f0c0f0b0405100e0c15040b0d051f090204061103030402030618160e0105180c070201031a090f060901090e030904020a03 72
    0x1100c4c2c554075200710303040c0710031034005400350300e00a0b4440c410450315070b01207011440c041103859900001071089400601d64645100103000e4808424004e40100b605054040e00400c250329203103000c2540c40f150169064041454116034110461080329407401580e041000a8030540071941c03208003190000700255420300404081514401d50350290070000701c4810018a94000e80340100600b03502c02090b040651102008104564142c03841a030720b4013050740310001142d40c0d17618000d801d1441080450800390b4450bc42c00700b084441940900152480d4bd070b00c1801403000003c4140e900c1c4801e54020b0351507488200000d0694241c05052101444550300751441500c810010384e40000460300401c80d1059240d006100900380340c03a049a0044401000ca0146c0c00c1580b2006c4503403240000c00381c10181c03a503000c5102c0c0303624032401c81c58200000e800b00c40145009c410b00c43d861300096864510900e900c400004145200d4001c281950b518900590b00c0e005049003000002d500504000c0d040c0364 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 269675566 1250 269674316 269674319
    0xf010512040b071b2d1b0614091f050f070308010e0f04030f03020c0a020a09050403031406101d0909030a1e0c060f091524050f19 57
    0x20208260a01440c0705180007201410303d090091303c1900781808110043c28400030b80c10114041164a0810000c28845c030b0300001950b010030702402c04903c8003d0600b83c4404045040309450155450403101c1507528102c000f030030003941c0c1d02c0c1d07031046980c07190340f081c04520612180c0c0c2100320100903286a50400d031b80f07000d010710307140340043d0000c5100ba804180054010024581c80d03201c001e61100c0e040c41c445008e0700d050740d0050300086840b00700100705a07000c28100b0a920f01004181c1e40070760020700f06003001c0d03036034042c89010b82000c44081b000a0300b0800341002046a413503000b4069003000308450b00c801511041110700002d110300700c502c0c0054001c544a0320740c80d030000d02401203d200025503910031074444c1c0079000880c10061080001d1219407401c107466800000711220950000011884086080c1c9450141404a1005e40301300f01445249802e2055030317000c03103009064040202c242210500c28203401c090305201d102d400105d12003c016052030500302c0d2456185c8500f5686c11290f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 269676816 1250 269675566 269675587
    0x70e091003140c04050108030c0304062006010905012105071802190915080103050d0c060912181706040f17030702060403090503010e07061110020304060f0b0d0309050f0105 76
    0x30b1200a01081e1030380007030306910414241402107501510882c8002c0d440d01000d0054160b0328825489044108034582e404020600768268402e400c0500200440c1c12558503010a007000304002e11900701c0018401c1030085c0007059040305401600e0308440034010207480c0c0942000851901c04024614503030810624441e04a190310701800040035076074000206042410080b804908041c04000388000f480040000690001d82c59900901c10310704036051110b58a4090080c0400c6030b80208a02070034280c102d2815441001c04901040c22003850b01c0c003554608214150703851074070034035219030050000600420f11001040c401a072007040210135001c0f02144600003a00300380d626500582003142030206140c1e003e8041d0b805043c08034000c0100e144080c04041c2c0c2c8803028800c132010301030100e081c1e000c3c04809200320080c11040d418107540e680303080d00d802e000500514024040e014982070b02c420f0942024101115801d0745502d131540507500300803c0040c4180071b280010b0410030204a54141c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 269678066 1250 269676816 269676833
    0x18020307090507120e01150e1003030e0103090209090a02030c12070504020c03040509070e010314010602060f0910060303210c0203030109200a0c11061e0c150c03010617070e091003 79
    0xc07140700f000001e480d854000103c5201da41030351010280d0801078049c025080c1c002080c2508480d13050800e03004103400d100044e0f0140421000107580244a0381c00c2208000000c200104a90b2088094071580e00c0d6a60030481d400c4010305005415034828601400a4181540240308648541d400c0724107003592400041c40100b0b049a0407030000300644420300701540c1500540e0000d40c0e40c08180c407030075810000700039070342d281c01400d030382c0d10040020115900005c01d00035032500e21101c582c14030031903071030303040c090040c00c4254905924441d9440014000203c1751041956400d42da40c00f0310314591078003550401401c008442c0c9900b4684107480380130005620b200503c0c4034256a00d07644400416418034006031900800344500440c01040403d40300003c0000305008045d00034400e90b00c900b40381c81c00501c3c0c5060751400c4080c9031040402c0c03125030381f011806581200d0b82c0382c3d201004403c440c0300d6514601c00c00d8495101044064081c00224a8075400c0f07141d0000440d111180499903a44444e0700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 269679316 1250 269678066 269678081
    0x2041a03031308010e28060b060a0e0f0d0b040f0813060305070318080901140903010603080702031e1009150929010f09020c100e01050105041802030709050712 70
    0x4040c021000304000f003520a000b0f00010703040410250014200e080c0c4501c402d00078044080d403032103411041c040708000465110005240c000340034aa21011000005490080340ca0302d007522514494110b007026150190000d4040342e840f00b00031a458880e640c1e60f1545a01c147c0341100d01c07040078000585542c01d030301c01000081170242d901041e50305104201070211101a01c1c2c0d030300340460450065000c510000300316080b41ca402c0c44e0400754103c8aa814081500589603115455400e2000000c1448070755005841941c0c0204c007030300d9581d44441c0401c43c030521484074140c01c9030803020585201ca0426401002e41c64001c20030031490580905195080703600350032003151001e109181030170341850422008500703014901030a030b41550510b92081b80c604294071030b00810700c1e0001000e5135a6030044c0700c0051111a000800e01c060781c04000024040c0109004083c0a6442c05001c124217542914116014075000b501030200c4500700001f58010300401803140d03040c00354010700c00c0e0000300035205955 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 269680566 1250 269679316 269679337
    0x140109110f01230904060e0112030305090304030b01090c0e0907020601150e03060115050415031b0813030309020f131506080c0d0b010201140f0a05060303130302041a0303 75
    0xe0669000d4410400d05038002500d035070400c840d0040d400c5007000140642c40072410a100a15150009000024054400c9800808403100d030000002003148130341100d05056442074905100564038088595620700581c030000d05910707084001040f1012043d40281c100402c0c520b08105100a940c001c28000c01c01a0b4480c00183c0c400001081910281c480c07024036800d491030018a0341010100080e504e10042c080d00c2480440391003c01d01050190046400400c11424156a06100c0081c0070700101403240410345440040e6401a00030741c0300c2c243c0288150185440d408038030324240c8045009014241c2c089800032140008940d4139a0750324420040b224140703d01094516041c0780000c000d03c0c1c1d9610200078400c0d041d09000020311000c0c241d43ca0446401800182c000020340100c0c05000d003084040c0300780313404400740403003160b142400700d1003105c0618084c0515110304040c140e4901c584407185c2a100e00d00701040c030051905800451404003c0c04805080700070150009040d6401420b0b4103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 269681816 1250 269680566 269680583
    0xa05090c07020906010e0f010e030307050d0c03120b010912020f0a270501050102030405060310050604030309080f1203010b0d0b040f09020907230901030912080703110403050d0804140109 82
    0x1c0003149404000141e00c240286403001c3c0f00e0101c3e03004200c4200700b2a03c0c19051000389400078680740c07000c0066030032040d007001c01ca070b80e01c0400200140071024941d4080e030008019047c03c515080c01da00034060150300607511006040d140902d518084100300700300300c0e8041c02404203501169503242003803010309807085102c82500320f400000c1c000d6492000302c1c00b0300d403828440100180da80200c256002c60307605440d1244d0305c0d82c40c4980851030400c83e411044d840803000c90f0100034558480f0fa182c01f943c0c1c5410440b0750525040410716130340d980042031100202000c100522602d8034910207409031148144000c58001c00d0f038070020701504c220f001c0c4070324120740c0da0b10082c0a51800700d5240360050898140103da841007a503134002101c1540314002c5500300c00241e801c0040c1d00c654098828507402900d11540d043c001c0d0002015030b20203569040000c0d05281e00310407000c102200311000c4175408001407240100d8003100342c0388007100400c1030769560b40c1410f282d8a0a8000e000314141648103600c5c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 269683066 1250 269681816 269681827
    0x51509100501120e12090604080109080702150c0a150e030f3703091a04050f0115140906030109020d0501021e0a05180a120506090d0203091c020a05090c 67
    0x140f469100071020907116062440410000303001003809042c1d0411000ba140c0d5400502e00426034a204d180d001406130340c80c100040c0103000040c0081d040e20b500c200c4080420310030042d900806030141a5035902d16070000004200004c05082c0c5c0d0001c1580404d0b40400c1040130945181d080d0f4019074013102201c42c0c00039120444010400316469421350410001c401409190302103a10515020400c01c1419502e42e110401d01200d490004002c1e40c0c2038200c0d0a080c0340501d08551500c40120031414550708081c0c008030b00a14509450041d6504041102e070580d40d08002c10800d010040c2c0030540555a6406100241e10b460007400b05490052001590302c0001c900420070b11501103441240d058010f0050b40107241e80309040b0360341801401e41c0c26818603101c00c001a16801c96910040c0e00c1070529405404010000c40c0c0184036201c0c1d68140c1c1e0070f21703100300420384e180e1158400c2e213648499407038403411400b10340310918410a800a001342081035100c80c08100303007003410b403880d0700c000038080350 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 269684316 1250 269683066 269683069
    0x6011e02011d0721060212090a1a090c240309250f03060e10020c0f071508071404031707050123010504020a1110150b0a120515091005 59
    0x1006642c0122200060070244d2400b48a01503012031035520001d224040c4000c03206100068059441d0141d068014076141c0c1030040405582d4005104121101040c1d2645855000b0b4104041c500c148092409030030503a0303880007001a204280052100654442454159a08540c1c00603500c0390b980035006001c40031452a00420303442840802400307020041c41e040c09510700032000b550483c1d074010700120b1900395803d00340e8100741c40e00c03103007030a9203101080d0103115800000d5603486d000300e15070540b0b0b007458a41e400340c3c0f6001d5402c2ca650012402040110385614070800140229440300340c581420151280c2d40c481c1c4030428051410000c01c0c01003800b0f01031040a202d070140003911140b41d004007101f500d140703907882401481114401d6130b0100e000c41ca2140501d911034900d00981b03044ea140290501d031840d009100101602d03a0f1081ca20b40302003154148801203404884454803000081c1300d00d15603800c05000e0080006000c2c400654040815468011242e0b000e400400c080d144030506040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 269685566 1250 269684316 269684351
    0x1201030507052d0f0f040c1e0c020f090714030406090c14031509032b051b07061a12010501081606090b0d060f03050f060a0506031506011e0201 63
    0x140b0f005500289502900701403044550200ca4007105480c6020703034242e0b03540011a10008600100d41042c20103070851034040d80580300703954404800700c0399101c090540300100c44218061a00a4001c502c1001c81301d140e1415180440d881a514070b000c003054440c098041801d40c0040d40c080703035516214810034040000c0c1c10f00ea0006840e008450b44c024120243c0080d1303850400d04425468000120b0125075410402c1c402c480300d40fa517401e00441b4800814a003251078101c4071002c0000903180030042000ca09c03014503240300243c0d1040d9010306148032921900010030000e07801c000040c000d8841140152101080400017980c01d500001e465890b219000c2d04140c1c08018400b9442c81c06100cd01c00d082d0030050304001d803445200c2e140e480b061750846400082400d608440f04907030300b0460010030484000781e01c842007000c0c80c055a000f511804401816503106964080e415000b440b05400c012660460842e4081014541000c40c1c030102501c0b244085802c102681c010307516045424100300307682 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 269686816 1250 269685566 269685589
    0x210a031205060105030a0c02010608070602070e010602120d2f030414030a0203040b030c0c07082119120f06091a09010f17010e030d05041407060f14120103050705 71
    0xe841030041e850301100080c4a440002e043c0001195030b100d10480c0c0724800d5018401420110044074078007915180065a03030042c0d80700f1491050b283c10000300b0100d1012810144000c49007a00a0900080305805000b030048030a00c1c0310155810040450044031080e00780000001d0418441d560742864140050403803024034104c03043c0d40c4100050701c61b0690010484040380e5414a105440b40c5941c051007400313108a4004a5a81c031440e440401e1080022030f0410440f044030103001c484290114101800303000301c1c0e4411032151110345150174201e0165644101c0c903040050b0000e0f400081440f0031080320380c04d0b0440aa91982c0e0701d80103800ca05c45000751a10050304440d05c0c041d40d0701d80b030030302960f0290600504401115040350904600000d401120442c0b00850540b81c83d025103082d43d900410040314161901508001440300208001c9072050903141c081c0c1c0d40e403042e6a1008010703900801c0141c03002d1000c080401450844450013480103020b1440342c0090040c40b49002304020108644 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 269688066 1250 269686816 269686847
    0xd062705010c0905150703031d06190c09061110090516050904020904020d03091208030a05010501030207030c1e0c0905010e060a060207051306080303190c0201022106210a03 76
    0xc040305011076699405c002c1c2c0c1281c40180b00ea40d43e90300601e811030142c91103841800303218160703a030590700640000c03a501b4450340b092540182c640c0030020249003503ca00418540100c0c00801e814401c1c244151a0240d25040041c2250365002655489008407800d03203070181c0305034012010b50445c0c003546e41c1c450002800104d03013108581c10541c000800c1c0141c0031300000e01ca46015a003c001701030107505401c00400420035201c40300310f014140344800b64401c5851b590307003034602800800c266010b88280e0f25030700d8040c1c2e200c0f002e9800310390782e90094007214115003500f012407010072000160308040507405014041e4010906500d40310844400990290040d03108480c2808244505980010b0b08001c0b11001c1b0780c14004c0000021483c0c1c010401a046040d01d1300002080110500c0e400c00500415000d003242005a9001c25404900301c1c000d2188900003c403141070b40e0400d5542900032241c002c1d0000305024002d444101640700740c0d0724034102c0428660090031409042c5600b1001a4003003080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 269689316 1250 269688066 269688077
    0x1906050603070f0509150d030e03060705030108030304060e0106170106080c040b03300a021b0a080309190503030406170f0118020a0216080c04150e060d062705010c 72
    0x43c401c12140180c003a0140c0c5000341c95200000c1c544c40605000300e1074408010303000403c0e04503e41030052280510594070381c001e1080f0404505424400d0f02202d04036680f410295044d41c3f515583c07030000d4a40c0151942456480b00c00109091040c209405d030f100880c0e00c00090070381c1ca4480c00030704001d172030a402c0d440782d4035110309502180c60100390091007035004119154115200110313001c00c0d81d15100400c110b01d401151fa00150f540000e0030b542003202e40010700800d0490782c400c02c0640a40d034001c40e078440e00140195801c0c1c1c14103000030b1100b0141c480c10000352a4550300840c0c41e40d00258001400503584105110007402c0400b1350320741143e0b0b071407000580c3c1d41c14a2024501391030061700c03045009170300181c511141c510074001004921f2144c0c52107030b00280e491640b165140d0361003a02c540b1403440c00d1a01098050303e40c041c40101c85021004655982c0c4003c10803450002400081c4e0328a600d2390100c100c40c48058100d400f0564529003444685034285c104a400c550f00340c0548001d100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 269690566 1250 269689316 269689319
    0x20a0201060b0310120303141501110f030d18021206160f080c0d18120219020d0308040c0f121709011403090c0607051005090a15050414190605060307 66
    0x120342030b5004203907100340759100104d040b17a240860003070140d410002408aa52024814525041c4001600141c0c00b40c0c0d8848461958a000c81d0b01d9090405d03072650607600800c070301e0700b000c5480d800864081c0c0410052100d9141d098001c282c40c104988611413550b04084100600a1105290403681040d20300c0d200340d000400e548094900600a4010440614003181c10714410840360010715001c01b0304081c01d80c507008140303016101d0044e1001884058012411781e5001050f9a00c0c1311600d03d600180405030350001a00c040c1c800d504082c005485640343d000c4081071041d1540440d2000700141c403139401070307c138440c1020032035001c5c40e00825403912420882541a6a4089101c13010b2010180699543e62107911101e880d010000710030301e0700200301060200c00c0c0040400d0000241c25117640901141e601c4000c101d8031103000030402000700c040782a041d0000160b5604c2564002e02c81c0d004500b04180d00301c0607071b29110741c18015086540c00c1030444030800029014003034002005400500186 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 269691816 1250 269690566 269690581
    0x1091217070206040809120a03020606030709021206062802070510080f060405450c09070804060609060b09010f03020301150c020a030b0c04030c0e010302011e020f060703020a0201060b03 82
    0x3d403005030010f05440004182c0805039600c583d940400c41c1078000449003640c04918003e500d07a4800c440b004c0c4240244034002036921198000c4407840035003d4030002c920b03a91041081015080f50341c3c40d001b44800c10840300341258901044400c804c099400a0103424074000800c01e084e080a10000100094101441150035a00c0744485d0000b904607008900e6030f440242c4c3c072150b940071910000703181d1820828005051580ca02414011a000d50b1094981c1c03140c1038000c0c2d58600e02c5540d01c0c1c03c001d10a0000b0b8415100341c850a170080d20844000c140a40d81d210700406645280d0091881d242e0002000c500315a0406c0d4040010925402c0540c15503151200680f20200220300c0c0d0703410b200b0041e40b0300045583c0e00240401650b4011301c41d130400d0034030a500540b1600180811103403000400400304514a00c0c07200c140c100c2e64165100b40088200d0300b400151452140c000c030042d40300d807995044588500703026603031040190755070050300c4140c103ca00903b5aa101d03489840c0e0000d0030000d02964 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 269693066 1250 269691816 269691823
    0x915071403091e1210060501020f3405040501030309060e0103050114011404170f0f070b07060b041515120e030d022b09060605010e0901031e05010912170702 69
    0x100c3d044100a003684010f00008a1120b0720f6207a4102030780c1c068107201c0c40c45200260710940641d0f000703070f00701e908240045e80c150799541884040ca41d060318031340840c0c1c2c8403144c44d128441c0095148040c51003203942d607040441c0070340c0d000780c2081380442c01c481400d11043d60b0100784401c00b0320091030280042c1d4504060a059071019200c501e042044401101c0e400c0160041107030014190305540c400084224107207261030b008021707c0540740b4000c0216010482d42c0006440c015202030000b51480c1c003a40e9500c8000501e080081650400d803940741005030707120000c04001c02441d50034201e24030415040c0008084c644001c4c400d450b200d2a140c01003030480d0000054500f406071000c070061362200c8030820540350f0002c4024520126050581e0302e51241215000094028403500d014010161a1001541d040c2c0070540c0245e0801c4105004102280700e203044040703000c034040034a401481e000d841d09070941d64419000d56101030b43c803081070a104d03440f40380b1607410f554102c1d140c212800c01420094a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269694316 1250 269693066 269693089
    0x20d1103040b010e09030c030705060105010e1f050307121a040609020f030a020702010c0c03052119030f02041a040302030607090602031603030b0907031a030c010207050105030c091507140309 84
    0xc050540041e411010801c100c44a088050081f60340320309c1c8500d000c6035100d10034003906002880680b48001d1600307003481d5025041c1d44444a02c058000d074180704070740c2504018200b50421054080345606440d481c410721080034030f001034000c00c850800050009540c001c1d88181052071042201c11b0700009900c0541e5007100f8440d0025a840203180012034802001e07031405003407414411000000c1040003c0c2d070041c04030001c07035810a0030114198a45c160300440b4000700002ea40f044c2001c101500c6640140703106000090018202512241d200030001000c4400d400200400107007402036240070008140d208006140840246042410003502c83c01289909003503420300310401d904050080c0c01419512201a04103002440d0410000300a015030a0400014401221540f540c1e030a0200e03105e100a84183c0083c581a8079000c0115580d40c401454440d8400d000d001c40c01055482199010b1449000000a62602c0705402c0a540c448200320110240c0c1e403081085c0c00080d216501d52a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 269695566 1250 269694316 269694329
    0xb01090609061b170c100c0e0d021f1206050a030c03150e0d03020703030e0705211005010303020c091501210e060a1a01020f0601290d020d1103040b01 66
    0x10f20383c0318a041000c0d22041050001803c82c0780d8907444190b240d5101c0080c2038842c020070116051101c943c007040045620038103d07000094500019440c031810016070306200070f480501075401c40888101628009092218200001344146a070032801d41400d0107401c001d440203d0700c00781c2c00c5107550b458011110340d9100040c101140c0c2a41007040c1c181c2588541031519540c2c0a407802e02d4014440140254030031401140402d113000070007420f1190025203813098850107048220101c2810503110407098205580641c640b141d41c2401100300103500401d4003d5110350018100e0f94203032401c011441e84003e281009145500035400803aa0784000c294203003581c25085102c09203648140400034051400c00354002e0712913002885052801035110062039860801d0380c01414058130012602c6220448400c02c40b64040340044c014401c005c02c200c00c843c00403182480c1000c1240b440b1004580045520042041d404030300c20741c0a00103400b485ea1642101078955244d071030a0383e0790400c030840601408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 269696816 1250 269695566 269695577
    0x14010e092202030a0f03030c031416120f09050a0203010c05030c04061b30030e0c1c0b09030409060f080a0b091207060605030d030c1b020a03140c040b0109060906 71
    0x106640f028401c03400900c0e00840d44441a08090a0280c060709003103900c0070010746441d07621070190001c007911600401440366107000501f0340d01c508031250540340c0b16400c130a66a0704466a8200414801e80001600c520064000440b250040500319841c0001c00e5040c000c04000b0450604e03d498100c80641e03c050030486c1807900318440f42d074160b581941c5c00a10340e01052044400d400c040000740b001d0003c142421080c080711300745040701907450340a0007a1090f03002d20840780240c035048010140003007190f4104100703504c0503152145410300c00d41e024074150b00001400d000805050050401405a060200644603e04000f1903950300d80880301a0030103810f0004100c20040c14800803101560308107009858012500f002c000420b124450180b10340b04090070310309454002d0240c0c140c420f28130307165051115410140108070050b01007089922a50403240030001410b001d4043c841846031000178031080307080900740401c03200524200c9050056452003088080e51201d400c1c0191074076840d20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 269698066 1250 269696816 269696881
    0x7050d06031707061b050711040b03060c030f010918080d0f05070e090603010605090f09010908130302040e151602280c0902041404110c0714010e09 65
    0x400004080507000105445101c01c00c000381811032001810082d809520108040148035070350020429001040801080040c030210000c1202201c00e201d8064014002050f600180300c006800c16800b124885010400803042c03006c85a0040046409411720307d80030050301c91900c0701c40542c041800001440000b0002c0c3c0b11165034103907006018000c803e50428851070422600241464210542c51405019000001040d07032030140202c1c8110313036000e4034812103a269443e013007800c12402454200c4940d01c07071216a0001c0e00d42002842000b98484030f1a168178254410002652140c0181c10030550048046815030006030f01429040f00c0c40170700c0c0030400070b5039000590900c03030204803101d0b000320303a421100c13042d1407030001c3c010703036284a00034005000d41c541c2e03c00b07412400385020300031030340340101c01040490a060707000c40d501c0701410510a09101c00e5038522840d001c0c41da000030070042e01c8544940c2603544c101e041d400c45418100e501c0e030800d01d0700c0e69018022030740e51a0640b1400c10b04810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 269699316 1250 269698066 269698087
    0x308090609030703080c1203161b080f0318010905060f06190b070b01080303131104020405130603030f1d04051503030708040f06090506030402130e010603150b0a05090705 75
    0x1114500710014090310340d12030380c900f069541a0000d54694003240074810154110480d800200c0740720b2032a0600f0418003000240046641c1075200c560004200f5001c205030000c18a2403010300241c680c050a010790300d2800304ca02a40306908080c94404a86c10003121034006000032070115030116180c500741d142c0b9aa08000100561080c030024003a10007048400b0a070302a50b00c0003086107030300030f81c46007949903600c855083d0b07284401c0300c6000741d200c00c0d0589000060b09454041e584100000c10141c10191585c001503e40d100b031845041d00700390f0310401001050b8001c004410412400e0515400c04c0b034480c40a040d14500010b89139100b0342c0e950f0300180040252139400e10b0000006000c03030752200e800d403034032102c10b51090045017076034002c6040014203188a007a07940e060b10b0003d00406d06603251035007809401a1a003100b40500754172090380c3c40c20017400340f2a40d4015130141a01c0750400b801000444201d4000c00c0e2124011310408506024a0312690401c9411100c2c515143e540d44420300b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 269700566 1250 269699316 269699329
    0x5010906383006030f120c011413031206050a0902030a060306110c01060b0f0f16020310060518060f012604030809060a090c0b0c0304080303330604030809 68
    0x1400b0080c000d85000126030207458003141690600001800c100b02900c4950405586070801002d403410769201214820200711b40e90040d1042c40e0310b190000c582e6102c5100d84420080c021120700c4003644c0485048018150b0209524015400c001d80400c182400e140201c2c1980a03070740540c810254002001c602207034103035800f0300001c2d60070150400c00400c116007072600644c0502d5883c3d0240d800c10303c000c00c4011410313044a41da1201c0703448644c178105022a1303140803600b21070030400210003112149000340e1002d01c001442c0c210003200024403241001c041250140c0c40d1003141c08400d00840401c81240c460280c01e04101900b400c00101c400e50a504a40c5011a80c4841341d01a00542e014001003541080a142c0501080d109413140380d0348003c0c0810888500d40c1001e8204140141c0401103000014001c2000100a6042d68900358a894040e4a154401e032207000600c45050100261414024045030b820b40c0c90308a201400700c8501b001500c0d0f4011400701400c1b0201c000392205071a900c00303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 269701816 1250 269700566 269700577
    0xc030c020409061b0504050d021e0a0f0807060201060506040512120d09120302120402190305160501090503150408090d02031e0606011112090102070e01090501090638 73
    0x1081445084020f01d410005800220702e441c8000f20b60314103640405005005503415150003a0506091a02580810201e5140352032211840446240c900076181c0710410400c0150080c646080c4c011840e1415251411105600c8401103901d4590144166600c203802c0f142100c40840741188081031030410b107418180003040c085154280010348804e44600e541280080030700500045844000010081d1f06a100301444503060082c00b0b0002801490310288000491000040c1643c107907071a607980b0b524050410b20b04141c1d207070003400104204d6030f00201c0000504000e401503c0300c580c4480c5900c00c48940940014003804000c01e00d01c4460b150481c1fa03a00c0650010102c2d422071700c850540503504084040c3d00340c0d460083c40f0028080394040d00d80e10040c2d4500c58000c1c5030f0462281d045000581040c00312a04500650310000f40105058603514060854204001019403420491108035540c1d540901c200b912400070644490404d00d110780c101c0810305540050208809003e8101485007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 269703066 1250 269701816 269701819
    0x506030c160c180605061b0c060d020408060112020604090c0201021e031b13060c0614010e19050c03060d030903080c03070c141011010905060705070203010c0f0509010c030c02 77
    0x307011442003400004040481180c4407520340d03942011a003d09401034440d03601034550804400c1180b032080a0b0000541031a0749440c005442009801c0e40015065034130000c00b000380b241e0045404d0280d543c0c248050341c018416242041c0f031074221355002c01e81c00e01692048600c0c007980c40c900168400d000703404444801c04002080c4014000c03503002201560811f80f807007039039010900b2040302181440011100169030303100904110741d1030030004403003184100004480103502d034106031009032901040d1601174011910a030ba007502d40482d03843d2040d462000200a01400c001c2800044c10846c02201d8011000703807041103201c0c060741030a0354850b00756400203001140014206190000c0403010b03003045840707030304c481d1240c1e03079221504201e40c0070640441d40e000405031600d1684600030444100002c1007075001080308005a21060300f4444200c40600c0821000a02e20307085140c20721030120b0941281c109440e02140349900200a80a03070803806061165009030201031501409440d0f19a950 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 269704316 1250 269703066 269703097
    0x1140f060c0d23040312080f0403050417010605091e0f0412030902010e0d0516270b0111010e010501060318050604080a02030c0601080a12020a11090604090609061a190506030c 77
    0x2d030307486c0c03217281008040441d01c001030712800030520078882c00c2a424061a0150395a80c2800e007802441d02c9001e94503620907050303650f1004001580d40744d503460300b0f1003240c501207410300c915034507035442e102030100900d4807500d040407508220004030302d660594048031481c940000c059800344010390311240e9207010340387d001c005008001d080210000c1d05c01691200018564081a500c81104071520780b468503c032101c2c0c000f070340646003c1c1e0751503200e4100280140b4040a0102c0c2859045084a01240284040d6511040107002c83c0382c05004e1074400034422000740310b86040f15101d00f5210321001e0801407400c2d00008007030030005d01c20010b603424068400152803440d6512031656548240c862421940d14200a540a100c24004580c80075004d400c1341042c1040c0d00110108006034200512169100703039a0301480000c076040303208180c80b10380b0851002806100305085810300600100300c25100b041d11b5554900d40c1e841d20ad9810080304c9055807659100d4840005c8042d090141a044203100320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 269705566 1250 269704316 269704319
    0x1312050d02010606050f180f1e01080f190905031911060703060f092c060709050306010b090103050903070209040f030915050f07060b060301140f060c0d2304 69
    0x804512032408240300d8008000281c2d03909402d40391405040f403661300800e81808062a60103044201d242c0d84400201450a00340e0310710009518000601d5220b4016601c00c0d492400950f04102c6403030b0840c0728502460200d03d03010000302150f00e240080a5403040d1100043c2041200800035503e04034004200c40d0720034101000014280003000080304900d00c9020702040c0e81c2c40c020b104100960f80210f051940351401e0a824101405064002651100700e05945803c3d49094404d00001070505102801c4681881400246012480c0d048541300790040e9004000c09064081200c80c800000e00300801c1654901c10000d003103000d64580603402c140c2403402c12040001c00564103080a01c640ca0700070456131510b20440d180c681403003010020440c1002090115010305028004036841640e003c100c3d03c0855000c200e60340c00a90040c1010b09400d83c840c20285007070800102c8100c2c007a51458105a040d41c2060b07a80c03803140d481c001c217100d00c885000000404440051080142c3d040040d43e441307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 269706816 1250 269705566 269705573
    0x1090e06270a0b1e130209011502070f090506090a0c09060e0d05060903040305060a05100e0406200307030608010212131506031a010e04110402030711061807050108010b040b1312 78
    0x401921400002d1410313a00d0000701d4040343d014903401020f070042e01510940c0c1c2054080044100c02d03814000c29031103001000202000f0414000f0082e081c409404145818407000f4045c4410003c3c0031030000906011005e02040e40c07003028072044554600d0100c0c0b81044c0d90b804038100b03030011400a492802803204201c0000b50020041044a1040c41225610380c4c075090f40100b201c6003034600300003a84035404e080000d820b1440856030010302688000513660303600c1e5480d0309000d2254018080c1c000e0003004101000e034040c0300c0c030801008000c0003581b4260120100050003200140041d40c80880c9440c02014040d20000f16070f003031400701104100c01034603070411000d8004d20341d165414045018002041da000c0242c0e8590285610602964400c0048020013000c5c1d08005c0541040000c402141e009000040040500400e000d1260000c000c0981011307d0804102c1c1d00903d050190701001046144104000c0320204c4019030000b944822200c201c11315524102e17840400c80c00449405403050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 269708066 1250 269706816 269706841
    0xd06050a090608060117030301120614070305060109081b12150a05040b15100c080c420a1107080a050903010e0f0a0818030a0b01090e06270a0b 63
    0x1980d1440f0b04680c040da0b610010b0038156240b00c003100541d40c2040c03004010404100300703030020b4107109a030080740c0c0d4100c0b802c0e500a0140100c41e4031000035200e40601080d5608a01410007a010007005010201b40c24942807140d01d038054405401085465081a9280018002500300100324400c042c40e42c100030181501408081d10152084101c03400410083c580c0762000d00d241800c040c02500c40290610000d40e00c80c05950026190403030104461000c0110074480c5d440c0e405131420540704100d0408060000400d10f90418681ba96411000b0000051000d582c080d032180301c80c040854120130149500d0300038000c00000074202200420001c2c1c0b00ca03080f00190817a00000d4000300001d83c02030003515030b6a66441d0351400c91781c000020700c05c0426106030040600c000c03c0306034081d18461300000300c1e28210034410143c0741d11092600500c18220140a110303a0001d40c0320080940f4100800c02148600e003d50903c9404030503690b20b000380c05018000c021140342c0040603482e5500c0c0a0718216038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 269709316 1250 269708066 269708069
    0x1050435070f2c0711030301080a030e030a0b0c0a0302070b0a0617010614010509060403120203130e011d0a0b030610080d0507170a0507060203070c02040b0105031b0d06050a0906 78
    0x2210050200072402605400141c3d08811660801a1540040540c1441c80e110003500400070041100340004424100b04000d40c024074500300202400c2e034282c00c0c0200703d40301e641103052003900f010b000003021950a00845130000355116650307603100720740c034403d50080c41180c0004001842d842c08002e01b004c030a503c880c0c00c8030042c909038031049030070802c51400c9403502d000341030040300f81607008842540310300d0250040700c0340a0003a9290035241c0d16a00d010144040c800f4006a0000440120034100c0c550548010407001003007114035410304d0030000d2000c50019002250825420000e501d90400382c00040010070040c040c0d80c2682030158034034460151324000c001945c807172421240c6110340b0400440e0303540c54000d0014a08410342881d440e8441e0321415100040100510140d03010810500c025400b40b002c0c0d480d015000b0180e4030502095540280e042e40c1440320900400010481c40c0307080d03c202d50341ca221845e0f950040020740000400d05074220700c1e0000703400303038021580c0c01a9600210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 269710566 1250 269709316 269709329
    0x12010e0103140105040314090d0f060203040201091203020601090c090905040b06010206180303011701060e07030e0d210906061a12010b03010303020318040f090501090209150105043507 81
    0x41c6050041d02c06800d8070815600103000031140c41040310a240098054011701303d000700146044141500d03241002555a103082e0380d45a80001404115032300321010300c1c003c1c2407640195007109903a0318080e4070b4071014896100f00d9500c2e6030015500d2440354192402810310180208807a00b00fa04044004401c11900c0f07501520542c3e0206950075000c940c4222031803000c0d0002d502c0d41e802c0c090383d091703000c004c41d0040806648405020a610280c000031501c03c0006036000034140c0c00d6106205e24005a018044040c021500b455004100c0081c030015080111103e001c10148174070302d4000020502c59100040500c41c0d8003100b02d804500b040101000401126105c050766214440d0b1541c42c4828840180035902c10001410040c2c50000c8041481c20001c000003800c00c5000e90040503185040c5041b113450350740380d903901c0440c41d119880d150401801071803060f0300308603240060054412405000d0340002100034058812102d505081d550101072400315040850445c0c000b5501c1a4501501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 269711816 1250 269710566 269710583
    0x1804110a0905250e0319020d12080a0f090c03061e0501060e03061501020312150303040603060503010e0706390f0506150a09020906162d0809060f12010e0103 69
    0x88501c3c034802d01c1803009801d00100548a40100c0d03542c0c4500702d00420004a0704141c081304000041511000c42c0016020f030703038841629a140c501038902c2126101c0e0710450199181840940105407404500002d4981c889800510703905054075640c40d881d186002e52039120304102c0089201603100d40c50b24142081035003158800c1c0c43d400c4054a541456250301801a881070013502102c1884501c0070341c028800001c604448244480482d040d42d00036002503020a495500070841030609226400b60720051300b02070300c2d01a0074a00c00924191140c00d40d030700b519036040d88268580e190b00e0603030200c0c035140b40021200034181d40382006001c09c071020141c40c2d6004407000552074404038039113400e2410004060340201c13814014500025004400d1041d0480e2040c0000306070b00c2443c00e00e104a140c01000b505080041132824510125075408070903003507501c00d625400026034039000b503c1800f40100d828607190f404c4081040401d00072030210750303c00410f00000041e0000781c0407442d4142d03402220107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 269713066 1250 269711816 269711881
    0xa0b0a11070311060307200616030b090a0c091d010e18120d0b06210108030906090f0d0c090507021e0c04090c080d1d1804110a0905 58
    0x50740300e600e40c1c880548450001826a0440d01d01a40115809455410602c0c40c254414604802c400315905442c00c2541c011818820901c482c41c1804464040303901e814840b141c04113000c51807242c1c0140103c2e0400303440c3d00e04440000d000c3d12200001c1c2c0001044480e61a60301154403440b04800e02c210f8001070310940c04030b641e040f0a082902c0f00c066408005208010080400445e5a4060450042344582c6d8070540c0e54240d40b100c0041140010681c40c0c40d568500d1300c0f4030900c0190703060340711500d19802040500318980321841642c01075201194141c50243e402c40100d424070400c001c0060100c00c04220100305800b00c1c1e401280a448580c0c05c03603000c0403900304640405c420a0796100100c1d4030103410b0318060318080e0420010280b00c1d440b5090490398030150207103800e81034000c1e4004180d104428a2a0191601081603001401c84044089200b112074010000c400540081c0444e484100381d02d800d40c40301c812a00080842500070806490240038141059402000c021941e0514040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 269714316 1250 269713066 269713097
    0x240f030a0c021504201e010201050601030c020d0309051c020a05060a02040e06040b03010f050a061e050109032307030602090f01031509180b09061008010203250309020a0b0a 76
    0x2080c20303041865500f0180c20741c0f40c588600c900b503083c42d000d07110205031042802d40c041d02c07056400214140100144100c0128000019017500d100601460416160200401c0380990010325403129020a040000c0d050a075801c24509210624030143c0c15800c00c0020105882c0e400541c0300d050358064820f4585d6915942150310583c4035602c07882c00c120410401066407231030701d9804408843d400070000180c1c144403074551010345074200c92100f04680c0d60142000750740403004494581c01100414402120308020000e00340c1d0740c841c0000b524014410242c00c40404810810030740d0000800120b0701c51903600c0c41c08130040e40c00955064007607d503030425032020754064021420849e40715551800070320b003000010002081c040070410002d4103403183d04030114200030400d50064810f4006420946056040d00d4a41c0303145c3d038095070351a071041041289202c00e072141d42e0312201d204126a46030010f0140200c0281241440107507005001c4031001815088620041c00d0f070501c1511204025180c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 269715566 1250 269714316 269714323
    0x1409031e0f090105090d0c03030e031002040b030411010912120e091e1b0301030b1602030c0a0b060f040e01061a12010504020915070501090302100218240f030a0c02 72
    0x741030650307003441071101c290302902c06024061000707000d03003505a1403510761034000485a03005401050740c21201858904090101501c1100016025442c0602d0030900b0011444018800ba21510004080e2800b903031154030118000c100001c503908903160282490307070b402c4065685074800314400f000c40000e1410b01c5101c15101d00301c500c0d0705400000c403040e48240d40e0700e8010108070500440414029540006034051406107000d02481041c5203801c550341d581c1e480c252107481c003c0d98000d100075401900c00254108000f81e00c01406411600c0e10307030104003042d1309800001d5100d03003090649540c400055000380115400070805030400c440d2840030500501c200d11818002414440050000c0d08068004150044010f070040d5155204841c042c40960080003046600303944038000c01091560400001c0000003801004514146014450b21010052903e04034000e07080f80011102c401500810342090500305011290748810414409140d9482180ea050200c2d1810030b01400b00c52001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 269716816 1250 269715566 269715577
    0x170309011d060403211109040c050403170d02041a03040c0e070f110c030114010602010c050f031519080114090a0503030612010609150303120c051605011409031e 71
    0x3100030300380c2d40c0c50340d03101114000444e0f00400c190309076880e100315031405288102d21781c2c0d152450300681c070b41c1010340800081d500c030160036104000050209201040b0608170829410801e0401142d4035034503d2080400390065134451440c0356140c1070f810706aa16030740000e41c8900d218080001c109511241d1001c99000140c801500040c00a0a0907190724080ca0940750102c0e6103030700702c0360000c019100080c251490742500b03078801e041c400c0041240c01d030240101030b0320f0b02c03070b40c1409410b003170030311464240500004144e580c02c100c6180c40914031351502c2100b4400484200143c1d050940c540c100b0b240606002c0e4007071240610b0000002e00c0326040401c80c0c101c0f8552001c080c507e551650020040c40d441c0c14030006250795a1210001903112051040d81c840c0580d10380c10704411451820f000e05403403036100011821034103040265180c950301800311001c2075003100c5121580303035141c24100d00620180c0c0b080388410b01d500040c04030700c100000c044e100120b42c03a0540240803080255820050003607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 269718066 1250 269716816 269716871
    0x9060a03031202070309051c050d0305041101141201090c0f02010509060403030b0627040e01020a081b070501020c03071407080604020d030c080a0306030203070b07020d060e010917030901 82
    0x1000072102a28500c1d0003d0007164001d1900071021b40d218000143d80e50092103e170240e0ba10b520000d1001c0003000d00903030000184034107040080d8940f42d02c580b24a1080041c0890400c4104e041c0f11080c800c0f0f820581d240c0d0b201100900045603114913020000700743c50003500d00400d04404a0001461050007214440d0042d400035111545495070305401409004100310380c020401d21030040b000c1f030074421900c0d6500c900d1121024800c42003040c00200c0700e58206003001072b4010444440c10981264155401c24030001405000d0310141100c03940501070080010b129500004c0c2c400038002c0d00001501c070290043c8072501c04101c008905540e151000c4c443e001c00740e00f2110000d409440d255240c05290703030203030404860300342072030b41c1708405a4014840100480d9a45000b407041d41020000030000d070072400b4045140c810207400007401c2070b110000003003040c1d44030120070841100a412450100d640f08415007149010464081d08607003044400071410344c605818a48a0320b0380d02d01d03801400c20b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 269719316 1250 269718066 269718077
    0x7020a050f120910030603300504150809012c01060f0e01031218030609111009050f1309080d0b04050408040603050402012304061106160507050a02040203130209060a0303 75
    0x400b424810080e51054840c01456503034507000000c100740a501c0305c2c0d4012071020440c1c415182c00100f00e01601038008c60000c204088c001441081e005282c512090a0f850030010078a03034591000794050035148001840c4034040010101d00c6103600e0450b481c5103081c800080c000103489505020b100741d01841040d0600d41d4a80042021444038107011022001a19002c0c148241210b400c0a400b910344d03204594890381c4402c0c038001e00c04000c1c110194904120344000b0b00400714a80108200003c0c01094400c061000400c446c540c1c49426114400c03603000001c0c4490000740c18040c0490b0003924980d001030307003081c04180a83c50b040c0b04551143e640803200600301741c20035000300c0080074001c2049060040054000c0c0c40c0001c1100b03d2a2010701c0503c0107652142800401400100c60b202c02c0f05e10b59000d0f00034022107041140c1740700c040401074608207464505a040480c81d022907190301a4002c0e00c00014000e00100481e07800079414020750b40712195454800c01e02040030310903c0702500060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269720566 1250 269719316 269719327
    0x304030507080a02030403230f0a082b0614090703090206040e07030b0301050420010e030c09090a0803011e05011704060519110d06050a03030219080f0307020a050f12 73
    0x5000b0409803900450a1044908064030303075481c0348a4040d2182d0001c081e5281c1010010340400403c50040301311042005400703244140e5580d01c41902a18032003c2502c2126462401d0b00405d203425032040f080084001d114240c0d80d401303040c00c500d40020038a801a0480c0f030009001a000740949521541e02030f040130b01c0e203454080c0c10003082d00c020780984201030300c41002c601181e41c00d000b00c5008a000d0348206407000521200030281c0c1240200e01814070071100030403c1c01c3d65020400d801015410b131240e0045a0340c040d6110300700091070303100804241c1d011002107220024810004410303a604040c4290783da4458006481c0c000c642d03502180502d8010000800244031900542c0c4c0214821028441036860b406041040c1d44803901e205064400208400140d98a203029400041c50140c45040c0701c9800c54030000d4544462800e540245180f20008904200c15001200c3d08801060090b076121300f48060300940b50035940c1c0d001d98642c0300c0c00342c900401110116a0452210000c0181031400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269721816 1250 269720566 269720573
    0xa0e070503060f0d0c0608010f0b04030f051e1b0a0819031110020322030f03180b0c0c010501090b0f242209090206070602070204090c060903050c060304030507 70
    0x7030788002c25064000e41c1060a001080d00c482091100e0148584659012141000702c01803441c1c105030321284205800035000c100310000241140c080d65007220426840346002d05040d031819101c2581200d6001328680b202c902410301254001004500410301060541d9003020040c030000c2c3d074003075075081c1c0d00060100b00103135840605807404944a800c14084182c0300f44122400c10003c061002c3d00d490300002002800302070001d0175903082c402c245582c4187e4205072801480d0040d9102c509081c50390741d443e00400011107010380c1ca9055800010070b5002d2070103400011082e040201034058540c00c00d40003060045882c011601e122030003400340302c80689960204034445140d680411124008400c1c60b50311002020300402c10101c4001241c2049000070448180c0b14a0a40c42800b40300c1ca80344071080160390301300407030782c0b1b942e0440000750b2504001c2c00003600800042500500f100b00050b0300040d4150031208031401c5a0203102510019143c540038442c041c0b01c01c58000b00081c4080207000d001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269723066 1250 269721816 269721827
    0x121090f2609100c0312050c040f0b040305060f100503010903030c080a06150507020a090c020c010908030a02060c2104052a090103020409140601090b09010b1c050a020c12180a0e07 79
    0x481d01074900040206c0900d81000f0031214182c916904c07851002406001c0303605441284c00c010061309104031b1400e031842d1035494444101401000b041000640406c145441d40e9141d50083c0c0801002000f0046161070003600410061f2120404911600000b8601039120b10843c030880300030000300c0ca0801351030ba500b09c500d9408020100c5c0e01c42030b0064042030704040c034410320f500c5040503001420400e01840002d441600243e2140072280e00802001c11300c1540403031000d070003000318044c55403507540900c0144404c41c402e040350b148000e000d8040000303101b0009110700030003600144203140c491415003505068506083d0540c3c000e400e0078010801030400354000c1881d540211401d080881400249a082c80000c2c1c0c400ba1400b501c2d65441901403174030b40d108600414100c106e4610302032110326245510000030600341005a070701c0c400a000299250100c035004110f104c2610a00d40e098104501c040d007101d075802060100000e080c19807401e01e940c0c0b01041d142240020103c5946241d000c076007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269724316 1250 269723066 269723087
    0x5012d060e0d08070506041b18090f05010504030906091505030c1b06010b0c100204120219053105011805090a0b0c0c010510050121090f260910 63
    0x410201410b0460040352540740540f40140c811380c041c0a0504060600c010b4000d10200d41480c1c9055686c01000b02c024015003105011440740c03008981c0c40d040d8104500000c40b4600c001e40035509082c00c100c06c155001c128041503074070f2621038240f42506c0344002d081d517540c003007883d071702050041010407021510071000e880041a1030b2410a00031161120305814800c080e40800080c4e00c6c00b2034400f22600d0305100d00e4500c022180e000b18200b91824040107001c40d040040a401180442c100d108090200440d06015042c0a000000000d284244101c2c81200031040c54803107119441c8402c4880e022409028121059580809d2600100e040c0c400003c010151840300c00380318408981e03001030002c1845503c500f2a00c074505403141500c181580c01d48400811580d002d0454907824040790b0f8109481c040300b5402c0300064540e00100c1d0812074002c11620344003400c200b45500008082140c0701c1c50160111660031881d0018440c2c80c12440c441e40595040d155105000c1060034101d548100310300c80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269725566 1250 269724316 269724319
    0x150609080c21031c0509160501110109060c020d030e0d140f250302010509150106030c230712030606051b0307060906021308160b0906071505012d060e 66
    0xc6840b00c004403218910360011364139942d0f4564000a801c8a2100351281a43c426032103405001541d40d000703e62000c01c00750b07015060610007001e80001c3c2010003507125070700e016400101001409008036000e955070445540e030100086c10704501e01d42ca900d0201d003a8241403c0c070340343c1d80383c490800300c1d0f0706900740c000031581d95000c2c80912030b0300b28841c00f40b940d0701c448840c918100c00c2c0b680c00c3c6090007030039620014100310003070344417940c0c004001058100240c11601a4500011040501d440c120b400740c000004082d00300152040f004022403840f0003d0800e00e108910402064031a070070260f06481d60f5210340c401240041c8001c80310100ca0b5a02d62542c0325520065a28201495407401c04456448500b951056404190aa1104805a1903001030a540801040c43d034244d83c4d0356002d091002d00448540140200e8941c006403101816100c040394844014152160001500c0c0001c140c2480f5508075120946030601c1c0c21075007024211a0320b605134105150140c2041410760703a8121414025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269726816 1250 269725566 269725609
    0x70305070507080d050712200a05040f0e0a050106020f0d0f050f0d09060c03020915211e01061e180f03060f05060105030609070309020607020406030303150609080c 72
    0xb1000120680d00810800c19072140004043c1401170300200102202280c0c20f20340c514107040e014070b241201c01c0e1030542016101496580704070301e82e02280d4501440d40080b00308190070401041c040c401104041c0725201c2d1010810842ea600d180881e0368884042186084d9089101e145031824415031000c040c0d05070340e0910301d00c0d040c10390382d00700015888040070b160b0183d82d510000040110174000d01119058600d015428511000000703403960002c07904440403180c00150704514240304102078030309145100080b568600e80404450b0180981d0050f010445903001c002246044c058414100c500c016000c1c0b002810503804410340e1181103c8a806509180d1080300148080703881d1b01c6040070394442e42c00807406914180d80075091b44e41c00340c9114180003050040040e241ca0f4503050f103921042503d8041003000050000c21424070940c0800b81d04682000b0011017803503011303040020141ca00030414485c45641c0c12080b60440c80070f0160f00d43c0360b00310320300042840c51304019000142d54115100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269728066 1250 269726816 269726827
    0x70807020102070c0b0703020c0a06120504111216050109060c02011805040c02030d05100e0408162f0a05011e090b040306050105031006051f03020d2a0207030503030703050705 77
    0x1118590b13a415844240032050010380c90b001c0641c1440b034040d290406403004201d0505008001d46110000041850341607a5140050244204160400c0a4a6004d01855003891013103083e2629810149400c10700c4100000e00001c0d554410203001045958036941c0120002c102c3d40116800d0344413001c213607018110710f103020170b255441d44691041580c1c242c004540d150f104800400a80300020413410550503c00d00801065420040003030340558407401c4140d0750383c1c1184070b10700d440d844d0402c050103984422021962201e6840070549456698a00d00c281c0503580d00d0400a0311b40c400d000b01400903008104800c85c41281010b8000000b000b0b080c1111110703191171117481c640e003059105a0b4695224001004281000c0c46205102c200b100802c0c030102d42004082605400008000740c1500007210030840e019103e0b9065511401c8640428801035017901900b141e07000c81710601c0c03009100d441408a403100c1c000100441100d0313001004c2c40c11580c907000300340d00512000300705030b003440707410480c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269729316 1250 269728066 269728073
    0x3070203042d1e060305063a1b0b070512030901110d060611120a050315061803070801020705071502070314030c060c0702010210110d02160b06040603030807080702010207 75
    0x58140c058215500810204105901015000f110310350250040c9032510301880019283c050300745110040c050760842c1c042e024185d00004c00501c061304094080700072906001040a80e040d20906141c1c6c3e0310210b04c84c00d4903026001c10620541d4002007940d8005400808507400b040b000d540e001c0020b000001e8100d18031048002c07690302107244070880035a82c010500020b40c1280c184000d4030003580042009101c1e10018001920458490000348030000c07000035a0b501c48601d51142c85580504200d460740c190b181e10b07403052aa4201224424040c508000c184444144291294290004010180706250964069039404c41d051948114020080d021010440444a01080d03000c211300642d40d840074150890308050000c0e000d9403004c40100003200260380d0002c5d038018500d14400000819401848002080d8420300c4020504d5070f00110b04100050105219203061602034280d02c0c9855540400704001c56100c0d0000401250505000c42c24907032286400650200413070000502c1c0c904641c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269730566 1250 269729316 269729399
    0x30309010315050409140105090c030d050f0417010c0305091f0b0301020706051006140406080106033c052217090607140d11120c030f0309010c080108030307020304 72
    0x200c1516071030100c898100d0001024031230a58402d200c40e01901c2c4618540340000c0e02e58013118081000c00c0f00220f500005081c10000300c0d4000d040441e001c96180d2040c1c80000d0187c00c1c0b5040f4a030100b031501c00020110341001c40c40c43d1402c000001120368420f040441400200b210080550b01998207004050000d50b1a01c5014012240540c15040d01890054001c0031584141039010707400c0380900c820800c803900841b016041d16901d0074081100e903440c1c56440d5543d947c915842c207004603441400b00c0c1e42c905074003d00408070500c1806209070703a10603400c40d9050210450300d9007410034101940c0d0100300d5a050100a114200c0300b154941403801000072b281e038011002c290350000051010400214082104099511071828040070603d850f205290f01c500009a50b080c540c1c00014800940007401c0c01120350140031464003584a0826400003402094404000c40c04244c454002151649000054900c55031056006514090415a04d44444070b407800480e2040501d80b02a42140203001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269731816 1250 269730566 269730581
    0x4020f090a0b041511280b07030c0e010e0d0305030603070f0e0a051f03110105040f150207230f011e030504030e0a230a08060901020a02070509060303090103150504 72
    0x100d050b6511681409090241030381500c034100144035811041c0c050a20000c0313007821107024a000d51120902041942c0203d0004010008060302c6200c030800c0072039900b5910103220943c3c60340c0c0d181695140d44006503100440080b0155009030030040c10000280f02d0401140c0c050350207810341c0c200541e1564500c1d04c074811a006010f07081c0e100300030040d000440d031145039840b07400e05289200d284443c64141590340a140030140c11881c4200103094503034040c800b150002c014501d0390110003a40c0380180502000303150307680340c0140904000050305001ca2803107003840d25848000302440c4204c0d1380c200a005403c08041c941032045c003104004074050071400c4600c1d0780102c0d49022440d0314141c42c004003012070000d00c0d0352003105448800e0003c0840d80c51451811714090b0541d203c0300c0314030300004884400c140d109011501c1040c0800502d0901074003c4c0141e02c10030b0b000c49600e90b072200204481c10501315a5641c00d40d10034000c01d409503220350056080011012003007a42c90b80c480e0007007025123141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269733066 1250 269731816 269731829
    0x7230a0f11041406040b010905100e03013207030605040903182306030406020c01020304050708060c040b0a0f03062103120e0d080403020c10090303020d080603030904020f090a 77
    0x3035400801804149410a9064001210100312030415500881c2d440c0a020302002c3c050350b036918402c1c85136401501718070094040104034100f02980036600070005040811468008d5080901307a44c0700134840f010301a450b0b041080b421f80080d50400000b140c5900080400341010b8440d51b0010300d40c0c54501c00c282c4000c3c002d9440890117041d42d210324003c1c0e2000d0340120700000e12540c0046000035030a0000511503400c0396496520380351070400c40042c0c020502c85000f654070010601041040002d20300003103034071140c01da03050360fa40d0340d00316000ca01075441210b48260003084401861486160200c0c0c256101d4200020036030b40301d40c4041c41e84c604007081c2e50209403c1c182c065083c580c0240444070194180001804031000c0034070341d59264800403644400744009140402e003014000c0c0038a510105001d0726880186c446c500e402010207032603100a40150086403c030008042c4640c1d091486404064001c40c681355090f02408006c1d4816140040c4442051022110b10360780c20401c1d40003002d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269734316 1250 269733066 269733083
    0x6190309241b140a05070c080303040309090903081501050c010501080c0a09360510050f07030513110409051204080c090f010e0604020d020c0d030507090b07230a 71
    0xca08021908540d4541c0302c0b00300ba814021800c0d05110b03442070a425282c410801c4807a1200100d01080c0d0306401790100c0100304515070440032a48480010246102d14004e6555140c250f5540449504450054101400003030310000040e003e01445180d1484140b4181f50036490007102d401801d00319442078111958542002c0d2515030185855003840c0081d0689140800c50203103118141706c6005094a1100f003a4507034050368244400c9040101c0748007130307042400c0d40c0701d403268005407000815044840c010f15118000c082020340c0c0c840e201d110300c2030225124105c01c03100c10f40c40390007004114078a2540e219864041c0100083d40c2403120f03082103070000411503256030622429505090840840d240554001000c00a5000340c441d90340e41110001e41c0701c94010f80f2848045006032207003007003000d465800040d41380c505c044006600d41560785995810040b545038081c0481e81d08206104131003596030f0500114000c10100f105511039504504a442e400b640e21003400303414022164001d861000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269735566 1250 269734316 269734373
    0x13050a060312050405030a060f060f06180b090603040b0a151409010608160804080f040e25050d02090a0510050a030501090209010818010b031f06080c06190309 70
    0x2e000301c0341c22030708686424038500345420000401d695429804000d0881a101c00c0201d840904aa101c400a8442c1100f0342103035948811018190304d1040e0701d480c8052804a030001132600c1e0300000d031034040308003d002070b180d919962960440d111024140c600040e94401700c00c20f5a038030801d049002031108010080214020804000310705805034401c00a102c180005c004626031036000342203002c0c501e420008100c2d11181080500c90084010b81d051a4800050224501c80007296143c4614a500581c1202c444c100900d500c1c0001a0118400850000c0c0418150035080d50090040c44c0b0703002d0580c0e8841555040050011100600600040385000441c5400240c2c14080c56000d080710f40425413811103810300080ca204c0c4020200940052401c2c40506040420340010002070002412920450210296101c0c070000c0e80b05450402d40c540000010380035000700d008100e5842c018820b41c1040040d4a111041c41030f91030303601003050f42e100010350014280c40d0700d01511400c1807a1041070315 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269736816 1250 269735566 269735573
    0x1141503010506030607050a23040e0f07110601060f120c0503040218090703030f1e0806010e1e210d0206040c051e15041a0a090b03010b1813050a0603 66
    0x110400f40a65000360091404c1110742600042121080c080511741012040d54241c00804860000b10145070703100000600004c00100c1c1100040c02400748005c60b0f1a1a281c4560a48900110380c015045940100700100310203801110b1803540c040345810060041c83c4000f00090407507242c030724042c0c0858404000d003c1581040030100842d0800d01c80100050b007050075066076681c07190320000f004c129002e010760000c1c138803514281c0c032904603091a104103d8a6210003900130002147e003180050100f00c166406442d00700000303140b10030780388180a040c2482c82c3c02c5c01221005480700c4407416250491510b5010010841c02c46810030a03400780c14141014603140750320001e9507119611820301680501d15503080c884072074a42400455900500307681c110840e400c1405180d0040740324400b880d15544038800b1050092a00d6141e903030366804400d45610f9680e419010a010300032500c901840910781002c0018580180100c004044901d150b0b00a19107509407001120064681c5454a00030401c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269738066 1250 269736816 269736821
    0xd0207030813050705041e05160e101b030315030803040b060a06050912160f03062030240306161b02180708010b1801110114150301 58
    0x2c80701e181da40000540b05903c03240d6561140e40900b038401c2d50f0b10840b05000b056002d00d0ba03c0c409840390803d001510700b1546d050031104c0400388400200d00d50101085d02450b00d643c2d448414038a5844894042e0102c102110914203803480440a1650303c8000501e510480d0450400031072041c43c025540749401d140c5441000350291a50340034030802c04041c016140c216090326044007040d20f41328040b80048015620b0300c8060303406212080400000441c100000300d2100056034002c4006107e01846056000c00c1c5c050202d240d103d00d6442402181c01c0b01e2003900080ca002c6142c5900c5650030f006c5d00e003202026150079544101c49400030764160034a1390810700b41c80002c01c01280030301402d25100d24000294280c6840d00000c20100340030503001240e50402440d2032640280c03455480d03a585c6c8001d9500803c003540ca80c00400c00000001448086900866918510781402e040c400c061080040d1240d007102420072400d9520380c5101031010002c0b20a00b44590042c02c61541c4041040091508 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269739316 1250 269738066 269738071
    0x3101a0f04030503041814010b090f10090618060905120a06021303020f040903020d0e030709060303080f090106030503040b0703050d09060b0f010c0f020d0c090f0209041a01140c010f020d02070308 86
    0x2200c50521001c52000d140c003403c0281101e483e8070600c1ea8440e0a00d001420400c50080c44651000d00c2040069480c0d42c400c003500d059500e141c41307040b00301d60740c00b81440101c1c001d443040000140d505a8140002d00741684000c031510415821251801034030354410050380c001c80301c4820120b11079001041540307090500c1c842d06000c141c1c1e040203041100d0314001d498101d890107040a1040703542e40007504c1e03101000359000500c404a010040d45850b031030005c0c015142a9015140d09001d072001c10200c00c010301c01d0340d0031268031000039841c0c50703d058180c5940340c010510644c03d2110034001094820468003030780608074410301d800145451103804002c0b0304449401c0e024108444444440005012034a07801002034049664070300041e56454600001d03043c40d08a4410181000080c4c00503d4842e00a040d011104880500c0403060b0841c0580c40e00800b44081c5000030142010003130311940304001400d1740076107600041584a00031200d03505036844590a0070800782e00290714010b040d4046400354 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269740566 1250 269739316 269739359
    0x14030403020109022106060f030a05010501030623010b0406030b120d0c030305070e06030a0207050c0d1a15030c0405091606080a1104060c03120b150a08060603101a0f0403050304 78
    0x48002d08800b84035984510081105010321404052030002d540c0410020ac1c8840e409802400150307103038a81031018020612134019000e000c181c0c40101210410302d02416603060b0f0a1050801c0d00e021303400c030058000d141c196074100c1040d03400600449030174401d1191074020798841c41c0317101a8515000b821100c0080c0510304000d903282c0f0200c100e030707211411039411042040d009030700c07030940703017800760410b24600425648410580a00c8081020300502205282c0c0c4400c2c010301c0d69652202c10540e5801040310095240e0041748000c192840c0580c44944c110180c141141c81599501440c10507044150b0803050120315030008010001c00d080c0107020902c0610002503003401d20b03101d0081c015000c864801820f00c04007003001d14100310725030302c4001c15050041818000d80d600b0b00580c2c8896028408083c00140107000041e01030500030b003228003540d1a241802091480d151000410b1a0344240240701c6040800420320307400800d40240c400f850291001d150348900c1d182c401a00c5501046100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269741816 1250 269740566 269740609
    0x3390603020a1101022109010f061e0603050606040e13140a0507090b0604061202090303070804031a061c05120f1b0c131d0d021006051804121403040302010902 70
    0x1d41c3d1505010303000c10800071b014500282626004115405030a040905118052618500241205105000907481307110000754a901c1a2510320403407e48004517000c42c0c00080800007046420007000c04654411080300c030904840300303151f072a5006003903e1f54803480c06611050401081c40028040c480041503190f108018074110700e0040b450078001d40c49410144140021040142d01341c80c0c0480b0203201000702075a40c0c6060607d006c40c100d40081c0404e0340c3c02c0010040455614191a142c54010480100410385412801080861a040c840011a041d00440b141440c404542001030320210200202040d150b00000364282200500c0258003c0b03a5404054070f0f8845451710070b402070450251a6000c958103500d01c0d644406480d1503240184188665010161455404a608408a80480b00c18040c2c250f880c4208005c61307680c0306030a4004803507100400c001440e45c40e0102100070706400d00b01d038048a1b149403a1042c2d001142c003500176075150007448007140307018099040c103404000e515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269743066 1250 269741816 269741827
    0x601030f020402030402120106030803010e07020f121b01050c0301090e030307051611100906030507020d0210050a1515091706040b0601020f010213080c0a03390603020a110102 77
    0x1404010240c00101901555002000c58103645540012424040c03010300203104443d40c0e4501581580e0091142006048080000c224614030224400c414030380c011000b464511158006030b4420790051400003580d20b11841d904244003400c2c014203105104003a01c0503200d6141406440c16501280100b880a03003040003040785c110b4114055072903846d000740c00079002001c1d915151101c040701c0d0417050347c00120007010440c96607006a1080a54040350b400380201c0e00c54409c02ea0f9201c410080c92005600101c038400b50300394180d8000750748902540b1020030400c0e00c903400203090b80c04c00d40040ba5190706007841ca40303145400c54984002070250b2841e24901c0080224116217031040604000c0c18158460302003042a07100300321244045240300021561000b0324000050f044403240700f1308215014040800000d40f804882071300c105ca40210104941031090354880c03160f8054030000b0004881840c0c0c1829081c0e036002c1650014225540707005903140c5403045c000c3d2144c03403011740d0040c40ea8010040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269744316 1250 269743066 269743073
    0xf0c05090a0306050604060902070f030216120b091002040312020c19150c050d020c03070815070810031502041d091e151f0f240302161211060103 64
    0x103850303084030382000c4000340e11703203035800084c01800240c1d00030f0400c9800491100306001050018515441c1320f90200d42d1100c40c1d030481100400a01d1003150b0011140025120120782c0b2010302030340c0726040c2c5064031400d60800c4410000c1340c00030341050704d1410441c1111801035404000905019108580703849031904a1281500d0385800f60060707059880394000c00c1c0301d2440c01140c040340d042c1da0140580d030411398030304070003503a500b409040a88280306100d0700040081010480c03444046070412103426950319041c041d0b0b1f00301c8000e00032020300000d0640c0003020170002081d98940d00085100581e58a24050060b8006042803c00900312140b407402d202d003641c40099022075050309586c02c04502c0702202d003550309004031301c214000100310130401c200303081113003200f00301d0306244900d100c40103030303449900d68125200c2074090040c00c00c140300b200310003118203040641002980307854054508142001c003990301c858022811129035080c0300000f8841a040000c100d00c8507038003001042990b14589 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269745566 1250 269744316 269744329
    0x60103030e03010209040501031b0f140d21030f0c020c180a0908070b04020102010c020604050601060c11190e060114071b03081204020906011b02100306180f0c0509 72
    0x4401030a000d480490070300191000c1d0151840260014020003040d81d40f8108404000d191915800480c004050301151041140701c103481610713641e0529142c200c01e0a81400740d4040041c100b996030034000403a21142c80c0c0503408990304414265404580d80017024100c1c1c0c240c0e4500544038003550080a80000c240d190081000e6099019413002e2540c2e854241ea00b0006165000e400f03880510001a41d90501ca141c40b0840c0c0554800c2e80204120161410220b1311000f040d1801807407904200010000544650004c4006d10302411152300c850303200c2c50000e52103000e00b0f01414032002d11010b04000d0b400308460102c0c4d00103001e00381141e00214105c198040d41c803900b04003c001880c0c147ea51141980c450106c0d41c00383d94800b0b0200e59800d01e4601d884890801101d003284221403d070005025544103507004092198002440d0342031440303d5013080110700590145a0803d80d88060008004504a2402d00030f58007400c00040c411030007904070015582c444005074140103040202d05495101c00c0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269746816 1250 269745566 269745569
    0xf0604091b2615060a090302030c09190b01091d15091303141e1905070f0f05010b0a12050f010c050a050309010e06070e0f04060e130c03020312040f090b030601 70
    0x100c116a40d8400b0300070000030f00300110354000d80b011400a02c44d541104006098074003c0b800c40380d80342021381c00c01202480c112103451404800100c58843d4406d0b030b4104d03000106050508801c0e954881c021448005070a29070011549001000d010f864481480c0414240300c003568026002e24111000e55108408400002c00b000580754605a00560407026107003000c405030010343c001002c00303a005585170800d07860114444a1008030454260140c0225080168058031100781300e6815200e004001c040c8480c251036554076110302d407071035039119803a000162800e003a0300a10305142d400c201d85040d42062000304030760715140c40700001c00d4011095a50380b01161820960f6a69811071890250000300c64500543c4211020b01100300c0d000500798400100a90f045030b06074054004100075a060b074816200411100804640c02a96200e500e20341c8a004116203544e2941d241c1c08245070503814041c0b207034807450200f4240008401c101c00303040200681c50051040780140800240c071140d06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269748066 1250 269746816 269746877
    0x3101a030105060328080c0102130f031203050a022115010e060306191e05150901090308090105220303171e0711012c01200304020f0604091b 62
    0x1d03030b110345000240c030171512425a52240910384c54940d60304602d4041c0d00020f440403200700c03d0050125003402c030244000c2c112030308049603c034100c501000940c01400003a00850806401b00450300c00d202100380c0140030341486a02d029085c0c5400700078200d14016880400d4108031051060400d9a5107201c03c0d2030700180c3c1290b5010440c03e407086803240e031156a0340300384051a03800100001c240c00c030900303200885100f0344509220843c2280042094442c000703510b8049200b080f41440865039250107803c1904040c10058075141070080c201d00f0751401601d00c811300104083e4240304061707000d00000c4903604024602c1c01035007044d00034480d00800300c0445004c2c084040000803000c0344942504240b4040d000000c212039000700c01c0800210074a028146881400403080c00240b00051060176a540c2d4940c005d60000782c1400c05124803070307002130400c0e6400720791010303025000c3d621780c0300910007022241000108051a003401d4400040b1000210041c00a010320890018a02c0d15100100808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269749316 1250 269748066 269748103
    0x506010f060e0418050f0705091b032a040e1e04080a1d0405072d0e060d1103090303010f05090103120f0309050f2a24040503101a0301050603 62
    0x9082c41c07000280484600c024100d44110b120800712800b000c02c141741523580c1a1b07030344205a5118031840d030742c1178a07a520620f8400d030200009008030302d208120b94100c1421071070000803140c0c074005180c03068000350065650070a01d00140420020480406205210104206135151909803130740d580d140922176030b06d41804074003e404010503404100b020701040008004016a080940d1300805070603501c095a03100340021110102c0c800110380c1c00a107aa050b5565100d5800c40040501419402220401240300d444554040902c100040030f548075015500045803258900040c501c14005144d101074000c2d0910b10040c00032503540e0f1113200401d825401c00b8000c1b0f194a0074224001c1c284140c018000780102c0003100401070000c50700c0f100b0944403105180900b42c1c00e4070312071102c2e2005601641c0c040d1106a151000c001e40d0303603c10a181d0980c032041c5013403541e10b801107402d2242000d0003c84075523496100340026400c81000304040c001c1980200481d1400d500031030b580351950390301151200b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269750566 1250 269749316 269749331
    0x603010b0d0f200c24040525090b0d0b070206070216030809040c210507111516050c01111c180308090c040612021c030903230607020a0506010f060e04 66
    0x81c010400d9080000c1c0782c89421700c03851001c6200a00441d0140c0c0e089805005044040101140030803079100329624103184102820b20302416407000304000c06526802600b0001130710302052075244e01c107124852940142600740340c070400003410001039031554103250341c4942050000c01d07410400e072450220142d0300010501c4c4550b8054608903041c600222180d0854100c2d031201000326000380c0d024a015450f01407802d0f0b000c01c44280c854042101c0441ca0501100008865180a040c404000c8200d030509501d802c2400c0d0100d402d507680080c036102c00200014682a552a003844e1400c07001908250412114005140584811441e804060100000381001c91b8070340c2c8040c485415010b000400422036299508000005d074041c1c0c907400e030300c01d0005a002c0c10038100400d51504d103041d455550002d242e0300b9075403400761414004100408140300c0c4007103100100c40c108046401050036030001e2a060030503117411450b19030140c0001c45440c03c13421042001c40d4021502c3c0141210441c0e0100c6c012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269751816 1250 269750566 269750587
    0x70503180d080705010c03150b0f09040b130c08060a080c01111e06100f0803030a020c100603150c110a030c32060603060402060d1a0603010b0d0f20 65
    0x7010707182000b030b16400c2e00190140400c40154807407016030761282c03030500051003500c1c2d92a0040c2d503103101e182201c500800000000c40020b100422055100820002e01e80c0310703003804513180205c420040a030180c3e844210802880d02301680d140d0004e0100d903110062814a9012500c4400111001e03041c41a400706101100500348000e0030510700e01007422204038580130015a684405880034281004064008a0000405a950410303030784484021441e54985c2c00200c0001d42c0201e075000135a01450b268004254403a000d1807009500a450382803141800e000e5003400c03103005103055000d02200b10b0402058000101715090744c19010f0170101402491410100002035660090070100c0e181d1030f041100850206044481c000c501034210f404c0c0760303501b40505940b0407068a0280d40080103100700d80038003041c2e0b00100c9504540e00c076103c2c80f00c600e210101d907040d002a004004400000b003945103914525105130510505045420700c09201c0712071512494019005804c50030074000a00c0c1041c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269753066 1250 269751816 269751829
    0x1512150912230d0b010e040603021c0312050a060905060d030f050705030417011e0e03070b0a0b030727050103171b030c0106180c0e1003090b0c0a0807020307050318 72
    0x25840c40180c403d954a0700e41160500921010307a58074081000051030a4050816204001c241c0e070b4040c04034600640580300d02d0120007801355003241044000c0c01e100050075000d01406018130211040400c41c9402e18061105a40000744042d0040c001c101d624808603a210100d802c0d8101c3d41d0400355901d081c00d0510343d0943c4070315004442122a00100d010130404154071020315580341019018024a83c016420281c44120302554200c1d80244414030214042001c0c0d41d80090010b440068602a240046414180640d0202d41442d895080c55000320b8a6088040d402656a0a0400c007660440d6246444d0b15200d80707a030041d0f15404500e500c0300404460100b2010400c420481c0d03112000c5c046428068450380c05400307084401c1240c1182011058040c3e103500400d141c6600c402203148c0000d121004803103200050400d0380b503840792800b1440c0001c1c001d0080b8007501b0916910240100081d100407409402c05045502c104451800320b42c0110903101c0c0e8100e806002005c2500c504c000506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269754316 1250 269753066 269753117
    0x1030f0209040204120308010609080d0f0e0d05010b04060f0515090609120307030201061521020409060f0e010803040b031503070f08031209030901090302010c05011512150912 77
    0x8000f0701c0014080740000003800112805032195a071456140c0e01e8542c101d81d180d22510806075190300c02c20380a0159802481031800030a054607015500090326000202e1441c9880410381c0d0302c2c0d54800c0c56001600b45030080c44043c22011101d402d08904d000085072000120401d1f80c44050000f040300561580c07204d0807180f8002c0d0003031070a525404100c5030551070760b00003c4102c0242d0f2806400003104043c000c05003842c20925241d807400c0141c0000c080c001c0c01c1c142c40c2e441415603400c03c400326075681e040c0300311000740500c1880342e02020309103141c1d490b00c43c206802c180a542d1041c4000c01c0103032529000c13a40d00c000c08504503100c08220001003032038101031b50410305403007150480c08640003400101404000240c1609070245444035070b203942d217034454201d41e203000a040d00f4051015500804806030454803400000401d0703080880e014100c00515001503540d551903480c20f1040c4043c9070311071100354805071b2040050408541e0341c036002c0700c4107801c0318082c00104403010708a01074201c410071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269755566 1250 269754316 269754319
    0xb010e0a05061804112115060c0109050715090f0311060706020705010c030507030f0e07051504120c0501020d0203090d060c021504060608011a03060403030b031903020a0b0f04020f01030f0209 84
    0x384030703581c00c0c0e514542c100040421001c2c640c0e952019401c06c0724032a1600801540760454000702da81c1c4144819a071141c66000302664840c1c80c0f40700010010820b110052403910700d00c007412004060001d1141300140d2002c19440d0008000740003241001c1c1d0309140907502100d036659100b1062130070b50040e0180c11405801c551030540c200344401d406800a611072100c0d0f0346d04104500444510750211001201000125404102c0500c8503003040400ea0ba00ca0f140500080c2c181a80c0c1d1030800030f81c80c40c048080320300945041c001c204558040101c6941c0c0e84a600103181030050000c00300703241c000070302070182a1360b4a40c2c40c1c072080c2c00e0003882010b08000d80c031a0b084016140604111010323203028821a4901e42c64010680c0032a132140e0b01d00320b80010014041d01d0103480d541c50450203041c8046102e5450f010380342c1030a03414403003a540b07038050307034031a401030700f86003006062207051184000c0203014030b01141e40800c030042e680c011229070070100908001640519024a02c0d000f070240d10880c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269756816 1250 269755566 269755571
    0x31a0907091a210c0f01020312090a050618030304080d060801020a080108061617100509070f12020306011e0201060f0b12010b0c07030f0807081b010b010e0a05061804 73
    0x40602c01c80d4100a8082c940a507a220310f1500c4224489403d000100c41c50b10154100480006140c42d003d00103095007501407045905219030f18110b440220030030741c0c2181080e400a19100308210080c000164440d20000e02041c03400444000f881d00c030701c4000c000500a03400055503c190940301c0e071024002e000c2e0000219180d0480c641c001d80000400e00030140c59200d0364000075001000791403003400080a40d80c0e0005441100000181540c501600c87c12034901c002c00c010489861b050b40c024400d8246640e050640c00d94903002a0950003104011686640100304100050740c00108a101c6510030341c040f18a400b038508022070050055810600001c898028002010800c1b040a0300c40f01c824100b061f040c40e603845003805607138410080e03101c104c0d402511040001c584504440b010361402444020b140c641140c0d40c018003607200361003048002c10b0910349001e44250074420710742d04d18001c0c00c040d10403d40c518002a8840020300c1114800c505c000f90141c0800d682410400c111800139006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269758066 1250 269756816 269756831
    0x10207030b011e08030f040b09060403021807030e0d2f010204080114010803070c0e13020301020a030c11070302010503153d0c081207020a0209040605060118031a090709 74
    0x1141021444401e43d24402200c0c00001c1614240070003107408540c040002c0a28082c588081480036411644015a1000d0305000000c050388a2501c0002580076410241d03d0074234210a0140c2140c4c401400032525610012045024030b4011602243c42181d460700181900b15502040c420404d0103d60454603500204000a4a460540220741010141c030b401c40a980c0e00d50287c281c0d01d0003410005010503084440400a0f0700c15040c5e295040081c03090640cbe40c00009401007400e903031109c400301001035038460440e000244c2c45110f41030004800700191044618540000b0114040509022413034607180484211030740d280001c02c18a4070380020b000920310005980c22480216036504c00c00d9001d010315000d101584505064503009510050395820200351134800c0510000003000e4009510910303804d0005a0703540c04401707100f00d10445001c200da24090000428050b01c0100440e80c2440305041800041da200c030f841d031603080d0740052000060340ca00d4841c03413800c45141e028400c240d280c08c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269759316 1250 269758066 269758079
    0x3040b1c0903121a03030f0c0703050a0b011517071107050a030c030c0e1b181c061113090c050f0a05030106030b0f0f01080703020904020f040306140906010311010207030b01 76
    0xc10611183e08481c0800c454101c803020912010403c40ca45503140c0c0040246840c10034109016106c2c00a102d000c5a03440c0c2d4030f942c2d5032450421501c00aa820254800041103a845144003040101c03c041ca000c1600d011000c5070310b94001c10182908081c0070700c01802507410300b1308001da940100002849007402903624240992409084c2c007003550550b0b0b820801040308000b903140c860240d01d500f041703001040c403003101c0081c49800c006550320789c201c03954a00ca080ca03602c0407440051001924005010002e15160a41c100d40c008542d040e00c1c21014051300007003541c860f5031502103c46600000c0340c0b5802d0520112051f00c107050071008140c40105090307104540c40301c041d40c180c0d0490b442c108045005c100070001098110303010283d0064882141e2266940701301c030459002029400e000d8185004c00700041d00342d0304200e175540038295011408000b8402280981042c1024804081e942414503c40c6640c81d0342c41400040c2c032042000035005c0980c1d10030802d6200440d0007025200e001d503101c25 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269760566 1250 269759316 269759327
    0x9120825110c011803141501080319020d0c0204020c10090302060106110604020d080c01060314150c040b12070203090307150f0305010609060c020409060f09150b010203040b1c0903 79
    0x1554615220b000000005540110340132082d000741c20922121540c50765903101183c16080030200b066006a0030030041c03004124075001d0291444030080e585500d0103841204c80c0c0c100e6407a29100715403120b41e46104803600200e80c0c080701501901c000d03941d42c1c0000a0589040c04480c0c1815901c1d103402e0042060607400704006040e62103d0355a44c1200c040c5464541ea0f81d01c0903607001e940f080000c1c0070f1b1000140c1050090864088400010401030384d2611400040054007407645e01c1d940000003086001882c1c4504d9591080c0060403e905003814007013800a103020304140c108141007008041401d0364020410b90391000d400800312a43c07980c80d01d40c071501e07100013101000086030501c0d5091100f54080d000f05030603991190781d1001504c7c40c1040071583c400321554181c0e00b044c3d03a0002000416040c0c0070344908000d0300040820030418908e003c08218014107690f443d40b503c0c00410b45040da9002c011901100d40000002d91a0705102802015115480ac904c4200c41d00c0c15070304004140d0042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269761816 1250 269760566 269760587
    0x10506090f0913150204150e03011503050609100911011404030b010b0405040b091501032c06010501090f0e0a0c11030c0a020f0f09010b1308120705010b0409120825 72
    0x18104e00f440091240080001e074010781c010507020004006d5000a4103215842440c1822030060010901c500410031440440541c0d801c16110b541040c02000b240d82020001e541c1a0940b1000802c4031507003d403200710b010007144441e14104a07007240d110305050304210680b005550044103d002c9540d460040445560240c0320781c07405281080c099034040e10f081d805503440381c900e041016244162480c01140209074a01c40241304140b0740c09007550101402a02000e00355100c8006e10342d80d41030800240c40040035074041c0500c400688014056098075100c485d4125035200710104554140200c15102e15091802e5480d16101c00700b41030380796800019a85520a00903907540780e00400000920981100100359140c00200041c010006501c90350003c1c111417121107061061182c54071003090030b090f151a404003000c0300c081240c1080c4003080c401e503140300b10112000c200190440d5150403800203100c0120040c44406000529a82d0034030380303852101d10711040091204401c1c07840c0640002c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269763066 1250 269761816 269761823
    0x30c072301020c070609050d020d03051e070507080d02030a08090c041107020f120d0c02040b030303040516060f090501051e0d0207060509030723030d1b12060e010506090f0913 77
    0x841300000780150045030b05000380e420281c00c40c00400c100c0e03001e000803445003c03030444c201b0800b0446031407014400306004084100d2008025039840003414250314000d035039049208642c0208240384003441e000000c131185590f031070070804031666410701c40908020001d031f002c6400504146105d401c0d02c24001c0100748892013117440b4a10090241e09210f0040d5220020b56074941c850321b41901e5940c01070711006041d91008201145c1c01100401190035500180c40c201c6881d40040100e180d184405000d90f40075041030b19141c1b114840101c03005002c90018461103050100003d0100c0c49003010351480703d08035820000090f030b14801040c000c0c0084d44148004d40e00c0c5440c0c00d010440001e03000c0101c0740750039086240500804c689449521841000d50f110440311701c410014800700d0446401045160b46e444800300720280c01286d8040c01d00c89140c80b81440380781c5031990510660103500412410741d1401d03a041c6440c1c00348000400d981e100d810f9101f6910002d02401c02880004d2004400101c40c070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269764316 1250 269763066 269763073
    0x5091c170c01050f0103110f06090a030b1801110405010e060d0507050c120403081912092102061308030603070306050f1015090303031e0c0f0f0c0206030c072301020c 73
    0x107031180302246800c8280802002c40c0c68610404000d85400c0e422120485c1c001027030309203000c2c000d9001a1403031055600446003c6030410822045075001c003640200b141403031780240864100008200d038640305900801d810300414481104440c2c40d00410740e080c9111441c800c10544c104500082c1c00c035041006d4202c010700c075a00142c040d41041c1400d1798112684041c40320305003403035100752550903c0003d00320020010001d403100681000d40c019641d0f07890003400d2848841c0200101501c5800443c1550015035010f0340503c0b85030b1410010a03400303d030b005403103ea00c0303032102000641402c0650744081d002905000600030040000303009140507101301c1c9071100c8401c0da98900c00030350b40544140c00020a00000381040442d0080d0081c600740e00c0454076006200525407041412502504840d1300094140b00d0700720784081d0000c480e9041c7d45810304003000010500d40c0042e03400c0c40010402909500007003410010020f88a1203e98a14071245046130420401d10840e4002d40011000803110310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269765566 1250 269764316 269764321
    0x2040302180f151e04110a030f1112361501080a17070321020a03060b09030d0e040609050910050717040f02030a0606060507020a08030a05091c170c0105 67
    0x502d024144201c911001e0007010a00018403691104664041241380c0c00075250074143c46901540b1004040340d24641d20700080c4c414140203501c084400b0b9101210b030014040000985407105183e680d5071020180403d40401800b01c8100c0b1482150721110a80c503171503144200340c10403400700b102c1400405003a0781d40c5807a81c0c0c41560550703c0d4443d00b009400791600400c640c0c10500d140780184401da0190070300030100e80c48054041a09000350482000c21540495040c1040794540100c80007000500500f07410302e4605000240c48102d11003002e418084096003036041a00e468001000900f040c0e8420041803601031401c507220705e17003444000b0703c40745820300080c4058080c144501054607260740d948015a55552400d42040d1031f1481039a140c400d840440002030510700030340003d4016a80c1741508da01440c410720000c501d103500001d141c1d4006110342c82c40c0703651000540d01410800c0798107002c42c1107124082c8140f100504409000300c681000c1c03541c043c1503540002c040c40a41e000c002c1215a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269766816 1250 269765566 269765581
    0x80105090a02091f0f1d0a060605040b070204060909081902030a090b030a0207050105270f03120c04030c0b071104090b16030f0e150c0a0c0b0a02040302180f 69
    0xd008401c002940071441002082d07141c02001c1d118400f00c07104940700b00307045465140841c0040b50a601540d0002130300000b040142e0340341c0e02ca084c0c104c841100280b000038100900030f042801280151544168017090305c0b030555946070050001455603400c20040740781c0c82d0811000303551140a41401c600c404007407c2d0080c6d48000101c5150076000d81d2001011070400c2c8115480fa80003500200c1c405400740a1b00012a10a108850150120400000850990f080e0301c000c6031000c4080805107030492000300700301c40404000c44d140c000942e41140c0d010303906d00c0341020039406542c0002d0501d030611b5001003030a0319400010030f0824001c1010740081007407c810402a1017444900518045154010995803050003c40e003581c49101d06020031011844004181112189085a00c1d6a03100b5101d01040c03484900c007490300402c554080768545a40d407180030b01200c0e00b25000070f0088050100191520010f9410748001e5503000300303284070b030700030302e02034070001e61f0060300c80043c48200100803ea11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269768066 1250 269766816 269766823
    0x10806060612041e120c050c010f022d0706080124050703080402041b181e140414040f1406010503150603070f03031d09070c0f03120f020408010509 65
    0x80c2c0aa0390075044441c0c1d1107540e841140b049a10903801c024180b00e03503c400240100c060b905c0240b0840d41d840005c2c0907503041c52440e1102094041b03050180b241c0300048684c0c1d01189944a401920303a10220590110b001d244042800c015401424001e4460209070558024040381c121444507203010407a00c0f503614154400c1c45c04284660201e0300400000001a015140c0d4940c8a40000c000050341d940d40002040702204400d0110001880e0100d10f011105003440050040d001d0341c9200200d8000c070318401410380c0d0003401071503000d0b03000111074111a039642e004138005488a03010b40c041c6d0b0a10740380c0459031181019003198082c402084040d4003a00000c1e801d070481d0390040040c90b03000c940c50a200f20000e405407005416010302ea201080042c0580e920400442c801d9407a105002c00004040d411806060b2a091145c1c07031907010310255680c8510441c02c95030b0064a0b4420003041881c068400500c04c00c42050100c1c1400014a030511040d80500700310761500b40240429525941003546 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269769316 1250 269768066 269768077
    0x301060608070804020d060f06050909010e07050918070f0602010e01051b0c07170f07060f0c023d1205040804030809060c01020f0304060605062b150e0108060606 71
    0x1d4440d0005440c45204040094101340003500b01000380740d0544800f8140c4901c000c2d0b21103580e8480d4001c0226017003584400da030210901d80200005404440c031143c0b222150b114076441180e05101107a02c4460159403001d2881000c41190391080d070f5644141a01e8103244684000b6500e0002502c0380a030040c00780d1441101d03850032154504540c804c0c0c0807103e810036001da10b82e034480c80300041b40600d042e03c00c128100d440d1400500795074280c645114541240764206004111264003000c087e0303a00454a804807550448607103618080718440820351080342c2c512042301001501044d0394550b8580d2014000c3d403440d558044e1110400c8234218242d50040d0f400130200c040401003000402ca080019200b1400001c14940c0380c04110400303682a0b070004140440d19400000521040289901c50305008220564185d0306100ca00d921402481004c00729105080c401c0007161403001c401580702c1e80302c1c0304407074100610998843c00b00000b010400d018101c1c0a01c107541c0456590301d84401030340c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269770566 1250 269769316 269769329
    0x3030c050f03010e1e0f0a020d1409070e0c0f030403080601030b100804050d030c08040f0201050f031915030816030e0a06020f07080304030215090114030a02030403091a041a0403020301050115020606030106 90
    0x7990303484d550058002548000c0274241500e40e01e200c103650380b000f44078009001d001c0300c0c1c0050400d2070600c061540181c5c00980311400e40c0d5000c110030701c10b864040381070380d50003509400e1070031203030795441d005801604503600160303845200d009240c111340c2e4102d2002c9001d580150101e40d4002d07200d90342581141c01d2110603d0200d03482e00000b500180c844140300d09117904c185041d81c10081d84401c51400e982003560104091980300f100c40310000413501c074292103503071015071111402d49980c443c00c070070780b060011040c24011440e03015428140200c549040d0410054090030750540e8450300251150666040380e00f580c02011000107801e000081550305894005107810748a0000c508110050303485160341c0780c148908180c00d070401c1a810406148200e010503000740e900e240030b01d001010640d1542100f090f00209000c0d40f0582130b804426034007900e851802c084190440d90091041d98040d0390300080d071541c00c10001150141034204055003171010f036000c0700c0c0c06841c3c9408140c02c0e074400d0302601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269771816 1250 269770566 269770591
    0x507120203040f12020d06020c0a14010b0a17010b100309020a0f06051b100606050c010b1503011205010603020d0303020c0d090602210c1213060c0b0403030c050f03010e1e 75
    0x600c0700c0e1040d00c0b00e44c08443d100800b0000c40402c10765540d0141c1e0001c810702013aa801010044003480b10113030071280107124420082205c0704103c400a13080312280d014206a480d8598005c02440e4001d500c0b90342c5083d4000e240507200000d500000300038203080342d0308038003c280c5c0610000d40c0905071944481a80d103d0740380c642c240010403490100e5030200d1841c0c80a244648181d40060202d540314260241078650f44d100d03521000d00c4a098251101c103400c180c003405001c0c0d8010300d040301c8001501c0c15070703039081850944007a69040132409040e4075000a035010200c080300d1010581c240e80202002c258000549503250404a829900041140b15000258010f084600d240b001c04c240e41c6000280302c00d450f581000c0c81030140c20311b000c100002c2068410b00008504840507408100c91008004a20348110422140c0e912081d4008000c0c2c802403e140d1079901000c00a405001a640030102d0941800c0c0c89680d10b0400120300700c01501c1065031040820072002d445414402080d21412a44420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269773066 1250 269771816 269771819
    0xc05060c042108030402040230010e0f0f06010e0103020909240108130201080a06030f03030603060b1507110301091406060f0d050d0f020708240601090302011d0a150507120203040f 79
    0xd01001c0e602520275410807006d282090070840c00754480103500b003103211214180e60340c1808089210340304050300321020b001d40a402c05c03a0b14440d9065003584900c00386410b268048081e00180e000c0d008922943d5032246c6034000300414040c0e4800300741c100a0144141d6611100d650005540380002a2640b05155000200c0c000141d40a04400ba070041105440001c845e6541d4655160b5030984580c1180000d413160000c0081c4005800341c0c034900e0404441180311100140740458062050010050941d040f0001140c02c6a50030b40c803100d4801d40000d542d01c1d032488001a40b030388400c0115503152003030070340f69a18000d07400c0c003000c60300f904c580c400c1c001c01c0642c0001800341c402900c8140c11000714070600b007000c60400d100703003c070030190860514000305a000000c1d80414800c001000c250400001080400c0940e1b0f0240e45102d6070032905080710000844c45010810b11300d01a084482d00994a01c04821019800f00c01000402d000d42c9181c041400e103248101c0c0c80e44241d20401e040f004d0050300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269774316 1250 269773066 269773069
    0x61110050912250b040515010503070303211e0509031e071110020a1a0408040e0a0e03071101200717011b0908060907060512070c05060c042108030402 66
    0x200440410261604001d0104960000d0071500900c0300712132564043e0700b0b010130400c007080300f4031020303203c0c0c42c022a0300d41c10100800c0d55a0001c1c07201604205c80c1070240d640e500240117241a11198000007032180044240310b043d562403444140d005502e150500243d83d408012058072021200e8200310074902240119080064008590903a13040072040810809951740118004545420741c002d41309001613824040300800c508160390425007803e00400c00080d5600c81141e058610b080c001e094a51500c144010040c180860112500e100c001a240280440c5c0380345110198002d0b40e460481211000d10341c0d03d2090141c210a0040e4403004062007900d4003000124100010301000150511048404108600b080c10000001c14882c00061143d8101881020b5201c0390f918001e114951900f88010564811100c000c1556035203c008592070134420100d0408442c0c00204a8515080c1600000420b078040d104809952010341041b1140d00c80707000c40105600c2e00300f00d803a81145e80d140c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269775566 1250 269774316 269774353
    0x30302070b03161d0316210506061c17310504020a02010f09080a0e0d030905091012030807030f0606050301121b060c0618050606100212040611100509 66
    0x8003c80120704ca00200e100355510104810754400302c40150022465281140c2d81c05080100190390b0b1280d540805464080b07040000d20540000c02500c03102c40d030801001040007503c4c40340400034490290821038000322007000021300085c1041000841e8510a90480142e21441d0103c0b41072548201200400203898241e000d0161912180004034020f400780e040c0b1822503c11800440d182e290114021605503400103035001112019901c800010341c468802524000651058501c503090070b00024081c62581280200100301211441d052000c2c2450054000402140c1c2c060000e0b1800d031184400e0140d501400080300c03200d4440c01d10310303400d080d8011200c680488007616400000d510000038800c140c21004002e06c96507445421511451419406444200c2c01c04049650b422602501049000c1442500300400f1070310030144e0480e0000590800d0b5103035411110b04c00c0c011800151030740d00454646112030b541300580766031200040c10b0380704560702903440c58008d41c01015080b04044011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269776816 1250 269775566 269775587
    0x1c080603071706070f090b37122d0f0506090709171e0304090c0e10050d0902100f080603010203010609060c0602040f1d090c01210615050301030302070b0316 69
    0x62400c1c2401c6074845160302030961085503200342603554030340c048010b040501382268000042c0e030403a610075608014010500d8403000700d1227058503a138a903501407281040301e442d00c1d0107032a42040000449406010001001034440780f60390a03040900044981c03911000b401d2044809443e440007890034483c025040c54240c181140161080d01c103d80c1111648021851054009400856803a41031074011400d03940080362800034820910300055603544c1d00044010000154604241c964580308028400b0748420704c0701940185a410304c0344001c540c883e00ca1944e405041d200c41045031904070506080741b100f4440e83c400030310780613021f000c1d961080345800e1005000704000350905031030340302505200c0046c0c2d00240030700c0d20710380c4841c9030400308840e80c1c1d500060280141c0b01c8140c0c88400030300386410720f034101c8000b0f88940c080402000425071051001c1c050380b890a84180c0305100c00030b0055072080c0402d03405403141900015030781c07045204407881081041d007801065400080140c0303880016 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269778066 1250 269776816 269776847
    0xf0c031018050a0c0303020f0d050904020703030b040501082406090601030b060f0a050a0906050c0a2d05010c0e06071a0402010c0501051f0605070c12051c08060307170607 75
    0x441c14040d0105030700300202e10120b80114403407881070b45945000392528440b1030745448950080b00034802403981210680b41c212100750340241e034840c45032504400900d00200d480340c0c0a840c100010034061400554601c4800a4401c1c4012107414000c0102500100b10358423544030880b000040d006500c0394120083e0200041e0045040241da010100100d0b0040000c0500003071003c200e0f00714041c0c0c0a4100c03802400d85007030061030509190341164980c0703c0c0030740141025035154240c205c4410381038280d1400c05020300640c0361321001031504078041d00e24604454001440404002c03c98036013001151001c0703a014645501030010120300b00000325000b8016410b20074441c1c0d1100204000b8000ca500c103003203c0c075042d0008486003180c1d29020080b5003001c0c1c2003110134004400000c015081e404107940c0a0104000c0131480c51820300d20305504000c1c610740c1c1c00204440341003020340160040c0d0050a045080e00c80c503d44600c1a0111807840141008060f0722400106000f039008080320b00e011181b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269779316 1250 269778066 269778101
    0xf14251416080f1210050d0201120b060d0204090605090f0907090908090a17100c05040e09030d180303061a0d0c09081902090c09030d0513090903030605030f0c0310 72
    0x1044070b00d94184d0030040c2d4504492a10008000161040b401120068403040b64410b0501c440c0350002070802062018116080f59580840526590b5003400e83d00c0240c540c0c0d600303554131a250303250180548054813425010306548004031305c54180c1014014411400352004141440c40c06108202a1041d041c09031024101000155030f070707880b20b41c004d1019120318540c10003400c100c0078180b45814903e4210044180c40d060b07000284d250700c881101c003100c0380020003115544a140f04142144501d4040640d81c501d446044001c10ba080032500052500a8138100415a5149100321416888018028071800100704002000c512644207807441e40c0135140103c0305c6511140c480e4034144031850110f14025507100c00100318500b0910540c1e003c9c03171071003001d810082200c3c0400d0350b8686000c55001844400301d030410400352045485130041c071246005015846003030901900611260240c0c9000b8007a101c5a440d05181c00980140f0b45480640188980140d42c0c000c04002d048840d681d900040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269780566 1250 269779316 269779327
    0x4030606080703034103090d020a0809221401050a090b0607060f02070212010516020a0c050d030c050102030a0603140a0f0212010b0603090d180b0d0f1425141608 71
    0x400281204007402c0740c48a00031b44c0c90a00c0200c032480c03c001402080c08642c000b565100004000100b03a03040800d00380d0b400707900003140ca0460280c07200849041c01c030046c5450b51418512034021811030407902c3c15075503000125281c0d60500d0a544011100c04e030404810814000050030940c0801a0081c03481e400504204060307000401650616007203041c030381e444009004114803800f0000c000407480340010044050941c0d1242a40c1c1d22a02c1118840d40c801038411003071501910344186955405802190349151108641e8006c0405000980c1d84400c0c0f8402c3e0b500e038003000151002c5d5a0780040141003401082e600300407140801d41c0c0b13001019521621250f150b626010050350048850802802c481c0b039504200400a49200b4803580208420140804c022400340044402808844074085282500c44401801500c3c503203403048508030b0a20100440c0c0701c200c480300c10002d04001c01000100c070410320304603086003100341504480074081003200c007400d880160501103d4800e540590500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269781816 1250 269780566 269780657
    0xc022a0a050d0b041709090a050a1b090f05040c02060f060604150210050c0f070f030c0f030509041505060a2a03210216060b0a0305030a02030403060608070303 70
    0x180c03158004035440383d40041484100150054103440c0d65103885035460810128800181c420f400c01703001d510389903945402049000708560410381c00b5a189a80c5c2d20f11021150710000c00c4172440d48a12555080481e9000ca494903050107000c1d54a04290300a058a403158000c4034003051018003941e60209080100180403d0030300050041c00035250090004040e62480410584038024030b1b041d8080010082d415804400ca001d6901c1c064101395003803854022450162840c11000e1030140c40c403280d840ca48020107510100503c0221016242030002c21070070455030b10340440c01e0080c1d80c0e009006010302e502061142108104200c21271901d00c000c402a4070584081c10100c03002500000d801740c40d0103000d41900d007000c2c1c61220300e4000452509c2000040003800140705a002060307240c640c1c05090a9a449114000103160001c0540c0d646858280c000b0390f4a500901c0100c4403182404070029000d01d0100ea56001c80390140c999000d50b694150b8542c00912d1180c1806095100c050b1045122 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269783066 1250 269781816 269781829
    0x2010605190330090807051207030f060207170306040b030601080d0c021f0c0314090907140d0606030f14100302090403091203021e061e06030c030a06020306040c022a0a05 75
    0x1030001c030780b10f62aa480c05c10560f0f41c14103902d504042d02944c00e00c0b240386011040001c000c422030360410011145000d0ba0324018006e4464050080d147c100d1800810b40c6008481c8001c3d401800c1c12501002107c003100705042c0c47140400d1084170a540c1100f201c400c0841e00480e05090460310041c8000b0800448203040c0b10811001d846000003d8500032149081680141514440d0100f00c80643c0c10020480001095160020550020003402403c582d00030350810b819180070f0080d4540502c41240c4400000f1b00070454503d400c1c10680c00e21468040c440c02d403100150003010441d50a11038a8119020303c0084040a0811400c0042009000503040c5a001c4c00c031203440d111741e0240c202c90795000000c80d0303111021446201560010418091411040c0300d507142100c01d4100b4030411541c0d214002070602c1041502607815020760b079050b07000c212450380207510840c01140c04108000000c1400c0360380f90900c03c0c440800d0628850000d49000c00240c400300000d1008084408082e10380021850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269784172 1106 269783066 269783153
    0x51501140411040e1302090c0a0806040504020f030a050601091d0a020f01090b120a1d060406090501060302060f0304030f030e0304030813090509030406020106051903 73
    0x103580b0640c02960700518403a0300c0c455035868003800c4140c1c81000311304100d1003201c0701e400141038034403d081652208092907484603116034800c001d11004040181050307031f0007550b00344c0f0415142d50401c20860344038450720240c801d551510051500303981c4131220002412a0101514022000008411441a0301140c0c007802109083d40140c2c1d2403c11074110b62040d400009075a240c80e4030101c03a09000b4000c904003045800522000a070244408110190032600200c000c50089038070340c1c000c40e000a000d9000014050750301d40c0010190390050312075000040e4003000304002c0c10380008401c80201e220381030a1010081001e032140d1648030780c0c08010301c0741c42b0100d00800800784c0196104040c112500c010009401c00c00c806507541e4200f842908010760034242c01081d01d0a001c00000e164240741c564842002d070a41ea601e400140c00001041c1c4d80703422102c3c3c1e5040014a50f000c03001e = true := by decide +kernel

theorem cover : BRFrame.Cov 269604316 269784172 := by
  have h0 := BRFrame.cov_init 269604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269604316 ≤ n) (h2 : n < 269784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
