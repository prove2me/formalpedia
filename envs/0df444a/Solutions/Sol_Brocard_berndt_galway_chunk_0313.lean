-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:08:27.058583+00:00
-- url     : https://prove2.me/submissions/7fcf5913-a9f6-48e4-9690-451f1bc30797

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 56115111 ≤ n < 56294967 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 56116361 1250 56115111 56115127
    0x501020114011e0308041403190506060d03030b040c0e0411040608060f0103061707030b010f06020318040f02040602060108010c08061807020a080a020a260409090204110a0f0306050402 81
    0x40300340605440c0c864801020f203128099610044400b2a84054503008000901244c07011b4100700b07501744581d0507801c8401e07000840e50065100601840c1c00391040d0009400718040d468120000e64000e8060300d800f06800408100050844030580440f0010038018500c0115030b09240c054524510344a040742400c0c20304d000005000c0e2040240800e20496002407607200e140c5c020741c0400c2c081c00350b500d840840f40d0844100a541c1c4d203800c1c0401d69499900f040005613007100e4000078001d076070040e070241d41840e0350461400e001190501d09594042d8654060800b5203140b4405440180069801800785514240240d4216a03040364074130b042000400c10014291510b0002c100c6000c5c01400510107540c584008074180f0352100c0004000020005030031288075030008409586034003445400c06440820580c48601010b00b00c0c00f10a03045007400b08010707030380c1554041c07481c40f400a0070205140381c0008003102076620103102400480c3c0e00000c1d100865625203d10006070005480441ca00488 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 56117611 1250 56116361 56116391
    0x10f0218040209030709050f09060622050907030b09030706050c090a031212050c07050d020f070501111504060618091e0f0204050406060515161202120d0203060a05010201 75
    0x4080c4034040e40c1c00065014682e1820498107000b000591810011801d282250380c400700d6003078030f09a40318404c000101f1311914040200300400c1d1032003070321459079000031030900740548001020680d1600821000001103007040c004a44100707107120185580d500d16180003400c950000d040c03545517803400e001c811503c0e10388143e00801d0f241c016024405110b10103d0071103a4446610000d20f0450626050000c2c611081001d005410304c02c0c41a1440b03e400010101e0740c40c00c0034806610f45034049081040780c1d50150740800e0360011036809075034040049820ba802a2501900c0c12101e003a0b0390001017000111091286854100300d003000c0c41200c60603201e240d01440304c00c02425444084101c0c0600b00704803071100c07280c1140e02800600c140d10b49030a00700000e00c140d200c0c0e07601801070700e44e104984c40302410864007110030b0200307c3c0c4010020354991204004241d02c54405501c00c2a060110941480016003034a40b50240050303900c0c80d0440500001c0409a40414103584c145502c1d00c1c1e514030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 56118861 1250 56117611 56117647
    0x8090303130c08070b090111060f0406050c04050d0507171c030203070903050d030e0c01030608030d1a03030705010501061425110a03150b0f0108010b09011e0c020102010f02 76
    0x260728806040080905000003200043e0344003c0c0680f052000010b542941700f0054008500d090700c2e1442d540c1002c100e480e8071240120b0f81c2c1d00c4100200300008002501583c020b50b0051880700105080a4640c400300b8070b2070200710000d44d116440702c0410400c0448100400d502c036039690000d0510380086000000c1c15602d4404260189a00400001c1d03640d44036900301401140c1000841e42d040c0d001020141c020b1030701001c894094001d107a1800b0302540207003c4c2408031501ca20040d45014401c0ea4540000c012044814005058042e040c291b01c1d41c040001d840c2460046000041d29450204003810b040002d0a0344010800f0922901c00211010700104107441d4651010100400b811701e40303c5048007080020560000d40054007009001d8204100120102034050400c201c1d03642004000c102e2010990b0700740090820401800643b405101400c1c01c03003018108142c40c4600034144030303c000b240281010000301500400c0d02990390901a0b402d203403801c0103045190441031580c89190b21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 56120111 1250 56118861 56118871
    0x18060e040b070c0803010e040507061107050609061605070f080a0c090e25180b03190c0806040605040303290f06072102070f0501020703020913050a110102070608090303 74
    0x1c0d003840e00042640d4000d00440301425845042c6a07038030342c2c440142c1e034003201b0169804d403820310940c00086900ba0040c0102c10040c5154030050000d189010208441544245540b58019130180030044071410344013010940580b150020341011800c040307201c44000b140398000380310390340f1240c1448003164100b50500142c0e0140c0ca8049500501c0320300c0f0601c0c0192014040701c04c8004524074941c54401d9a4081c001d803001c4a03401002d82c85800182015200c444030800e500d600220340d07461258240ca07000d0310200b0721402405900550360030403503040c004126000e54000f07488034100010964148150a81c5e029050307040354525500358504240b10b141480d801d4003c0090340060074980c3ea42c9000ea440c0c0d0350f1720251580c3e4611211030740454822049100c1000b52068240200d110781e102d043c0c1c80b054a0060f8000d01d070103881d43e0208504070380050001042c4150a00d041404644240303c00c9a00758010b04072500d40700c0700c100c0024603000c40c0b94444801c00080109101c1e01d41d0005c03088035040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 56121361 1250 56120111 56120123
    0x3060b030f0a0b060906030c100216050901030b070305070210060305010603120503040c090b0418060c08070c03050a0f03021c0605010905040c08160302040521060f010503100c03061505030118060e04 87
    0x5070b0f41c1d00340400d19002341d4840c050b5110f442e131a84a24525030001d00138411441060098060316a150244810b0031020300009202390744802c001058140300303900099004840d44100e50030084000e04500440303800360800c3e641d80e5100c85c01481401503025492069032500d00d00303545589800d4440c1c100003a80c500420703e941e0b8440d00d0321040e5994580281e80d1110b20740c151100494900e183c100001c1c000c88014401280207200000e030503602a180c0b1700d24440e05601e405103081e00c1c0b040c00f02da1b0580d803107030900241503003072040000004828a2001ca08401c40750000385541c140000988065555400580b00d02d041000040c50143c1c00955980c00011160306080004604a400ea001e4002d035040142c0118211124241a000c0100d00d45203518042e016908940c43c0c5240030900170409000355501644a420900c0d121000c4d644200e00a5080389800542c0a840d459030340701d0011440740c02e100017107021005000440340b94240480000e04924100241440c24000b00c44c40c08e0010005455 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 56122611 1250 56121361 56121379
    0xb0306010e090603120c0105010503072103140706051f08070b0a03150e090706030b101b0302010608030a1101060b090102070501050714010c0f0315030302120c01020c060103060b030f0a0b06 83
    0x8180c03000c110855240945c0445d00b0340310b813402c964203402030134240b00b0b03903110b0b205424002030141c52409d40d0000c1401c40c60309180e2444d40948040e07902da0f505d00444207940c0303401c001d0f5401160080c07040031700802c0c03100e5400c05182407287c0c0703000c45003065400c15000c64011b0141085080d09040c1290849410350802040407d044034242618003502e500c20007055a40c41c04104800c0e40c04640482618803a0700c0c00c000d64100e1200b8040034902ca0208840031500300011310983c0c0d0b2030f44c0c00e50035010f842440045030040d20350302d501e4115008601d1100205000c1c0c02400341e074030800e001c0c0f83d0182c42c10780f0465051418440c0006d549011030310410f03040c00310014820f42440310444584081d411582c00a004250346018001c1c502c1d03000e81901c50000c0e02c0c100c003080e07810010b840d1000490360564000d000d40d4200410056880e4000100001159400c01c02000e04502c207120080c000c60080000150b08d1100c98103250524500c1401c0341c0c0e050708410350310400158a0428180c019500307541e8005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 56123861 1250 56122611 56122621
    0x150e040e07030503030f01091811120a2123030c0f0a120b060a020606010815040e0303010602070b0a08190902061c0b010c030c08070318080a05070b0306010e09 70
    0x1004054020401910340502070010050010000083d4040e601c401d020413556030303903950b1400c119140807041c540c260305109900c00220b4000309290a444000801c10342114a001020515102e01144101e4030881307509080307007542201040a0490000e142040d803413101c050b480d20140064250490003140307102101041e14180998142c80004460f2203142c0e51702d00401c400900244a00c940590480c1c0c24844200f006003040d0b0140c80300100d05070020481901d0301d5005450f02c01d001030540070b82e00740407000a0f0003075650b030080361040a05100556034075414580c009082c00b0325a0080704011004215020607181c3c0300a045620500b10740d444404032400f41c0c0d207200034112004000e0360100011440108110f10300300940340702c90114008121000981005640e2580b2008000d004160225810004030f94448001c005180c4280f51402403442105030540c1111102e4000c0007480d400f1444c040d041000800403030000d000c008098034114900000024044042a05094010409200410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 56125111 1250 56123861 56123869
    0x3130e090c0a09020301081c0e09180706030b09060102070806011205160b090414010503101503140d030c0212040504020c070e010803220302010e0607210305060f0a150e 74
    0x5150280002c110744401641d5500e6800607410070300500c0b401d40505000d0b12041c2902d80741c844080c186a0f156000010314440c10046216001440c5040c0194030443c20300041c2418003001004d070005882c0042c526810b41e0900000743c0c3d0042000b81594003074a024880344000003030310f50444400c1c5000444011507440c1c82800c01512204070076682c46143d40110314001d8070000f800e9048415070741003105004090ba107040203c8203102d800e030503810140c3c0b02c0a17a407040da045502403803441d15001c002c1c180e40390b442103e90544041155420b1300410f0000b040c103981401001c40d000c02c54030003070075518410714040349070b8441d51165500c19a40045d1582e03000380107100240051891601605075582d582c102c440c0c503540090b4000c003e00440b140c500b1541d25031000140103076601a51400644408a41801501c1e231010708151450b14201b1040c17040a0703041c2c0061001020b00e69000308160401e40c0601040c80b0072000340314829246604144229240d046181d4403400d11450015004c502400203e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 56126361 1250 56125111 56125123
    0x302031c02010209030607030e0d0c0804060c02030a020310090b01082d0c090c04060f11030f0a0c0c031a01060c02010c0b060109050a03060e06010b0f0d230f04020405060303130e09 79
    0x30f290107019078400c00c11041c8d055804120750407004001d0710f041c0f1313500b404100c5000d281c603500240959014081800040d202e000c3c0600003920240496400031140d8002920b080c0607180703640141c944402c259010001001d00460040c94418000e0000c4015403080b640c1060220400c030a900c002d03890300c0096070740108103100444030082c000940a007806001c0c07a11591050203900301007000c500040d1107242c8111150300050302d884018508006400b50300307c92540c002e410b000100107190032110007244520a80c800110b200ba0f00a00b1000c00d40001d515000718142e01020501c940a60300d00d0150340c00401a00d030141c0d1001c0498000d58403d4016104e900c600e4100a4004140000110401c8a40d5000002d8003500c0001ca8160b60b07640c80c00e100062083d0320305400f45010074000f9402c2e412164011010b4210803030305449030a00c3c1c01f182d022207080104c441c040310310a20424072095007024400c0b15005442a8059490031100c10046900c0460600c40e411403411003000290b0760704410300c05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 56127611 1250 56126361 56126377
    0x5030703031d04180b04110604210f1a01060f0804020303031302030f010c020102180f01050d0504150509010902100801051813050a080d0b031f050702010603021201060e0c040302031c020102 83
    0x8801c200c10a0750424450b070300b80c100c1b42102c40700e66012600e0558940035042d5012100590040b0701c248881804025440c6000b504c101c80c45850310804000041d05034a0b6402017500c11a5001d1242d032400340000d040031250044071060061500522016132004000c03a688110806141d20694042e880881d10301400810040c015520b00100c45030040d07410b4009003030701c90907030407800d039142100700809c509000c000a40b240420420404106c4180564004541c002c1c01600200da22840040030321050b600100d03480309250355100c00704011894003401d0307416100054584841d056043c58042045c10110310300e0b50304451002000552507500b05452010156030000039103405000500d00101a5040940400e00c0d40342030201c165101c2c00d00180e103050000c4c005c0381c062200c03035488954000800c0080d00701811035403200780100268444484e80c0c000700002e030000090091a000b02d413101410082d15001083e0000c010400140c2e074001801c0c15900841141600340e04e022071401d0f4028820390704 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 56128861 1250 56127611 56127641
    0x3020306031c0c02090108030a09060c0303090611030601120615180308040b070203060702120901030b01020c03060108030a020c030f0a06020c190804051c1a060a0b04090203060a05030703031d04 85
    0x440b0607601075100340d109064501c2901c05d40f0960762103000d4543c82c0d0040d00c2c000740000d0302811040103040e00c2000d205050070f0080c1000150381007a42ca0750010740310404501c034010071000083c4851942d010092036040c0100c20743c00c00000382046440090f41b2001ca41c0a400c001003c074a50002c1d55001c1b035030f400150340c8016101e41d00c80d994880340c009900440720a074442c0c000c140004019a0000c240035a03202c0380d1950040c076040caa64010b4004040300068541140f042c4401e01d0b0740754404201c01e80c003800c1004010b54a507040080024a40549000d20f503020b5000f0041c010240a00052a011031a520000258445803000b0000d4070700819038032140c00141c440c0c0142004e00c9188030042050714810754290b56074664203445001e2120606200400c940c8240c03187c1d2401d1400302180a420a0004142007002a9501d800c00521340040c2c11008070303264008207101d91841c4c01c1104100034101a400f9000c80c610711f403009000f01c030480300c61046600d1803100c488000e035220b50140b0f510207a80d032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 56130111 1250 56128861 56128903
    0x218070f112506030605060a080604110f03090616020f0a0f140a0312110702090f07030b04091109071103180a03020d06090605150a03080c0a060501170601060302030411010302030603 80
    0x141046019482c0e4030070341012074070302a000309080c100041100c0c074180b09034984180d65240d031414480104200221001c800100340040e07a601d0011100135401040341a006000fa4141001107038262850720740c084096501458030343c1c81c41c8401060700c0c96102c2d0000c84420400780e10342480d6481048842040c80c550080c560080d0400d50005a00c0c040340c85468800c01c00100b04007012481031040d0000a980a02c0010000b141440c0400b05540c0c880718a02d00891400c8444003c00c0c1600e5200030304540b03e0849107024091402c141c0c03460340d40050189414185800c06c50f1905407a0f20651606130a0700d080ea0702c0881d4036480b001076441c01164040e103440030004090504100a10401c80b00700c8943d4104404070300400603040303c5605600d40202a051142e1a603610316542d50711120801810303009800c81d8201282092060364000e01c0703547d07503094811003498034040c207000058204406162040c4113000c045407400e038886c409000c5c28280141d580d16103400192a00c448881c6c90070b1300e2288a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 56131361 1250 56130111 56130163
    0xa05130302131a040c0c080310090905061006020601060503010302040b01020709050c0903010b24031812030901050a0c09120c120b0403020609121819030c0f050102010b0306060402031008030301030f0218070f11 92
    0xc0c03091213078403000000084eea44400c41280c40da5820300ca13100010f94203200500251400d03500501150405004031040680d5400c0c0701803e680003111402650702002c210f900ca0350400f0300581b03504513001c60710710406c80140210a10314121b09040409140808030006210808008500c60282c41d5541201c22041402c47c8034641c070750084444801550905c0e0120354600c2141c0903219040c3e4079070315128541800c06040340c000761400141964910524540060b200100309402c5848500030800034189151604010340b800b0b5001d00700514581c04466070320b5132440f00700142c6201b180304007003900e4415540400546030f2040b01c042e90360391034000304000040280b0300040340c3c00c9a2105404400103980e0300d006a08a6512450581c0c141e00850009207031071906a00131540b016509001c0c1c8007940c1c031445aa86103410036003085070b0682e0b4bd40000800d5250420b00c0000d400352426124a4524004000501c040e410f00420003d0118102c2c07405070300ca40602900c03c80070451217104888041d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 56132611 1250 56131361 56131363
    0x5160e18160e030105100303080a0b062808011202090402120f06010302040506030a26040f090506011205010b0a0c03120c0201060509100305030a05130302131a040c0c080310090905 79
    0x10041ca0040b40000c0e0300c150351030070180112440b503150034480b43c80091031501c0075640c01d01c0041c001906c090366602c1341e13031103542c514018000100b80074660a440310b44206462600b404191009130034080b81d1001000900540e1050b1f491866040c2d07004074458880c1d10100f80a442e03401d000c02c500780258000e10858080014440b0704a0340219428005034031450309058499003021009400782000e16900500c12900c1c10750704250003614100c0c0c030b14084c1d0301c00740848030540325000380e69a581c9460502c81a0342e40040b0100c5558904402005103500d40000c0c4142845006086014804d45421850905018110f07000c9030b0590944140400076405400034020809401030900c1075030000c1c040344141c4100850001076a074000019860031002140070307682c0340c2241110412815544c00c000c00142c403004981680d5007400c0c0300224110800c215140010400441c07020300542c60b00030f00c0017450703070302095102b0241d4000d861941d80e034642c85042010b02c40f240d04540351480c2020740182c10040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 56133861 1250 56132611 56132641
    0x3030609020a110d050903030906070f0203070b281e030902040f06030611091008090c030a060209010f0309110d0f060c0e1306061422090606020c0405160e18 69
    0x16403e0980d5042075040c01c06a5240c02500150340e0140d009002ca00d00d40d051210080104a004001c0c0052102481d40028a04a000e41000c59422000700d40c035048910640c0d000c01d080310031440171518250f40e8030001005030f40c0785400300c9054080109402681030082c1e10035060b03190090024407040740b6886220b4054605880b0444a25280442125607000c40c03105440e00d40e000103204402480f4034120480d42d607500030744103518a0280c140d0b0b040d9995402c11007008601e1207a032001d80c85407420000904a402d55210791814181410468400201c84182d00541c0410031210700110422034201520f107034150000040620785452121010b00d900081480740080703049030f04d0511341d1208400744043e941141f00748070204583e1600d00c1b81d0704103102c014200104c0701c1c1c04d8105c042c02e0490700d501d824007250f6010000441d6141c1d820700542c1d50510880040c4001940c003404282003d030307400740342c1c06407030f0311114100308400307010031f005940701d02c0c0844101e050544204003a0078000c6030440448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 56135111 1250 56133861 56133887
    0xa020d0903090602160b0d0e0f100501061b02010906141308031905040f0306020a030b0d0605010806010909050c060702030c09190f05190902060c0706020601090e06060a1203030609020a 81
    0x112805c5600018850245000300548900296603400c0c0071440324180083c001440c000710140c002d4546185821208002c42c150300c90f4210070100720740d407400c6005483c907450f56040d00b80344100c0c1e00156000d40d801c01845001c880b6149030061140448400c0c400c071074022481c0f14a074140c0b03102c9000400740c100102903c65035050500c5510900046d90003595544030740d201d1020250707030030441080410850780c003a1520294030b00300030482c4a004030028055229150f821541c00f5038410060200040800100d40034060701d80f003c2107140896103886a464032014082482401d0009075441152010300260031500b801074005441410000c1d000c80004007620259505245401c581083c43c1500d8052103021389407145c410b1a00001035111781001d032007000ea00b640c02940c02c01c55503c081c00c04008480c010001540504403030350400d2103039416170381c03002c4034000c090b480302c005c0c0f03c00c50f0380e9205003c04859009414050f0380c01c2c141b4098020b0030303081d400a00c0310303031010074140c07421500549048101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 56136361 1250 56135111 56135113
    0x702011d1506010309051504020a05060301091a090c120606041502030d18030c02010c02040b0603010602031b03070201090605030a0f060e04031209030801050415030b04030201091202060108060402090a020d0903090602 95
    0x3540c0c40000442c105d82d50418090000d510540750729810498412500d0781050001d0010035203142c80e4008109680e100717a00a0001a503a40d1218002c074103010300d1484001030031201c042e568144820950320758060342c0780700c104500081c00410599940c040844000b40343c0c4400701d503814180309030080c0d140d0f000703c2002c4483e14100005000b241c612124581c101e40c1d49920340c02c407902802e0700111922083c2c400120b070003613616000390b0400d5071104007a50091222343c0c000c42d0784c3c0c0a00300c6d414003a01c4040c1c000c8451540184541c40040c3e070170101c81403c5d1881841c000c0d403070b6035070410790381c0140c02d16a02c9140b504c1d103411404181480007031202403145000391210130020a01c0140740c01240c8087c00e000c0c2c00500702c04014021450315170015440407240140c1e040c03c1036143d0311504210340c41641d0880150395249441c6d0100b02800c03903031600c0c041a50006d00081d42c035000314152240e400403c002c0c440d0003594005000000c950781a079207030f4211a030081049420343d14002d0442030040c003650000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 56137611 1250 56136361 56136403
    0x302120c03120403080d0216050106080304151d1005070606031b270213090203010b0703090e01060504060804020a120507050114090a170c030303070306090c030507020d080702011d 79
    0x6020b08680c21102140e03800b506561030010302d9031140f40250002175150003907040c10040c0e1004200d09000d19000380084201031a40d03145400740000001040340c1c006018841c0a148000001442d8036118056513020380c0d0b4240b0143d4405000c0b107080c400c212004020300d1030548048180031a401c124103d040c941c0c2c42c0003d10302e8031501c06620300b11040c5c1b602101c0204c1ea502c10447c15000381c01400e0400410141400502c1e00c94071803005980007608441100740c00410703c1c0d4140355100c60084010000c1c40000400c55040400c000c01901c02c0c0c0c01000c050105a001240854a0307400d0420002e0030300c001006440c0600e8504a9111040741c0b007070300e00290580b01c1411030b1700200c0d4100c0b00da0700b0b00140455029403400790008400904511049403d000303081e11101980c41c240000d40c440c4c1d0090340e00081450a28492404841400c00744400f058a40020000d0b090303000140000400c805041c0380c0ea8a50315464100d01400e814246800261000510050340080004452116444a806902c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 56138861 1250 56137611 56137633
    0x405010e060702030a032a140601090612060b01050403060e0c01020f0f0a26031003060c08070914150c0c010809061303050c0c030106030809040509010902060316090302120c03 77
    0x159600403128040c0d41368000301c001e0700000340580c00c1c0c103480d0088241c444e104080070300c1c07100d86a421000416240350301c0f459440e0084000600a030fa0241c815a50108856400d00048214858250170011308446d65982c80e0409a070052080c1d40c01140c4c03180041c0300340007280740c550340c4500750346485501601c14801d41c500c04c8000441c3c02292080303810010003040c0d036540c4902d0b0083d045e0800100f02c0d00c030b44245120384402464002d51242080f00300e0b0102688c44e624050040f00c140703100401c00c02201c1c03014010096848408142180c1401c6003424010403440c00052800c0c2d4100113085120100240c4490740c4c1e0404503c210480d0030980752400c65564030000540c403450f040303e00009000d00c065004000a010b02c0280c200a407071402154282c0d0609404030f421146150801d07030310700102290401c2503142c58012a03070700108500090000c00c02541c08100d49001c041c2c07207a6001c800189140903e00e00c940c608500454004002c20381910103030315100c0e150042060b109002e401050300c060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 56140111 1250 56138861 56138869
    0x5060117071b020910030b0c0a08060d0302010b030723060c0a02060307180608010e07110a03030e0a0605010315050907060e0108150310150501022b230405010e 70
    0x10800442628004680e55544901280c040341079000d0189021440c503950005030f142e180050344616409807101049501354100100298001001c2c0800110100006101503501c0b1940369006201600c250000707401a16044e405042c0380e0059680600c28001c0c0000e55101c0002c1c842e4901030388211003504800107206102061060000c0c07038407a40d1000d0328200c01820074600466006249180c104c0030000485100000240d4542c40340f80004c001a0040c45150000301a840c1c210484d4200100b070118115500b58039007080c14005806c0c55611076400198650501a002d40e083c2c3c0900e04100a603100c1c0742c041d080101148141e500c1074a400700260704100000b8014041d41e90310b480c2d03891115000c0c2c0c0111001c01c0d006240c801001026007244049840400c40e001c1910281080450140070700c040042c2e8100300ca91000317046520000b1205005405252404940516005940326450708032005548044107110955142c2041c2c00445451164001c05041940d90990320070200d140a00100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 56141361 1250 56140111 56140127
    0x41b080115020c060306010e0a0801020307031b2007080706080103170703050706090c030b010803090f031209011101020c03160b09010209010816110d0201090302010510120b100b04060f03050601 85
    0x1035400340c1c3c40034592002c80d140000280d5032002d030500d001000440b07804089580c2e260f0319800400f140c2c0d00030091240d00c50b054080c040403c41ea0f41180d00c5908824000248150501e0344400d0312005003c09803005150300784002c0c00540001421546010354600c0004c00c0c42009200580e00b140c14004503904810012040340e1500e41c0640d0b03030138101035241d10ba100080c604040200c0b101e03c100640000040d5008101c54024a148005903440f50b81000501490102d400d000c1072003600442c8040072400c1c55407050781c134041e0080c03038030032800401042c640b8028410024007034494407002c200071000780d0208140c0c81c05544100d034000d4260302c500310038600b43e0092806850114004000080304c003107c560161a031204280341c0046807450406065080400385001d03d00181d4680c408030342450b409020b0560040b058010801d11a407030900b041030360011007000101001424800300344c0c000c0502108401810084e04070540d11035650101401c184001b00c820400709003010300094140d8010b10780 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 56142611 1250 56141361 56141399
    0x203030105060c030c2410050319050307020d0c03140c030d0f0512010f14120606010c0c0b030109020403060c080910020306040204030b0907080105010e1012030c02041b0801 76
    0x11815a4206000c00403590004211028144400c0c40b1783c2042031000c00540b20812032648040e030745804100e14603941c50350014412a00304d01441030422090710300182c8800713034100200181130f002006140003030a612171048069801000c4541c05014031824a17003140850740301d1142100a06640e040c01600c1c0e281900307005605810401800080c140580511908682c40d864464588044289404480301c020b0b040788444041c8564103000110421501040c4444c045616040041102030640c1d41c60710010802410080010003103010080300c21034440260590060060b02d179a1511410f03002500103100550300f15041c1009426a14003035100030380540c0801c0301402a41251a410401a50014162580040e400c01c4000701082601c001180a103d00d54041d0103168070700035015094030b4041e08801c84a9807003005001204c020f100c281c20885040312030b030309084c4586d803c0039541d0102d520806900282444100003091102e64103030280e07041181ca641d206a604c400c41e41c004420344201c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 56143861 1250 56142611 56142613
    0xf0222080c2b0201030e030a0c05010e030c120f0906030708041a070210050415110c06010608060607060903020102040905070507051b0a0306050603121207030b1c0b180d0c0203071502 80
    0x100e034403140e08000c920300001e0b030b0060401040709020080750f14556805400901c1c0000d80d40c80c001e404000d020700561040700003c0000b14208010384807a15290741d4200401c4150300780014150003500c91346001d48415200082401c2e49904d0108400390060300111401c44040c4c81c545290184602400c480c917002e480f840c2d00420304124090b004600801c00600180c2d4440b4400b03040303c00300b14403030049880c01da000f029115220346400c210300307180000603048141404010740c20042c0d00d48440054503107441e0407030710204400c0ca45040030381c02442290420750340313241004104155141c210000305052803080c4212844100b000c03100341d0b40740d01c501460640c051800070003007000c10030a421141d00300c80d0040039180001c00081244c4980d80c04156150700c3c814440003004405505442040661b41d01687d41c81458920b042e5222012101e01c1e000421402e070341300205080881c00300300322107070580e200110744811140312400303807851701b905030103d1080c4100f05003c102c0c910060a0300c0c006401c550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 56145111 1250 56143861 56143909
    0x1c050c03070503040c030c0605070203070f080303270d03020c19080a20060708071202030705090d031803050606040b010309110f0d120305071b0b04060f0222080c 71
    0x1407411603941c3c1c4058019180c4041040020010600c10050400100381e01d448159554009106042c20003000703074482288442c8501c4208107600c000700c1200e5100c3c80e9984500301d01076141008005000ea101a1000356100320000c2c1d0f00c03e0364040c1e0040030480d080c82c046502c0480f1020010a480040318001042c005c000d0084101960060007c00c2c400d6040c088544034200d14451050b21740b150440305079001550b2801407040881c3c100d214405000840c0000303510710700d0044009030442c880e98100d18080c010085002051602c52400c00d4004c21004030484422a034034245565507040581d03e06208520308076489005e5030092080d544003550010110000c02030480400c0300020b01d14507041d4020101014000006808492071042d0740c80701d480000d150304000304d00400c0504030301d00c204002c070000d10700500400d14005205902c0b9500086c0412806c040d00a4800a8000c0e00790041d80e50b076540151010308070003054240b007270303c079540200d440a030039003c02c12000f0031000e419068115004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 56146361 1250 56145111 56145121
    0x3090a09050412121811040510060804080a09050405090106050114040f0909020406052206060c150c03020408030a020715140a12151221091806080706051c050c03 71
    0x41c400e0042c2641100c900140c110f1810f0040340d0200c3c540783c000c413000f001c1c40c41b440405140078480c55400201c0c400c0d00044035410441c02501d0300c003020f000605041030200c2c624128a10414610380a0b10011304180014140600c0b1b1502030300300c40c041c590100c0c600c0141410004003030f100361411141601c8010f8800352501074204004c1411000580c1c10a4030749401041c1902d40e1801c84091103019034500c800403d415403101d08035181a0001c9040040209195002c20ba0f40c140c0041055145070b40042c45582c1020164002d1203103034000b2800f03000200310320307903141d8000c1004000c0f21806604401d000484100c1261500c158403511940180300b804155402d910981000c2049600c11900203440800440e2101c28108a9403001223400c2c3c49407615002c1110003040100e03210303a60642e003d101c840c15000580366000038010640440c0c42400c800500344e2240e0807050040800000340c07980a0f8445400070250ba0104e00d22030800800d03540708040c950464070680b4072546c82c0520141c111b03119 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 56147611 1250 56146361 56146367
    0x304060e03030f2a010b060306041805070f030c050f180a06030b010311030d080c04090b010e0d12022506030915140106030c0207030b0c0714010e03090a09050412 71
    0x4030305a15050b11080c000018071905003001000391300c2100101850101c3e10b00780d84c0c0d080203001c9070201c610740d0401c4040949a25013405803070f00208100c0d0040340460843c070103d10b001400601c041d04d0752003292400070781070202c445020140c0b8002d544050400740c1b40d005001a000b0b10090796030300079001900130010b0502e5901600d401003095000030813901d80e680c840304e0452000303170003d0740c0b0311040c400071140c00d190070422002c0015150520281c1d6183c00b400b85040e5015920641c1e100644608080205c0d0b03200d4881c69428280040c1150b00c108143d040618496034040e000f000548184c40301c0340c6000f03048a003081450100b910034000f041d070501c24120045c0560150445449003001c90900c032121150085d88101443d00030100740a40c503104000f0305481a2166034015500a8001803020981401c50203a02140390194160ba40c18a840c02c0c8017070170100340b180c007080e5181000c2c100005c9008002014a41412202d05002c1921000100105c40081d200240f41c14460032200da10b00380 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 56148861 1250 56147611 56147627
    0x1305090a03180801020d02040510020c0f120c0d11040c36080a0302010e070501170105060304110303031f050909060711010b22050901020a1b080712170109050603030406 74
    0x2d498900b800559551089007aa04213010002179103030081414041c6041100c0c681540041e10b2004000f80111000440c801d040c54000307050040080c0e4225108451007002a980c0440000e44002c420340518240070796444004480c9900c254100030113000a5880b410036041100301000c4800700c1c0341d54205500c0a40c10031242816240c4840400018036039006001c05e40034640290004540c502c2d50f01d520070f00307150300c43c2c1005041c003051320b12800d00701060034152810341d203081c1c031750035034a4960f41403810815802604c041c4e49480004100004c450800e00440400d481c140c10b892216520b078405c01000040846450400f40d2044000400b141d11445130420b1440780030300000380714071560001c0f50401c000c03c0c0034041c100e40303a6030f04c039003a0441c03620640381e0203280c1100031810401d0440c0001c0002d1180320404c2110b040990f4601c05010209080381d03840e0340d1102000c11070204411014100b44500710105008038a03907000000c4048407130140c5841810b009024514003410500203840d00b007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 56150111 1250 56148861 56148887
    0x60708180904050d1b0b040303021c1b030e010605041e050a090b07030b0d0203160e0901020901020c06070c0905010f030b090a0c1a120703050907060f09120807050d05091305090a03 79
    0x840310170140070036088407485020342d000b5540541ea03071942c0140900240c0080c06e04410b614030302103e058640152005480c418a40d80c5008540001034850f40d60250030300e6000389078090b1130703e01c4003500d851401229071034000d8401820b02442c1e440b20041d40880d000514054030200c0c83c18006008503109910120110100800414403481d19802103450002d9004640b078528040c0c800030300c41960001a0684c0c0a500600290f103170a02c1900001d450b84001601540146004030f046c001304004280610050011903c1c01c1040d5a551096191580d00074030041c2c821000b52400b140c00400040b555251440d000481d1803401883c0070007807510707181c64904848807078006106080e5529601090b282c0101c500d5900443c06041c01c1c00c0050403c2d0842d4445c10074000c3c15880c007a24250884804012a07400c00c4454050200c3c40c10180c2c16485507040c000c0003401152411200d035504007020b04400c0341d0540707104121801a00c041e03000c03914141c600c042254401d40c03440000070b00c644020030000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 56151361 1250 56150111 56150147
    0xb0903010f05070f0306050a08030403030f0c080c010504061109090403050309101a03060610170604110310030c0b09010e06070201020106031a01060f08160c060605060708180904050d 80
    0x341e161041e00022650181c3c0c0e2000002c0c8101c103d200d8056141c041c3c00040e01c01140c5200c0e09a00c0c0c64032159803803103188801020701c040d4480da86a040e004040304440c4507006004540c1e82c001c6040e4041c002c1400b180c0c01c5400501d400380402c2400311100c2034490503140030380710201a490f507840c142c07881e030002041605031388101c218020b0a08154000d034018031031900e40d41c404141c601402c050034160300820340c9020321a0300c10315071a40740d03000070044048a0020300404e460707200c04021401819010360103041c0090000107004150860703000080469009043d88401540c0300e10300c0b0340e402d20591001900241160155403800d10306180200b600354814000002c001e9529a2503010f039001802448410304140e10041101d0380c0c0003a2071300c1d07210b00b042c500425203250a40e555192040050460b030304004c4075a8002c01004a2a03210101a11000307014584451061901c4203070340c1d101e13448120788140060809503503401c01300e442600136940400500361032080300008541b18409142d0031009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 56152611 1250 56151361 56151371
    0x1b0912060f11040305100501050114030106080c090a08060708010602210d090203010e0604030e09011211180a0603061104030507060c080712080901200901140903011a090f060a0b090301 81
    0x140c2c004800040000314444e802400b540550729242104840d4160300407410704c1081d5680c00c5100d4890000c407030551325141401800c0341c0301c140790851075003d021201c035040400d188011800d2000050038521074080d5980c4d207500d41e83c80351320490b25001040711940e41c0e0354001c002040d907829031101600307200180c501c000803c2111174000a09452000c40390741d1803a048801800b003816031284101c0500e1909644540c043d524005010380345105245010740100ba07040c0d140f500982c1c074010899036a1424540040e00c0d41001e50042c2c0040045102c2161518a0002e01d0044002c08030150360450760070901900500e841c04030709640700c28403c142141d07044d80c20002140000d511421000102c0c2d03040c1d6400006191800c80d49084036042c102120f441c071014400c4000c0e0344200400c44504400038039090313041803503099880700c031400340204090b410b5003800000c0ca080d245a400442001d02e04a5500314203843d03481401001c0308041e202960025042c050601c421200380c03008004401000d400003072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 56153861 1250 56152611 56152631
    0x5190201021e01330e0f0f180d0207080f01060b040e060a0305010e0d030509030c100b01020a02090408090301110307050702150f0d0501030b09030405010815030f03030405011b0912060f 81
    0x250b20084000911800c00e24200c000c030040310b8030b604580c050200d5140b000381606151000d94003080000b0b104012841e180c0001a0007448d2805080c01e144c2880c000702c80784c0344280d601c0a501c40040d07002d28446441801c4050b9080e8005005a004481c80005100c0c40c207400c0085084403060000c0070a0380040b41e482c8008005039007440f0b0102e034170440304041c04070801c014500a055a80181c40c0b8561a44284000c1026400200303001c81d0310032801c1030000e880500c4600507400c01c902000041c4d400000c007401c20080c040280010049840200d008200182541c50180d603640019900c000015000380148001402c1c214a40d681111141e030a1506040b03500d181c40d0380c0c40d804100100030443d00c5400400410031103504070b64020f4002d00296040c00d04120008000f60740061000d80d007201c2c00c5030036288135201404207a801c484908240c0784d4a180c54201140a0040318510000d071115a00c0003007406442518a48140c520740c01050b1100a00c54440c00c014124400149070601d51700c00503c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 56155111 1250 56153861 56153891
    0x7020405090c0904200a08251701020d0b010306030308040b0703020708030705130603060b0d05060d0204020408030a020f0d1e0228050c0609060301170c04050403050705190201021e01 80
    0x1e00c518881d0007200d042c250700c41905d0303a20400d2000000d00039000d65070140080c1d4000303e014080001084102c1000000a00c2e8410480c1d109038030800300304211075007440318100190010302c0c0300d0b50b024606000c1074403031000445c1125460f10014001402c2d00000c40c00249001c5201c44c1c10011514015042c0441510b80c14565402034640d840415000901015080000206600141510b040c01c100f417034030307160020709180310303079080b4410032540c07080021226a104400b4a600c641c004d801103480d40c2d2a00007140d603e920407101c0030050f1242c5200c0c10528500010302260108a5035510030001101d54000040c80e06420729000640c020109640d40d0304e0000000f24600c4484544442c90070001410183c0c1030203600c0020038040c01003001594160348078101120704661078030780c2c032030301d0000305005440c01d1040d2400c403540c0c0f282c141010300080c07640c4080500000c034010001e490700c41242c1c00c003045401001400003070143c3c1041c5130091452040070003070707846a403000300080345150804240c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 56156361 1250 56155111 56155129
    0x90b0106090303080901060b090607030302041707180612030503040201020309090423030f03150a0305030403030806102618030d091202070b04050607061d0a030807020c010507020405090c 82
    0xc000140000380800c01c0c950700c19003158100445030020000c180c1000202203c51003507d1300c0034002c103000140c5000301840703581210010141c90086512050944808584a03215440360800f21041e0a4000c122500300344542c000301d6040140355041c411940c2d50549513070708000c01c141d06601003405144070503150354287e98415172140f00d10400d0b5115443da030300300c00d4801006540c600c1e80144150807403215502d04403904841048200181102c24000244581e2501d400041079400003043c00003c1682005816005120403101ca5241d11101101100c001080d501c4100c0c01008091100d195a082400d607582c00050400750000c1006055000618592000c4c0030461031030340d9451040140601608144c600c040c40b4406030070310a01d0b20403c0e5034a80514003c0c0c074800d0100145c10800c014096000902c410704030141d03442120819414503031150f2003c041540807903120000a4441c03403011800c0c1078a854146c40e407e06003180d5809000003848001e0251086201c1c201619256548610307807 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 56157611 1250 56156361 56156369
    0x9040504030c03080c13031103070f090203070306150807031d0f03030603011505090c03100f03121e0c0b09030d050c0c1504020603040303050604090210023403021201090b01 76
    0x3050000030640c80c000300307005002400203170321150501c60b49044a0701c030038a0204036500f04021480c9641c2260000b42008907a61242c1080050030000048040c826009984074000d00c0c2c41c10880b1a0b07866079003981e004649048500020b10700d00028030030314000d034010744201040e95807549d480c8142080c6280703488070141420f0702c2c83d4804420844280b409000f02c1038000c20342030125051501c2c2a004c5035408402414030b003e000070200008080c0c9145214140051000100c046080c0303030350342040c0403158040f04540c80000d2040d01c0e403410040b0184440d00f402c10382661031014041140d00c0e00110f03000080c010140c2408100100c400240c5c007805070744d00a64801b41a0b95480f90141465071511640d0900c100760690030700100400b681e216810b4903445a01030402155642c0c403040020010031071460000e620402d40310503050b0032070340041e070030303c01704e4441d040071510a22410310b07a000f00c46040c1e100424403406070741c14401030500604000b20b4000700700c000f08104c9039a54400c9070045003608 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 56158861 1250 56157611 56157617
    0x91302060c101a0603071413030c0e0906060303090f1201020406030e161202040507020f100e0c030a05070b07020a0308030a020702040605060309060411010513090b010f0f08010909080904050403 85
    0x528002d204101c0c0f2038140c2e0700c010b4490611a8105040200b80c0c0d84c0402807a81040c001907000701b0080010341c0d030071a42e94600c22001050031544a2600301c40584a40c09482024074100c000105050b4001030914000d550050055040a5950080240700c4107044003460b00544d040304042001d08007400130300080c10094401194200702c04c410380303240c0101581c0c1c0442c4420348040c00c22240c24407508207041150140c801051076695120240c1c50152901501000c07481038010600c201d11940d8440e040140d0244240e0310009200c008050b520b80d00e9000c09402e0307810080041140342e01e818010125144007802400e640e079681d4455205640040303a00703140c040e400041141c2149030500c03869020705812204a415400c03c031592076643c500c02070009150340c40e11400c00318280c0c041d4050300e444411121904c400b460700d0301c5407240a40010040b03d40820380200020800a0003019001c03050340166480030034070fa207008141d001624502c102a00d010500300454949602c0318012148544d000c0e80b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 56160111 1250 56158861 56158873
    0x6160b0f0603010b0a06170c19020606031911060d06050a031a01050105072103181103060f010608071206050a060203120105010513030f06020c07030b010f060306060806091302060c 79
    0x80c1c185401e40740c3e010356161007407501d07400a00c14290000e41300c0740c058402da0f0340b4400b15038030b543c05a40103104071089240d0300703002d40c488c00c1000760780000c0c250b1040006505071403420580903103250000494800050000d0710000103403480f07080050242901004038900480c8540e43c9801040403240d55400944050211920f0b03a08000c0d0401030359401020f0030310b003442c509045030706c814662a9a44040e01c03c04402c0440300c1c040144a80c01000950340007420701d4003040382e80d10f000c032042c4103004c3c4164024001e141c0024072018032010454100d030b001d07489404050b6501a82150744803031104100c12040d80d295800704094494010901c050016500110395424042c6207030001100142c0c0520b042200c1007101d61510000c120064007141e038400f0841c0100c2d00d40d482d050000e805054681c00d40c91048845c0002030000109409048801100085c0e22080d15400e013101174402c03d0090002040c2202c000c034000d400e003c406181d0048050b170b04040041050390004009603c00c022650850380700c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 56161361 1250 56160111 56160121
    0x6090503070c122a090b010e040501260111090d050111030a0c020f06060f0402090d0b090706080112020a05090c09040606020607030e0703051c0c1a010306050a020909040206160b0f 79
    0x40301041c0400c1d4101d003207a96000444d11a0b5801c03403400d4018410459100c0e40c00244690042401c0001054001d006028a41c0c43d020300e6241180c00c0100050103181c6000c150716040410712424840c90300d160358140c03030012008140a10300c09039480c00c58140d0359420035004002030f480b000d940180138203000420400020b400003841c21020302040c16494101805012036a40d446242ca01003260070307200541c84130303041e20004407500c00281c009410848440100012a000492000282d03074040e1102e01659803100c0d55240f101e5044500290810546075050000746008039240b9400f00fa84103140345405c8200d0701042c240d4103241c0c00703100943d000c031050109550b00750103004040c405c00c80080140504c1c54a031035035202e10441c0a00615088001d0081c0703254851000c064007640c00c4801a821101844a40e010310b0350248015110700c0e16050101349545000e0088455166009011048588441d020404030354001d224000c07440080100080004400161061080c004600140140d00d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 56162611 1250 56161361 56161373
    0x2090d06150b12100503010b010e0907180311010807021b0d060b0414061005070203031b0a0206120910090b06040e011b0c022e030507050f160201110303060105040306090503070c12 79
    0xb44c0d4210b1440303a41001034180e002e176403040018101c00380856080c0c002c0c2d1281d03282516000003820303a40111454441d008014440d8021034008504030030307650312000d83d0354100d00b280c40300200340340302d003282c500030400b5446840d1200e9001741d410700524000841101080001701250005101c240080ca00c000070812145407400c85892100c0320b9041c0306103044443c0d80002d45901c40d49038400140341e45404a40016002080b0191490381d01403c129525810840c500300c080104585903e428482c000103460440a103000b50261540d00021050130303519618104000741214825581c00c540d40c4105084210b5a0601c060f525175955880360300682c1c4160040c000c081e203d10300858000c0400d0f61801c214440344080003280030505282c005032176210b02c01c00310703028420b0700783c843c2d060f0f40003040d616850200c84190100381c81c401d03290f0401001500c04040d8030790000701c50706400308009000c1080070a919401c007184161140c410b4924080545da1030180c40c201a80040d8015040480c2020800903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 56163861 1250 56162611 56162641
    0x10080405060a06060c0201110c0904080711010201060501050703030e0a1b030201020c100203040302011803020301050c0309011b080a020703121109190e040201050705101b03060902090d06150b12 85
    0x1805009001e00341c00c2050251000c5e0b07030300000904201c3e002e80c3c00c2000d000207001854184100502c48003040c20981030034111034000d12000e4981000d011450501503005100702c204a030342c117848850070711314162815001443c850040030381d24094941081c0000d01c0304684900c1003031060107426030160850000901d8000350701d00050040c2d13a90b03c1d000000d03540004c20f45007200d0b42481c080e5103030083c8080c5520031601940c0000d4041d800c00e4180b14540303034610051803080541e02e00030000039680e071a141910803580540c500c080744510022807140b81450300207050b880c2c02410490341407401e00e6059011585182d0000602c1500415001c2e118680384403005907241c86d907480142000d05103410740c0751f100b4000d00000e0610000007000c03800c008080c040030f90601042c1c1c900f004105050111250742144a140b1000000d2508070045002c000a00c2603034046103015000d4a203c610690310341000306050000008e0041c0041000680c1c2c41042d03004055446908413400000d00b4400c070f0b0484c0c10a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 56165111 1250 56163861 56163871
    0x1b010206010b04090507050c15040308070816030f0e1e010b01050c0c0f130f05070e100206130302010b0a090b010e0607080a0311040510050c160b030718051008040506 73
    0x1402030001084050441c4090f00c06603643c08500044a84500da01900c8610400101c00404d010380609403000709000d00d00b0034842c60003521041c0540e0ba40e0300040340c0c0b44c001201c070800404812040404014466842072041030070f4443c00062003e8640d01081c68000c0c05408501002c000705070032000140d003805014041d450a0030454148070141c44003c0e00d0702c40c2d1501031030081c0e01c40d1a0700d55159943c1a8032403150031031900100031050107032035070030040c20b0704403410004038030040a40f01441c100f406000e00307914241d6000e0310f0207031103858030b0900c01c56070a4000c5c0c0c1190340340c0701d4100303260f90f507110300e54020000743c40c002484840c0c800002d00ba1042d0f050350284601e409001c000080303140c11080f80c0340e20481e40f50001340c4502045451a0700d00958100716040324010001c82d400640000040410001090881e080014200300c025010012406903030300320002803004c140040e0043c0042140700403000b1410b10050345840120340341004002c4030000198000c010f020034000280034641d004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 56166361 1250 56165111 56165113
    0x709021b030a1407030507080301030b0603070503060628080f0609070f061b03030e030301081b0d0203120a050d110712020a051f060512030a120605130c021e1b0102 72
    0x407180841010344110f1000448144205000a5070020544210125403c642d4803250302c503141d584031305210301c81010843da01406407003a8440400c0500c0c00103001841035100170090144001013907144110310b081e0035680021002990800f240c20481400401c90024581c401040c3ca0324214504034034200072544112204200c1c4c0405000e400da0081c01d0348001d80010200f1400846180f6084001b82038108031802280800300010034003181c04110034130307030b528041c008115141c0c05108000700e410030b40314025410707030295021544415020010b0144c034101d50402038207140348941104103a03200030801c190220300c005100010003225242d0094411103a20051280c9501070f40c3c1c255880380080b404581400241c0301036500c0c28003982019010340405000009404414000c1c165280c101030111000b003070b207074480e41440c82c030540301300d00454800034515070310307201c4910588006041178400c190844c0240a01c00815201340c4038041903081b40140105440343c0180117500d041e2075000c050b5411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 56167611 1250 56166361 56166367
    0x307080717040b0711120a05010507031401080304060c080f040305010c0807050a2a06020408030301030201091e050f120f0709060915090f06030b010e090106060302070b1501020c030709021b03 84
    0xd858041d0f07003030f20081a4084080c0320100342c8540010403841a1400f000418490650394508024041d00240e000e00c506450600052615101700c0504000c240540e83d4564400d01007003005622030100c492009003d031030200c0c505400d0800341a02d0f80d0081c2c1060390345a4540462103041380c0c0c45504030b940914286090750822440c1903004010140080e0500e44000300310007500c01007481640c1c81288140d2081c03085540e41c0c2d0390011980c0300d0700300744016400308511940000f4940d022444801c860000c0740c80701e1102038105401c1080f403402e03511000340c05c100400c01c84402c10804001c4551030b00403400090851901d4040d8003400c1c2c51094114030001d900300f84448041e018100085000e85044040128503901034804060044c4000e501c00781c100724022000142030000c0c02d03c8a03014400d400c009000280d103900c1c00351306910a05000428601c1031000160703400c1410101c04a801d081481515a140d580c000000c1c030f0008542c115040c81980010600218444114040403001a4001840c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 56168861 1250 56167611 56167619
    0x90405070302101106040609050f010e011a060a0801030f06090c060e09241513120302010c031107080c0708030a02010b0405090703050c01051c020708040e0a060e0c09060903030708071704 82
    0x7890b00e01c0030703000424003030312380e01c101d010450300340030522054200360000c000104804400d00d0180c4030104500c0510420440c10040f24204a41100d0079181d030742d00c9503003941c0d21f580d507403094010414400381d42550340c038064140021444c0106000404440c0c0d10202030065003010052044c0b00506400c59020101b50b010031800b4800c1902c0118142c00c980d01203140191100c0605248900041d60511485404000c1022a005400e042c881d40c0240d000704031218034204140c045072804030300c020302d80340140b002100003101a4014844048200c065a4030315950b091014a1500420b07804001340c4d4540c0c402c4480c078100791142c280d01c03650f03c00050045519580320541c0315032003940d14504114000625040700908100354140c40c083c554411503031b801c024180b4850701e80160091680e80482e800201d0b0b21445640039007003d445403010852038507291202030050300e0b8004043e09801c203000b40708201031590f041c800f4102c403500500d07007a6980e0009182507490900d0076903101c80000800e0200380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 56170111 1250 56168861 56168863
    0x304032a03120507050a060e06071103040803090f01050d060906180b0a092301080303040c08010507020c0402091201060e04060506030d020d03021809090f0f031611040b0904050703021011 82
    0x9415807680c3c20031903522105070a0990811803030f002c2c043c2c0341909003820070412600001f0030510a0180c2e5031401d03c4001c40040b40781e20b07031286101c1c0a0881d801440110290324110241e0600d6a505040c41450104503001101c203941581d8803915079165900010040100790002016001c0c561070000c010400340c1000041809140d40121140c1c6582c802030582e40c051002c20000101c06007807a0f00c0d0b0300350394903041c0caa520350003160122680001001c00041140c0705001d40d1307000340c2e6a5005842140120003c0c040250445040c083d8898075042450360429000c3c420400581801c2c600a55103103840d04000080d14009060309000340d00c4070b40882c001c82d80c0824135900142840c0b0340542da644480c443c0d440d040c0c0c1c801049a034016a0070080c03044000c00010304034000d003040000d07030351008034034015240c6900803041880d0350001424203200c0010b9405038000503c6c0b200400000740c1e0008000411481e600441d401c85445e804000d007841546015448002481c07032034600308505023050b141d05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56171361 1250 56170111 56170133
    0x1140702060916090504030306120602071208070807080709090e0a060e03030108070902090f060c010b040b0a050607080c070b040602030a080a050105010e0d030c021201023103030807030603050304032a03 89
    0x40450325580300e0126007018409d400280080107180c803100002182070070105c0080d0b10a980450701d4217280c0444407403c1d4000c0c04454030846076511410815560f000d425281c1400042c840e408200c070071030010600c2c9003584100ca2102c40848014086128207203084000c4550114188040e43e00c14001003216035800038201c01035410b10100980c0f0b4004407008a1040610f09004540c1f0010208204004020560000880240031241801400f0071203050001041290248035081002003180d01d020414030001015036001c80004c40345445d0340c814642c46150869004503005800005040080650040302c46811480c003901c01c00c0740303524120000c0c1040c2000321029005da18804184014103010388514503071aa00503141a03c1c00440066060007503104044840220801419012844480c0783e000205080403040c14411a41541c60a80310703070200070020004c03d501d49a01000003601480a44002c44c8140313684841c1d4840c00e8540a011041101d01030101e401114081010030034040e00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 56172611 1250 56171361 56171369
    0x102040b04050d1e080304020112050c1902030702030a0c0e0106050306030a17070b010609051c0206030a090c0308120106030b030a17090102010f050c0403110916030506011101140702060916 83
    0x156034118043c5191003000b01613032204c81840b80d11110085001d110b008001144541d200341d88400100188000714402c9074010b49280590030014004902e0b08101d0200308c80210043d0b004880c1080d00c03541c0024a80102000d0840e4003178401a41086055011102140034241c0ca0400300d05515008000c82e03070f51113440c00040c0001c0c0000018904801611046500340c030b40111003020780390303120070010382140400d1260300d000e2001751600720501c83d80700d6044602c89a000704041e285483d03504c1c90b00080c02c4191802c0d1561880035400000007581e0740020003403080302105401040d07242040140448070100040c5001c2e401c0481c1040019114200c0c482180d511724507626103c5100b940101d006103030004000012914007818001c0b1742c4a01409002201d02c030b81d014200c42810b0074188410780006440700c01e242b1032840050f5440901982000b94828811300d4090703ca080c50503521825204907080903010b00c0fa0301f0084c801400c1d4140400380d4070040d140000c20a251003000b80d00e01070107a51003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 56173861 1250 56172611 56172619
    0x10204031109240f011e080709060309110609120303070305071805030c04090606050301090c03020f0301021c0c0302091e010e24030c07170a0e04060302090106030b0409020402030709080601080102040b0405 90
    0x4001d13941070307008140107601c0b51a0300c01c140c550000c9124001d01441415600d03040410a014400900d03140300303000308140141d1210b881013003a44000140007a5400c002c60441d80a0189005840010001c00c0694450915554007251070300f0300020151480156882c1e0303a05a110304401400703162000211800f130b101043c1e80018004010b410190024041504000c0d4554204000c400c2401600100403040d64000c4850038100001c40080502307d00c61003903c510074400b900c140d4001d110003580030b2900c10078242070251618150400003000b0844c0a00c0304041404041000502540c3c003100341001080107030b407a003008115240d420307880110340f50170100301c0000010016241c00c3d0300030300361040f10368402c0c10521060700a091224154014416041c00250b030a81c840c40e01e880c2c24002c482c102c980162002e85c044c0d08000040300035003003030001e940e00700c0d03140d054540041c1c5861004511502059035100c41803410170350720324100311060b80594500c0e030040c0414084480410100e90481d44111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 56175111 1250 56173861 56173879
    0x40209010b18090c040302030f030307080105011b05030d230f060d020d120206040506150a050402030a02071502180105071110090911030f010501020a151d01020403110924 75
    0x8800c520100512603150304031203c00301380308030003806902078004d40348200c2c10341d070300c40b500f110901d561390001f1034100c00014003910041159500508484407182c07184ca107091030b6003189440791880d40e4845d0307131546c100710358541e641c0d1401280411f504012030003102c40c000143c1820301c2003040700040a812144909010300d201d00842d500e900100c000c0640c0b110300a8144200040040d44030a8100d5003034a00d80100e800280a482c4000d60420641000805481809081c50140002500014030f00e803441e560070420075000c80c641e4007002016940f03400700540d42c0c4065080020341c01ca440790200e0306015040c4141000500328034241c0340754010569404901c80da100008840f41d00075a449024230b549805020324030500840f000703501c0340c1c089241458199076943c0049035031782c1014201601c41d410300d10b40d048190005070440403401090042d41d0b020700203c6c0d82000d00b2a80f05601c204c41081e01840403842c0350802145455202c0341420322840300310010998804d16a12207211284102061 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 56176361 1250 56175111 56175127
    0xf0c12030903060c0706050f040c030b0c0f030a06030203071a030a020a0201111305030105070906020307030e031c03060515070c0315110d1d030a0203040605030a020d150608010b03040209010b 84
    0x810a889512100408443c0203041036600c010050340802000d448290904002a00e000c03807240b2014000c40d40a907030030b0b82880c0f4588905141d81c6e005803280c22070010400904008060f0704020f580a203000368000a03500c2d20b140304051408cc000c0c1d000307041000c04c405c0c0c410314044100003030f41d030301100507440941d440405444c224010021145286954030021501b182800e1070407443c501611000d4000704800e840b01403094403c54254466040181c0c01007081d000042d106060441c0d11107005801c8800714040c10104074000e88244503da00081c4c0da8117400c00580c901a1b03082c00d5031104003503600c0d15115480d19040e1107131449000203450100c007000407184102860f4007403440f85c481c2d114102d40700c1d812004001f01803d0b2907480141803a891000b0b40ae02c041d0b000c41121442c0c2082c0e0011881c051602e202552035800007040c842c041d607030070701000c031103d01c060041c8180b5050101c108190a8202080074041030410380091f089840180200001600d42803c0c00b0b05407140000c0e02622a016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 56177611 1250 56176361 56176363
    0x7030c020409060606120501230f0a0e0901020a0207240507150f0b0306150604050d030e0604030c0819020303040909060207060606020c010f08040506070c0201020a05010e070f0501020f0c12 83
    0x541c510080855250050010f1726950003160254141850302c01840a0390703a40c3c1d40c42035200940c4540000b02081e94090100c107262070060310000d90809403140c1011691040c1d001d5040707030100d0305031280d80d4000600303e030400c3d81803043c1000f902c01c03580c1001041841d1a02c180c43d5044061003c0305102c800200c66003402003042040750308002c3c880707045c04800c4059141201429003860020300a00c070349408181800c87d09180c0b5403c000014090600b0903103410708100790241c1155064003071103203941601e07140b61540da00402c041c5000d075500c0c0000d5454440e0144c502050a48c910311103507000e01d14400160703008002c48080340c0d800c4901050004131400c001000b0f00c2051001006a450590000785450700400d02c3d42032944262034006510445980a1314418030480d0028040c2d000003002401450156511807203039030041c4111014a200b41e41c44c02e003101c110341008203543e40411010002d1040c440e4003032000c0d00d001e10140c042410a10102507a8010140800744100290891484c0001c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 56178861 1250 56177611 56177621
    0x70302060714121e03060112180512090114310b0c070807050103020418051807030321020f0d05040206130308072a300308070206070201050601020307030c0204 70
    0x100301042d102060703101c0d00307401460351000725900604d2122215a00c4541e8180050f284158810707100c4c442c0650100704002c0c000c08901c901c0d200c4401c800307042ca0780860381c2004070403043ca00345040590381d007482000244c00b0310b46400c0001600c4808000c504503a2142d5841e000a519064180010f00c40d500300610540100c1504001c081140200c0c800145400c0010384404481c04c0707130152448281c8401c0118103911a074060a1400346410903455000c40941d40010b51000c1c480d40c00741d416074420945c90b0f0920b1450350040e800511840401c0f14614604105496501d001c0b2900b14a4880461030300021405107140096140355224005807d64035040103d542c0c2c945000311940200d6100d24150609400140007641e006440b84c004c40141d2905190581180c1080340c03110350301d079140600e1590101c035040d01d40ba00c401ea11424032840074648080d0400400d02c40e4407025064500020000c1c80e2145c0104400216070401061017002e980220031150304035098501110001c42c1400071802400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56180111 1250 56178861 56178893
    0xb063703080c0303040605072f03070204050f100501020a030804140a0b090106090501291602030709060602060709050114070212060907061106160503150a031101031d0703020607 78
    0x10100184540a90b00e010008500c602d202c1d40041041e80c9446100b2551b8280c9140085000c2080b0040d040320340e200203d07842c0b401c0540c2d0b001c413403400d000e50780032030295041515000c01d1480d4075828084001d000e41ca40d038001d440e0a100030040110180c80040c164100548040c00c943c8104540795070142c814000b90812680103040c8004900f0900e00380783c0240864414242002d180a00100f141800d200503c00b409902d5620018412840c07040301c0300c00e0b40226078001a052965645000584043c0b248600400009a00252003031030076101070300704800184030100b0000e4184d42444143e0b0482d08038103001c10b90441850300c07100284080303480201103820302c00c03092007a41d00b040540301000645c2e4040d01d51540c0c2c0c1b1446000c0b040c1059660700700c00c0e41c061040261641d40070303c0780b03440303040034540c130406004c07480e41900e6542d8040380303018034990015a04106003040c0c084c400d58050040780b8030200d54444c10b9003a4214202000c0e11004603000c004c2c412000040c5182c14001e500342640300130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56181361 1250 56180111 56180123
    0xa0e06010302070b090304050a140306010915080d030209040c0e09070e06070506090c031204030803010b1c050718050607051f1506050702190602030a1101270b063703 73
    0x24100445d40e42e542c1d81103071140300e100d1640c514001c81c3e101d40d210103c801412014000701341e1a424003041c07402070400b030b000841007001c2e806800101c000c01008480340040c201d0b1001070b82d4540c188280800d4400c000380d0502803000c2040e0341d24503030319002283c5078400c0852408078423164064002503040d00c681c0c84050064401c400a000100c0000b14425080ea00c04030700f22692203c0e90010703030482c3d000724400a0036140080c80100701c0c1d4000c5500824003000b54002c48516031004c00707071785c4084500c00da40040c0002e2500320341c4038140b0a003902d200042d00003110a18241001035454550340d003558500c0b0b0504207510450840d0072483c03604944078648030340d035102525544070340d0010700c1d5402c207032410303440303040200820415411502c006205803595540590b240015000b000e40f030079041e5420510080d9a105814030a001003080b0808150344910030055207041d1a0400c1d0040550180c482c6105070032a203d001203d4003a0040c101601d02107d42500c1c060001003021b80080d942d990016240d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56182611 1250 56181361 56181383
    0x3030909040501151e120201050d0510050a230a0f0b0d0207050102030f0702010f050709030f02130606090f0b04080a02151e030402040c0305070203090105130510050403020319020a0e0601030207 85
    0x103061030302500c1e41c038000045d080c0c2066640ea1011002c00324a040400a404204204910981c05216802c040c0e4400d88040c184000c04d070792140440c040c01410b81c4034035028401029405071112200c2042007282c00c0c201d4010135194205040e0004100c1240300c1c440030301100180c140f08041c02501911060358001000315101e140c0501078078000700b411642e5900552030504461400710745071199602510043d51040c414900f5950303204902d0080070402d90380031549080b10500602103000c2c900150501e0340e00e440e0203074034180940d000142035400000c0d4086003440103104070f110008400a6180e0111843c1030703011100d4640c1d54240c031411018495952001d05900c0300c07443d0280c000c6009902c01d8604201c100901e040880072160195010300058008001500d210f40c81040074010300100118509107481e52640056140c0054130120390110b0b20200e810000c1d49000c4c0a980f45a2a01d85031042c2c0036106940011004107040c0034200070403415202003200c0342d01c661b0540300941e5005905841c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56183861 1250 56182611 56182619
    0x7051c060b03010e0a1b05030a0b0301060f1502060c0a0e060705061003030806040902010804140c03150103030f02031c0911030604110301060503030a0c0f050a080703080103031407020303090904050115 88
    0xc8980c42401a10035201c3c40f940800d0000e486803103030b406e4820a808034008250700c0440c0440342944080e207511441522050500d0a0382e0b802c2c40350100900412a000f03132454038005000c003005c051001180c040d0340201c0200043c402021040740c1c104422440d04006296a100c000348150080080180c0b5511440080050000caa130007040d051741c1c020340381c241140d07813840108070a0381c0c2941c100900049204000ca0f000640c000104135081c0121016100104000400319180900121300c414101d85030318010801c3c0754114003400c548100034406540713032442190b507118480c4c55002c0c141954a03900d058600038003007080c0301900ca0400040c01d55105040508008500001e6000040d01c02d5181100014040c40c0c00000c56203004107544a220354145180c488840b4404203c4060324107000d0808a0000030303504074010100c040c07103a10b41c0b141ca9415818020851290712154020021041045501698002055449524088038184003650342c2d841c004c1c0c00741c9602144502c0001d15944082 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56185111 1250 56183861 56183879
    0x813060203030601030501120807020103200705010504020f01020c09070e04021c091101030b0f120309040204030b071106060f06070309050307170c09060d0b042105070302010c080f07051c06 83
    0x140144803d81c2c05002c6e591300d401d40103140c0410300d000207000c0541040410015402500411900c2c541d00c4410040c0c0f10349444050382660100e9000c41303050b55680704100462500640070522000203100800c0601180e0000c41c44003600075000c40706111480c030b03010040c0d035187c0c4c040b07481000158031682d01045062080740040c00210b0022503649030f036900e040310594441d1144c04000f150080202c404001403005101d14280411310780e2070940010001c0070603944981c002840254480c0c540c00301d4600c2c0082004003104004000481242c1125051080380c1d46d80300c9110f076009030111031460383c1300b00d1480d042e54a80302036408281c141c0a42400041d90040101c1800d80c9517400d44162090300201004016007403808440c00340e4440981e00e1a640814229407100b84e20501c6549030380c255003a030600c142e941c0d0703002403030a40c0003407030004242042580c2030103204200c03102400c0c903081a00341814800c040d2080200404100139010030608990b0303510400d00e456001c4582c10030000c2548603c803034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56186361 1250 56185111 56185117
    0x6180316120e010f0813030203070c0608060114030702030d0507181404140108060a0903022514100c060213030c0803040608090601140402032706010503011d06010e040813060203 78
    0x1c10128410310320310001540a4502070b9004c0f8010382e00c0108540e9540d100804203844807406400311f200a000e54000508060303003103030150446403901802813a00c84001018262050802c52030050180184854142c00205440046d000d6000109503a41c5500c1c04503442042c4042031142160541000115103000361541c54549409450520a00b0910030100a5005080c07080f1016940300c00005a0300381c101342d11080740c0c81c1c820b00c152260b040141142000c05215480045c0005103410002c00003807100160107054803409840e400010940040050001d548014010b48803079000505010030031103108168024550250240181c0e580368140641e40c1d800600462020442d12004264980000500b00d4125a8803003642020801c150050202a4001924806420f48042c480c07a03941d248a11140c0c3c0d02110100040c8980e6251000301801c4d0303190300035404c041d4410401c1e034070041180800d010f41950001b0441441e103490700e1504c80104d104000c019425480c2c00100032075441d50200007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56187611 1250 56186361 56186393
    0xf03130204110901090b0c03040b0c0c03100501030b040209060616050a060b0307030b0106030903050f0301090c09090506010c02090402030c150415050f040e090703120207050411030906180316 84
    0x100204400d26034111414841c03c1056404109800d00800010900d030004140d825000402d503402c155a0f800300400a42240d1107008440d049000016250b0508000c05403c5904400301402694550b84888241e07180c041d0029010321040710005146840d9602152800c00c0840b00b640615009030400c40d4903240300e43e2040700c2072420460100d820f45400070704007041d60303040050300390941d01e0801e080d0020848031004800340041031021805444482c805180204030300d10020410a18580d002440d2a0513900103820b41481c110a00c00f040e64803100028007e0350641d2000c081e5112800001e14080340c81c4106988400040c01c0c07900c100c105503011380100c400705560300640445d075000544841c000d50b00460b10201080c0b004014030a072006415800040c01416a1301035900c90722240066460a207416000d03900040d02000359041510444154280f4011b60303074110300304910a82c1d182e04000e05100050500c403610045402d80500840305440f4414607034000e552941e290212501018001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56188861 1250 56187611 56187619
    0x10807090f060c030e040903050a050d060504050c2a0d0e0411040306090b01080a03020c060d09050f03190503150607021504180515010806091e0405031201061409060a050f031302 78
    0x50302d000321b06040c001d0090702c40e490388846080004e40170b0f085403150803000002c40410384905001950b030301d5922849015002c503030f1242d9510340124000d0a2148a88a80034000101d8080342d161081004030b222210000c25140c90805d0f020500005806001c10140888040900040000070007400e5404400311500c00c9413040926aa00c032071079900c9014889024003d070b0001000103545140c8140100140385e481440051144119111319240c803e103250b03030b40441d600006600f60f00707170311000380d50b8054015407914502d949042800140000c600d000080d014100110390b400442d80c82d00034000d2400e01c0d1580c000e44907a0368040e642c540380c03412200c5030011803400020800c075a121503800c03041214103864030802c64403400c06226194000520032907401180c22170007188404400641030160b8010b0340110f84401c0c1007400c160703180106901c9001130000305100c0810f001200e01c1a203103005412039026880f000f04070030036030351403094620260480300b00004002101b0701d2501d45032182c038003d42d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56190111 1250 56188861 56188877
    0x408070503060c040e130b04230d0507060906061806140904030e0f010504080109110306070203091e06090a031506140609090402060d090b0f07021506010807090f060c03 74
    0x303250702d9039825140012482d01c01c00c0140815610301421a4000ba5002c801540e5400d05403900703080b020082d2412030380401d104c0742035150358403203007400004094800007900301c1e400304900c003800c64401c00746d00414180d1111403000520040c4c0c0e0000d00100303405440784c52510380c4403800100600c4a4000c00e11001070307200401265051504410348150f41c10703115000790808440803c00050309084400c2d0400c4000c01001c10b12040030b008611001e88603500d200645181d02c41058140500104000d0441d4800c0c412111b00b5501c00c515403c800c41088520301320481c03400f001c2065071140044040c0c1000e1301030000020405241400c081c61003000307030100489611090800d50001d40d482d65542c2c0003c1c103115407900340c6030041800b50014401040649800002d20002042c0d0306004419103100c01107400b00032200484080203584940709101605006e02d12656001607c14050320882c100000140021011030142031210050080701203241800c076501c200042020f05031105c1100015005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56191361 1250 56190111 56190119
    0x3050604031716080a021303080a030207111503070503040515010609060215090d030c170a050717070f0e011106090f07120f0f0201121a0405070e15030a06030512040807 74
    0x10f007040b1600302d5000c1da10160541c45010080300030f90054980359095000d100300000c006003109004007003008407034401580f01c224174200706d82c400c2000c54a4500804030000d0441c1d40100c81012288e10501d5030503c2d907144e40365810154a0450200c0041c0700e00b280c040000308850350007002000031a401e0307a0132954807200004c50409110000e8034204196403143c40f9500d1100c2c025040003c110711145045049016500c0641021440544250062070341e1002030254282c0d0095003007415003140041ca600e1400c000d440201883c641c02c55100c200900c51094008580c071854000404446075012608981444811107440c1c41d14403510070018480d1100010300c0c4107902d190004c2d103503007100b52420108680d85800016a20040049040010315546507007001c2d01841280341c0c8002d80ba01040ba40d4000d00c00b407108a580c0500024180701c25640c0020240e13485c043e40e10400000e22083d90f469840c1c2c02260006042240c0004140b03004002910031f017800f4a0b0080d01c2226150303400c88561a40c1e07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56192611 1250 56191361 56191381
    0x110a05010219020907020f0714010f09060909091703040b06040e0c030307120c0c090e1005150f01020319020f0d0915080c0d020a020c120c03030702010e0a030506040317 74
    0x7007016161100007103000d0740c101526110b904617a02c50528015200c41ea46101d5209043c0811a0403041040080550b90320311540d0010f00507103c081503041c151100340c104140506400c1d01c5110307000c04143c503108210f0400401c1210382d10800300f902d0040d03460f03040c245403a410f4801c080700d42c140280c2c82c01c1e500703194030000055500ca00400c00360185150107810789480b00c1102d0200014410303c548200400c00181c4074000e850000e0000c04400a0801031a5182c1c41c240602c56403d42e05460500d0b060056118004d4802414100e00722000c1b0140061400140d045004511a0030740b146140c141c1c4207022a0085a1082e55094800c1a1451100100c074150b03080d05c11070160003401d00248a8954106005490640c0c1019010071010704042c030740090355090382e11640c01c03a801a00300701da00007900d09140307144800030541400980301b80f20010011940d04d0040036001b0341080310382d2504038200e84800321008042d503081810350b0780c1c40c601400c0141010b191526103030b01d003405500002d088184 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56193861 1250 56192611 56192623
    0x50406020304051605101206050303130608010506031e0a0b09100f08010203070207210b1501030f06030203120f04080706020d0810050d140114070305190902090c1303050a110a050102 80
    0x40081c2800c03211030103001c040791f2118656401d00c1a240d561100801c1996040014008245440c40c40718501070406000400c100c7c0107a2005008410500c203200015080300a24103482c100408040d0081d603451040741b002e0500540300581161000c01403080c510409000c1c0e1090354450841e1840c001e668035486401c030b1001704c6400b001a08001d00500c07840200c00d60306009a0110310184d41080d01c1034450407440d00303081d28140c650509d42542c60200f0358140c05050154010000304002c02da1035500400d80f15410310ce10005207007800540f440060b525801690044c000c1001203400840d1500b00195035a13542040f0703070010a9500c00022910120881010152480034022200c91452550b40b06201c00000c1081085552123246000a110444104a109070020342e80031802c1e09010144a07248141408080401400c06801d900540c5a60341c1c03113500042c100841a41c0c4202c1011441c02c1c0740f00e190030080841c0074a8040b00f00340000202518118502124040f20481d42d8030010782c1e4580c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56195111 1250 56193861 56193869
    0x303040b01030f0302070902120406060b1c0518031305030c0603040809010c1a090a020a05030a03081501050903030f0406080105060313030e030309030106181a0901170a060504060203040516 83
    0x400880d00500004243d070811080c540d100e401103402c2c0c9501c485840c4d050b600b0808c00607060b203c1510800c0140283d034042c50000702845051249014503107400000450009010494035585074808500b00300c2d00b0440700e41115044400303580c0ca5034243d01004100840c10b00c91140700c2e00c81d1030369180181c90304804690003281e021300802d1810040c90015207008846441c03c2d00c0c2e0031a00d4141c2c5868144d0304c92513610071030004016240f070444a104004412000b900264003942c4103403855070019411071301c0c00ea04052000c600c03075034440a40700103d03118030503150b000e41c26002c0030030074035268030402000d44195072054230366104581c0c80364207100050200720740d142d40007030b0021130345c10100e0b0144e41990303c4140c0240c10740345000c101d4800329094500c550300c03601d108480b44143c00c03402c440c00c0c4608045800d4180c0c820310700081714070014540203010b014507071014000031050307079407210104074507034525078000e9041c0903d28150a00b00029041220252014024800480c9031206c4005565003a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56196361 1250 56195111 56195123
    0xc101701051909050c0906040801021306020609030a030513050d05030106020c0f010503060d020f060a02070e09010204030c031401060e0a0b0f1906050d06050306090a02030d03060e0105040f021e0a030e030304 91
    0x10319002450b4013600c006012007560860030010448540c480c10001c0000d0071383c00300051f940342000845c5240381d000c40d0b8084001c40d04564107004050b4030210031161a8403041c500419951102210390041030388410005149201d40d142000300d46400002850407a5129020784001c079804800b40002d44401c84200b9002500c20000507069140404c25a0a0140040d20f41050340300d14801088440d0300c010320040140e841003408001c400e10308404a075020700f40000a508280c0755985902d10038240d40002032014034030128010328030f002580100300410301b1810f2101a8184800510001c000200000303001c0d03242d00191f40000c0c10b24400f0b2040c640c0745541901c2089243c450100d40c42d0300311010302c0444e00c0c0c8402000545580c104003160041100c00058449400306c0d03c1054941034034050500d0516080a004202081039000510f04440c0240c81c08994844a55040402882078440881c40d82994541d148503581c00d078000341c0341c001c00302e440400030b06070040041c1c5c1da0f07030108032402411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56197611 1250 56196361 56196409
    0x20030d03051515090406120807020108060111071401080c120f0a0902130b0a0518060904020103090219030212030c10020d0b1309051218040b030c10170105 68
    0x180319500c4503500c4281c000800d02000551000190000a8410302c0115660b000c283c0b0000307032805200e20b42c020484808141e1040c00d081c1d82e480c600d8021a0030181c18403424800060890340190040b858030140c00301074843c065100c1c1821311441c00c81401c0d050003e0000c0000880d264a0710701142d42e040c554030454481540c0321008021441c3c0024003c0c11540d80324000b00e0016110b030511001410b401e804089982a000400c0c03200021143c1c0c46540b00c0c206004030301c040d8400219219030840b00503601495950303650b00050700640400700d0002d41081c54403c60740320720b507003540c10102541e20850780309074000c0b080003689549006403200748400c0d0300882044512201e19600a11780c04266080c04034040c10154002400301020b01c0c0382c0354240d5110b003076440c10018240030981400450303900582c1040740c242d414a211044039114240a65030741d0010352025541000400903029000f410307001d01e1303d40031350003c1102024a52400c1010401400802d192030140c0310003104288a400e0846 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56198861 1250 56197611 56197633
    0x230105031e090c060c0105010509070c0201050703081b040305032a0726070803031803030f06010323011e120503220b0403082206050301050d020103020c1005042003 72
    0x90003100a04018028842d80303495050b036450320009400c1170030003c00001029890481404070b0400c0040142c010032910011000c0181e8226040d034000d2605072600c034040341d540b4400500c002c03904d841460454000420008104640000140250f400601040340000d08102e40d419102112465585841e00b01c10020b0081d8052840c811410711100310440340b040e03206150f1541401d003190400030300c40e0400420002500c0c200c1003800000003c480055145141c11000d40000780800fa100c103041544070155604580b2048002d500c0c43c041701015503080d965240102541c0c6210140340b1140e050a03000000f0311880040104030f40190008091890316281908254001c103a0a83c40c071030201c021007000c40c101c03000b04060301c0a1842200340d643d6685408120416151050a06048000c2d00c140180006a40202624119642514108442d1503148010f901034012040d008016101d2068801d105c8841d0780c204038051402104560038562504056040300121110040d415904c0424084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56200111 1250 56198861 56198911
    0x50601060c02042301030b09060403050d020a20010204050109090203040f08030601120504030206010513020a090504021303020904060605040b01170403050306041d0106080715020a0b0402011823010503 88
    0x491020b200420004222090805940342d10110720440e01c1c80f801e800e001070041242c1040e84a40048034040184680d02c1e156400610520402000c1030030607401082c029055401044030347c049170341b1074224000b03200440b503006000390040d20803140018800440041c080f025807003102c1c0103582001c1e8000c1c41203100c0d16003122560015102c60b0401040441214026407a413185034001d41c829409058254503100c04c0dc030300c1c8044040c2e55103940c0c0c4104415003070960088441c4085035400d440150b25281c1c00e4901200c500b5203030b48081d4000300040b04110401409600840c02d98030211410008040307094011a03400705904840c100780d501c03038404034003c03e002e00007031540100001c00c0414008000001400341c080511804400caa46508040c0311030a000d12890f00502000300c003c200e80704074000c009540e003007009005888008018049400c0da4401c003804403f10b82c25131002c040e00b41d80c5040100d03005850210a40348080301c8403086001d588110120b81c010501d0f00000c00402c0361700e510705 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56201361 1250 56200111 56200127
    0x5060720121308030d0515330d0c0203030405190c090b040f090f0201110c0a0b3405010b0303130e09101a0906032103150a0f050f090405060106 63
    0x10480c1050b021400510303100b0800061001d5540040b01203114284500f03442500090704449501c04d00e100000203a21100c144107420001910880041810014a480d0b078010701c5000c00b800c0542c1d0a0107041c141e11038001006601a46c4510111981c20241c00c0081144415000f001028401c009908104412468205041190707000b4400200050088103403c01c40f206080103e44a00100c01d4003000c0d0f40e0002d01c01500150501e000d44203550362500010300b0000c85000f40c00f40d40c1000b05c0e001e0389401d031141503403100d00c64201c0042040b1071a481189a465081030381144c0135805d194185a080c1008000d45501d1b810007075451348418200100862401c4009250141612400252200316840c0d80502403541007548c011040e41c1c00c8600038052002c000500407406035100303070fa6195001c880b224000b210011001611600da8640001204960106240f03803903012003a5140420240014440f000403250304030342c0e90380d041c840d000c10311002c9001260003030502d81100e40108183c0340a030701b00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56202611 1250 56201361 56201377
    0x90f0606070302030d02122e0b0706091b17010c0c020111010902090403030516080c0706090f0503130906050301050421020111070b0f06031207030309140303040506072012 75
    0x40d2420845c803102c54508903001102c80c01d0100c0e080c8030901c01038500c0b9092101010b003c07000c00884070041c20040c00f8001015108240c0400f80c00a00201489610742c0241d0003a54404000e281c1112412107201541546000d11031130224203602c07440c0d5010052187d001c0c14072445d01c1d031601510a9030019104003a8154a01c000c1d5502c0340041c5005969886100c2d105500c6910002042e080c011070010000c0101c08103801400301d01d10500420324040700030f91301135940c00320b0003240c541058035014040c0603103004014410321020412002442040301c0c08400d40c7c05d0071404104950742c031000c25003690320a64025105690b80302c42410300101e181d0031480e0040e403a00004c0780720b6004021601055100340c009807040d9018006000c0364502141d0032940080b000c8000707080c90050200255500e1042041c0181030565030750100c000c12506802504d007507010281640d44903c0e10b414407540340d13034040701c21170000382c500309018040312026511074000d2002000200200d84c81c001d016052030380302c089 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56203861 1250 56202611 56202613
    0x18120307120f060303031503230c030303010303020303090c09062103040510020709050f01061704021f030203041101022406030309061c27110111010c0e0a05090f0606070302 76
    0x8042035040c0c0700c2c020028101c4140c0c01c0003c00c0f83c03460074002c04a544240030818801c0210000304042150396012800840151040c12600d0095030f0000d490090f518040607010300002c80000203150b0040055481868440140c409120781c0b4010000200c1c030803107000d68000012103001c09208040e80300401d0398034841c000c070f900d09501c0c3e100250003522507800b03003030050388116400d0110090500929030400032401e1203d403e54140342020342a03806022100384100c4031080000c0035540c1d1550017200f070b032181020281c181c0ad1750140c0200a94412101520785518a000e1a0055440043c107400648040e040312030004250b0030414401d0800600075030f51600c004e002c0c220103641da400091911070005012500850794500070001030303400b840c00b40800f00a48051049407004801c440d108035942c0111880d845030080d000607a0b54002d0044410065031a014414a46030b4020780b548140030402c4416400e1142c0e20700c20000c42a81c100c40c42d807a401c0001c4049405402c4c07120140c03040c284280 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56205111 1250 56203861 56203877
    0x80a060306180204240b0a05090a0f03051506030615030a080c030a080709030c030f0201021603060617030f0d0e030c030a09090501050f03070b0d0f02030109050405010518120307 78
    0x140781c000540707580301c40e190400403a0b8003088085241c180f094004544c6442d40c9100381041c80300520807419440d22a01003068000113106519034403440456000c014003e0519211540361140034a0080150000707d60078480d080c001003400303100005442c42240b00070003c100325030b0f030b480410949640203d503803501446654030203000a10b185000d0000d41c00d6040c0150303200c101d10000107000280241c903140c140083c2110a20105180004907010380741c00850b10008603080d4070040785442c0046021001c1c40d4926100442044a00e4112404407501c07521500848041042c10b00d4480c4140c0e046410f50420812040441058607084080980c90310400d890070a014040d82c40d04550140341700c20b0008811120900410045100700340c00343c003050b00c00e404500003d0340401c0d80c9045c0c03070243c07030003100c03011401c18581c5055401076184107908502c103548a5941d4643c1d10050581a201100e00354206400140350600a07040d0700c05840311603000b008822846d520185c420f5202501150402001c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56206361 1250 56205111 56205113
    0xa060e0a050109110319030c03030c1205040c0305010c030c05070b27010c1409060711030c030307050c0f010329040906090b0402100206070f050d020c15012c07080a0603 74
    0x83c41840001d80c051a42201d080c0a5082018102415400030700c0070425a034044201081d070020b506440503915003000100695a4030058822920b20700c1c0c40600d05003460201b204000307440c44080f003242d22880080c409020708030720036002c0d140710041d8a40040c0003030200343c0c04501400d4a85402110300740c102411046405484071017454003028032400c582d1101501c105441e8003100301c43d0300e0400090002e041584040006940c2d104640010f80241c03e814a203208030f075000c1c08080c8a4120003401c813075690102d460800d0b203400600c2a294480e805c4082254915402401000c2d5a482d454400440c5e03a0415444d410700502140280c40c2c01540c1d4409420000d0071354410140642e0207034800c0038083c60503104102d1030301a4602108115004942480b040c190008034049512461f8106075403500d41c2180d142d00280903e881c01185803050045c5800c25a4280324042d06030349030012040c01c4001482d603111010005900c103403c606090b000055a450710521302c0582041c8919008242a596 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56207611 1250 56206361 56206363
    0x904090602041e06030504020d0b100f0801061a031b030703091a090c0f0f042d06081204081b011e09090c0c0c0303080603030f03090a0c0b09030a060e0a05 68
    0x4160000103030896010100d0651180090440c1c0044c001031500388011f103401d03804031b1101040c1c0b000003465142d135040421101081d51240c203003d414081d41d040780785a51009420b000c1c01301c6100d02142e24807500c1803800009551011240320700301401d41403201c060356400300c605a50004140b0300c200340da1850f64074001040c1c88600146045140281c401508114603c94181203c900b02544142c0701e00d120f040840e1540502440490b1048500049058070350442d24100c2d0414132400040400c2d070302003010607204580c041c100760b98010044038140c100300014440325110301d0040c3c044903400080c81c0940e0074011034401d00da8840c10f1508120300740ca61842080700628813001100412245035051000c481680b28521810f2294600040b040b0303425103800441c0e124500025040061010014026890410807207003100c54481c0d0030780d0380c0d2600110268a40704014012144072040d014002842d41c401d10686011250040280c851500c050380d44500030101043d00c0802801a80021804508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56208861 1250 56207611 56207617
    0x306010f090e04080405150304030c02040f09080705030a0905060f04091805030a020a03032004050420130302010e060c030a080a0b1c02040506040c0c060e1e1606030513080904090602 80
    0x131041c0baa0399102d500304000c004108001c4489444c0440381407040002207036001e6170203d032207a0180c900003007103400441600003404170180003404003000015404204140000208980b10181e0360b007540311600d80c0100300607445640e004d00e29450301803005211001595104909900111100071201119603450358110781004a8940141e00f00f08100002e0503010302a004045200340301d83c210b219075810b0001d02d00c0c02a805568051a5200c4548a03c2c07a0f52105c406249804140065103846502d6009885040140070803800200c8410b000e40250400364152802203117000301543c00e088030400111500070006001c60161034580010011549541040516241c0b03120004c080100b01401404160340001d402d01c0e01440c41c2481b84140c15038003842804901e50320482c00b00d81003507940005450081c20f4401c1d00d2200740c00e107082c02c0e18006d0028029500f4181e08408a10700c6584003c2902114421292003400d91070045140c0c000904501c014042d4110080c40042c202c206516030500f20f030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56210111 1250 56208861 56208863
    0xa15080a0816240608030c0307060b0d0b0c180d03050a0c03021f0e01050105100f050a090b0319050a0902010206070e040905060109020322030e0402090d05010e0d09050301110306010f090e04 83
    0x2944042d66404000c00d10b0003813501a044110056281c0705c0011003195481c03003503407001740c2240e9407141844003640d107600300c0300702894001d50030001c00e00f00b40c0803415042c0e00154240321415001603010742c0500b40304e040c2c031a04a403d034480c00d0070844601d0301501c403010f8082e0100d04600030244000c0c030040103103054030007400401400041c80d071101c00803d801c454068000c0d52203052558124120141d004a03548202d0300341c0d1501607100c1404141c240c80d41c10042c0c012a90330301001c400c008000d0f100601c4c4030840b2111220034451034480d001104121040158042c0c0180c0050001410a034050032024404070710107480054200041d444246c140034081e042100c000b07400105008072940c0c1550800040b80d03030a0803688400d10765603409440c3c003100444040c045c940206100b030b140d40c0d40e5440720444a40000c024094983c0109400303803140703140400c030030119518520129850905115107441c1d00d2a803071070180b85031201c03401994880c0c1d0f030301a07600030011520340c0851111004000c3e14056 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56211361 1250 56210111 56210153
    0x1a1606060501030b0303030907060e0d08070303020a0305012102060f0c011b180e010504090204110d0c090902070c09020c01020408120d06060f0804020f0f04090b0a15080a0816 77
    0xd400d02000501356520035501610aa00c1401884100c038408140e001c01c441080c2414101e4408010100b509661541c8014110004c00305d07542d0103050b0160001d200740c0e11555400c1049a0300c841040c100b000401c14000d500c0310344d4031a0300703006080c050010401020002540c1d030800c1031000b0080c0c25900000209821a608480b403501029003140d00c0e9141003120300d10540144e418604c6110070080144a4903114540700c2058006549803980b2084410000c010300c3d41d40c4503041c1c0d0050001c1d00c0006110341c001070038004005541b00760745c803c0d42c0c411070784056400d0b15103240c412083c001c0d410603424501e4a540c200b000281110b010070080c882030180195585e100c400e180d045c3c00031210703107a22480520106416440125a2151066600c81e40c1104c0500204c14204e006c03c25001114440030b80245c688400300c02030001c0520710305c0c843c60138000240040311520000f03254041f018401c8044030b82c4210100300c0040c80c2d08000d407a50103144241014a01003a45071003000d00e581c11000c61300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56212611 1250 56211361 56211371
    0x72a090e07060c0302100c05070602040b12010506040b0d02070c08070e04060e011401030201120908040b04081605030a0b041502071202060f10060c05030904021305100906091a1606 79
    0xd00032007032148000030b000318140710b80150001e440c06500c410003000c141912640c1c07140b1114a01e40554251071131180c1051045480b00d0311038600e05030720352003003a081e2402180c10000041e685001c030b08a41c195281003076860f0410030142640740281d0450a021504102c040c40d010170b160700c042280e41c00a10036110824494142360820a01301d40d065030b00e03a40a0303410024561040b13a00b40302c20a0440b94207203400107109403d032075058010016480002c10600000800280072041c040140054558081c16a80c402000700018040d908171403040d9501904407d001c0000300b040b04400300d5007c0d001c1d1524032a6040e29a034001c04a83c00b0080c122240c038150040d010009504100b0154084a40c08400d2000e040030110541201d0252007008100540c6604c4501044070a00589405481c0540155240d107105401e195800b8a00e000c4c175400340040211442d0280c0c1f144e801e8008880980c2ca0704420030b0304105c00c01d000d200840c0d03050081188108440070071452131040c1c034030740e040c010a00060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56213861 1250 56212611 56212631
    0x120c0203070212031c0b06031518010801060609090e0705010e060f0c031c0902012709090506040203061f09090204060510030f15051e0d050a0807050c100203072a09 72
    0x1040c10800c0410b400046c2c6440c04048040c1c540404594002c014034280c0c5210320900340004001030111007404c0d1100b11050000281010150800800c0c4c07001506c540d00040c0d1200d40c21411101200c00c06051640004810049940202600701c01c04002410b800d24220305840300b00c0a03035100d109201c40380c0e480040e280b150780c0d0003401c82e5207141040e0300e07040c44000c8a07600000c0c035a040681d444059924030825807014100c080a02c10024151aa0305011a41460402c03c1d15643c1c11503080e40a80210b50005d211081880c0c2c102c1c030142c81c0f03400280245400e1920030300081c2176080007240c0040e610500818981d8818100d180003448542d03000c85c0e54690810401c007680c815000340020744454074001d0200d50b82d16846403075514600101300c41c0b544241c03030000b5001c0c908400d004d4180d00031000c4070010b220358107005001c030038003e03411520506101800d112210050780714180c01600306001c010000b680c03405654200345510141d500707043e6440301e0160309002c3c481c0e0207021010341da02c424103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56215111 1250 56213861 56213887
    0x20c06071407060509010206150406080d0e10030506010206012912060102151605030c040f030503030915040b0a241403010b0609011704030c05030703050408010b0907120c020307021203 81
    0xb80a0000e074a842400d100e88580083e5a848014101a1155400d80410a49601c8540c0100020010002140e4601032560030150a080c070707201c410f6018460064281c00c01c03500902070b090185006078003c1c101c0b03a1818990341200450302c10302d074441b0b0b6030405451140f40300c0b040c003170003101c1150300c1c610340b44c2d00b09100003a02d018012a03100e18002d1104040014900301c44403000c6681b003035810004e641e43e07500417402710300b40b080c5d0304080c210103061403001c001c0c850700202542c4030340503e03c12039424080d000c41c0344c400071304c0440f00281070001200018000d40480e4104107440080042030010b500860301480c0d00b80c030580d070004202c0c846104070300d140d10700c1c090081115a082c155010361422034880d0000f404e075007100b21410340e00c000032008031301014443e44824140c00d03046010769449034050300e030003082ca48c0184920b144540c00d192038103440345030401e0707010f00821075900d804400311261040310000d020071f050b0403030640c04180701000240e11180286c89042100a020f5941c4c1ca40e04100c00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56216361 1250 56215111 56215123
    0x8070e1806120d05030a02070c0e040605010f0b03010f150c020901080f0d11030a050f120103060506040f05070c2a09020d0e0601080a02090a020d0e0106090b040209130507020c060714 80
    0x240c00b0070307480350550800a41d004000c4a400820407000581d44403244c0c24110010b4285a10030000b40000800300010b102080d40000d059440d401000501da43d903410b0000d10a000a00802a010164501c1080108088800da032803400c0382d4101820505110b400203240c0302c100f64000c1c100340d000203044206000d0140049a001c07402030400c201901941c3c80f01130359138001c2c410050300344200000c010815040d103500303451001070030100e200301715078403450000c0c01341000383c43e01e42c0280e090030055072105001d030050920410b210b99030610381031107580b40d119540400a101c1200552010080c00000c000e0501007005080ca42c0c50140e51042c200040130106c0c0c05031440064560040001030000400c04681c07407130081c2c2c04803150b20b070a4440c40300759802031194914905105142c0600c0649010301074010004903004444100302201c0c0044c1840140d00c038095403d0362212103804d01800819841e440107800010310f01c125205508002d021400550011509035425010b02c0c1c042020140300b0030807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56217611 1250 56216361 56216389
    0x20106062006010311012a05010c0305060603060d110d060203160e03060a020a090906090c020c0121020d0609091406060a0b030c0d0b040606030b0118050603060108070e1806 76
    0x1d200345040c051440e6a16100103010003071144a410440d100300b44c1c420030001e0400340362020341e5075602c501165415400c040000084450303508001420f2207241c000d100303051103280040c0c0340c1c1d4030b5696980704112880c41c40550440d055007540c188a407482d140c01d0907185585104d640300696030f04100c05000034226600904c6000c01a10001002c0381d500c02003103ca8200c0d101410150321104401015203110f0f1140d0018080329280150000d1081141c1d085118000034640035210380c141d0000044503107640104514403142c1424140000d04030710361307000701a480c04820300062000d8682e070040f03094480d0b0308010356664482158803481d480341840160780000080b20030301c00c020315010040c00300340070041c90900854000700b070460620b10190007460303001d074004004102c4903031102400360081c45500101d0740001c00036514040001030181e0414240c1d080181240e06542c1c950004503081d10000b0300c103608020086d0704510240e00c5038039142451882c01804900740c1c1c0781a005004888442e282 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56218861 1250 56217611 56217647
    0x1406041202010f0215070c020112060e07050d0e2b05180f120a24020301031104051e0f0103020f0913031d0d05010b030105130c0618090c02010606 64
    0x4410040040c004041090345035080c24100c1d09401c1e2944143e003000882c0d044100440010010014880d03032000d4a000400d03c01d8880184001c0351010b25003c8a071540541182030110700007003041d5a0046000d483d60003034100c404034420a2040c40d9a06220036914158a00350302880590342c106038007100f106160105140007410440095030a158164441800e01c0c0515028040300303d00c4c2d225188240c0c01280d500c81140e84c18691450101c103141c0ba174410541340a4000140d512494040b0300807a030490707070494110401e5030690420400140030141070a102d000240c420700c1c11142c080440b0b10b100d0005c1b60640f83c01c42d0b165006000c124111a00100d10802113001042184a410707584a010241c0600d410745100d10350160805110b141940e5056000d2420101c1c1c400300031054018124a140543c002d100035224035100c01c001c06580c40006181180204044c400030780304038003026444054102c40700805039100100707411600c05520400042c0d4451605103d051b0b0061f1562500c405081 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56220111 1250 56218861 56218867
    0x20f0d0f110c0a030c0c0305030a0806090703090809130204050a1203030f0203011d090c030307080d0b03070302010507060e0307080c1005060105030114060c010b040c170702061509090111030705041406 88
    0x91902e601c03011406401410701075142504c905000250780d401c0095940601280d5a413100c100024241a100300c586600c240341c84000208003d10902449039101d5004480c0c07402d00a03800100726280e0750441c0f0306c200c2590700344800125555401441c20041190642c40950100b840c20300600780c1d000d0f0491400c2907401040100a102001c03c803500d600d0300310720496201c40d00d03003c05903824025280c107030a606103c00b0400209000e4043c005085d42280f0020400c2900805802c4c541c54002c42c0c0b00c064041001408943c01041c2140c1180031112240010f891500c2c406546004440d00000c0d611072541d4005080e414001a00348207040d00f015003424054115850320303a00c00741000800311002d026010100d281e03428400c00350010300c027040000740140200c1d0700031907004000c050341c02140f120494181003c82c070464000300d1650f00626800c100d01d0300301070006050086010001d003012003590b41c0d4044880a000080c4065030203000c7c250384d030544d030f180340409003815084a44070041c0310b16020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56221361 1250 56220111 56220127
    0x1050603010b07020409051e06060d0b1f050a0303030212060901150302071104050c0309060112050a11030f0a05030414010e03030d18050106180f0905060613020f0d0f11 74
    0x540381125001c0d042e143d60740300380e440814082c00b081d00c40201184109208420a41403418a4040341e02010003241d0603541c0d85400c00c43c06642460000c0c20310144e041c00314050711490403520381d49143d900e0300545400e42d12400300d401c071a1564010f8000075400f24003400d040c0d03040680c4030340001e01140c81c0c5440d941000c96014050039224928410b050340040c584040022a0309070b1164014024010001c51030b181000c100540d004030b0f030001e00c60040c1c0c00081010350750100c4000000d0780240080181030322590380e1580c01c40c00800b885a0603c203805240c0c03400e4508011000e5510710403400f4580329454218400c840140303900e044c0c1e06101c5030300e1030010940c41c00019540800851003000c118000c031042d5040d900415424090559401e2800c04541003e14200e4594107420301402000208445000c200442c1d643d14001042604541e0100e40c06141c045206110303c0c0880a0051428403001902006640180340186015850310044850001648030b4001c0448141d44002e10f0100d51b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56222611 1250 56221361 56221369
    0xa0e040903120c020709320103080412141f060501020304121203020f040306060303080c0c031602030f0703030e030f0105071b03030204050d06050609150d030806131b0909050105 78
    0x10040c041c90080c1e50783c600c03400100d807080150b0001043e16000c100801d225903180c012a00c000d02009804000034800007070784244c078040301281260303000a400c034102400c1c4400300d02c04401400741914090240c0e030407440182c50601c641d80d20400c0703c18440858109641c01c000941e652540483e041d5001804100079141650030300600c03051384010880c02c0c1c0040e07c0c1307042e002401a441c8401c0c5006000c2008020401750b58000e03403d59020352503090720795642068503070aa1040c40e075840310b941c000b44120442e1404181d686c00c2c070280700405485540800b11040b0345004400e61003580000c503468a8141c20303041c140440c1743d80354000c0000707000e40c1c640350002400e000c011a10fa01c01c0350030112007080526200c2d505541c0031704001402405000000e0030580e0203880c044e60003901ca1002e00f0301240c02601c80c5c446000c11800003030142c1c684031240740c9040e0303014180104000e410a8608101162103201f620a6a003420500d40d4000640d00955100802507106034110381d9403d0b2400005100e1691 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56223861 1250 56222611 56222627
    0xb1201090c0f1b0b04030f021203010f05010c060f02031311030a0201090515070204050411040b0a0e06060a03060306060b0c150402090f0601030e151602010b09070507020a0312050a0e040903 83
    0x303581085111071803c18156140324002c0703d00540150209400d000405910248843c0c0652856084511010459a80c240c45100030b1049600070034509a0401580d406280c2403401280210030024951058850800503680204d0b0303d014880e803a0302c0040100100c010f0030202102081d401801d68085950010b4884816030181c03e100b491403083c9000f2081030901110702581d400b07041800142890303c0d064502c510103c640c2803180e401d054034103001d410040e07100302c104c450100c10340c1d900d43c81e01401d1048690014908408054aa0f4000702c00b01300140213110061a0060950303940d0b140800015042480154075003402e080303c0428440503a903031184041d000a0703103a4a0040c9034440b800183c0c01052104100c03038544c0140c070806c0aa100c800d40507284610381003010004c0c443c008038000ca00300c42c004800c0603404900d60b00412251441207004e003140d28030140c03520203299100c0d101d110013a011110b402000410009005c804d1540c40b041003192098151020300c480c400c26074015003099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56225111 1250 56223861 56223887
    0x1060f050906090c0d0c02010209042304030f02010b03010e0d0905060301030803010608150301090501090b07090f0e090a021c1e050c010f0315030b0103020a081207060b01030f060b1201090c 83
    0x100d491800b2803944c0504800302d81a10405040030403540820f118064041d41003120348903c00c0d481d01c5007005201e40492104941a81c50b16a20f051643d1260b41c1916a284d00e4010681150769a5a0f00d014a4030240300320348116074210000c2501131450300004054454540009000b80b6060004000183c0700109681c10344a45044c1000300c0c0d51000d4102c0500e2070309149443d810b6007070085210900c0710642c0107c034420f001b0f0055500c2503442460580d07000c900ca114040220b400740c6410010302c0700301001540c110309010180c5039144400d400007094110740f594044103034180b120310300301040481c4200e02e040000c079106241440d003058a440f44c485060740300480c18000c40e11541c9180c580300e5030181e09107841412001022549900385030314412000d000c00c03809080249c0c40030400880014109654407001342c00586400007a9a07900302a00881960078103140c0c540e04c900c403d601d11402600b024003401e50049480d80350791100390340340d040c0c107074004013019140c01c58001205034800d45660f000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56226361 1250 56225111 56225119
    0x90b040b03100908090a0e100b0a0f080c070501020708040e06030c0a0b03070e06030a0f1505030d0f0302040f06030b030114060303030a09020609040c030212160c14010b030f010e01060f050906 84
    0x1c9102824120150700c0340024491b40311440c00f070003041c00e09000c2c01c02e1f40a0b200c8080c0b03c6400c0740c1c0740c0110740d0f080d201c2c031850f10020401d84060000c2581c40f611786154001e000030040d508110995031381c0d90998208003001c90726080081001c2c04940580c3c283e199220508a00600218200d040461204110740c00340400d0500e00100040b0600c0c000e44c000589504003504495507850f08481510091110102420340b050401c003410310310407003280d0410140d92005001c3c0c210048035090a40d0310403010050242403517024000018900503480b400750050405071000b00d48088e10800b0542154442048800d400c403400b0144046921b001059075848200c5510004028005000240b0240111801290301c81c1c01c04031140c1c412035154000c2e1002524507090001c0941341c080004180c542540440c20000d200d0315100f07004141220344096040900c0800020072920020100b4180148207840881d140c1d1100c0c4001c075103a50901c55032005150001c0500c1c0403904200c002140500090045c0d885 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56227611 1250 56226361 56226371
    0x80703082d0a1b090503010605040203090c09180703030206011d040c210209040501091a010303080a0504061b0c15020a1e020c03030307081b0315121e0304090b040b0310 74
    0x1d0b04002e6480000c0340c0d0225800c80c1d1420030100002844030080e801801c4c000c0d401c101000406007024029a130141c140171003d802054800400e11400c02d00090031080142c0350500340456400e020b10030316003e540039502074001503040541c40d03103c1061700d0301d80c648000005070070080800e42c41e81040c01503c409551089030314509440d0350079854880900a58004007000621041000560044200d1482291580300e140918444001c00007401d00c000b8000c00c002c2c000080c0c041d42b1070342c4007d9025115402c0020b011041d500d0f90b80c44141c0781003d4a0204da9040ea020003400080a815007014a24410552130010302c854001c00c2c0d10300420107007a030414038000310840b840c002c0c07042c440d0020016040b00e8607890901c0d0004c140b0002903070968400c2c1c101c4c6440317050b86585041120310400340c104c000c20b06d4083c00c0052000700e4003558014030a81c05202c08006408241c90000406980910020f6444034207154064084034809062980b14528014007410140c6000c14981c0c014040380b480003078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56228861 1250 56227611 56227621
    0xf020103050c0910051305010c05060411061303030507020405060429030109060e03030103210e060705150108030a0e04060f05010c050c060a09030b090d080604020c1207080703082d 79
    0x702e90040c0c202040e4001d4200d90783c01c0038264040050004c0c0c1d94110703844410f59a481c401502e040c00200405003075038001800103808590a0803002d086a44080c003450f207000c1401004241030390b06900b0440c001800082c8280c19807426000e1650407000c100e40070440d100001c0c2c0c4118401c002079040f1302a080300c0310841c1c1d1065400f980b1034610b40360004c0090141d030080c0d00035141c0701d0f4024042180e00740c00c1c080d800c1200944400300780800c254551550301d100c4c00c8403400c100b1aa0000c01040702c1600c41c4650449001090200c90f42c001c0c682d12008540ba90005e8901404c070b000820701a03030041d0300d4010708101070301603a4482400c9070390030b0800d80050380c043d051040c01c050200c440190043c00000e910781e8400e0703100781d8540849000740d200c0892a120f000c496030321900c9130b5404000103003000d8007040c2c2a00e000c4d8002e0070000e01140031900c03079401340141c2c16140d4205020035948141c0c0800c079401855003042940d80d00030000c070701410362140d142c200001855803140e9030041d240c1c4a280010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56230111 1250 56228861 56228881
    0x1608060a09020d0f0b1b0301061d03100f020301090e01020309030d0e0304171c030b09010605090a18090506010b030112061505120607020c01051812070e18010c0c0f02010305 76
    0x400040e412030b1070184c240c007050803c000141c0080d5010070f15805450301142103c00136109a80c141c600680c1d540b01c002551103645846041000e554ac0d61500620401d1051200702c0d11407010304440602d400745e140d61410051f5001c40f1039050140500c0c0e4010802c002d0b1011010040310140384600c074000400b442c903d8007441c07440c000c6800c041941303114244071300b03032905001481c40401c0515500311b0246903482e150407801d5660111400e0f41207491781c401405110300070000303000b80b004007408085c200c640e01c80c045141308020401c1c01800d40c0d078030883c4406014003441601d000d0910f06c24428615494a1036005138402c54003005040690b595105c510310524525a6000408004207070200c4c40e5560742015803608401c0d100e94025206808601c407040d406001515040003005207800c1818114a061150246004000151500031020003280c0583c2035092070307014114907005a90f01440305e052140c01c580310301019005008104441e000014450006403078940d5080ca070101c1c40f503c03482c0b481 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56231361 1250 56230111 56230129
    0x908030301030302010605091e06010c03050d020f031005060715110906040602060601031406010e09150d050a03030c03200715110702010201150506040e0705071703091608060a0902 79
    0x41442800008000000d066054216074180c800490380e407455a01c1d0a845040003407441000700341001100c1000903410341c040d800e809945800b0b414112303d0308241c0e22480c0f0490b403122400c120801e07400710a000c015410000300c1303806848144c80d410302d0f2426684440b08042000c5c02175140307241d15808109000501030b411349030301200c054060768440c2e0710390001030740b9100221045030020f4680391042140e00840700055000c3d407810f0f1981500d18000100f403000358200181090043c83ca00d28003e00c1c0d64852290010080d03000341f0160504100342e1074010240e5103146006010907003010106a1701e1004030714500481e00640880650394403c61034420032000b0b01c2d40e00c0104251410210600203a8000010100e90b03201760b000700b003155170405a0012031401c5000d09900b1030f406210604c00050301c036580603080000b600b400f41c00c000c80703941d9105021100320425203c10a0100512000401c10002c806104094100c410a418142807900d603031a580185107010881d00c44d0028000d40d1034803030380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56232611 1250 56231361 56231369
    0x5041a15040603061e0902101202090307060203122410020a0210081902030408090402070203070807080a060501080f0a02010827010501030b06090f0708190c0306090f0b030304031209 80
    0x41840803c2d50307401d008009042c030781c000c40000b0b4085c01e6001c0001c0300d41d128100c01a94028406003800798500c804aa000d805107a20b022803983c00c2140c103001d07076010007180d4014041079000350756070301140c510103400715405081c00048d540e0240c80c805505a03441c8502501070350a940200034070034485406ca140000c0c282000c0e412a03062058024020340c09500603124141d4801004640c1c103442401c1c1d81288422640035080c1e0740184007010451030607030000c0c0300340c42c0002c1c02c4510098491100c01e0410b440b41c0d00039083c5a0040d00210104407240c0202401014014003502225020742d100949034020003a0090401c041e01000030541101c031084159142c55000011010340d401e8280039000b84004e000c151210f103140b00c0098103600d8401c01041c072031175000840d09001e8413800020780d6240d10141400b501003400d00002c6000380d0603846074900707240c00d555000c94480d107044030300400c0340c0e140c0e02c08440380f6042c0182841c603520004201c4007280d91111161a04c4200c620040fa6241e5943d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56233861 1250 56232611 56232619
    0xd14040308130f170a08090307081504030306060c080307230f1209030702010504120203010b09040501050f0108031306120f180501050f0f0420060a0906080a05041a15 73
    0x710b041e01c1c0da0021846030240e0b9400c0058450807034071580b000450b50102c6140c80d50b10352142c0d4148000800c01e031701408003c60007a040f9501c460b10f4004c91814045401444115119150104002d1540c980260390041840742042c2144006686600b422840010203c8091107025000d040c1040f10f241405200e03140d4840382c8540398100300c121905140c1c0440c1e020f1041c072030264049030940c9030102c100c884040c0d05171034151809190985c3c080c191102204143c1e815540c40c8e08045054603075110b05482036104500020f000d1a0044420400140680151086900a01070b41c08005002c029140c01d45a481c02c0110710b111540401d03402800d40c4401496001c0c1c2481c002c0303100b64407010141c488541c4142e0003400306940300640704070828400c03501a50000020004900410003210000e203841780c600c401c201981c601176000c0303203041d4001000e090004130118010400e8540c03040c0d0503074001900480601c103d0600b6240c10071001401103440042001c0c0d40d01150340703010384901b441d00004000d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56235111 1250 56233861 56233867
    0x908090f0f04050c13240f05220302130b030303060409050a0f03180b0c030702060309012009030714090610020a12020105150613092409050103050f0a03020d14040308 73
    0x6942c1a03119041140d8142c101800d2107004101000581c640490403d1410240003010f009000c0c12180d04810085003014010100202d00d05680900071113040301000d0310030032701268614418401101041e8212044507890507054902c1e035030300842143d4000004032400700760114a4100340f818001e440c20014244014845184109500720b600900f443c2e0382e00552400455464004000e20f01c14106d40d000560800c0000000514000015582004501c0000200494040190520040c0007440713070b00806400f103134040440c50f0800c1000003511004c0800d6420385035584c0070510b00d20028203000d00c1108040c01510619108000282843ea0010f4900107000030050340a0f000704070a0795541c01e40d5076071a110007418281001125200700c81c1c142510700052030104c2c148003d00503800943c03130a10440c10000c01003800c1c001c1401c003503c00c50308000f03055407540c03404a02d003800e080c1c2c140301c0c01c0d040448240080b0350003040c0c840480380e190501000260481c07900f05074a02ca56080140100404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56236361 1250 56235111 56235121
    0x303080a180f0c050d08040303182601060506040b0904090203030913022203050a03030e12070506010e0f1e0402030a0c03060b030c03120409020c030c0106030f150908090f0f0405 78
    0x110358841d6880e00465401c03c41c29114024803010341000f03040a0079043d410801040040d20030540d080304c102c60aa40b19100b95121104518800141c002401e038841b00140b95000448083c800e60340148402c07980d103490589808200d60246c010031b103129110781e0340e910981c002d544083c412501c100c28020003581c030070304818546a000b9040b810388280c0c1020301c3e00340c02c001032a03519240f0b019690000c0041c04030400039038088028018000c0e40d002a801003100c400c4001c070b002d0340038051062285020b01140e605020710020200c000900340d58902c6084402d10030240707003480c540741d420100820319084960780e90010a01e0407203c41d40050104d03c100c800001840807540c4a05481e2034114199a0b031901c464080607030b1181940d41d17400044030308101c00c1080604d903038020210a43c1c00f9040e00e0130401c0c0043c0060031210a5072003030724a002408c02040800c201300414a00d000414581004604400e441e45030380c60064410050040328031301c0020b0101c1c2e440b03054040070319900520503c150b01e01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56237611 1250 56236361 56236373
    0x40207060e07032108060f060d060302090108210405010f050c03120f01050f0103090b0112030c0204060b030f0109090305030105010e01031b1e05031302010e12011a01090b130303080a18 81
    0x25010802580d80854050003d13000d21941595014a1000f441614107001403000c011890f4883d50311641741c1903440e440000140ca810900314003e0414501921070000007110021608801d110080305a281c10001030085070b13001204007040140c1c034544207841d10100060180307135100709075152041c840b4800c100070402a07038503409410b075842566442e801c1c0c071400d00154181c0f15008001014807440074014001c1540d45c602d40e804490091800801c810241c0d004501125840d800407030030341e00c00008000024a1800c1c6690040c0082001040050080c0e10b0040490006004890411101c001083c0c0180c0c42a08000c590990483d05480d084d15401d101401d50030074250905141d11040c4168000140202c09503881801881c556584c142500d074011103416503100d50043d8001c0d6403424114100e01d0921429a490b00074420f03500d55400c2c0400051318000c01a8042d01170003c0c10003003a0310002c2d065441d0400c495040c2400c0c1107644a00380d20f84060304980c501c4045001003c13806000b4000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56238861 1250 56237611 56237633
    0x2030c070f03120302090906090a11071202010c050c030f090a0306020a09050108150a05090403030908120105092401030c12020f030a050c031303050711040c0203031b18040207060e0703 81
    0x2110f000c4606603880c40c010140c0990045080c000d034460008070000ea25400c3c20303003005900809021000408035080801c1c4006508031400503240140d056020740e143c00e809205d004540711440c14400d0070804003e000c0350781c0e4030910202110103031010451000645034220800e010f03552100c0c0030b54a484d5080d100a0141000b4401c160001d110074000c00d681c1010010b4400c0201405440c00c02d44504181c184031603c00d02600c203d040550718000c10003c01c019402138100ea9511580010055140900f0418803440140c031042c15142c0d140000105c1402c5481c80600d460030a01340030400d0802d544065941c0540403401309000d50000810030030f03003800103004600c00c141a10f02088181c60f000c5619221b40022940d070a9a641c0c0100c045c40441e0080024050583c03040038003008507000d20001c9000d440700c20445a002da8000b00a11000c0281e0f0042c41180c002d42d0171304c1e2801c12003a1510007024194407200c0a00a9074005260302c01d010b0140c11203e08002c4220443c4da816650f4642006454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56240111 1250 56238861 56238863
    0xa0201141305150c0a05090a030209090a0b07020d1b0507031704050301050a060305030909040c0f0605030f070c12050904020c03040e1b04050d030e06130303080a150b0d02030702030c070f03 83
    0x20050449983c8800c5120035071600407040c50340a41d080c090342c0c807020741d040e0b80b00c0009950300c00740d80d0307000000590721400803170b00c10340c03a405c0500986001490024000c180203130441095400031140500b10a50000b0440074202d404602c02059800340d040950420300705400142c001c4c0803409201c030a1070444d00c01003045400c164002c1000d030b900d00c3c0703a0b5012920240002490358204120b02040b5150040a907034009020380146252a60740f4603880c507180d50789a000d0408143c01000b08000780a142210700d03800708850601442c640499982e0703001c241992840f005c00d101001c20018113586031759069400000d081070860f50307540d44581c0301e607a42c00012102c000148810a460850341149035041d0f8044038400350801403192200e58090302d0402d0b602e06d1143d04000e040c4070000c3c00d4240040b40200942c007949440e00c01d4140b00c802c00068502000f803190840104041c100816036810003140e01c42840154010380340c1d22210412402c51040014601051140c0310000c03841e00c075610301400480f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56241361 1250 56240111 56240113
    0xd0e010507020c0a1220010918150501031a01050a020109051b030d0203040b030c07030c060f05041502070503040308070c08120c0105010e010608070e03100f0b040507030e120a0201141305 82
    0x10f0355a580c5c0c1451080c5d9100000c2407a003a07842d90301d00340344003032281ca9142c070014180040710549803401c2600c048020a00ea80c03400d500e0382180c00b042400c4007101006401c0a1038140803003440400303c0c0c03010f0090400000e04208002600c0f100d014400e43c00802c0c82c0b0b80c44419582180074032044a8042e940307403c4014401e0088515000045000100321411545007000355800c558641000328459080300d541501407044900c1c80c440022103a106603a903130004c1450018a50a1504003c810030360740d07602e00c0c02500d204000310310128034000244d80c1165030013012035680302c12518017a03d00c03c890380d024452501c02c500d02d40001c4546440600b83d0381d00040000c02007a0390700c08000d01d110500703125000c00301e0340b05004980100c2c8122a0101404400350440d40381000010105044905895441e107103507560f110070780d11a150600406030030140c3ea203000c3c00344e2000e0000c0e00d620b035044802020009003000550071465030003900310b5941980000b107803124270f1031b00d803400181600484100b10f0385 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56242611 1250 56241361 56241379
    0x402031e0a0203060105180109090c03241109030703080306040204090603050d1413030803070c1b030311010e1e0a050604320d120615020f060702061b0d0e010507020c 73
    0x4242088064072007e0782e0600c04061141c0d2800e0101002082c4000307044e6881c0141c06404004203254a04400d2003004911b055804800300b0303000c900c100e034200320340c11030a01d10030440ea81d8680e034006801000d59401c032110554070341312080010b000344a181d0241070014100300d40081813000200d9024201c3d001e03500c1d41141059001c6a0700036a11404841e9403445c0ca070300505001046080014542c8410681401500070850741c0301c11039a85911440e808040f4034803c4c06000b0560b1105c25010048480b400a110320b900e119846525006140a8024130300034034002504800b070b003001446801508a0142d44050400e801d16030b021049a8140400c8500c40050702003400600c2810740700d603540e01d01d01516691031588011180d51082c0301e000021a516902c0c0450149100c04500e0303a2074410360018880c07000000296070411030b00802a1056411072020400302d6065035140c9903114840d410b825581d01a045100310090080303080c0c00f0810f40c0303030034104000c0c182c001550081582044488010f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56243861 1250 56242611 56242619
    0x40209010906050306070503060102030d0e010b01020c01030e070e1e0108060a0b06090a050f01020c0306010f0e3312061906050a03020f06030405010e060907062d080402031e0a02030601 81
    0x1c140c03400351241680541c081c000003400c15101c2c0c0041e60700042c051050f6441c000b8461203007416a07001d4542e524860b503651200181c99030701040810381c41c070300a00f0f0038451460004003c07901d403005882411109045d65001941071944c40524006468140740c0e900d9043d44c50303a50440c1c0e5a101101d6034256240340980300b648601c0c11000350b0345c0140e00205078038843c6082100f44140c1c00c65080460b410762140c03a48654090783c0c1808140e001e882d5840754011884e01e030000d100340d00240038100400c40b4030b20790108904c5482d50b052141c00c2c1d294040510429800324000300c1d12000380302085403143e001d0381e014807468488542548180c1c222481091254540310820020071824070f102c020740c0000070809074034040c00c00300091540300d4011000080c905040302c3c400c40c1484411180c01010390070095041c007210760019201105020008203400500da541c50081e07045030010310140040c01140d1000904659080058090410205141ca8125811134900d036a03130341d0200404034070a0040c500046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56245111 1250 56243861 56243879
    0xd0804063b011b0302010915090c030b06010c060507081803040602030a110109050109050a0303140105010e010804060e390a1e08161e050a14040615050304020901 71
    0x10030a4000d6a00d0341c4000c05158403070720308840c03003881c0031418003a0594900703030380b110b692800c030b200030f800b1340c0000c540d9a41d140350501e001c001c4003106803103841c50301003140c002c0303a40d00c460700f03060344da00a12255007a2200c80052350140c9090340b0041c0350034188020000c0355580325040f40d000704001139100302c0e20421480e680c1d460340198050040160702c10b010528080c0d06c1603413040384030b070100400024105001e403075840c2551805602521240d0107060ba41b420103505114000344030007500c040610075414080004c0560040110b1541000031801c00f2138140308160f4000c1114008550855503c501c01d002d205850001143c114170541e40b079590400740192000301c03c0303068140001c05203020b10f13040540c1150f040c02c0c8000140c1541c4903500011a5150301000724903078400900700c030f12005500c1d000011000126155481d500d40c6280081081151038804580080d1044104901d4801c9034440c04074005001580c00b120322000c9400e440650f040e0007200a60245000740c8a40000c0d1ba201c55a030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56246361 1250 56245111 56245157
    0x60f03020f150f16080a020303180105090a0204090503130e06240a03150905010b030f0a020c060a0b190906031110050711040f090b06100e0117060f0d080406 69
    0x955041c40341042840301c3c00c841580145140c0e103180409003802c0005843c0c0c00344a400032441c41025a10001c140300303208500c51003421510003500d00074801e9107009400300c0d868000c4010000c9c0281d032030b0000001080010f00c19100c120510b10032003400700b6600c1d4081605484107542050103100220b080880802d5103035103504200c980c00350300910306284400203c000b007918035083c0c4c0100220b17900c0402c0504403401641c1c020204200100d84a0902c010b0380d1042c82c038090140860544100403460141c080410015800075224400160094142e40030501c0b203004080480c8403280d411002041182c8070368044010707240030b10700b8075420740c40c02014400330056507050b801c0890801e10411000a800078071039003444401a001145100c0e201003c0b10940c0d10a21084400040a03420031826040c85800301c1c5208440703103040701c40030b80e01c0300020700f6240002c1c040e54283e0088000240380d80e140c20550707206ca850050a440343c405224107007901c039600705010f81000230384501019070a0781070f68010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56247611 1250 56246361 56246389
    0x405090a0b240d0302120d061a07050a1709031e010c030c020319051b1b1c08070c08031207030b01080601090e091e150606040e0f0901020d060f03020f 66
    0x2106a0014401005040f10350008110114400c140e403202d5140d079180080c00c140900e4940108010f8141006030007070040c0d04800413100c64007402400d001c031710002803e007036654101d0242022040c00501d8100c6602c03d012401e030f01407040d80e107026103045003000c050b0940402c7c0c000170003032201032110850503203c9141108005030320900240b10003d0500c1c009a45541050811502c2c191561800e444204011000758038960040e50440c412031820764140d001050341298080d82c05007069044400294203d00090710b8960041303844010880c0d8030400310042c000d01400c0b00c5d150419440d041280390b604448a00009041500b1440d455001d1a00d0358000d04050f102c0c215150f04100041d918200b008000202a200300350300c210740301f081c0c9881f00b800001840d0140030341c41e5400c01c400b600b4400c058501800b44c1404c000408c074000d04580d00325003200b901d000454060312500791080c06402101001c65100e0325200e0f001400010286540c07084134820b55040f8814080082044101c851183d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56248861 1250 56247611 56247661
    0x1509010c0b070201020405151b1c05180402030109020c0f0a020303033405030711060402100507051212070f0519030b030f070e0105120712031d0405090a0b 68
    0xc00080000c0c0c04020040e40700601e4030005082580d580000344c00307000030403480040351100041200c03d41c80c41500320703889408142c000300b00d0a04480840c0070312040041c00348040100108030010380710303400f840d681074490004009540700d58613142003100031b42c0034441030035032440b076036100e00c1481501096808107541c00402450850392031009940c1c00c000100340c88007101200c81c450300341d00181c1c0c0160143c0103490360b440944910b803140340070301600c80150204000b50302c51010000103982d210000c003000035180c905151507104d02c2c6041031800c44803a1002448610101e0860720f449000c000047c8501350070f0380c80c803c001c220b4500a03a0140301e10311904003502405200004014047c1c0c02c525440b50010701294200c00803610201e00b404c1c20358000d420f100940f84010090784c80c19a040780d0a031034500d4054901240b40c0b14120809030b56a0500a0a0010031400716500303410b0030a400e004084054800d0055140c03c1c1030f071603240c3d4918401125040e8070710740419144448031407a064821000c2e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56250111 1250 56248861 56248877
    0x9040e0a120806040b04020a030f05100e0c0703020c0d080c0105100b07021e13020d42090c0206100603020c07030305092b0b01120c06030902030a050d020c150901 71
    0x101c002c541d04140241400c0c3c109454103034022051b1a14401400142c00c503940006100c2805180075007640d4010300984032a6922203014080341c100b007418581c0202c602040e4030360b036428a20f4240d00303014800002c1540484140b40c41028446507400801c1c616403220001c002d81e541c0e10300b4050021089000301c01640600f40700d03540050a014408d150350f450501c01c1405029a280002080700f200f03042c041c0241078000c03502606058440c0102e050290013113814260140c5082907060969541400010a0381e14521002c40c4a01c8050004809080c00600510a00360250f05c06551000c00b0340e04d4000d40c05141100041c01d6100780301380e54511082101a03e245c910b542c404442d00d812039a90541e00c40816401447d125100b40c400400418400303e1048681c2e8043c24089402401644580c8641401562100024031081d20380c006680c0720f401c00081c00301a5001081c5003002003a0000d10f103100700319a0f80c40003500050800e8007441e00302d07515550345819a10008403070203020001408a0505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56251361 1250 56250111 56250143
    0x5010b090c120c041419030204061d0c0702010503060108070306150c0515040c0501030b0609090a0b030708010209060a0f0e0d050105090c0f0303180105120c0702090601030207021e01030204081209040e0a 89
    0x4c6440415001c0e06c042c00700492031303c0381c000138110741c2c0943c80f0082117038148040b03100700d12400f05080d030310011001c601030910441d030300081d100b032200801507410005100c0c002101c03d03020360f20240c00b03800c1e085052822240b40900c060010701e0210811366441c45510180d1404e05003520109104a034800860711240c3e10b03040054014040740b046070356000d5400d000e0400d40b52500b5a1070303482040c0100020038543e0150f810325040c2505a0046041640104990552500ca640440d1200310991400584d9513580040440c3c0100e030300980c0d541d000402d01062000c5c4041500524050080c035000e84400f4500a82042900d0b690001e42542582060020042030700b0804d030460107114060500c9483c0c01e440e4146402c0c2c000d0125030039420726401150803815401d080c000a6400117017803d04504c0c1c89035640010764803052002c1000c420030140307140100310340d10940584004200520480b02071004030204400c07180c100d0a81c980c000d40c84c0480303554004000003603803500c040c0c000d80c2490002d045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56252611 1250 56251361 56251369
    0x80616030e01200702040b01080103080712030e010207150e1501150e060406050a030506010c0515060f040606030504140619020c03070803090c04051b09060705010b090c120c0414 78
    0x4008000115569400c0007020001010f4010f0740300300000301c2d4055658900b84100400c56400603621810001000300600005031610300b00d07000940c10240c41d0030342c1c41c04081c0031000f9108104c110805540042030310010481c65415041030840b0501091000000c4028800ea03208628140c54020f200387c50010003003000d2403001510405201d00d8004c4c1c0341c0340090080307030156003d84d000f500002d500049660109038540714407034100809180100a171070060b150390b030b65140640c0440800034000d0001c01d42c103940f40069043c0c0303080c016000388a00c0d55a80006002800200c0d0291282c3c4070f041031001c1601404120300d40706051000d0b012991554000080b0000d400005c4401901d03c0300f0407408002c1002c4c500994401c214043c0204003010310706082c00195400505100c80c03440c4a21080d17802c81d041c1d6810fa230fa21040923510b0076203c2d40d081c00c025000d404603c8101c2c0d0000540000d000e0544803c5000b0000500030f100044c086844190f030f000c0c0244294403441c0c01c884030b030740c03484801850 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56253861 1250 56252611 56252621
    0xa02131b1130030c1201050a03120f030f0509030405010801091404030c0f02030a0b06031c090506160b0114190f0506070f0b0109020a020111130905180105040602120108061603 77
    0x2042c1c2c4241c40d1401e0301c40141911584140e4084c08038100100702d008004102c1da003100d026000036107140020320f20755650071a4070440850030000b0f0048000320403d0141c46a0300444040c140040240101e041420100d6261b40c02400307110b000582c85400484c05541c580169803541c03c5258107044980e8075030b101200c21245451040341c0030f020003070144016a408120b19440140681c0c1a0344060404800705403030103c40a0804941e080c0f40d440341c5007000e4000d1420030450708240c038020755501085081408103248540000e0010500314008a00d80450300612088203809079103008101d05561012000d40e0340c04c3c4135615503c03400020522141c2800800307084030a2191500a03562802a0f4030059401c4098220343c4a09a0200307c3c2e41c4c881d07509002e101042d811a80505140c00000c00420216114500032810450340314004511060401141b41854070081c500810250406103003e9010394049803aa01c0031540d8a400810922004541c1602615840b40b6001040c550b007202640500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56255111 1250 56253861 56253913
    0x4110907022b0806010c02010801090b0409140109050106060801080a0303090204090f05010b0a0f180c0207031704090605060c0a0b04020406051e030d020f0714030a02131b11 76
    0x7001e0394102e003091140c46018004694600036000d00403280214000b005180d00400007410040d0b401c4010700541d80001d515415907550500c0840c505a5040104004c0c06000d00014040d000010b10b0140310700066205034440d5100e2402446820b030398003003c5601d1442806141205e401c8515a070380060302950103011030342c0c8064030120301c041c0d0f55110b1143d545406c8100f0f58569443e408103014900e424130000000e48403400b64a400d050a050038200410b090740032450141b5592030807524518000c10100008641c450118000407100010021445d0007600c101a0003905044011802d8500102030340d03c6959400f00034803c0d00380588032150080b001400998119940d20300104180d05c900a1485d540d1800411044400a4000a01d071030651503015800031900000641e840d081800705441c2c0171100710412110040004900003418884505402507206031000d010462100c15501310405141d2002d0a421400c42d510030241c407550812203040301250012800c00c041c80c2090b0011040c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56256361 1250 56255111 56255113
    0x9050a061211030a020a0f02010515040509031614010b06040506030a1d1006180b090402011809060e160801060203040b0f04030c061e112e0c09090e060411090702 71
    0x14502c0c2090103003d07401070f03c038001881d80001d64aa00d00b90881c0e45c0540c401044c5c4002c000c503180c0200216100803a650105120326258008508040c80800581c2d00e1812103070401c40c01c050491504d1140c2607040180c2003601e50920340c4c006000d24200701914110740b000780920b032940d1781d514a2400284803000300b4415a000f110001042e11504000294500038041c0300065140d00301068601481e01900803c408641400305030411502c43c044901e07009942820418280c0629000d04035041407542c104110180c80c000000030103005481d070850003200262034034000c6180f100030455000c1400d001300700140c1c3c030030001000520001c40080c5034401c0180760302400d06849649800f441c8078140d124000280b00c251703100805c9640f6a02d50384540f1340c18140200410001e410581d142c0c4640080d8070030010b4541101c1044a100440e040d2043d203114108020f504800710307004d0140c1165009000d102c600d41030450b6581d0303200180030782c01a50000c00c60005990350318200a041c0d0402400e200071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56257611 1250 56256361 56256371
    0x7020d230d0b13060303050307120213030809060c01020c0706090e07021f090602030c040608010b1e030703020c0a03080a0e15040807080c0706030204051314191b0201020c0d09050a0612 81
    0x40c510344141c1c4d0145101e42e50300b0b5501c2c02d002000500014814180c0000c061040140000c03217a2400c030f02408880d8070640c20b6231141000d80c0000c0940c010441d646003107500008011241503804501c10082c0c407403d4441c1c14406490b03144074413842e80100e0305000941d20802501000b00743d45206040c41d9000c21a0200e40c12000eaa6200103a0304141c031000b0662802003400e0081940148465000d425078611190900c2035090011701c11401a03907015060b4000040400c00d0f4030300c030360100c5041c82d1311002100c5200c0414074000302114002c0b1690b006003881c0c4444502c807401c01240c40304d82880201440840341c0c5540d02c40c562181c0c00918100c0394028100700c1e0006400713007404000001d11440d20016160342c0b4020601402c0c45030910350903101031400e50000c1f12014208405500000400404113031132542550140007408041c0e044091a603c1100f1a10883c0e070540050010300c04407416981512180d480a84400440f4041e032940246d441c0300600ca1184200c2090390350310b4660300d000c24 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56258861 1250 56257611 56257639
    0xe240117040c080307080301051002010e06040b0601031805030a0e0603090a0215070b0f040c060f1d0a0b0c030a090801060305071208040504090303060e0915150a0e07020d230d0b 78
    0x704c0e40c1e0191800b00c030310f81c002100401842c90405140c480031401800244071300e92000c0d19032a191480100010680e800c040d0110b440b99100794440c0c07402059051142c100d03480541030140d030340e8202d08801000580b4880c2070140d141082e5003540d010703810000040008a80603420403441d0100111150b1b54400140f0040b40400c89040545029001000260f1142d003000e080c0092007204035040307501440003401c031a4014940c0401c0c090b6400c0c907804045070200c00c006000680508060740400030424000c515464440c03070100c010040c40c2e12645520810315501c402d400d003600d82c24030024100c2e8104a0082200c54029448040c01a103c1da03070451401d620341c40000e00b1a007482c0000ea0000366190001d02500d070920000caa00003102c0030040c07034180e0138113440c01c114013001017400f8442d5410124000c82501c3c3c148228000e04904075040c00c1500d007510b4021758401c0843c3ea402c0005513400c9560740003000d14803245403504100011103281480d50340810002e481da1001081d000400e51943d94 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56260111 1250 56258861 56258863
    0xb0a03020603012d03120807110619090b2404050405030901050a090e0403020616170705091302180a060507080f0901090302031c03050a0b1c03090308040e240117040c08 74
    0x2901452040c00c48580c100c0014800802c7c2070002844407040c000d4011080d40c0503000018a15844055404c400c8640800207a103003000c2d1004200003040f02d4640030070700285100802c0103020b00d444440001c40d066064600f04810b03114141e83c09031180e0002c01640040d5440327800144001440741c104656901e50324504254411003c88081d80140c000c1400c0c040243d075401c0c0310000c4c0c42001e01e0a21049070410050603503804000e0100800e11000103815502078480c074800c00041c2c49000400c5464102c02010300b984482d00300162407042c11070000c0845c0c494019070903038815a030010005402c0001c104441445540f00c00b00045c180034180c100040181e504002c10844010b60080c0800342e543e000c02c1c083c05440001c0c2c0302c80b00c0e803030800c20340d280562034501c6464860780211101c005240c1c4c1509080c0c0301c0d43c0c1c0b01e400140c20701c10b000074042008251031907154080e1840c050384066120492421410030740700c0c040a80e00041c0f5892185000d00301c020172031900680035441455246ea5103101c91 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56261361 1250 56260111 56260199
    0x80301080604031202030403020c0909121303060b01050a17040203100504030e0102070e01060f080c0f0c0318030102071502090310020a030f140405030415050702040c0306090b0a0302060301 83
    0x390096a214804120405902c03103206842252600401d50960503c1d87c1c004c0c3d183c1d2a9034825070f0042c90080001252044c0401103448a42200c41180795102800303030071019001064041511803508007440f0740d4440d403148040740c01581c10341d074848075004415050050782240150090b6490f106100c0368121a404a10480d800380c1c2c40f80d11802c0c3c00c03402d044006410040194403034100c0400110040000c181c00c4561140000c0c0e0a1610240c142d982e9004a1039038018040f4101d0700c1c200124102c0c4441c1e8002004188000c3c114090302000c804a0301014203134407480c94028151074900c2045690802c2070780203405262801416148009940c5000b1000c0f43c008030b0901d400a52603405050030143d551140240d5011110079000861415807109551b074800c40c41241e50003046c4179484184140b00b0802c0d190200e0b8000c00a2040c001d1610f8001c0141c440ca0165055161030400a41502d1402c005507004482d40580702a0860f0f1034007290004903594864000c1f0b01c4074a80074030f1500150b0b10300719 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56262611 1250 56261361 56261369
    0x90a060503100603020f10120f0e0a0c030c0e0606070204090201020c1509040b0109050904020613030812010906050402090102070306050702070506030a050f01120807060c09080109211b0b06010c080301 88
    0x40003402920b14010840c10428072109a4002d5140d9034042070f60a238821505416000550300200d03803034002043c0c13600209610825445c541c041c6a0f41041003000c45603440342120301810b120025240c4031868105c150501f92011503104c00100005001401c01d504600142801401944d40c4070344410041413102c04001030341041c000002656414910f000e1188448241080c64031100150906001c1400b403d400342c00613201c1c081c00b180e00c0c140f60003c07603540800780d517104502c03a40741e445108503001615030078000c01c84070784d0a10304042658106842070315003a2905074028a1003e165450310b80003454040d11101c21401545004949600d4820056024145038040021540b410001d80081c0c004103800800012040241e0340d800b09000c9015104c8080e004900026403041106055031060103d6101c0c2c1015420001100c040c03150b1418074107110200424003525200301903400f104c83c15102c140e5041c0c00035000003124041040300810f2540100181400c0c4030024664403103e200c0e0304240c1c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56263861 1250 56262611 56262643
    0x115140c060f0108100b0d0204090507050a0305010e010b040c0e0907050408030a26040309140409020405040605090c01050c0709020906040503031c060b071e11100309050c031b090a060503 82
    0x100700285017001241e0040d1840002048000503050000301400c1c0c40e601d020348a03d4a42a43c80140f140a21000000b030400628150350140d8900c0e0a901a184000300f940595203000120400f40c01c2501800c4624403055440e61483e158100421145440141402c1c0410805020204410307000304010020314141d5140c1d8100101212410078000802801d02c4981601d080d00380000241c0011103001600ea0410202d101003400c90040b4000385804d001c06540142000280014049150300441c040e00c5d405090305c140300c2145006407158401d60007025030580c4284820401c1d203099030301401c1c00f54001021240b41c1a074981c0040e00d10b4001e10003045071825140343e2000304200d11700c00e8000034130b0030b640c810381414903681301c0c00090200e0440da121099030340c41c80d020802c088401c001c903070820020000c1100c1d12514000800418031010220740ca44101c03151510340b441e001680440c40d20200400013003828900042c4114414050200c84d020b0362905008078056a040c41f540c114007014613 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56265111 1250 56263861 56263891
    0xa0302013209150a091a13060e090a05060f01030b04060b04030309210203070306050408090904060b0109050906030601090b011b050c09010b070209041b0f080703030201140115140c06 80
    0x4001c0002e40c5450304241108050101301100301c0c140c00800350f10031601e4000001c072681c0ba201c0c00c412803d10440e00c140e150f0422080c00071545035005511031b02454801c0d2900c80103a501c1100100807181c0a0f118203034462540410300019602c0788c0c1020300407040251000c14015950041e0b0003081c0c0068104030081a0040d105100f01c503d01059508034a82e44418001155031680201e5115080c0d80805800b4130b03151400142400580002c8940d49640540002c81c1403800d8180040101242d80c0560b00184525a002400380740003c004d0b0301490340200504402d9181c58440d07001040002e00a6050010300c006100d0421540441c80181c00d00580240c4000040380e800c00c940080c0c140c0164554900911454016031560140903602c20703401829415840700008030010320020031303403150b40400105040410981c0020038502d049078480c0d0001c0c05420381405a03a0180d5400b4000c0070001d00007404403410301c0d880780c0c0300c2c10f49443d9986025072602c0c051540d03030b60409404a48480e12140c2034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56266361 1250 56265111 56265127
    0x14010f051602011401030b0c03070302090d0302010c02100b180a1812090506030c1b0f0109110406050d05030307050d0f0204060305090705010519080406020408150103140703020a03020132 82
    0x280102c0441041600d644c0005605580d12601e00000c003809a0300241d101100040e4000c2c0658129000b00c0801080218650340340e1600034041d22000c1e161a00501038280440e0407009140205240090020041d502d002c0d41d10402c407140c60801031100243c503881ba441907150010304180d280e4054002c903005409407208031000780245080da400540907401c1041005035a01c0140181ea08180c40210301040c0e040b542c4510501d0074948060f440000d5180c548900100605404a80040001941e051020326a10760030031800860748080a4156003080000a020724441c00c0140f05502111500241000c0e6042015080783c02035040308002c81d0b5100d0901c481c411f410000302004240074a40f0380d2400c1c254281d101301e0340700380c00300030024030038902c0c0030504229658042c2c5014080560840341a0301c0c0b018440440380f030003880103036a219404402a41421002b05900003946d801030241e0341668a1540111030301c403002d4414000ca1013101b209070414101c400401528519044401034540c500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56267611 1250 56266361 56266363
    0x20f0f12060612040813030b07030f0b0405010302030309011b0f0606030b1311120a0b0408030f07020c0312090103090b070201020405190e01060c020307080102030f101203020a14010f051602 83
    0x20207881148500000c0c000c00b40602810080190b020b41e003c0c69070f940307482c08058084c0300e0b614540c00044c02c2804140030404840c0d491f03130000c580d904008406200e10300742001404121503080c0400380d0190030800605c640d0703500800b02200b40220700390300f44522a090362108801c5c01c075a01002c4403c507444507410403c1c40002002c3d5038100e200e00500d60084040d0381d403030424844100384214010f403e8000134442d008010b200207208190030010340e050501c0c10346010440d650080b40c0ca440c06411200208501e180700191030781038114060020081b2210402101c035040d048002c145041540754244272000405c00c000b0540180001e8001517103490404041200b51000c01c904108450002401001020724600220381110407508000030f100f4058008070b401c1120319040410030358000003e0200000c980c4448900c0b0304000c06034038503d00d450314950220f0040381103018005921002140c0d0115601c00211055000c4003800060f25401c0008500203441d01282c0ca86c404062084416a01e690 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56268861 1250 56267611 56267647
    0x9090f02090609100513020904020c010902030706050301060c080d0605130b10110304090b0103020903060f070f05190807050c12180a030b0112062304020414070c020103020706020f0f 80
    0x90110f41500c07092510800400c0100c40d81c0c840c01d0b10409082d00c0c80344210503e50304036100e4200181003507540d5041041c20701d001c0d00d24000124042c0c822500000b80c0503205500f62410b8031050381e500c00c17480c840303a01c920505400c03000108140951b94013001640c1d03038071101c100c00e502450440c00f040d407440004c204403034440c000e042c48090241800004240701008030485e03007a5100442c1c0021501c5000740101e00038010b2859071501886034030144091402044500380c802c454a0b500c00f6010307100444215824007881a008084501c0e007014500307500e000700003c56101a883c0760031414901d070380860500c0c00c0e04205402d81c411000103400c1a42440d090060b01580c1c805880004110345503540315407460301c052003840310115441468800304034494000c4a002448001141001c040681d203120020340182d07005c91281e451701c0003001c0e0040c1c1501141d03104104a4603503e03103100307681d00158082d45c4281c100721080e41c1d003000070250b400c8402004c1c00c007d100014005440d0354446e0188c40c04c4c1e503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56270111 1250 56268861 56268871
    0x100b0714100b031e010908030118060b12161202040b0a030b0303040630050408030105090708040201020d0e040e030d05010312020c0303030103020f030a0507092403050309120709090f0209 82
    0x28200b80e081c080944000400c4aa0122001030a40803502001c0f030940c0184203000c0b004100d1000000002200b024010702e100c034900494200b0407500e40d840303035014902c1c840c145041106112072800160104500e12144540aa85091401d20040c54446220403a4004d80204208400200300b07140401d03810b102e0104469400c0e0029854641040c0000e890303d00b1138200138403d80ca4a2074042d0050301401c88850103000030304014001c1d41000d01c0c01c0b1046420900074680500c02c030100280c9150f120303c1e0712034002c3d501a0041c0c200400d02c12011149100d081d14000d801c66202d100d03680440f0002c00060180d00c0c03004000080550441c9000704101d5051a400c0701198000c980400c01650b020040340d0440e0342c12140c44019401d0070000c603081c00009580500039026050002406070090703080904415908803001c00e0f05e01c440000030075000010b000203883c2d41c0c024440d4040e00d0030209984990401c50b07508551007140da03400318005070b0b001c403441154040360811f1034104500341406029000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56271361 1250 56270111 56270143
    0x20a1506081207080f0309100c03050105100302131505071506140604060503060108061c030309030e040c02030405040e071a0405030d08090d0f03240e0f01050315100b0714 75
    0x1003807144c0c40b0703090305006608561171030360380000c00301b0b01d000310030400c0c405400b070344038010303c00c0f48001c1070050300034030003403113100c0c0980c4001220a03085440b902c22155584c0c034140e00d510921342402005055145210f0300c5c442440820042840400e42841c81844103100c0c00001080e5907091010000e40b60803818092801010180010b0060310b4210080c0e951003482840d1119140e0348900c00500314000309032107c004846041604d200f81076050300041240c5000e51603e4034101c0c00d220074001194001c2180318016003050005000910307164018240c0300c01c201040703442c07203501c4840c54109041901c005280c01c04002608101905040c82101500030140c140742865107000c803d010703164024480c0c0b140401c1000c03404036614500903449800200001d0400c8203254045c0c198078403280085000760030b180814180001c1d140d0201e01e1000d416540d000c0c014017010480801e44154030040600743c1c000410149078003003007408102020f40b00ca20300415480d04200f42100d00d00d0f003800b032411112110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56272611 1250 56271361 56271367
    0xb040f060509100309050c0402030405010c0f1409040f0b090106120b040501060f08040303111b0c0607020a061d04052401020a030509120102120406090201080709120b0403020a15060812 81
    0xb05580d144558541d2454500b000308400c40b191805500b490000a01c017984140f000c0280300c28807005500502da08d814a0f165600780302c180b66416100c4002e0300d0814004800100503400040c10039030001805c0d020503400c0824143d54580000f0795a075802d03040003000804052040c242144180100b50700c1017800c0d1810806941030120080003a031800c2c1c0564140300030f100201e03003014469440240c5401015640640320700c1e004030a0f01e0403404003030400c0c46503c101e444500491400070222100d4503401000440c07164584982070314000c001c4204c45258103215440b0b0f40f15500c541c0a100d00c40e000700400a01c2600b1640d103d21040d00e040440281151300142d104c0000940140c00c540206404899005406403455100ea0181c03080709100c83c0c0a1640200740001c100e600e40202e10392034401d03203e003180781d90b03802001c9540c3c002074494030403410092a05400032038855181e180d08280a0320507540201081c4d1a40305c040c807000c1501e5104a5078494081002030310501814445d1101844c51900d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56273861 1250 56272611 56272627
    0xd0e1501050603040308130c03031808011a0d0201020708011a12010207020d110d140d141201060c0c09050f040b010603020a02030f03060a031707060b0402042106060f0b040f0605 78
    0xb9107808000d2000302800700d1b040c08a4217000180001b054883ea2104d0304d01c3e00c541d142c1c034004044c45100008044c6003034411f94003140c120018041c1020012060034010900c00142c0304110440d400b80d08264194002d030840410403040a000701d41e46500c1006203604602d80102c00d0010036064001c1e1004180d01c14000c4000680d80d2909000701b03a90803100d00008109a07600196840303c051100820346803582251540b640b2010580640810403a00d076991880c4072100540e0907403007031291001007296040c00620502d4054181040301c0c0340900420070302e0503100c1005100b1248182c602c07001151a4904120401a48544160242002d0720f000e40c1402c2ca0040003940d0b070b000b0402113103c094008400116140c50740c1154100440d00080000048100b10a01200580c0680802d81d00d513800c2060b1840300341042e0084404944214030480d0110110300b409018002d0840d004490441e1151800591084029901809400d8601c0140d54451409a6002c0c8103500c5074084410302c00203001d082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56275111 1250 56273861 56273869
    0x318180a05160e0112050a0f060e01170601120f05011b020309030c060f0a08220807050607080403080703090611040b0a030b3106092306010e0901091a060d0e150105 72
    0x31126171090040031400b80c6840c24800090110300d10204041031804200103084c0380210315642c121458401c2d0403240c1c500780800c180d1255024020300500c00d202d43c43c40c41c00517203d40303010307a401030040000242c014000c00c09941310b140d101d515180140c1c40070403c480c461405000352450114115101031034005480a680b80030f0080303480304020302c01c04200040c507003001000702d88484e80001d60420701d60590341c9003654480e001864150740c7c40c400c00e00001c0c4420301603e185805590107481d5580390750b031080300480180c8045c1c4401c4840760340343c0d81180d04814000001c1e02c050f0050b0045031381c440e801048028101c0b0f03628100c89103e1101e4586180c0e06d03480c0d0824180300c94081d01800c40300294010761900140c0307450f6100e0062585403803004c080c0058200424880c3c00b82c2d00101ea0200e440d405c004446c400d04081a6a41c450801001049010015800030b20b8024401e80141d418080071070000e41c2c2500020f001b94900764494a19070783c803030310600410540818254402c1400d5041002007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56276361 1250 56275111 56275127
    0x2060720010b060301060f0909020705030d0908070506091f021c1808030a060f050102010e0d030209030a0b04260309120a0509090a0f0b120318180a05160e01 69
    0x504803850554a01420040c42904408401040034100c2d9940356901e0000500c001c7c860001c00340018450540843c81000e01c4c021a032aaa030080c00640c01d0202ca45094801004800350840302c03148100324034400500c086c0304080c45180d800014180c03058000031804406508019142d1841c4d20403c408980d6a5649e248031800d0858404001800b0b50b03c4d030003140075014190720250004c007001c000c108680038a60000f106030350440b0040c40c10760b940c3c0c00040e4280c0d5224000d501c2180c1240407030001062095015141c038002c010115400c1071040e4a500c444010300303450903a180a00f51241003620380c640c0c51460480e00c51201058694640085416102c101d1503c88110010f000a01000d0f10340c801c0b4295034412030020050766144c10f10209580080c8020b807000c2095a0520b901d09000b8901020350203034460084c0701540c1740404040132a2a400c030030145d0903900200001d10082021001d0117141d102d10500200094982040d0741c8582c42d0f0925030724124100403003c07031a8001640e1081203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56277611 1250 56276361 56276387
    0x101e09030827060c070212030408030d1a060702041104050402040603151403150703110d090201080703060b04050609120105090d030b0303040b04090203101e030c0e010e0c0c0c0603010909030f020607 87
    0xe09031505e115100140c3c0001586591038800d210105012411404c0800100514030701500100000100c00340920b0303080300e420101942c0103600b484088090300345600440c00b115035114613507142c81d803500006001c03600260070420000b56a403c04150300c0000f555100040c0c010074246c92403d006610000f550740007000c00180040703000101184205d4002d0700306180003881003d50503111307083e01d912100140f16030101a0b00188c8040c003c200a14001d00c83c1c5016a68400703c05403800f8202414400d50b64000700009070410011510244407410030b200c4d060050789100d019100000503044000d00395948101d245110350810842046032000c1101140e0845000e1100581c603541c1d40c00928640c44c0c160b5000f0f00c008803a1060412000c04a5800c80050328030810000c51101c0d15840c0d035000c20310003401071104580d260004641c0f2180c2d5400a018400b96000072152525510004980c1a40080c2d015108580d250004001016042000265900e60b144004c10b00c2d032800e00b00c000d0402100e041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56278861 1250 56277611 56277631
    0xc0b07050d050c03040e01030809030115050108060607021507030509031c0503040605060111072601060308070b091603061b05090a05010809101e0b01020a0302101e0903082706 77
    0x69445915032040c01540c0040140c421505d1b0301d981e40b810045103e6004010b4184254a004011303d24841303d01c50700000e568060756080102d6442c0018441168000c0d003080c3d91100110840b001170000120040180340c1c0b203503072134039141c0024206061134000e00c0e5040140d0107101610307110a0799444016070f648540c00040100c1c05403141030050359141d025121305c4030940600940803800450220b14141e41c0c4ae0101040c2100c403400c15601d03822039243e804020400d0320100403080c0030502c40c1d0034940c2c10403440d40550780d240340c03020007100d00d0080c5640204c03011074403124000254035100c242d04c2c000c14802c0c2002840c10b001ea20003d00003640f1400b415041c480f1200218803014010410301350445407031403040000059076880e00000341e08200d00090482c0c00c1000403400d40d4800b2501010540e0b00d80c00070b1000d601c0c070b128407001610071094109041d01d024082d80030030a5050080e1030b0324502a80f20890a8102000110060a1080c81e03141d040c00a0180782039124800142103036000301040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56280111 1250 56278861 56278867
    0xb090108040f050a0b070807090e060d0303111605010507080708040213020d0e0601030b070c0503120c0f0d020d150503030406050d18050d1b0c05010302030a090803010605070c0b07050d05 82
    0x80303850b4900041c04100500a8030641c925001007044824241e40a1301c05901e51004581e00d08104452980c001d001d54001e545031030300442c80a041000c0d020014a01c01c0c01e0205032980f05c2c044003c3e01c1e410401a04418900240742c082c10704c1802e2040b00e070404010b2410310380e9860b058201400702d107005000240560100310b40100070354269810b07078030b41c034461040034480e051142c0503031030780d50a0a00041c0c800c50300303440c04181d803280901c0045e64002e500402035820302d1211580700c00308500007407080242460400c1200140441d0380000d000003c404100140c40e102c030106098100d5042d01c40b030400620a00505001541d800410703203084032214a84140c0d079a6102d182c040140850500801c0744810030742c407a07000c01c203000c110f003c401d4440d50355030344000d10f04080f26011605400800780c40d00e80101001c0c00030394807036001540e0000600001060441c0581d4503981c103940300741d102e40009000850980100040c0844d820024130344000c0b6581849003546030b0a4403104410044002c1c08000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 56281361 1250 56280111 56280113
    0x909190515091f03060204090b130606200a0b0c03010e0a090503041503060905010b0c0d05090d030c1b08010b0a0603060e0c090a0e090307021201020703020d0f02100e0d0e0a0b09010804 81
    0x1205043c009580c2c406004e544a541c0c5070100006040340ca5101c80c8201c404220461800840307118003012124a5511100b9a005100c1009031500d44c1c0c00070740540c0d000e1200c040021a0307000c801c9a028035440c3c01e0b10350b6070390300d03002c5401d08040015110140e400d0810a0701e60120380000282d400307491001021400794001110103400400051380a01002030030b02c4000144011580d018140f082c2c44181036822440003071504490900c02e4030f68007648181800468000710784074840302c0c1c4550380304500190f0714000c400c0b0980c40c95a2a50b20040c01603448485000c010700709a04560018011418240003c2c2d040240700901d02900038940c80d003000012076804081c0d81c6041111000f445242d8021016043c0440d4154880e0f0002c1001e901980c0204030544030300c0814070844100540690242070002444a01251030384400c42008085204070046490540e08900c10084600342607030062020403030a034000b40601100c0b0642501c9480c0c086410041c1e22128130445540c0d800900e091111642c40f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 56282611 1250 56281361 56281411
    0x105061b060c0a0806240702150304050d021209090a050a240501020106050f0f010e03010e07170d0203030108071401020a0b0112110a06020304120206090919051509 72
    0x8012040d116521400c800e0209012809004183c0b0400503035032810b4544d10042171203c0c2c1804d03a503201400381c61201c1c0c001c01c55011940a042954401401c5660048010300c81090070341040e20180c0e0aa040852402c4040b43c04100d25001c031118035000c142400c12500004100f1a0b00900c44101517442d0000501569000e82c002e0704503580d500d0002081c9680c40202c20810b420302c0c0110303800342d880c1c46404101391406c00e01c0603074031040c020840301c0000c001000450701c080310201d0075034040d9251210300401000910500003d00110582c1d04d09442100510705d250802107a0588150741003000140140080400c0441c29504880b13015213690b161280100c2c80c0c42c0c03607604083c1c90f02103c4400810504c9804000f84012805011081c2c0b0070301003102048055041c622803c40981e100308010840ca042d140d070a019002d00080115003042400e4000c204082803c54405010304030708004102a00010f1050613040300d21034010009100a004c042218000040c0110090f405016010b0280c560 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 56283861 1250 56282611 56282647
    0xe0d0c0507081e0105090a021e040603211b03020a0f0309030203030f0d15060e130e01090b09060702030309060402060c0109120201061409100e09070b07031d0f09010506 74
    0x6081c0101e46210030b4980d50103c0d4500111410761081d42800040381ca11100007076103218164000348040c0d0014901c002c111025100e108015420644840c0000007044a640d10b4520740160701003012180c1c103241200402c1c000d51000003005030800c02c01e000c0086540040c7d0080e0043e41709104613180c2203103003401d42d15043c0c283d00003507241c800080d41c0c02c10b03aa07003080a410b44900da5001407010801c035007812400c5080c640031b810000b8000c080032220350301d001504001010b08071440015400c070340b454110b01395404114191007000301d00003480040f240420090703501c90200c2c409941507003071050449403204c0018001038450800401e00081019080d4002800290f00c10200c201d144403200010f40a09142d20880c1c02c4240d1421100025081850030786100380d045d210b46241c0c2900b450700c0300421100c040c000700038034418814040b913442c44070001004c2d503501a4036010f101d1909104442c40c64407030401d0f81801a288101002c650791102450181511821240039844180014104200136 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 56285111 1250 56283861 56283869
    0x30b0c07080f030a0b120309090705030a0603050111090102060601080f0103060507050d02030a05010819080f07080705030d1401090b09070e13060308120702010b0d080d06030c0b09040c030e0d0c0507 87
    0xd02e0000612001d034056a1149864500556241350711880510201d6101c2c005e00103807a8001c1c0102e000250380d079210308000d5a2100070b134500054206d441c2c0d00c510b0308440c28644058140c00c00011301010941c0c04001304d561100091030611482d01d042100b40c0206039042c40001e2400340c5850201d91018001c009031400b528110b034045450b4541402c240c40a0309083c8a21200b5000e40c211104061100c1254101260780011165103040b4000558111950007020142d492603424815180010303000d10040c00003110707031800400c13150b02514000d0a0b185069201646161902c403250060351103042c5980ea0101081c10882501980e010103d450b480441d2400803d0350703d0440084200984500036140d00c0c01c01c2c400c86105030740d07a82c10680c200c40302c500c0300c581d001d04011561000030b00810020038494010010105030243d0b2503a600d1030220603070b0404111075001084100213810a44900d6080540d186401c2c0040e01c80c0d5500c031502c070241d012044041007490f0810805014040216400078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 56286361 1250 56285111 56285137
    0x714010c140a060e010209010203090918010c0518060a0c030513080d03090501050c130b0a17071d0301090305031311030f010b0a060305160c1e080901030f0204030b0c0708 75
    0x31030040c0041c2d00c0d140824000c461076881d2052000d0403280500c25150504810f030000d6240111480401440c0c1500418002d000c070100004003003001030a0081224031036458680b030391941c040a880c488601c07120061540a41380610190982aa026008440c40c5415007099640c41c00f0b002c240350140c05868000040b40e02c90442072489040d450f034840421031b8020802042951211602c98940e8403402d400034680c1c0b0b048250a1140c0c04051008000010403810440000c1d2100e00c1c0222100808942110200f40c4101c11420b6503207082070f603050840800c80080105003501d036009826800041c4c2884046280c048105040000c440014407464a004048402402014034054013034110403840d60700600c024000060f01c18001d000301802841c500e500d01c804090041402c480c450040e240c143d894414006003042e030404d03c0c5000d400404e005402c141d6070750810f50005010780b07100c0c2c08170b6070b404d5104010800100744030303255641d004140035410300c1e610b0341c090500107081c0c02044d01c0440b00d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 56287611 1250 56286361 56286383
    0x601050d1103090c090c09010516050a0b0114030105190513201203040e07031a0907080108070b0405010c02100201021e040302030d050c06070c031e0302040e0a020406020714010c 78
    0x1c80502140503500c101c0014049901600c010001e11102041c290b61070302c005482031200c14a10740c010b5000c3c040d80183c040341c10128000684890340b42545031007050350410108001400741048014410b00c0d1488294024042410b284069803104084400d07880844c65940340804c01032242284034000da41d030040362030b02411040310f10aa4201c41201c1c1c2c00e51080b0440b42d00001e080301701109a40449000c2c580081031903581d050142c0117040320301c030302c103001c0340441001c92800d98038540207a001d009241d84070281581400c40d514582002d50708401c00308002400201300b183e03408103100d0900d90341540c10304170000c03202405031b02a002d040c4954a140f40400e202451520800c0e0203003003100c1c002c80403a84400d1003140241c90703074420001401c25136044400055003080c041c1203200c0525119241c8411004034110003456032044171019040001e40002e01002800c3c08080b140790054104001146040d00d0020302964900f19032141c01212082e4a0b102d041c80d078041c9000380455500b00307c107002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 56288861 1250 56287611 56287631
    0x20c0d1401050703060e010b160b01030f0b060a0f0513020d05090a0c06030c050a200105130b0a0c0804120509130606030c0806090c0c0703050f0c0108070804030c0b0601050d 76
    0x8200e1001034000c480039071070309001884180c881d001e0b40e81118400c1e82c20848590030500d640015502840070724030001108064807002980e15000c2d58000c50140e8513004802c9500e203003e0420004c0a0b19241c85a1039404e07081c007041036600400b00860310f0884084c0f015026025081c0701070f000341d00c3ca001583c3c0c5000e0401ca21400c0116a44200d580700d20010000244c43c0c071300503000c03500c84005e0900010400d002c50b0000a00451680003c56031a0911060383d14050a00074255801200d6503aa48200f2094100070070407800c904030f400c01c1d09003a051240003030300d075402011040018070203451480c03101401140036000e0f40845000f0400039220400040302c0c0500700c0080c051a00c40e010001789410b080d241c0562269020300d00070031004000080a484080300550107400089e04105903000e081c80c0000081c208129485058254001520380010a0350004d007180034010448000d02c21100104030010b0b0b8450f01d0a05207503030200d4280c005886150040712140651503074031401a2034020003034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 56290111 1250 56288861 56288873
    0xc0409170a2003030108060f0a1b0f0e040905030a080403090306050c040303080114030d050a02030c030409060306061203020c100c08070609060501080304180203040512040e06031009080a0c0201020c0d 88
    0xe003101409110300081c42d1180c0c40b0b001d80d00d220910592100350080d4001c100c1e4541c0010040d50045540300700418482b0780e0550b0041c0340c0c5926468007020a4198011003030081d00b02c0791000c100c04080750200440b61846d11041d499204894000040242041c0010205030007000700c0304c051500032004210901d0280340c0102181e00501068010aa5400000a0006144070384184140024024003c0c400c682c0000f96620781100c481c2100f0740c001805034004104042002d4401402000804031340c291641c00c0000c200c0c0e00a0304a0040076100d410410302190300081e401354548820b03614190144083c1104841070342c18000300030461080003c1c0302c0144075158100a003c1c1d405580e0810541e41c0c2c13141019540c0c4102d01c83d01040308004004d05895001a50155a2260040c2c1c2070328508450407c407081c1c0b590168001035416600c031810301c030460034100182c1c1590f40c413960742080401d10035110000d07a03008440f000f1040100b104c5d11442164030900680c00c001c94003800503114410940303010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 56291361 1250 56290111 56290127
    0x60d050706050715020703021f0f0e0601031403090109060503130b040b100e01060221040504020309030706061d160207090f061406030105090f0a06120b010305010b040605030c0409170a 81
    0x20b0316100120130b4030b0310032a5141c2c4200d98050398503400400840300320031400d040c8101640c0b0302080c415610b0310b031541301c24110300685954502c100080d080560540c038001c808011224854040c9a205000b1850b007642c20100100944109041961f100e43e070b0000d5041c210000007400810060b903100c02d0000300300f010180366008580e035003042209291640722402c0c20340e00921440005a020030b062218400165640d074202640e078440e500e01d010307200c2000c0b07804e992003a11440040d5000090340c2c01444568071540c0040c000c20302c09214844ca0781040c40b480c6100185c5400324840300310701ca80807414003c01c900340c01000c4414050003402881600c00006201c240704211600b001040a4400d03171404104032410303034000070900081c03510385403100c24081a008141800d1950349000c0402d040070164401c0121910404404a072507043d840c09a0a481030400101d0060b0308082c000d002964022a2540c1e0300d85050b100028640307400e00b414118886103c46442c1c4000000035000e030090b0f0310246d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 56292611 1250 56291361 56291363
    0x1e0b0d0b041a090901140c09030f0a03050a12020333040c0806100203120c16050f160e1302040c0509041509051b031501171e0108030f030609060d0507060507 69
    0x20910f81d50352208418240d070300c000c0034840042000c000090102009002a16840d40b0107400c582e280e2100800b0f09107400100c0030203402003000820031000e6039500030007008141c811040c0943c01c43c18400c030300e040902c45a4404014429003000a44002005c2c60096409030348010400d00c5a03101880c40a40203030b000307890150154055401d00d01506000008807041c0c078250602022a9036148840030f8502d801003203241328402e9040346030310081603003000b520304a038200501400b42d0305444010161103c03103e6102611022621003004411180e480c200d4038100d805541c081500744a11504803268403404282d20b60061514a00340c000100c008483c6091741c0d0110402c221507102d40d4200c1d2442021441c0150f207400080001850701107520b068a000e580040c1000c610b5100310017500080305204031910520a0281e40850815154540c0c041d801408460040d51508071000d002100a110007440d1500480c40440868142e84581c80c145598680140660b00c01ea5140c4400030120b9000c500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 56293861 1250 56292611 56292619
    0x804032a0618020d06050c13081518030a030c0e030d090509150603041203181a0705030717060f0301060e07090b090f12010f0e0109020108011e0b0d0b041a 68
    0x40a5140c00c100100b00d2200e5400815000070844c071540c0d514060080103004003030301ea0041c449150074002c0101703000301a000c8400a07002c10b00101c19241180c1e0401810101d658002801c1c00c3c40001c0e0101c1202c50a0041c0d2401040e0744a05e51000c0e20100300c40a10b058141c0f00d544480d20036035500444410640d002296401495112078606001107820452040e601800800c04200090b02da180c04040400c541d01307010030001d41ca130400410701c41c4104000e031841490010b480071401c0482c240700358030204d141030050650801000c02132450341c68800c1141080c9020001c10681c1c0d480894201000c0001002031000c5500c07401a402440307025102a004242c0e13042d0003141403200c88080c5e5640f20303000341840118080b4201001540b0001e103542c41000d540c1c840c00c1c19000040c80c090280c0300c4000200100d050006072000510484050b40000d0350352001001c427110540c4800720241c100ca00b180c15a076291561800401c0041250b242081d074014a003c0105a00d070302c110071030800d940720450b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 56294967 1106 56293861 56293871
    0x30408030406050c0c0301050a0e010e07081209120f03190203030118091104110a0e1f0e01051308070e0901020909160e03010e010501090509070e06010804032a06 71
    0x10f100c01034442e88ae00048000c2350801d000f11444802103600034207105150403106601c1e0034100c43d0385400c48100141c0001c0644d2018001010f00ca000310a4035160081d110f0599500d901c0401c42040031140c100900554500101c00e5078101c0711151160190600200644001040003040440d08c0d00c3d440c1001d6541516544144c00f106011003030410351391000c2c41400b4000105806680d44202c15410340c2700ba80418940c0403001c922201d04012072199004001616030340a040c04501400f0f001a00c001841c074400210138080b00c1180003c4076498484070159400d1707202e10f50016800c0403604012507a1070294040d0484000303042d20b04090090050b800003803d50341008511901c0343e440308014481302c00303244125a0003d038024018480300385004d41403081600010170160502c0011000102410301460042c1020698003140b03058003c0d000405a2100aa40101780c030310b01d142c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 56115111 56294967 := by
  have h0 := BRFrame.cov_init 56115111
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56115111 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 56115111 ≤ n) (h2 : n < 56294967) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
