-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:55.507034+00:00
-- url     : https://prove2.me/submissions/4e640d66-facf-442e-b127-ac4263d49b8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 722841726 ≤ n < 723021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 722842976 1250 722841726 722841799
    0x203120409020909070c020105040608040201210501090c020c0906120a060f020702100329060c0106090f230f0c0c0115030b01051806060d0e0f01060501031802 70
    0x40004245001920003400d48050169850444408100a42800810740424015800c6a860250740d000b0291070985440c1d0400c02c545440c3e50006070368881c8442d41030250b031070034030151036110001900243d0407950070710002d10410b01800c00c01e81c0c031104040d00840d040003449000482600e4003445403480d028089041ea4401c415030748400090b00c00b00f1039100801a0001003020442c100b4440e08014020146020032410301c000000f000c0f030120341c0604100c04d400801c040d04041e40c90f001100daa400d0326000030801c05580744890005000600c40741d500080c9852007a240c0012140004004080d4002040c1050b54491007504411000034098581d5003205004801d010303102480360031801c0400143c0c018038245546844444424142c100d18001e15504403c0c2c89803a00b042c040c6500032004458103500d0701b50903402000207010240c9410402d10a072a40b0343d05d00c0006501000a030355080e41c003400300e0304000340440c3d05c0d2a06220002c1d00100c140194854541700190302900000321030005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 722844226 1250 722842976 722842993
    0x16060221040506010f0608090607031d03070f0c0f06050a12090609051510080c120f07170c041b0507050a080f04170a0804063509150c0409090203 64
    0x6840e882900700c030100c0b019840000140a403402c840c0418005001a00c1c010005182581c2155114440905800d085c5030b1503079090110244a200c8030415032201004682d01c5010303609000707091445e03107417069035140074001340844e504096103c03050a913000b5440c1c0b907261520161089800d45619100311020960b41d082d1000001c0c00c6014407040d0501901c02440110400c11403801d1010001d064583d04070285803041060000c041103040160604072040e20f0228800610142081c40c1030170100c9082c084e6690100e0820175824200340c00100c414229880e00142105201c200c9034200e69100542201c00c800400061180d07004040c903600c2803080c0c0d480c2840598989d000764128244484044c1804103007880b1000410703c031000d041c0c03292070080c0780c41251500d0b1103940e8031030b9004090030050391003206040300c4241c4084420040c0707483c20f011b844403e8282d1041d0360b294150f46d01c540f00d0083c4c00141000610f20703050301e4020010003507150b00d001d00e8401544011f0003903500890300350103403411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 722845476 1250 722844226 722844277
    0x10022a0111071217040c03140f071203140a051314010c06090816150b0a0f0b0f1921200d06050d0b0601020c01021c080c16030f0305010605160602 64
    0x2a1801507208158640e00b56085260295101942306044480d40d8004c600c0800d0080001030003404a907481400c0104144490038212a6007804100b909000500001c3d48528203610200800343c240f4441040081e1a40b5039451b040c5952800c6002400108405510404148543c0c004294244a005a2440c1003c0d405288a0f555000d800a40f800c00d150702d2510340500c6a401054441c41040320414005414090600072a03035007402414030300311010500c0e0031306244400031140501c0b03c2a0422403540e4041900078007a0741c615409130340d840000030882001040c14003c00c440c072503a07800d0184071220000742c01c0c5095040400e0340c040d52a10342c480001c2c1c80d00d4581c105404140a19003503680303458144d002902e86880c40182034115030108001c0009825030081048000006181541d1a03407107024240d001409143e800312512400e56007008209504039100e2085010a40c40c14440c9a030386910070358941c0559540b0020342c00740d103950b290008d0702503070060401c50000c41c880441e2085c40031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 722846726 1250 722845476 722845517
    0x909050703090b0a06030c0b03040203070806150a0f140d0606180f0c08160f020a080412050c04020901050409050613051006030b102010022a01110712 66
    0x210340c0d00100ea51240d06505100810302100d501441c800c405002862071540c60304101d06840c40303103641840003c00442e0855405000d400014030703040013150301038144802c20b000d41e1131484200c00d1043d810004000340c4400912100780c02ca641541c1c00090303250040b8207000803c0c04080f0101d0324a40d4487e004694040907540d1240d02d202c20706800245082c003100034104455482c17410b07a0034484000704105100c0d82281a0f480c10381054a40200c9841460905a2416203d5072000307000c08804240411011409040040c7c802d0088081710002e0424200b844220311070350600600240d0b0030030007801240b40e81d810164000c200a0481e11040e40030f0141c0c0d1044480540d0001c80710031442d501040380a82c1801000c144842c1194400401c001c500360140810420322507100203000300d0094400042d900340580858800314000566841d4008030b850342042c00741c204210040c545007088902c003014140320b00b0051b03081c8003035000e18100003a29070024414009020000700036420f001890148940c0c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 722847976 1250 722846726 722846731
    0xc0b0402181005180c090105070602120f070314010e0c0a110d051b06060a12082a070b040b07060b03030d0c0e011d0904030e030309090108160501020f030f0a090905 72
    0xb00034071044a0410741044181840c3c494101d540c955001d00b4040f441c444c01c81260b105038000d0070a241c0d201024034180b406802903085a14103e1502070030803000304004011030f0703c14480343ea0b0030007018260003c07406140d070080c040d030801c00070380d140000c07200d980100c0140201c1100f4100b8080440000340d0080c54506080b5440b00090800b0940300b070800d040e42000700b6036a0002d804ac000610303284d808681c00034071512805070350407280149601844a844100c80307940e04059042c0e10a40540500240c0744040b400804406125640002440005000c01d85064400003c42d1a141803600d4444c980508040d0400c1c03941030008021258003900f940c4201c5100039090340b5280a15a0030354005420b0003e20102100101a5501585c1d103a80e20b2595081e441907241c200a41101c2c120310100e850b5025070425190080348440010031411000038040c3c0749010078401c081c8107651030300c004a845900d1003c0381c824650051240e444c1c0007800034041c1181c603416280c02000d1a030b03a4003401099440c01d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 722849226 1250 722847976 722847991
    0x20c010f0614030105091f020d0f290105040806240604080114010501140703030509010b180a05060105070803040609020f060f0a0801051210050a0b10121b0c0b040218 73
    0x4402e403251802c080c001c965014a110000c4c100245410038514156880c07400410010340e170001e604090b060304c543c4465140440c1c0c0078200407884e9201a00740c80c46800240d19034110312a60001d0003998803940840b07064410440240956845140150b85090b82d44103903544500c0d0b8840240102d034a81e0700140004150361000420300340e81e403002c003425402060300b00034108659118a0f4083c500e1950842e081c090f41841c0018441e610020b03028010302041c0e00e03a551006000b4480701540580001090240f0303502481040952030325030041d00c5500c552540284010410f0001401080041d03010001075800079040080c50b1401500003034680c2e100412201281700c0104881c4001c5070301c48200344c05800156407409401c0c040780f502030364540b584800c8030341090700c54000032131803d442d0300441620500584494002c1c051200f003e000a04a601c04000f0780d1307d00301c0182500c04007a00000d5220907903840398100e101e00c0e925100b455103802882640c01c00c4007250307041d000e040e900c030f2000c0c805d141c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 722850476 1250 722849226 722849249
    0x90e0a060c090302150a11070605130e2703041a07050d0923120a03020106081506090121121e03060f09090309030b0405010b1302070b010603020c010f06 67
    0x101031034240100c0d2000d80000c0c040195984003400142c444140d28258400724001c0e039526060340260031104001d5014100d4824095010001481c0c1c0d00702000c0c0054480b0010115901ca49a210300303241000112811441800207032031030704030f80f0300308a00c8000b008032020680c0c4c90681c03540d44c1070111541c0700030079000c1e007000040d120701480b02c00d11600420710b049241000c007103031420020104081c010141c80c00c8068500d503c094103035580504006421400341d00344c8109150b9802e002c1d00801d010b00c60040d090140c00100e5101042460780d142c40351710001c01c045e416034246448502180c840700d208007003042c024140071000c169030041409001c0a00c0e582c00300c06410094001c0d100c03411021052041c03608262041c405104502489010703100010b100041020386418116900c00381c650000e4861a148014081401010f410503070025a0503030703a014842503000d03202d004074854060041c040888c46001480001d11940007401280e0b00c1400105022809004010440d8040e40c0505c09030340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 722851726 1250 722850476 722850493
    0xe09180703080a21024b0c0c030a121409130504060612020904110d0f0605010501031a0f30011a01050c0a030c030c12050a021006050d020402090406090e 67
    0x34040d4407501821008014203500740102180b02807100809000c41440d54800180c0b90881685114170220614100c403800318404e00d502c03019a91b042c1e02440c0032600703a000310122100c181c01d00080f0900d920303512142040501243d400212849010141c1c04c07011848100840240c40e554043e08121603c0f08010005a604151500074101c0350703607610802c0d500b504100031802503502d102095911903041010f210710044c0c1840007802d0601500c100410b03040307500c0c5112040c011260f0109059540a0301d0422103d0105481c480c103007207510095030341c06940b03960001400e0524684a0f0317207841004061180010fa0b4004520400b000c254442200f030303545101003102142440542c112059080c00c0c4540741001040342a6261400010080c0c18416a00d10000400d032141843c4d040f419003100c402c2c00d00c0d640c1410700410741d60000400070300510942500c1c1e0341c0f41038a842134004076040100240e000d03400550a01001c0e4010044440d4420b5a507000002c81100c0c034001c50803181d4100c03001d0a43c0d803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 722852976 1250 722851726 722851757
    0x402040b0d0f051506160b0405030705071a07112d0108062b03050c060a051f08030d090507050411030717270a170a02010c0e09180703080a 61
    0x1182c1c0414440c00080c1040c3c1800000c402c04000070703582d4101036940c030b5038804c42c0c85e150039104601174400034403110f483d108000501001101900328288107005a890159a0384080c03031404040400e0b40c0c2c40f42e00c0422400c000560680c2c8044003841014029a00b000c1390320080c029910100c075424400050540c5294600d581c1c0810101d50041048500402a00c103070070001880c5035030003144807102c00c0c0010000c0e00345400380c019101c040415030100d40304c03031402242c5000504800c1e54205106010002000d03483c03810b49a00800351040f0200031400e041c1480d41500213400c2182040d60103024101000c034003a190380c090544c501c0d4000c040a960703420010380080c4118400c51000303211014600c20701c80300e80b111070a80105083d07049052500700702c15070b184a0030442c80d00401800c1001024442c442d002d28400074022640c0700750001c0000054114095440e00958030656501900c02e100050f070300c5500e0034000e082e840c520000c8958254407a030741e100c0d155106c815013401091500e4040c2009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 722854226 1250 722852976 722852981
    0xe12100c020d031505010804020a120602040312020307020102060403141c0b1c0807030f030b040f0f050a0902090103020607080c03030a051b120f0a0b03011a030609071a0a0e0402040b0d 81
    0x150b5591808110001000d904451071040034000c043c10060345202040a540e601d60b1b03d80050140090444282c1c0040e140c060002d500611003142e00c86813820494410301d00110a94540b10b4040e0040c0c081a6907903602140c035415040c0102541840a001c60b1540340941100b0030744c07108552200194003400030041010001484400680004915690800040c40d82c070030f6460096260610305076010f01882c0584c00345c078045045540042c81d181904c07000c207280e600f002a030800c0b214001c0150b5141c0c0100007094030310401c0065041242000100014101a0b00522105003e0602617060505802c800c6003194000d68081c1c200c2511441803220148080c0c000c0280381030302d44130061401200c4c10907810f0401c1c0003009290b00040682c0041c1e8400d8807a04000c210050041c0200800c045400c1031100121920032901e0091059034000391000c0800070f440c00680c0e29900d00049a44c03840c0c201000664810b800c0e440802200040801450b2160300180c00907100c14281c2c2d513203982298440804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 722855476 1250 722854226 722854243
    0x106180609050c0406020a060b010306180f05010605030907061b020303040e0708091605281d0c0a080c030a02090a38090f0d0206040905011809050c010e12100c02 71
    0x40c3d40081104000054000a00b929565803104001c40d925002c400107030001d1256a110114005108604001140642c2c4c003081010001e044100000c0c0d80710702e021591404100d465002039031041909104d0f0b28040c860344201c00032702441305081500b8650201c0d0444e0055030000140107a08000d00000079000080d1607070003440207009200007000c00107841d0f2000c6051203014041c00c0b0081c00d907211a25400010700a40910301399003040320b0303900c15045841480d5100c100c6002d07800d010100d107142c1c00010441d50084003540d904c0c1342c140c6844002111a920261503a0340e103540c00c001e100000d48070312085100500b401001c103410242d10080114402240410a210241c580071402544640c0341c400c0d64a0001c094450042811190004c140c00140c40040030750310100200340044ca4030040d4001a058a00c2542c1442440b10441d0000741699414600100140c10a551000855204480d001200d03a4010410b11105008411450818140b16400000d4603266440c0141a030340400c03007282c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 722856726 1250 722855476 722855491
    0x4050339160b031015120507080912041d0c0705010e0a0b0705030f07050a020a1a040c0b04060c110a05090a15060c020616031e170c0f07060905010618060905 69
    0x10320314942a00320003041c5140d8010074001c6070b6800b00c481200d0b48901c0d80500c0601b283c41e130411141c24180700203400b290302141e551145100d51a4180c0750b4400160a0b01c080b642c0c42c40c0100780d042c012212070805041c0c010404940840b040c000980070440900036920500901300c0030744660300c0d1034180203911000c004c2040d0280001017003801850208000c0440d030003040d41c6002c54a5604803202241481c91402d006408001042ca10118450101c0c0c12a03000e83c0c8100d000048541c0d031030040301c4103802144140c0b4003084180e101500030030b013411045191848001c0c580c0821a0300c480008000c41e006a900c0009240e8840194043c1c800031400b1101901d001d05054801582c00d50005605114091a154010440c000f000d410107000d0440d4035143e01122081d940314042e4031000403c0720300d01e80c03103d0501c4441200810840009142113400c0740180030740c1c0741d180a42a80350306c4054050000220b600c0c1d0b50380c6000207044c60030744903142502805182c01052881c905000304068410190908 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 722857976 1250 722856726 722856749
    0x3100e0c07020d050c0d03090e0703060f121e0515060a050a03020126090a0c140d0f0203120301061214150907020118030302031801050405033916 64
    0x110000d68094252880180e04866281002209107400d40c140105424459002104039443c10201904043d00f0b1058881e0030017060350a40d6405021016107446124038540340249074400d10055a4194501880700d004030651802c1400340c1845140385040010190703180d41041d8484c07918240c4002e02d054000d401100c03128155410000014403401580c40003d0510601407400036913900030390790408100d4000d9001c1c0201c0e140c92035655407101203120f0221140648140045060001c17444c00704030080000d44000051601075580d0411001a10b00980c4d1612400c9907a03104400794030000c41c047c04043d6104013540c040070360801d00b0342d4004514050604019010040416010383d400d242c0c04204075420743c441d44429000342e004007810581d0702c444100000401040c50f4041c0c0085010300300c00314510303011000b0748095500f00d800603600208503400c10410464003924440c0d0105020400500200c2020034440784036011684218a502a641010f42140c0d8071500806a0500800002d2041e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 722859226 1250 722857976 722857981
    0x5010f030e030f090d02040204030807050f030301120f0813080d09080303041208100905070c0c14180a140a06090506012109030507023309010831030503100e 69
    0x702500c0c0d0185500030084104042129030711a0fa0f0820148503154016208660700d0f610b03801c180341e155000c84001d55180c4201c001c20111610000103d904075120f117426006808015510359201c01c20210080d40e85000c10300c00c40d4564201c1820f004003d0034108000c03c24141a414060620141940140c0c0f06410510800001c034080c80c8542e042e429503854040d06598071640200c44030f00481e00810001c034541810031015640000d508014240220050030300107590760b012505900d8501c44440c0c1003054200c90b1203481007580d040e203401488684010500700c003042c1202da035102003164010038460302c902080158807240c0c03017925000682880c110540982c94001c00b81c450302004020108107665080c504145031003074042c2c9000941c0100080c801d1190101071025050b29604409520131021401c81d040001500c21580e0810060310b070025a5079030040c900e0721034110030303840c00c48600420307000501c0f035800302c102420258800d0b121651241090320010250f04d0040c0c0045060000c104103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 722860476 1250 722859226 722859251
    0x60108090a1109061f0c0b0f071d040b030118020a080705010207060c291b0a020d18031b140102060103020607082b0614030a020a05090417030f0105010f03 68
    0x10303044180c40070f45a520301034076001c0100e4280a03000907908514503140441c0d0040940c07044035480e0329805100e2420040e21750320500042040d056644102081024001c050040001c0103030303140c8010300410002e480c180b0040800c0c01d45803880016903030401c2ca200079808514003901f210000c0c0c80001e000300b40300b5061500107540c0341c1c0d190140ca41480020130403641085512051801504d03072100d140c0e4842c440c07625104050b00f4068400c1d54038032800e01c4941020f04100000c5d55080e43d0903500400e804160b154050710020b5250030a0746061009045c00700100300300e003d4200042041c601c0c0004201d1910340a6880c21400f80780c600e0448d00a00300402c0560b4031901a20b11305074101c410180c0d5212160140ba0300240c00c034500c42041d00440140c40002c10151344004100c035558003030180840007100416071078a500d50b00096001200034028099820110075841c0d0040c8216001040301181780d0041d94207170001c41c4c00c1401541d40390018030003035038005480c13142101d59080034040f5003280e20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 722861726 1250 722860476 722860493
    0x10936030809010e070b0406030c0c05030901050c03090d030c0210020f0a0828050a0e0102070e040b090a080c012304051c0302040b0c0303100e040812130203060708060108090a 77
    0x2005001c1100d5000421a9500c0c298482c50000e0300202c102e0b40c4451341c81d813001c00a500944201030200703140001251085005014420600e41d018002c2c0d49052001001503c05411200100840707200510020206032103445100d500c07a802515603102c21003180c4100480282c04032640c5003113400101b00041d07248030010f030300301c020b42c0d20906841c0c58a0600326502001c600f029a4810000340320b5101c40300981d0828000c003042a503a50f01c105030846041c00581c0d665049204241d58401580c00040c04100a40407807a00303c0440015564a4041500c4080850f0030030f81d10024903940d40c0b10000040b6262882401041a505176454004c0c6402c6d142c19455000441140400c40054095041024400c4e0304803000b501305c640c04991540c808203050382d07603500304a4000e00c4050b90036501080c040c2072004101c0c4100e45c410485441c089219050451154016216152011901c0172083c0144d60900a561050300b0582c0d54844500c0d00000040c058400a0312048031a04031402c0707a800b00310f182 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 722862976 1250 722861726 722861831
    0xa240501030c170709090608030c06061302070f0819110307140705030f0a12030e0304090b010201060914040605070302090d0f1106040b031b0405010815180109 70
    0x2401c0c00075400c1e11075032003034645000000d043c1d919030180e074042066042c0c0049808082d0350700e4010410000b910750040c240e0b00c0c460744c075010f811030b8000c0c40002d8841c5040900c04e0029120a079025061462558907408100500c0000300c0708108007081800358804080e000319040d0440b4608030500c0561400c6c016200d00c5104005040e9000d00d02002913000d00c100403901c002c00e0080c04880d040043c12503529114132640342c00312909d80d00941d00c07140c1c0c0b901c02d0280449050800000d185881c1c03070440d114005051060295040d952280c2c0005144000c80c0b04500d0408c490b0090751740c01d07140500d007440455000a042006041c4140032151980d00d82180b851340c51a40081c103445402014100805482145000254402c0d00000d02088020404000c0c50241c00f07299100c4c8501d4248007144642400f40c2c0c0100c0340002d41460003d03609008a007440f82d201c080140450040d04040d601e100c4c2058402d811185169480d649201183c0c0403080d00ca080d040c03d0b00e070501c3c1900e08060840d0003812000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 722864226 1250 722862976 722862979
    0x1914011e0e010e0a1b02100f06050916120504140606090c090d08040e04080a091512020307030e0f030418090f0b06131a010e0108042d15050a2405 64
    0x240001071110480b41d4071500005c4a1003100c00140102d001d0000e40d29032039010039600c4241851180084508240541130943c1d100a0a080c02a607038100c00c5030300c034003003600102c0400184d181c080d4059402c52083c680124081c8500b81e50400340d0054841c40c00001621046c00788012a00b00280b1542200c10781311585001c540140e40e01e40340303050000e0b050040d0b80042d40d05038445014403080005190003812200383e151a030b1085140da80d015122100c1c540c0c6100400700745644c100c1d040d944603d034000d5511404038100010003985445010785010080d00640217a42d00014050000c1040380f5007030b804000140f68180b0000803260742c0c580c4c003100100300052004501e0b1010a61944d600181d56195214100c8200402c03081d012030114590320403a0054003080403000703000104d52150401c64440da41048900f0315694012240401c2500c2130704c01d04e000400c07c220000b002a0401000e03100d41e180300780000c5440c0c10b224030701504880c801c440b03502c400418001888600319040b0041e0040317030300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 722865476 1250 722864226 722864249
    0x1051008130305180a140a050a03210c140703030207081b09091e0601090f02030708060d170d0f0c02030c100209011b030804030f261914011e0e01 64
    0x501130215416601803183c0541d200b1a9100e01080003040300c480640030a204803201807400d40d0724014130018400d18000501200c41c107008445103090141c0f100c00825103540383c03100c104c1c580c5896610070025902406003c030303003000c901002070590400110000d01651000761428000c110003e132500606c000d0f90038000c640e0000000d5030a0380502c4840340f280c03c2c1901c65516500210a811344400c0c0900980b15560714008004484004900c2036921540d44c98581e04220385035041080049584400111014015460180040740c4008058980301707481d44030110714800c00400c41c000360791501c90f02004661080c082030075444400507403440d15510122005945481d002c00403681e803148191105a284901c01c0441c081640c094010b0740315501941d121a44848c001101700ca09240080f41144402c040214405000e2440f80065030040032004180c02d6009011042d030b410303140141e01a200b081422801000007240d0150515101000080d600444c142000380c260020b82d410f0190f03800a04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 722866726 1250 722865476 722865487
    0x3040b0f10230619030c1704060b0d02060d1a191a0c01110703080601090510050a48050d0309050f0115060e0f0d061e09080301051008130305 62
    0x8a00c2c001120604a019010560341c2d0055000154040011031419002038503144990302c405104013914280c480b901c140c1000c2e180c6864072004040c207102c501240c1c1c480944140c03000107079110300060a15a182d80c4c00480c0b60180c01110380300c06019000e206004200e99141c54180c021900c0c905400d481c0500707074212180c520401c10072054010521540025843c20846d40280c1c01600c01400e100d5110f41e80d00c0d0299a1190011600044684162500410740301008901540600e000d005404407901c3d100c90700c18502c006920154521030000300341443e82030603070041300d1003d005070703903014a00042c000c001541c0d594a0583e01e01740352544104050791400043c04020301800401041150035000f8040c99070000064000c0080d03522135500824015400001c6070b0400302c0c00c540d0f0004000f070008412801540780c0e50040c14044070200b034125402e61814182d1401441900052800754044946a60500d402d22602079154210f4005200c004e404010805030703004147c4014a40c1445c0c10394442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 722867976 1250 722866726 722866769
    0x6090a020418140304030b0c1c0f02070c1508013c080109050606040506010c0510150b3103120f1202040b030411090f070c021c05010203040b0f10 64
    0xa150003004007099a583c43c4040301403c0040070b00300f0740313000f20031045194843c0f40c5004d1480c8581c81d0703900401414081040020750481e4030014280000c45805460094541c1e180c00c0c02441c0c1d900410139410b01b0440e00d01c030b095481441140175002c00c2e1100001058203400c420381c5010b19062a84041010034262584820071801103c02410f0000090001d000680340860725460101d80c0140100e1510f00018459842006540c0310740f80c00101400c904060041600b000d0410b41c0709a0760100c4e208080050542c44d101c1c01001441e842035550100f81410443e03080f010001c5000080650070b4820050000c6034102d020682c410304282407440c8030714080303d400d480555203804201d0b829031000c45c000848200b60401103104a103d40032a038550118001000b68443b001e0b41c2c2d140d0310116020004140d00e01920501092500050590303610465580000c02500c1d8210b20889242e50040140000c1156a642c420340001076600d1940c100d00d081d505104000b601071040e00b186450058402804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 722869226 1250 722867976 722868011
    0x60d0213150e0703022721010b06040305100f05013002040e0c030705060309070b0a0e1306090e010b0303091302040332030f030a0e010e01050f15010206090a0204 71
    0x18000c0a024050030720f0419000b500a400c04000540000f2200da08101d03008605a0341d540e00780b02c010a041c500c0721590315900d01481d600c840210306d039980e07402414583e940c1d40340500029031060000f403409030520500301d0306903101c4048518145050500610a507031001004584038850102121243c4007000c10038000481414806904246882010000500007107100040440164201c0e00d01d20350710300a03c808c9100c216401c20454001400078401640900300a102c4044c2500e08503004218090008030201080310800e4110f66440e90108980c030303018003c440441c03102c50000c01c0300589407400701c2e880c1c0c40354102c440e100c2c1e041019101d6a24205506450140d50861218050095400d0f100e001800c078507010010741c000d20345020030040340004203e81c02075805901840c2980c5508441801030702e150341c43d0039003d5403a2803c62003006d0007482641d200381151480c00d911400e00521031410700c02c00c620a1b9045400c11820440d2406000030300d40c05055040d00d0024010700614403c0c042c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 722870476 1250 722869226 722869229
    0x20c100203070c03061514030c0f0d050d050a09080c0a061211031837020a03050d020d0f030e031b010219080403030c0e1809011113030b060d021315 65
    0x74020743c820012043c400603902c200c107800e4941b1b41e40900552500c86031a980a51220307202d601d544554811007240c01c10210701000030001a0902054049983d50380d07050401000c1071170009000411490703051544800d005c00180b016401801040d4403903008074650340450f0068034180b01c2007d00344100c02205900100681c0010b8003002c0c0c0381e0030142c90f0084518030450081c4c20501c40c411405800c000c02c081154500080365110308014106680d42c0d2141005000040c0c1e44061044c0d00080414001d1000e03510101c0264040c110f4060442800b800050943e4003030000c2614010715803010b880000704480d02010031009242c1407000e10325015000e84035609150742c1030340e0101e00c80205150801c0130b0074000c5109403421310140780c040400b00c9000c01054a071a40c010700b448501d1036034561699900c1d81003000c144c00410b01e01000306c052842c039071080c91106070050b03c400302003003070000b41304809400074003c032140d00300d0100540015618604215401e91800c0d518600c001103048006994070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 722871726 1250 722870476 722870483
    0x15091e162703050c040b060711010e040207031107061d120106092c28030207090c05120a02040803072a06080405190b0c0717070503030907080a03020c10020307 70
    0x5a031211860800c500c0c02107244000c075014410041204164a000c1c0110081540d01602460070003040c0e07254020344c92540c6070418107001100c04211465203070350000b8400d1500940702c05480d031120040c91484c0ca2925404182003003154003074061074600400307210306d10b1241101c02c841060700c1d01c81a540141100d900840c6480e1904030071f91218481000f032075800300200c10008804590b54900503032106000f0340340d5a0080b949141e601c01d080514000d0011190091040714007040c0c580c4500c3e0100d403540614403010400c0401c022500100c503030f40b40369211501d0401035080c58034014002d643ca00070700b0001400c02010240d161140723007810115540700c80702641001141c5950704030261100509641c151039601945a0f4001d945d6008502a60f0740c0741d21507508009035a0704543e00145800079502110091841c5030300d902d08c080c1ca04083c0603d01d00500180d076590405250880c5010300c1e5920442e01900103001c0740300420b07008542c0c510301520940310a062100702003400c07800d5200701c81008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 722872976 1250 722871726 722871767
    0x11030904050a0608070801180f210806031204150e0102030c010204060903140a0c060e030f0a05060a1401080a033605031b06180f060315091e16 63
    0x110200c0382c190455002c81d1400000d81d0300403a25941c1580c08d0399842c291501c110700344001200c00150003000c0818813540602010052813203009030806100c5c000000e0003001605140c140805498244560410960b082c0c0480c1e18144c07400d40d1755249200e8030030400040c08070f51500340469900a0048030341c04000d01008564440d103d04020f44401c00a00007507030048088485584005070000c2c1c01240240c100040c0f82001380b40840840301c403444821155050f004405003014100010070030035420a10990280a6500d40240801d08070303a4410f610b04010020340004005203180403031200e0b003003078040c54401f14212410404510000c4980010300c0802c941c00f101c1c45038000e1803000c450070341e2412030aa44c40da144a10744c02d4001c082c8034081d1580540200481003000c6003800d14200d6060380907080c0702640d00e43c5000102e494004840d010743c51013541c0c90b01c600c00c0c5404088264000c88001c041800b152010035100388400c4014001081038106282d2050b61500500c4203906002a43d03449 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 722874226 1250 722872976 722872981
    0x11713050a0f0b0f01050a0b030f0417071a0901050610030207050304030c150908010209060d091406071206050303120412020106030c08010e07080f03070312090c12210503071103090405 81
    0xf006034180c080380c8802621410b8000840e803440c201c1070900440d0310507510141945c9800c0400800003001510854149003c3c244d080f031b82078812800b400e04d450041c940c1c80302d5000d07580b55495500400909a1400c2c2e454202000060350f83c2611800d001c4090b4580180c43e0000e51820b18039510490b0805402c0d12804000001c0003107010100e019009010740d91400895a200d050500380c0c0240302c500d5511080c01d01c41070b01c0d0542a9848041c403540207000700c0c0b070121742d90b0719010b090050079500b420000c3c901c0c0c0000c040c0e0700d5460040500900d820f50046103455011803443c41d8110015100804661b0345030342d1030450324030135000040515002600c40308520b03590948103009102400c080390745401285400980c5281c0840c81080a0346028061450003803284c0e01190041043c2c00d95901660b901c4014601182e040c800240142030742d50402d215403089800e28030010700c400c083c1c0300156107003d03103400702e11035000058030f8202844e414180e8290022a440c142940580c060254002e880c1908 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 722875476 1250 722874226 722874233
    0x20604090b01200601140a0306020414281205030903010e0c031e060403141306050918070c021c0f06140c0304030c0b060402090d050a11011713050a0f 66
    0x240d424003000340c0780c480142034620020300d40800c0340d0410f52201c2d00100010410100c0b400c001107900030000704030a8459460780d451204a030499004a44100d401240c10740e10340c00d00c0f00052031554907441d11510f448841e070318801210750260060307a82c000094541c0c1800c21000308259620388000078020f0142c100f0f05070341c55540e8150500030074070902c5119a001d21060708005000c800d40200805030040e070341e031604c0c10f54804000008514001900f0412818402c06c030404402c090071903581c0782a5a0226030342002654451072504070012080c0b0ba06120542c0e4010309880c5220b0b50588221082d01400c421100c1088035103400609011500c644540800811b41c4c040160b607405041c2680241c4c840c0080802980001c9030001c020400304007004000c1003040d0340c042e600c06801803026140ca660600412001e1200400c212490fa0203000c0301810000c4414001060316000c0c038014840348696400040e801c1ca0252a001d0811218103084090040511070046800c0d000f20312120644000c1c40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 722876726 1250 722875476 722875481
    0x150307180b2b02070807111801140405100602190201110d0c0b0903030106080f061f020619050c0406110a21020c0907090510091a041a0703020307150902060409 70
    0x11044421480ba105031030512a01510948083d070703030000d00b0103090a000d0f6403901028003610341d0740e641c82043c030728049400e1105410500e01a00c0c0d44030b0b44a00d240600c5040c00141c0d00c000e08142c17001c00c0e1406044c40706540c001440301002641108420915181d400180c0300040846001c0c0c1650041e03c0d44422850380000300c4004040c0320301458100c80e0740703003079590b9203c0c0000c0c09030800051030b00000c18503d0010181c1207400000081020400080d40f9031510519a4001d00100140c1c20280030050100822010240d110701c04280610032480c0c140404040ca11460050000b405612410301120803010044100d180da030045440b665080c0001704949121141e020f200010304c61100c0741c10040c2040030180340a1540b0b07840d250340d036030300b01410400e910001658000420030700e980000744141840d486158915060f58180d9607550506d4004c05603003081480f21506524104088000203600000b2148001c2e0000d0311420003030079102041c0c01428010340d001e0b520040204021510100ea179 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 722877976 1250 722876726 722876767
    0x2111030c0c0f0604050c270711010c03050402010e01140c0f0a0b07050a081329070e060403022b051506040c0309110906041d010e0c150307180b 63
    0x40040b203580e1201803500c19910070003110020210b4100e8804030045080503d0f0036030203145071880c070319844402d4400b140d40701c1008490603000a540c4420b0031100c00c03000e209545469626150501c400c1c501500040d00508400c2070450422440080b954850015034054070540000c8500755004864030404a0750355610747c25058501c580031202061f5040d0045045402e00112501e41c1040c82c0c0e40c46010181201610f001501e96064030000505443d9980b030195411080b4058401030f40d040010000740001c1d00c44641a0284104020900141c0c1c0da00c4292080c1340580132540c0e00c40540d41c1307220348451020600c02040e40c880c14070b190b40c0820141990600ca000181d4040145031141d182c1141595107100024103402d4a42c0d0420806003080840c41d0390081b0090b101042c01c80d01d041090030080c0c030700b030340c0440c1c2e41e551906400d4200d0414891140e600304100c1e0030303100980562140c0303000703840007826100030300070000000703044400f41d200080700030504502103540315904241c0328050303114076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 722879226 1250 722877976 722877997
    0x10908031803030106121509050708100f0308090415181b030908070201030902010302090a1205210d0e0a02120f0708030406050405010e1f200307032111030c 69
    0x42000700440360400000f502d04883c1d440c0d0380c030100c01111036081d1008086900240b02c240d184c3c2c500218800000d4000c0b14041d000f25500c01015150012103040100150341000c0a02451170904201243c030003429500301c00001c442c006000664812510b00c00c0b00b0035801010141c1e05208a0300080c0e00c03030343c400f80000f46a40030361900740250410840c21104924002040c3d12001e10040b009540319500c0310071440d02c1030400500c0d03d103a1100050300d1020035440013211240419a0808100b41403200301c1ca1441000300c0d0349d02042e1101e10f211424043e045500c01c00f0340e500d85049140040c200160380c00140c016005000442404a130680c583d0101d1100c104148121040000c020100004a9040b03404d0790340d4103400c00b0300b410011500c070000805907a600c011007080c010f0071064100e480c1c0030b98401d1a110403507001001004e880f80701d20000d0011020740c00612440010a8102c0c0203120038011001c401038140a82d480a40010220402d030f040d0007484c00f004225010189a0060112600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 722880476 1250 722879226 722879251
    0x1110a21030b04200a02010b1306030c0b03040c1217030a0b0f0901051f020705040f150e011409070203122404050c0f030c04090c082706071b020301090803 68
    0x2500103200990300c0144c40045900d00c0c2d036040403a0480d0001c041c281040e024030000c6103484002d400915800c03180c000c952001552010104204500d0195a000405000310082e0440c47d0503290f044100700648150b01c00b581440740c486d020402004644543c8280d8144282e891f424600d0f02a4010b00c5a1248a4042d03007815444100034644201554120782004101e020342100500800080c0d40400e01c8210540c0721384d0340d0101c0c0d580c0e2a4010400e10038080900002d50400c50511380f48000c189034481540802100014855000c08407140803001c881a60903200380d03203903050202d14600c285900c25591380524420300c80442034207a1594006082c8140000c0111101400c1004403041644c5071810042c4c00c0103140c07602a40b490242d50701202c10140542801d43c2c411281d01652035100190000030140070030002c030214070410044140220241c0f61503000303404a011036588401805460a204c50450500c90a20b00220f190415030740c060001d2220b8900c2d8030380002d00e6002582c42480301078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 722881726 1250 722880476 722880491
    0x30103022b15050c16110f06042904031502070309030b100501030b3f03180405010621090c0f0e09060708070f080702070306020a020609010b0a0807030201110a2103 72
    0x80c1084e0644884840004041e210103006542c1d030011080301c03508064221380e6480001c4070550b6104060001419180144090004a1403515100c8080ca01603103030300d000e080c0270502c082540c511200300e211501440c01607440c070301824183c5941125500040c40c4128540070082006000d041807011030303e081c1c0301800b11203204800c1054140142d8042c1005040343c0000c0300e000d079194140d10113641000c5002c101d01c1c0d60748261842c1991b0003c04038072590b920b43c50310141a4207151103080e005100a250525030021b0498082c4076000c10031a00f00c43c4a500c0700742484c2031120505d80d0400a060718441140603540d80c003c44600e28600702c507009440d01402c00026241030144124910a01041c0d5905032040300440c015907094601501100852048000100005d2aa0707c02030040a41030380040400c1c0c505066001e00b92243e11003540d00501802d2010060000005403004c156542400c0030400b0b604860041403038044864006800e00d020110144201225140c10444240c001da40501146 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 722882976 1250 722881726 722881741
    0x7051b04110d1d16030b06010f080703200d060e0a0603050718020c2a0307062114040f0b0a090305180301020c01061412060c030103022b1505 62
    0xc480a4520489524040110000002d810f0303100d00c11030024104920303c41c940b01c01d615442d00e050b10010009222000c2401d01c14461440002ca034003100c00d02c1c0021180c0810380c401400040040d0100b0181030301c0300d54000901c90301da500c080309240f440180700e4454124024030009401544941034120703403140040384581d4000d00414045d40e400c1401083c00c0c038581840304400280c01c402007041c07039a007803101c03820f4501d0501c02c0f1041c2c615403441c1ca1802c68204000260b2042c3c00c03c5100f840395014030070406c441c03074005840c407610204902c05071281410300e0310000046c100e01c1c1c49d52000130780c041080104000000b034112403000c0c0a540216202d540d82082481213a2a5200207408100c051008041c0070014001602140c00040d0026061143c228107480c25508990401c5022001002003001517040041c007a02000e030302c4800808950505400c4050140b0041c08040e002d24500881030f401000c1d1982c040000c00510440d0755682c0080d420501e442285524040e1403160a250108816 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 722884226 1250 722882976 722882981
    0x702030406140405150f0d0608030a1e0804110a12121e09121505040b060907050403110f0a180b0a050603150108042603060a0f030b040303051b07051b04 67
    0x6940c000340681207001d18481541700305400c201004440c1200c01c000f00e2074401d070f09000e201d00400e0b00c0c900568030b84901c000d0203494805001c0b11401c501408840106000350701002136600540c11246604100324518085600b00300590031041d40000050034036020803d101e42440c40c0220036a41d81341c407001248104107190070030390840307400141003110288081e82e002481c1c1c0301d0061051013280c40b641c04210501c0241c0d14202c806079a4261410100003e508100c0d0a85038001640e02e022482e0074116502d2814002d0200d401d0b40c000c1160200415158a07441c90f10740207000101c4c44000003003607056148001c1c0591a8426000300718030000014581404029240101041c1c10700241044450740116401040208140d419040c0304000b11288440b00003400d00d45c02000e1000ca640345020404e010310001ca661101c4266818450104041680303503046541040c0e1626010030300f51920654031000c1c151304d903041102003400081c80c07002c0010000d00007821624404c0c0080b141d040c004104401c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 722885476 1250 722884226 722884229
    0x8010f0e010605030103030f02010b0a08010b010e010801051c1a0f01031a0c03070815100504140d0f0206070305092e02010b030c010315030b0703050103170406021b0f030607020304061404 82
    0x802c0003400140002401503054403548e001a20001a43c0ca401c4400101681d408c1e0303001400a9554140046003540d000061070643c0500303007084c026551410003c60a10340d545900e00042c0d0b42003503140d004200c00079400400340790000d601d887c40e5042101c03002002c2e141c00e12045441004104450045141848405201c0c00a09030403c0c150340d00e2032005d03a280030740140260300b03102510200610750780c3c903000030443c24201503403007a072194204041c0d80883e1708001161403003600b800c1d0541000903440e0191a0341d081e0705803003a40c0c54049924040e5001d0040c964101e9010012000707104540c0003e411b14201c2601c102d00202059500000513401c0310f242034040c6415070800c400f40512ba50090b000100c6003250750101d801d01035901c0e12881d00d4201d007a0791080c00a512000100140010001042070100d01d0602a0386002d14066020b951000c8030b040810b02c002465400300100d540e00c404107864403001900b61801c0e0b01e030103540251240c3c041e005907404a9014159402856202810b960 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 722886726 1250 722885476 722885489
    0x607080309070806162706090501110a0b060f22020913020a020601051c060f020a02070b0a09051507061b1d0603010e1b07030c020301050f04020d020d03050d02070308010f0e01 77
    0xa0700e2040c02681107030b91500f42e03152a1170b10320074030600500310019403240c240240700b9541c59510403809c1c200014013003018200e51034015403246a403100414400c0030b03d40d402c40c40455141c58510381500c049420748040c01a803403910752010590512440094000f0f15030321004a80c6108812065034140c02240550b194a50050740010014002410040c00c549280c1c000c0820300b100065056a072201039030009402c03040d1b080d402080080c031031a01001a00058504091103d0900c0c801c40802071000c4c5140c850184502c00b00c01c1603128400190040b18685a0800707018000d50301c02c0303203000381003c04040c04580000c107c0c0e0300382c00345003e003401042c01e4000e0040c20070340783d41d00c0c05240744030310407014195545540d0858100300030355000d4002009124800d17160942d0362a4507004150840320028484100c2544000030400169112020b901155604482d440414071580c01e0483d568090890100c078032501c0044c2402c240364120a03c1d5048030040e050303018001d1381303801130142800c4084c45981c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 722887976 1250 722886726 722886751
    0x1080112020103050a0b03030a1d0a0305211e0702090a0203091005060a0f060f0f1809020706060803031302041a010f1d10080906160207170c0607080309070806 70
    0x140c006600c40e80006812803100880420307188804400281954070042ca1403001c02c41017a00060346081c21001d02c0c0c06540308880d500d440618503110b050701e4440751914607040c01d41d10000303210102013440548020650309a100c1141c1080078030800e01c0e40c1e000107426031080f13102a000521841c800d00840e4490704215015110010711b0742d000501138040070700328030b5000d9151030f4003054041c084140c01c8002c0c102680c0b4034401d0400e4072000f42804e0182c10f0b4450401c10b41401c200b1407001c026050104955000e000180d55000c2410300a00800007504284841e000c00014003640100717400e141c20a45000f102c1c10032502c0c03003400d800a0003404917100c841c04107580d81c40e03403244c95000309407030403201c4900c00103081c0428403440056000751401c203103500403a0000c030030b120703820b20100881c0d54030810b9200c03011060410070308081d5595401780319401c07004e94140809640c95406000c520122403010302965140d81242c6401300341030f00120f402d800c061240c6000060703230301c1c000241a8060103510110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 722889226 1250 722887976 722888009
    0x1806121a030d180504020c0d1b05120a022d0709060f03020f1311190c020f090c0c01090c06030510140418080c060114060f1804091502030108010b010801 67
    0x40c3c1e45080050510036074400030140000b01c0d515940024108a8500000303080d219004a10140c8610001404c481c1a92911a146400948001a41914031341310401c807944915a48404910b403070703112910f00c482e6014001e5120740c0111650300c02c2d100d2120580030340303540c00c1e10340d4140400c840080c4282487c2d240072610420250034080720358a80000c02409446501744006003c0301950003045000d01c60242c0001c424081107021181c488914495181401406a164001800200c041c49800d44510405000700b130382d21600d074040b41ca00002000c024440035400f414500001b42242c4908c0002c2414000000c000d0810030300d902c01a04c2c0550241c1280403081b40a1000511b0306216000048190396000c40c04200d20401614500d1280350080c05c0560405151607080c2042078080390182c1c2050000e40049407110040d9900d40f956402010740d2079002400040141081070000b0340722280c9443e107500040310710b80045068807881002400410761040044a20000c2441284003c42300c5210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 722890476 1250 722889226 722889253
    0x210050a02071703010614070210200f030306090906010b03040807030c232109042c1501060203040b180d080412110d11010f1806121a03 60
    0x1450300000c561000604086142c1c0d01c0300c0920359200c4841c1d2410002000400c01160710000c00c200a8140750348803420561a5400b0420743e0a420107208103206d01814120807000700c1041103041c10a08008946e04c080b20046155125441594450701822140b030020700400000624281221001903c43d451036851f80c492108941102d54100d00300b00e040081c01c00450801d40b40000c5040e52a0440100360203400441c503c0c02102c15244080c2c1c10040d41c0540c810403223401034038920f603802e50380030a5142510b00421f03190300b8038034101001480744044444103a140000e440c200e2807401805020240d03220402641c0e00d0280d8883d003986001c0410403400c10b07610748075800c00142c10203005224030308507558911807031b070700980c1040346111044084903051009802c0741c40042c00041e109a0002090750b05d6910307044080001c40e5060199600c51201c0280c03107010829030713600c0b807000020400d03030b00c60030000c2020f81000c16001c5400d0806642c0e003890108030303125018004005004003643e60440c1d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 722891726 1250 722890476 722890481
    0xb0d050c121c0504091406030303131403070b0f090f07051302092e14040b0c1c02060a240312140d060501030c0507081c1b0c021c030210 60
    0x1120310703a00340600c0034402c540c00d84950449030320b450a030319400d803254108000e49003126103030006d07442c40f0305034a003e00600792008004ca940000c1103094000025489090064a0313869030203280ca42440002586001e0204409400307005200e4402034000c16115440c05070760360010a0480d0046400154080040303282000341d29052462880015060203102c5000901084690126904080101c4850005524442c06e008110038040c1020407a0011a106410b901d01460240e8100d00704001280b554190302001428841402c43c80003811080014030700039165002590380551260828000c2ca8030440105c1d042a890303042982d03100c03841ca1542e15804a0301a15200413810310132612a042c0c103e21a501c014400d441d00000041050741c50000010100c5070340c40c0c6131108000c130601020000036505002c8803114a00d0a0000c4002c0c49400303c039400400104000025448030103651608060304404200c140e640200c41a200060244049200034124914000e005802000740f100c2c40b415030b44e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 722892976 1250 722891726 722891749
    0x42c15011b0f0b0f070f09140d1203020d060902030105100e010e030d030e0c030c060409090804051206090d0513210503040806091b09070f030f1a01030b0d050c 70
    0x1004041241819520741c003551540c1d14005a440e03000300010003e5102c030448075217802c6072a614200b030f4429107440004100320250f008804102c5081d002d4401180d42c0e40c01143d003000d0700140d0b0035644030301c4020007800a42c00705e4030349a0050b081034030024158007a0f20a07603040f02da0140002c44004c80d9602c0c01c607440040010f030790341030041c407149000441c0c40030806443c84501c243c0380050b90707840000e65949040c444905040c0310794003074035030740d44151100403d403011140c0c0c0c00e5021440541501c0c00583d1070080703801c8160000b0507000c41030034005001500074000c0805030140d84c0c1c1c5a0030100106c0c0c4d1031090b0381032030600348d0b80454100070640d001c00c2113101c14182c5c00d09907104003010f55105070039540240c0c0485400d038000c0c001d0041c991400e00c080600081d04c242201c990400b00000718400c200020400018040f0540f402000076000390000794480750602800c100f00030104c100c100444031940040350000380b9004500c001030504c03065280c00d0a42180050458a21100c200300740c0e60150b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 722894226 1250 722892976 722893007
    0x201090e091e0a1b0302010e060f09030a0c03031701060e0d060618140106021c0305090f010e03180103020309340603142805060102070308042c1501 65
    0x124100e50610600300d40c6021540b6001e200540b8810f1510304100300507103004524041118000c0c03c081005030307040400f0200b0400c00740e482c00e40340c5104941701c00b000c2c0500000e01c0d8245c050450340c1010000c886240c84280c0788680c5849500b81162030740342e560302100340507030008a038140012281a1034620310b000700301d80c801c80300842c4d100d81b6040b041811041d15400828000c0d1103c01c80038a41d440c807031a01e80542020310041c0ba01141d26146c0c01005020046c0300c0c0f050540d230ba0040343d04004140a081c41c0202030400a0090b9600000c0c11ba64070303407049904903412411000e402006600c24002c69026417008001411210717841155000d8403202c00351840b170040d2640780c1800c440845114144003c1a00e502d0000e00c0c0066260102c0400d4001040200c0c0342083d40b103078502456604003900d24803995854000303100d1340d5040050780f601c001c640018001000c049000103050b403120010101d64000c504030140110076a40454408040560700c1c4c090181041c003074428030354802c0710340140300ca03074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 722895476 1250 722894226 722894233
    0x90705031315150f05041d0c0f040603081207091406300c040501090e0906070c0206090406170d020d05030406050c0f0a020a0212031e070203010e1204150201090201090e09 75
    0x9191192480c49440f0b0740c003103003508004140c1000646450303c034410b1081c01c0b014407401e206a9900d646510307940d00d202c030329200718103044404209032125400300010310781c040c1d42c441c8d490281c44000f880c001401c0b03500800040900340c02159021541d815003022041c060310060030001142004000d40d451130b110041d45c00901c2604060711400403004500840c01c082040c0d6886045c080010501482070300001154038041c81841480d1100240301c540c0316010b0b10302220300c0419071000070035501c43c40c0301c0294003504103200494410b4001d1410203182d018a030444d40700f843e08038800c6e03032190001c08200b80810000c2c00000d000c9031841e0420756000d00003284480c903203665180c1500080e007082a00c0380c0180d0182d210f81086086c4020340302c401007101001581001202192031480c0c00c51802090300d1142c0114407002191025005a400707100c222054034900002480b4540d019001482a104243e460a2010f0b00050040c481d00362a01d4040c1d54002055007001c04400549102420070a42e611 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 722896726 1250 722895476 722895491
    0x1e0a080d0e0d0c0b07031a0f0d05060702010e060609042111010f0609180b0601050c1e010e0709020414060315100905010e040b06041a1b0a02090705031315 68
    0x1401800107010442c6141c503141030311159801c1142c4102c03402001034080c50702e007282c2e2014400c550b04a1140c0c50300120b8160401503c030030049400c4441154004106104940c248070b0400d030190000c0304115006000c0712001d594803804c201407a0300a031805000b01da00c142400c8456181d49400c00d08200c01828001200c0465a1815086820b4903d00e44641942c404091200c503000d030049130107801d0f07003444504d0500203603202c46d100d401d005828a0305104001030070030300c48201481014601d80c801001000c410041c0081680a000e941078820003600070004040381c42c450718401c1d1000c0c0c2d0f2811000c40011486041070249030751000e041124000780c0c1d01c260f1403440e17842685031400ba001c00c1d0781b094003480c0b91900141210350030802e8244114101040b00c04952503404c01d540031215003810705160f084926007051068421985458a410348010181400d06000111000c1192003540c03e803030701d6a900b25003290a80019100d698484039075001101c04039030000381e200980c6050b01c5c000100c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 722897976 1250 722896726 722896751
    0x4080a14070c06080c0c07050f131802120a1509020d0807052a2d0d0c1401050c250f080106150c0b0408030405010b0607141e0a080d 58
    0x25040700000b2100041c07007042c14000c007503020b404180c1100b90681071500f0040442c1c1401d84582c0325001e4607000f0070956110300c009586091160803c1300d44000c003008450202d004580701032100301800da00030008005200b030183d400043c8512040d0300181001007084002c50400003400d0784c51000c4c1d078854031130b0a000c400302c1c01131002088001e2049005003884c002e414110b140b0500c16814090282500b10000300301d41c2c403060741400e10040441703220510b041c1c0945d044a070185031400000d400480b008601410480c4c00902d0b18180c451400c20054100c1101c80111141d100382004c0542b01e13000716407901040d00390410205002038000c48280145601c1d07807050300c3d1a030000c0d44003020300da458000811011270814480d00240c2c1e1285440c81074081c1c65150f0701044100a04001c01c00640040041c0030f1000030340c804121240e004060665900e41c0382001c4010807100d10800705103020314505aa05414000c402c0c07076003550803602508400707030182c5030302c030140d04281580b03d080c584884950044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 722899226 1250 722897976 722898017
    0x91c0b0a050c042310050406020d05090a0f0b120c030606040303031d01020c0a0b011a12040f020612060909071401030b010216171605010518040b093c04080a 69
    0x8000711300320702e50303042c2d1500c400c22009207400b844800c18000104010701841d60b01041c160b4254105c1d0901650729240d6502284448645920441c10340704140400719026425000074420b07440d90b015a03042035281c482c01c004242c4402e9810315402003003003008000281c020b8015039920340103081107040d62a1404822420382c0d02c000c101d0400350300130b407a48004100c0313481c421901610041d811058000c08211900030644200010703e01c80b01103180014081051041c509240c540d030103418a038a0748d0048000c144ca4240c00d03581c0724072841c00348000030f45140001801401f140c805c135100d89841d1106c94015801000c4050b1071034118002c0c42d1990485480845c6404010982d840058070b01c801501803807810800c0c480d00702c10381c9018620b01000f00b82c1e80321040e2001d4164080001b9402254000011700902800306100d030060702820820080d00710301172400b40711030421000542c44080f030000035041405100e11005030468141c0120340070500103030140440100c141070864844454200783c841 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722900476 1250 722899226 722899259
    0x20706360510050913180501020a030204060e010c020901031104020903062d0f010b030a0912030e07060c2328020103060e0402010c060c0e1005091c0b0a050c04 70
    0x40c001100104214508002440600105091400b5820481014001200304250542c4119031941750a000850021440d98804080c0c0d8440e000715030710103030310001038041e4010f0300c00c0c140803030110211826194043e0001070700850707004200102030303030965560040d8040b40c070002580140d404d02501b150341e2001c10007a070140060300e0600710028200440304003021401c070748502411201009111518804031ba00c4c6065800f8210040e03100e83d41c80b4034072001070020b074001074401c0d00345114844082c0c1d01580800b450126a1317048d114280d0321003100b55880d03503007140c004050b07440314100c0b0070840d807014440320031501c800409d5464550325442421292211202c0504003841e890038568110340e010321900000f0320302442ca0141d545015000038044d5030501c00e018000f00d84440358580302611036200305070003850042c00ca40400000c0d907c0141a6004010210b01800070f6100d40388100c1c1c039141d04915559407080340c0c4c210a588221946024041c0a40782d4400700381c0600c0301066100118400d0923 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722901726 1250 722900476 722900567
    0x7080c0f0d06090c0e06030a1a100f090605031005040908040f030318120c0e060102010b120717151305030708180906040e06220c0801060e0903030106020706 69
    0x1086410f000041007100e801031303001c000307120b00c10344642440d4440b5000e0729403002c05c401000400341d002d140d500f140c045048070900c0d4411a5a50442d41c20740d000206020417192541d200c030038444d100c1000384c8540c8010303603a060650359000d40030001c500c0c1135040446802d20580310241003954590541708070042e030741c10850114002011031051111030030a0007004007004808481000569294200c2c203030b00318055060140314a40000380c540c0d000350844252200081c1c034020b90103104418160711402140038a1018a01203000800440300000d508800344046030000905c0749c49020290741c0c14500108200c84a000034880c403c003242402010b44100900200561810507106041000031400241950b100e43d00c2c01c0303010700da80b06000400741d502100c3c1420140d06d40110b00405000341001c40c40080c11202c9040e404100c021041d0018011107042542280e015124116480d4030790009000f084d0060703001003030401810744100c1e01d110f5090302d114201001e01500b0903d1206101c4d03402200c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722902976 1250 722901726 722901731
    0x7050f010b03120f190e0d0c060f080f070503070c060509061b0a09090f38220507030f05090a020f04090213020307020102090904050a020a05090105010807080c0f0d 72
    0x200541c10140443c021800710390090700c2c54840c031355483c40d505005c0c441d64160701c002d051006600700d0f80142d110003000c0700005c002400d84031480c03410030030714882e901412000661202c019145140205045400b81100c0506160195540310048505d80c00c000c1c81e220030081002500800305900d8840c80d401400d20002801d503500c1e03d034a0001c604001290b0310350415a040265501581d0701000c0a03003900e4049a0100e010071a910460014042d003c055094090036024030078080032032540710300d2400e0076040f03c442d002c0c0046020071140001c3c05150303075151b0040d001c080b010301d251540410307407118503401d00140164200d84130400700d030350807030725101107501600f800c0c2c00394541a5082c80400400b01c0d814000f02240c0d5000c035507846016400102c00540110102d011a8000c1d019034400500c090030b00382c0e5518060031700540d00d120702d40090340100402038000c200c5080a40e0b206058582c1070715000380c540c58513402114080310003080709002c41010300212070342d074004100900001035190000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722904226 1250 722902976 722902991
    0x20901051303320c040b042306040605030309060d0b0d0f120909051303032f190503010b12090a05031308120c0a0b0405010b04061206051806130807050f01 68
    0x4019000c03c1500c0041402c10740850080040c110008581110f01c5050790086100030744980414007604010b00c8181c00e4980806a010341108500742c050701c2034200301e4050102550300e5050584900c100700d03e8603041030003040890b405c1c2e400c0350051121090040c2124043d01c038a611008a106100502180c000300c0015542800540c0805440050301036502d0401150510b801100d5002c590301c40000c0526840b0407482d440d6403c003460491072800480200030520441c0c1045401d95400303041b4400c0301c40020b0210083e45845142503234165460b03869480e181003003029100340140001096552103200d03030040d400008030140003501084095401070604141402400d81c02c1c46402c2400c29941034090200b40c81a08000032860b2045802852050054685007001400f5006405110b43c000b400c01800298128103451400c0600d07000d0b8030104565101c0345540300d821804151880e4403544210301050003034001202603811030340b1400f45280307072500d40c0e0350700c60810464490f94101079549050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722905476 1250 722904226 722904263
    0x304060f180f0e1006022d0d0905100305100e0c07052a15071403040e15120604031707051b010b030f06010f030b06010e03010f0501030213020715020901051303 70
    0x42143c00c4002c144c4141013050600703a0003503441d0b40e50444085600072001c4184058016151070507110303940d00c1e05440801403070140c040c0c40c20259125550003240504e4040c1c44062092044c1b1303018042852060418514080700c0e154800300103444214404403c00440c400140c00704403602032001e49c003005101d80c240c14940142d00760301100f0303902d0003510011410301e01e640502d0222416154040c07900103520345c3c00610549540100d4105140030f4070484141b114801002c24000d200c0141113034500c20407054004050345501c400d640041c04148150340c4106a0454060502d5000b001032420500305100c10313150000301740009000b0103541e5034030180c11a16080a03c105c0c0a00141d030001000b035075151007100e5000744224400602400e45040100350140e1041d450a940c0440040c024005c5203920980c0b9802000c0038403080784900c0d24403001902c038502a0003520812034001005c1d1aa000b41e1a201070044d5001c00c2c19175040080c200710794480001c481017080080c60145040310020ba45085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722906726 1250 722905476 722905499
    0x510031d1e03091305150d05030301080d09060f030c1803080315012a0c03380c0409111e0712050f0301061b06020d0b011b050304060f180f 61
    0x10854406800c01c00200c5941e840e03151001200c00488113000480b0381c2c40344140401310020403c070681c49880c2c1346219040c40303170000c0558140e840fa103068821041460a00f961500d0a900c5a94082040410304450b40360281e4000d12016130141000e0241491044071100d4009041d0400ca80162012040c0b0164104840d5088094842030034204840c400d98000406c0e9610718450103030b1000b040c5a21081000b22b4840e600000350741c01159487d034511600c60501107a110110641500102d440d09882070b04885540180a0350402d208286090306008142020303021030411401440c50411000c01403100001c0301003e10103164151a4440649140141041b06a1101070382040f9043c4101585900c110086904441c0703282000c80d03d000011881031009080031201074521840401c18038070003040d075040003440d800240d80e02c440401441e0404040805929006401c55000303020a00c00c041c003d0035071001c035100a083c480120300c1221503441244100b608411001d030748062003000ba410644 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722907976 1250 722906726 722906773
    0x30f030408011508030f033106050a2004051320120702010c090b300601020c0111071e0f09090c120213050c070b2d0403090510031d 58
    0x40040c62418418042c0403d135804003800304100d100fa5580061000c11423032200781c5d00060390382c007900ba07101d906050900050100300d0340500c2c031a0420b04103950b444540790451841c40c641c4800142403d04000074000249544007200d103943d43e468907982125900300d55440505407118010710360354018a072044405c00e50107000002507a0600c8081c05e01590480791030016240075803000c6071684904c1d0441c1115140107400c0c1c420700d2444030007500e007200300090f2480c4600b000ba02107541d2600c0401c0111490041120905107581040205000171003e5645003140300c00396000f418082c903140e0307020307107185401303139108400b41d5603109031400030480201710300c01c014840842c8a001c0740c0380f2900490003494070b41804071314250743c54001801c0c0c41810f00540e01c5135604070004503490724010901c5100414030400c002004100d1480150000b401c0110040c403031640340c3d90307a07403125140c0420b0104c1c0c0301c2c0500e2144181750f101c90229214058828a04800010620085c00c2c14a0103038142041d11503403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722909226 1250 722907976 722907989
    0xe1b011112030112060222030204050108070e130c030b07020d080f070e010e040f1e0b09040210081914060405070f0905090a09050303041424060f030f0304080115 71
    0x441203907a07141c81c030142581d044400240c064039a11070140380c4480244208085c04010100842d085e0740e1000d010781985040e0392095138100620398841c07003078039601e404522542d2842d010040004a03201c003c98103006140f0b1088c0e40d000015038403a99040c501110896102c4010fa000c01c07445c80845030b2101450741c1048078801f020316035090104000301014040a0011b040c0a031071b009040c0141c58583c0882c0c141b103030340c0b01c04101d19181c0080384240b0341c08030450740340b42c5801c01101d086186850440300e40180d90043c2491420b2000003026038141070003e11003158001400c13032200c03110780c041c0140b00b0700e00c8080c8000d40c201d1900c0030420084440140200041003111010300ca661500415400e043e22000c903000c0d503c07035440d2403e003c003800c0700703182c01400790201000b48000c01450b0805920303041c40307101c00c0d102c0400520070080fa0b20b803100300c00b070403090003c400404c115080c00d98a10250b88405015a01c3c020b800e03081107460f651140d40280700c16996006401100741c0c6400441010f03208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722910476 1250 722909226 722909233
    0x3030f07091e05300a03030e12030f0a0b040507030e0d0801060807032004080f121603081905160e0303040b04050f060c0f031201080a0c090f0e1b0111 66
    0xe2040d24103075111038a000345030040031160b04441100301003903140c80c41003903410030030b000c00d0780380e04c01080e2120007086085001c82d00b00700e55030725200300201d034000294294000c114290350b01d0f0b0880e0101c1a0014008040456a45a0362512612540100c9100c0d00d8240c074003007204100c3ca460246440048540b51003000741c0400140001c0d90f00c81030098102d9401d150100e856410290303178403141985510700d4244004006000608000040b408001324022007003540c0010003401c0f6200324a11800c03056050b080080003413000001e000e10340d03060b00040112540c8000a4094000e9800c444090b0f441c0480181070304803698140f40e101c05000d00040e07042d4003441c10315160036a82400c6010718050315201e02e418a0000c50161a8032040d1250300740e0315401c030354040802d02410f03510303540248040d042074041e480c0041100e220000d01d00707840e41e502044e00404245085e16640041000c403210784c01d500d0711192612000c010070825046581044004041c480c18141c0015005101c0308000405580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722911726 1250 722910476 722910509
    0x200a05040b09040813080f0a0b090d09030b0408071a1605160b060f090c1914220909051e0d08191d0313060e06090d1403030f0709 57
    0x1220070305036030f40059210614075200c402104241a078002c4941110b400c1e807080e40d0300d90100100010b00d0031000ca0007540904e0180c1c031001c28007038030354160702c01003004030700c8241081001680350041c0d42d80c028080d4510b6820b00c0310507951050402e00c80b200386981c088409041c440045540180f0201c42e60300c5003000d41c0381c801220319001d81f90640c10806031003845c510002075210b0700c40e41c0d4001600c81000704100514a482485030006800c03000584455201c2c01030401c54090240c054001680d141340c113620f080055401100e030b02c1e151450f400072802108071000007008003c6000c1c0e14013240c070441c05000d000d0b420181c1c5c13900c0410140705020f5070b41e00c2020750440d0b1940244107641c204400344841501c0d56105105800a8040d60700d5032072601d640318560040d001c2c8044003401c1c0080c0400c01c52203c4a40d1141d080700c540c006c0b095659481041080349400d81e15001004001492003885460b00c52404149441d007142c200f180c0440011a1a0b4200880990b11004003006841250102007084 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722912976 1250 722911726 722911729
    0x1101050a0b1e06041703120601080c0403080901021c261614130906030311010e1209010201060e0406051b070812090c0a0b190809060a0b0d200a05040b 66
    0x482c400c03442c25a403108030315521095885180840d0081c0c102c0c0300f590b08440f51085042c603969401004154500401107020404540c40796090074080c102581c10785003010f081d0f4541100c6070317100c1305d040d03415031080400650083e41005014410610301d030711401540c90b07840740c0305d655818030a401c5200300020b140400040c86018100880f01107903d261030400c61031441d4481e2014819848210a050754010002405100035080041a60720950b285510007042c0603d150990310720800c0700b0642d40044c2c07416040c002a60010b07141c1400e0520012031001d50703c181032080b000e030680e0700362100d945a03420002c003521003000900e500a00310080a02e09011611080720354018420395040c40d1240c0c0c0081841402c041100152a410060003044803c1c1c0d44c03c5000003d5200c50a0301d4080d5050401c1020001e0091403224480c0e60a00050003403650f4501d4903c0003406041071041c1d11400710b090b100040341c0b040321200807200d084482c03401c03810909420014064072550105210b5410881c251246 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722914226 1250 722912976 722912989
    0x5010306031203020309073f02010c0b091608060f3111060d090201020d02070501230c07080a031806021509010618090209010501020703020d12120c1101050a0b 70
    0x442c14903d00103131203440b03c0605034241a0151312040300840700111240080c020b60403212a0b20700e80005100e0844400c40040744021000c002c080e0108502040c201d01080361510065840340003d0142ea0111701c2c640c108404484113078118104a510440030800705031a5825500d402207404541450100d41e42c0c2501c00755041489503002420344440075040400944407120403416400816903519074072007902c4440104060b4130168014400d400380602024004a100403d903401a9244c0318454550301d40c0c04210f40320001f091590070310030800301c11048010f01c04200600b80b803034050300041c45541001025200600710510450320400d0003042410340000c1c01c6007542a15682c03040719a5204140e40d40185000c1e4071a58040c040000b5443d0110141d601004440380300b220310f41c0b2180d80b29001241e4031090341c0802034001038006807140209580d010310904080702880c0881555004032600400e842100f41400007050a04044c0c141c031039400e02420390300c501440810400c0c000b6110019030b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722915476 1250 722914226 722914253
    0x6070813080f09040608060f1f1205160f031704150305060f09070f080903092805180103290a0f020c0a08130e06090601050c19050709060501030603 65
    0x140000003992180912080040d00d01c4081d00810170404944c0d100c5401c0d8036400100c810b0303806105900d000440c44c0d103090001e413911404c4d2140c80498281003940000001d0000301051b505846a08802c484040903490312001508580581c15502459450b049060058020182d40c004e02e0501046c06541c1c02e2854403170745220240390204654840300040b595030032501c4e07822504025040108055541c01c150300d400540301035681e102660342d4103084039441380a18102103500480d040c161a4a0900c00c8540c0c14a103905583c0408000344c0d604001804c00d59000d00d00140c0c0041d1400410502c6143d071a20741c00140d040d0000314031440340c0c1c0b1044016081c0209001c00d80d6035601d011081c2002150b0588003041c0714030f01150200031617410144c0c070b160401d8030070050412241d41c01095040c0d035902c0d03079405000060714035020707030322840015030780c80d0043c0011341c0d100e21900c6041418000001d81c141c1e0307440d01400103458a10308010809043e41d480390000b07810f250400c401040003070200c03520200d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722916726 1250 722915476 722915483
    0xf09030917031912060905091009081206060c0307060603060c031401050111030d0501170c01020f060c07170a0c0606150512041106030a022502010c020d020406150c0506070813 77
    0x15440e0f10f1800e8031148008900141a20315000c0003103008842980310303502136010282142d0141c043c1440203020303248210380040204006000b41c0404150750000e55401002c003e080030304001e0801001403640d0002d038030554143d07460b074808005001c46031250a0700000320745428092080740d525410011001813050b40e04000f1500103641021405200343d44840311507035810300803543c1d14411001d100c100c078010000f09010301512609990300016480d101c408000d00130344103650740c03111048250b03040181c003602d42d07401039054500c600450b00010203c00906446521408805040c007400300c966a4101035251080d501c13003c10155080025114964400c03502c000e07003652246030034140003c50b01c20701341e04900040140b11802c4447e40103440040010600013260115482ca10152401c0144000e804520010b00d02070141c00e11078203005c0a40e00241c000305840350380d2803504070320f1480d0104100000b2141c550781c004011086c00700b680c02903150f10385608203062880a00c801200487c2d0000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722917976 1250 722916726 722916757
    0xb06010c1221020403030921170f120106020d17070c0209151012050a0203010f030204020d090b331f0201060b0a090602010506040911010e0f040f0903091703 69
    0x80040782d41d651805051240600d03019501d85507a07140c042c199588501030454503e04440b18508400307050070b030031078000390040c0e0181c0c5001c2e000d00803130105a1050a518000314420050f0030320b02c1880c140614001c1070700e5801004000342c0c903c0000d000784401c4100b0f08401060701c0a0280700c43e8001d180c1d003010340c4c0495480385143c480c91202044040300c0c1806d1904000d03451480307411070fa00724030325016a802e40307031060106544850203042203100900807e040103980a03002c2c80542071960140403450010036001075078404035290070b042c0748000c80c1c14483c8c1280d00d005810720900a40c04084191640100350aa29564880010010b00794808000d02005212486014651003508200010100c2d884d4482e0b80f61180d200081100c091401503a02640c2490701042550809205000009400c800014000c400200046801d0341c6825049580480c030741c1c0c280050b980d42d41c840c185c1c01e01715010b1300140d45501d52602a00c0001d803a4460344040d0241c0303001c80d4144001104456036410080c495 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722919226 1250 722917976 722917997
    0x15130209012102030106080f04031403090312090f0c1f03090510090602093607050409050109020a1107030f0f080f0c1b030a082203050f0a0b06010c12 66
    0x100c030000c0d04800144001658030031500b1400d20380c2d03030066060715080d81c0c070340886a45000120307480300c0040c0c070000c0000d161901113a031480c803240301a5400405d100c0607270b0310b40914901c0300861820103075544030440d0003070310000912000400c080500c0b680e0075901c070121074100c160800d0144260010034003c3c59101c2441c1020040c041c03105050429090000300300054241c10000f0003900020005401a51602c0d00810b98200c4180516500340c0318083c0e02d01e501960f8000d424611102404240500c1424407010468803000d0060a010301440e0200585420001c440180b1503d5502c0522420780c00071081071010580c039585090200b0f81006006403807181c5850000720510660012665404020031a01000c400c003003902074240c0103803014882d03210044010103840d079001b8100240030140400241c3c249401111042c8900c50814401801a966a86490342840101500c9113356044040f0031010409034003025600807800303203064210710002d6503800002010714038000303042c00500c054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722920476 1250 722919226 722919229
    0x4050907080f010606030b041a010c0c05030f0a0c06050901080103120203040b0a05480f0f1005160507152d061505090d030c0f081215130209 62
    0x1440e401400c641040300c28442100c0c0806000744058018040080e04010000d030345132410b405145004603080400b0034101100500644070308440403c1142d5207004060009802d517400d000c2c00e40e9182001000d041e41000c80d1600190303061580c1c20070000d01600717028441c001d1340d0045185040d03076409003121070041c0c0003100607442e501941d803046d070460a0014905a0090b40035028050300c40c0d8020280303100c00003000859941004000301c0449006c442246c8500320540d0b42400700c1241d02c1750f401c1e03035451041d03942c841d418003a5070303900503001c0d40c40069101104c100358801c881c3c1c0440d00c46480d0f0f0070900461402011031090000141034450b0b010700c0380701201d50b19444008060040e0309400900d070407141009401815142138503001a21340711000a910300307000c00d0303541900707050b0f030341c10303142510380010402c0d90798042c50309504001d44003941030001541c844a520a1600925100c0d4690440c82a40000740c100204406c01074490020000119103a1250741320202103c030001680b0307594581e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722921726 1250 722920476 722920483
    0xc01110f0712150615031a1c12080106120c021c090503100207080304021903060513020f0f011e140d240e0127021305120714040509 58
    0x2111465000d4a2000144024261101c000d080c3c41107981500141218802c40e0403a401407154022900c08100403540c3c10b403007948250704c42c1034014401070102000304046004103007491034513480846518003800900407550790000003d1f0140c503100322903605201b802050810000309074449103890300e6030749003260f0007405840903540c006004107002d40d401d00002805640148112806401610504051070ba92402229025a0000c28141c40c40c0c40e680d080c001605440480915906000c0c0804000902d242c09a5801501101e040b00b0410f842401000281810300d02018450120180303503411a9821049201882c848111145c041c1c4240001c10b6400880c8803540500c41c0a0000d05d043c0802c00c15401040b07100e80382240303a07101442c804000e100c080c9003070199008000c038600040205000480c500c650f00c40420003402d241041c4c0c0c890f00740c1070381c20200700f602d401207203118103000d1400c05010004590084078001c00e00e092038014100c01c0405540780d180d00494640340000c11021080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722922976 1250 722921726 722921743
    0xb0a0b03040510110c1f06140f15090a030602040e010608044107180507120906020906040803070312020f480606060a0801090b0a0906171e0c0111 64
    0x17015a10510120a94005800c2d04482e00e0054240303403040100303481840c079485040c41c190191a5200701c20003201001001d000e06248019820b20400c6441c405481e54503030b48005601c100d4015803100c2c10b28640109029050300041c003082040700400001c60702140d40000054040c85540d100404058013110b500c441e1150750480c049040030132003c40c407000155040841d01c44100910500079803c03c1070050300c40035501c1000141c0c001c03101c001e81158592007000c2803442060014076000026003c24a2600031398000740b219000440c0c204141500545e54800c1c11403125011850036075225100300490050741c400e45036204c400740030014410000d801c2d502d1050b100c00e12100e4950440c100325034002c0064850041c081c040e03000801c3d818100035096440082ca80d4079032104980c01c00c03201d04020b01d500d54009520407a80303080044e071030300036104802c040c01d05a00454001003401344154a40580c804180d1029105804c1c126040080440d107680341c86001d00e000c50700352032000d85030b84c43d00101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722924226 1250 722922976 722922997
    0x312050a0b0301050c1315080601050a02160f03350c010b04050c0a0207060e090703050613110a1803050a080f0f0c0d08091f0b0301060b07060b0a0b0304051011 70
    0x304400e01003174141c684007600000b201c007a01141c480d03484412080114484000d80f5000c950703004d002c038030550b010341c020f400d40078164030458003510b0720015040c060214903400369080040b860001c0c402c1c0410f40740c440c11041e440c1e01d110804141c0c4564400000b41c01980c020906240100745101408001e40000c20604001002031000e401c119440b544540c0c400442040548a8001c00041441c09003100c803120f9400204812a40d0350703017540c140d0152a0050101d0350100081100c294485600d00c90681c0c81040611b032580c4411001e10b0141281c2c41d0342d69040806840c2034010400a540010224151070f400302d0b04603152401c40703610200501075030b101002c4107030010401895004001680300031550351603440080a49980040c0c5480b001441c150101d44c0100e10070407558000c542c2c01c10310409230054000071301c090390344030543e015800c0344008440e080e4a48030030880518006000f280540116041d071861420300f0383d1003542e20702440f070302166115100d5200d1024642008250390b40d4011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722925476 1250 722924226 722924231
    0x2007050a1719020f0a020130150f0e0601032304060504030206010602070f0b070c0b03090307111f1110090303060e07020d05180d0b0c0c010e011a0f0a031a1803070312050a0b0301 78
    0x400b06050b08c040c000800e044015604003510000c1e90810419154080b01c1c084891a94952100c0004501911075400641400d0354aa120b6000000320300b500c02d4400c5015a00010301404c00f0b1038002e08000061703000c81e0440d807082c0420312410340d0721807150089030001d0240503501c0314a4a0300700c0300303844d140d40003441e505008003c00c80100c8010000b0501584075503803081d040b075000b004000020401101030031511511080c040c000c01d0107141c40d0305201c0707203e0007203444c2010802d031128140c40301041c01300d000075102c40301000941c40d4050340b42d8003d80c60740054a09a044848010464010045846102064001e0075101502c6a08110402d00d8101b20071270501e10b8283c8016080d9030100c146206158a02071840107111810704c40e071164480d04c42903288104080404010740303881c40d8001d40c0e034064401c0200100085036060001c2d01106903003041d22240c43c01100420880d0a196002d81c642e401c00c22180c07000a510034109500c0c441050b40c001116105c07110144020b1501ea5180c1e41c00d5031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722926726 1250 722925476 722925557
    0xd06050a150f0302030415050a0902090c040603110c1f06080712020f0a2103031401140909061509040305070609030503192007050a1719020f0a0201 65
    0x61416100400d4200a854951050352880003c41c100d120440700a0503580c102d01c240002202940c00542c2c00c002c1a40000c04c2800d00c54001a030f42401c01d0f1800000640c0000e0100482c0e605130085010100c4001e0409042000c86206962107110b218900c00c907441520362031252004503540604080e0000d00100d50850303880d203000401e07809503034100341e100e251200050182c900d0a0642e4505a56900302c01030001e001000308200700c0702175960201c0503d601c0b60310407500c0b0414142d0550080028066224242c450f5a0501000e0f0f40041c200342240d4000004101e50448079665210103100d0680d0300d607a4964450504450311302509000509050610049070240759200c0003841c040ca4480d01000c1c4401c094008400c2107404040c6980990900c40f0360704080622508013511400e800b0b0301c1035032190502665203042c1c171032440098183c40da0021401d07000c44901d11224122201507400108081d154207a641641d0f00f8215a00034104403c02c00190860507002c1b000004c00301c01111183c2440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722927976 1250 722926726 722926739
    0x5060118060c030e0f0a09152310080c03040209060d1b0f06022e0219020d030c030501050306060f010908100e0d0201021c050c070b010b0d05010801060602120d06050a 73
    0xb400d01094000a80c100c520210500d86030b400303402c9803040100b070805800d1611800d940602036888500c10b42e800b500301c0025040d40107818074042c030700400f0860401440340c0c108000040710a5403241301007041c030108000003651811f04481e0400d404842080d03490781c400700040c51004a0100040014080c503001c0c20716590070260700019202906048100c4540303601c1c080365545a00b9002d1240d522400d0000c418030081e180381e172034859400e00701c058a0032000640500d041d102d142c40c0b050040c0e00124a00d0071441d0307d48100100c2c3c040b1072505000c00e502d07040019030f0314400940080e108407044100400c2d13583c044e1510304000c02070201981d038200194600003000f00441d940c000002d005d18402c800b81c0f07510604c22101481448100940c0306e00c01d46050900034a40103189004c452030070048040400d260b038030418028030b800e40803d0b655003107046039031341a103c1c1a4000805a030406109004c407640118100d5035980c0c43d40121a2524107803200d06010304015480340380c01001801c0c010a18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722929226 1250 722927976 722927987
    0x70212010902031b03100b040f020c030a0210090f110316060903030216030c060c0609051f0f0506060405040c05040909050705090906010608070e0301150e1b0f0d0506011806 76
    0x2d0007141950a080c82c80011134911040c8188001d6050300301d22168103d1141650080ca200307100544000340010000c1060b0089034003442003141a0351002c50380460b004d17810000300c60880320354042840311810542e81c1512485150310010a55981d42c1c1c240d0003552030402110030b401540d03031104520b0942c0e80c400a4290300c05030009500500071000c10398290280c000384242102d07405004141014a0103404640b07003121080c04841e026190f00401001c10030070807114071910202c82c0c2810a0450070050002110b0040c2d13465410a0f09201c100442c6030785003c1500d044072070a03500450409541202120948240c3c0c000d5072270907241c103985205101d000554042914800d4a06402d1525821031141e5180824441c01d00020030140009280512400c20208500303405000810402e024010103840c0342c1c0745421241c07500102d4001c00224030824004402e03011514000f1a140a6101e090100184140c04c1410351194888003c141e00d039118684600682c0d84200305da142241d140c9200601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722930476 1250 722929226 722929241
    0x603111e16112404090e03040e09010c0e1206071d03150702010b0913170f12041112071202120706020c01020606041103061311211b0f03090307021201 66
    0x1802c044180c1811100d0b1002c00d52118040600d0640d0400b0305e4007803050060800d00340c1c5c0c2400c0303001c1407100150385050040414000c1e0143c0c0c0c000316210b07140c00b800404100c52440024802c400480c0100c0c8007000100d8015002040c604d0700c101c1d178128070044080c900142400c0c0503010f100303000e81d05550007003c0c000203000d0003e580c02031068503080c0c0700300541a84c0c16140400620104a84200050302c0d48124150070080150310750b080c0105096401040d800124800c40d041c9028001c120030000301164510007403104403414500c100d07d0782d0343c4c6990b9441c9805141c9100e01d0000006045d952940aa090f200c0c000b130080350306454540c00000c1d2110b05281d01c00380944160000708030303146414014020f514190f40001410365650000f04685c000140c070f206441c260b0303501c0d205500d40719aa001070050804154081c1200580e0011000408800a000e01803025040c2c2c0900e00c0440264103c2c0c00c02000c2da0511602c988485403111308501c1828002584641c1155441e252004103410002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722931726 1250 722930476 722930479
    0xb030a030809010f0608071203031d0c190b0f07050a051c120b181e0c04030308011a03010324140114040b100f230705070603111e1611 59
    0x101360a058144801130360f1a80c000c4102c10740085034240204501d110707074110800c0c001d207004510f004885e00e075201e0700300850b2849030640d0014450707501a07043c4114524128040080442d00251511246100e64050008108080d507000203049040c0601040354013030741c0d40c1010546060003150700080a4403603c0d0240280884d030700512480d0402071034410b0001480d00900003554071101d0102002d41e51000911007114402d51589122110300002045441000403c14460350380d4198103001c1d03e41d200580c007400d084a4440960f010f00d412000540e4110381d80b00403980180104450500341205460081429091900e03031191291890020014108c8000d070006420750415142440305452581c4c0360769800c01030041c0c41c6450780e40700f04224460820b040c80c003d120307414100c0d01103000318820303901020071820101c2c91900748107050001c0310003010103080c104942d041102020110740a40d0f24154400301c01c85490724a1008800220f44200d1001c1c000d40800351203a00d4100c800c2202c1c0e210a5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722932976 1250 722931726 722931731
    0x60102071508040314070b010603020c190f08030603120d02030a0b030a0c0506030a060306090501230f0f0c0f16061503020f190806070f140a050307120b030a03080901 73
    0x1100101c040340240400c050340d803114480c2d621910181e5650300041030742c164840d81000542c01080381803041da806030141d664003590b41d00017002c1061400b2510100800c1040789099910002036006d0003a40c180d940c04200b0544030391b10704000905011080310001d9031142c0010f0038848a0803d40d0081d071290020341d0741000f4400c0300500345542c1e0140c00c1402812000414821b000d5841c046d0301543c0e0040c035080c40400c4032510303607485905564041c10200e034943c0d110640103035540340d8010990300c08540c490b0156a0391415140d0648a1400500116214409032001c0303142070a0714011180f0705020b002c4880c0d5142802c08074200c0d10080c82c002034820525001c0e04201c200c0142c072650b07040340d4006100000c1003103805e04203d10528100b550f8040d2048084c40094844020300074980304200301d4651100c0800d403482d025004040b103004031400010304102401050703402070141d80d00029649404070801c040300c0c400e00000c2040c121000e07450701c0b46030707868403c06900208092040c407220009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722934226 1250 722932976 722932979
    0x30b0604031202251e141e100e0a1512050402010314040317160e01030b1201060b1903110a08070e060f1e07020102070315021e030405150c03010510180e06010207 71
    0x141a00f01006014545424451501b070001519000008411031404021404040c0b030b581c1c0001540c0c1540c010f00803020544036213003d00603280c640200c81c01010001d5640425182d014030081c080701c0c90300111a0003a6481c8003040079a4801d0303000000c000b00302070000c00941031508014060001c1301c05040c000d414520002038402d010106a40e20002d1542c0325103440012000040d4041c280d072030310442d0000540c4007602d100c9942405000000d0802c2614144e44a00c00c06100130500b860340700c40300515061007030592001e04600c041b119450034516080c0c8103900c40000c100d808a88100aa0740c0c0032002040d14001c00c80d804000700702e29802d0300c030080c059504620340030a990041040180c0942c01c214402c10104440d408180a549207a140c01440c000303c08a0341c191200101400e000903020100800040003010401104901800c81d5400d0407031420b9160054107110500919000300d007500480d40380503000300c1c0b003501a1092410306000440c0c82c2c400640410008442450062080080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722935476 1250 722934226 722934269
    0x17010c0c03021c111203180105060d020621010b030603011409071203120204030507060905032d1203090c04050106180b0912010f0f0c030b060403120225 67
    0x280c018085a0580140180e0f4607960f06a0240b003043c1000481030100c074800c103250114060040b000c084802010844d1a400d055520184c000c2c103e5110314416854181444501d580c2e19a14072030581d4101e80c00380c0d95a00d600a5044070340b031f140628003141001500007046a44641024601c1507506800800000c131402c0342c480d907014402d9442c41d20301e410814060000c10102c91a1610041c002d003046055a14003c014000720f03440340e03106a880d40c2010005000f2107500611540060800701c000307110b15010220750303403c841010604506000000c0e0440001136006003d0121100c0c4824403840c2c89140150b039054480700c100410f58401ca2621002244544c00b4840300602c18a00115407241c05091403089012a0b01000c003007980061600c40084034080e09009850700010708144c0440e40401c4030700d081050f620768031691070915040800e07019040c0c44040640301203a8108045004101c005441239041105199803c1d02d140c10344126030005010060140049031a0380340e000c401c840b161036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722936726 1250 722935476 722935487
    0x308091203010e060a1e0905010f0b09041a1009031703010810020702030c102d21020d14070f0e0d021002070503063607030f03050f0417010c 62
    0xc0d00d199008244014040040007402d1150701c544040d102c81441d5454501e00c088501c40c0965510100300082400c0c040c00001d40641c078010702450404070499418085211101d01600c410207004540e41c5c241d039442ea01110032440c54081c0080c10310880c6a42c1c40c1c0b07005000781080e00080c0c40b4035105107110703805140c400080342e040f00d03000ca010740400700c5a0400d81e0040c0d4003000d000c1e07a0601c200c05401c40d20380e581414440c4d130071001d0307107030215814030700782c10f0001202c4106040200c1c5000d03140c4205203240c2001741070b4500c44101c3d0707643c00b01032440c98940d4001d00542a20342d0a01c0d20f010141038420f00c54131308150003016940c94200903510f80c220221101d407104210f064100b0700e41240c06006040221074450b00320600e0054642450711b440101c0e2500b201264104001c466403003024040d1f40041201e000404203140001409944100e013081d0380c0c00181c0310042135001d500902c03905041c840c80075551030003034011004ea690355480721004035001051480310a03d501c2d0500b203024260141c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722937976 1250 722936726 722936743
    0x380303070309180905010f050708130b1314010c030b010801080c010504090506033408060405120a090b12160503060f090702100f0522110f010c06021204030809 70
    0x580c1c4034100a41802d281c4141580c460f4541c00b1060345a80c1c4c042c0001e0402e0149100d0307255560800034442c81c140000612080e0060007030103545078240c0b10702010071100f901c51a409075490000107507030115460710b910b00b40c1325022403092a5281641c407040e01070b4541c00c1088180f03026601d151300350f600d50f4104c2c2d4a03120410a81404aa07040200300040d0406801c01a0306c000000c0c16100030515800b001d54000c24014180d20b424003c101214800100250015010f420000c0c02481140742c180e58982d03466506520684503000049290b0304214824040c502c050f010070560561945c21034030300c40082003001e03210851584248024214075a100e401984d07c07854005015060b03070140c610078001c9100b8080c150b5411801400c1d59032524404034014005450b000d0380300024649010106960741c0c1c603c2d2084050072840340d6050901240c007140301941802c0c021180ca49103100001c005848842007140020010b03800031841c184211a070f40d0401d8880d42c001e4494903019603038110f6664031917215 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722939226 1250 722937976 722937983
    0x901060f21020d09150e070503151003170c15040807060f06120b0105030c060307090e07171501020609010c020a0f020a1d18031201150338030307 64
    0x56181d58400c000040365000d91802903210051414050303a8214040d1114924107544143c020b10705d105044525104681c18603082c0c02c044e002c2e1034203003000240c850010141c140e24200b05d2102042070f0200a681c114003c50384500c4200c1004030a40c041d822a410001c41081540103500005400b00a001a100e108642c0102c0880c03030300d2503d80d02d0500070820300710084692595484046510341d070314142540c1d564054918a4582d6150001701854003040c200180d000301403d03c01c2c0110701d80c01941c85410b88141e8000e12120742d441da5421281c3c0e814118400352503040071400e000d20080c80100d1004c0d020b1081e42910019501e94001c03500361940c15054900591040d100718011504203207040120600c01440740c081c3c9940d6014402400c030103074002481045040c3d091040c1c16250800680785604900b028509002d1400505110304005100d01a05140c480c480782403d10310a41c0047d008442c45004c04605141032584400000412900f48201c400708202d000380f24a00041a56038491b80b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722940476 1250 722939226 722939237
    0x4050a14070609150e03030a230a1704051002070c03110901030507150915022401080a0f2a06090603020c0c060906070506010b12180604170702030f0c0901060f 70
    0x151049200061300302c01c900008000c1e01a00d1842181e505200803d5580304558900c80904991099400441501058141649010880e0221582c1c200f203180d4841e030900c2c0d26540d5940c1c0e0307500b003032418101100141d81e0060b10005070101088421a1004146e03401210780700c422000c4403052001c00003081c000a00641d0000c282044003454101c60301041007030902e4081c100710350b501090686032104030310040143e00f0005646c80c1da80345105d916142d1850340003d00441d940340c104895101c0255103070240841c0d03000e11205081c00f03809007012100d40c1404400d8188031444500c50b244800c101d00407940095075291000804910034000c0da00103942c80d501401c00d04102c0010050f06600011240e504140300380300c2040441c0041c819940240071f40c01209556400d9110707580d450340f200403c5104502a806540a4019000034545a0250303011040c0c2c400841c8140c1500b8680c060042e00a5151180c070002c80000d12010030600c0e1307029001d0301c1500950f600d904045e40c400041a501d071000a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722941726 1250 722940476 722940479
    0x903060c090d080c0a12050a1d010516051006050f3303070203042610050c0c07090605090603010b1f030207062d06080a02150d0504050a14070609 64
    0x603020080c14211001844104103940d55560f20400d40c110950780f95854010a401c20b05110400a041911030310502e49079160071043c0501600854599885c0c4540d015248160a51a406001244c1070544152500d5035034a260b031a00c80e64804c4c9000c03242600c1414040c00082c58201200b50a091000040041030702c011448040c090340045900b5074003029000049800c03401040700d006500072000f03a40038554560030581407540a0381844d00c492a01e800083c45640c5004020641e107078a80d100a1020680f500d60604980c1c0c60301030309244a142d030185030b07000148040f0307583c4610201d80041c2c03003403207803a0b83e02c2c2c00f0182201c9154540315001031780602d5450071088001e140011034856400c0050a000198503080221403511201e404218a140c01014421160307100b48040410a01424802c035402d0004858503030008510003400307400c0b4440d80c003c00071310446c1034414507000c0e408200254035003800c02c03540c0c45440000503500c83c82c0e42000103906001c04501c1d071003965001d44940010700d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722942976 1250 722941726 722941741
    0x30412022e02090a0302150310140d03030c0905030d0504180908070803040f0c090e10090c0b07060603140c2404060507030e0a0303180b190309170f071205090306 71
    0x358000900b684c0c1c400402180800103981d0111104d40e114041d450340f646a1900f50b03003034091600c054004910500d0034402c0c0c1b110702e0ba110200e030103156a00d4600480c450f6101c400903240040d480d003140e035140c00f0751013904200c694020301400403550203d00b00d0045a61012010301200e41184004e4002c0200b04044008203c20900840c0c015100320142d4001c0a2039803140f02d0188c0007074014452a0782c5070901038544800070804c82e010f070511010f0812440315541c2d1000101421441030310545c1031b0200e541018010150f00080003550800f0900c40740302403c6520984540103e11024410318241c400103c040a084104e0801c2809007414240380c541841001c2c0c40035044210224108012400d441980e9192160005d0045100f0b8884003800c0001450340c180d026203d400c140445a0300340000c03900c81607120404400c0c1d1340f840c10001100482828042c0e005000c03c1c900c92084100050032a809505d40002010700c1c600401c1d0306880f0030b000580485162245035000781e07250740683d0216504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722944226 1250 722942976 722942981
    0x105090a0302060319050906010312021f110f07060e071d13060b030d03050a111e0f041e0503150105010206041713030305190f02060103081e030412022e 67
    0x800380d0600c0c01d9010311005c68038042519400c641c11075094200304010400c02000d01025481c90070640040c1580c00d0303054103a00c4c58080750780380004100da10b41d036521585c80d1804085824a0f1043c0702165030354035650034240007500302058103883c40c0c0f26004001030b40503166125003540b501d0b15151036183e5190300120b00d1007510006419201c1c0c03a5522021040c540d410403500300344a12580307010602c0d245c00320f404012110340054040d84100b0401290144016101005110700c40141c110345d112103040200d42c0450003250070100c602e40050003991010400707141e40100301c4202304d04513180c6250008961360400c1080c40f030750303015a00041c0400d00185e810015001e510b541a5011400c1443d0013400c2c07030b5090196807060b00030030300010790703800d48442c0d4452200c1d204001d81050580441c004200940e0744030148000f8140e042c0102c1c469003c2106441009031610301d5074585600c0b41400d0402903038040700c136038601000d4407031282d130300c3c14020042c00d44c040c5007551103070718807840c80c07454400001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722945476 1250 722944226 722944231
    0xc03120c09062b060305100c030b0f010c1103151503071d040609200117040206070803090705090c0a11070807060e0103020403051b0a0905090a030f0e0d200105090a03020603 76
    0x19042e0f00d010b5074080040c0c10302c9544021070150f0f004006040c514403101e41100c0d040400c1c00205418000812840d84402c001098040c01c20b28010040382902d08005181c070800361020f6030326000302c1c20265800401c070500745001e090415466000c0581c0101010b50322041c502c10115107459443c0340c0c4a00d003602e1202030b54098000c14000c1074001481d80c1d074000000106030000c2e8500048200300c800f03541e000102c0c0d0314801c01e030401408942041c0c3c0004000303000e1700000820320300300040060340d0700d54240400c20040174094805201e45c24001c5100c1c1d810f80242c0e40c1d001c00200f1207111000300010000e00c22007100c556030045c08419041139400c46100200c002124103040c0c0801000001580c00c01ca035146410050b9061150305980c4003c00545040d00d50200c2002800e1005000b4121004603142b419203516007032a00302c0190428098034107229000b081640300c9040c41460046c80782441d00220622000400485001e00d0b50005503000c1c0a4413407100e41150f40c0b602c1c02d04c0181000c03c011034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722946726 1250 722945476 722945527
    0x8010c020a02221d0f0a3c03050301050405070c1101080a0e0609010203100f060509010507061e051006090e0402040903031b02070302010f0306050f0d08090301020c03120c0906 77
    0xa04680ca44000c2c000d80b842c290b20800c003045081e8a105141c4c1c81403002007000103070b000240c080c00e2000e07202c200c0020070424100e480b02c0c0840d007010f41014a12180344800011006c0164000641c5042c06085500248078a60003242400005000903128591034420a81d004000348942140c403001101c001c80c00600401c6503580d6900c042e80c4c5800100b010302c3c41f440d0100000b591381d03e0030303401e04901e04490740c0c003140003070480c02403e10405402ca803c2d51301131203003803905903100d0303483d4100b120241440c10040c0045060524001d408000a0382040344504100c54200284076903562084807007010a05c104c8542c030302a800418014074040c0c1000c00840c0c00380c900403030a200449881401504080380c00300269104080030000c658001041390b10b1b40d5810b00701001000c1c9405d0210b408040940003051040502014040400020a0550b8a40030024000315114620701c907a01ea038076400002aaa00003215100140306800c00400b260240200584402e003402c0252400c0802240c03000c0442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722947976 1250 722946726 722946769
    0xb0c0a0f02280311040516030b0a090507031a06030601350117070b1e0a0c060c1214040515132f040501031707110d0f050708010c020a02 60
    0x941101104119402ca2450700c018220041e1441c0751100b4640d2280420074003aa0801d82000000410503125610751702181c200070071556500000210032580a800506026240105000c0102d0741544498028510020303008800d688110802955001c21501c187c0051312006201942d521070000a42100c164581d0304010140c4040d03006081e640309070082240740b000100d580404540c10013402004090440f000d40c80d0070040800b8103002e4242c412800080070000800d810424412007a11b95200e4000303508000552401100418041c0401900f0403068280390b400c0180c00b4225404c0c42c01541d0142c0200071014a282e414084440020400c0b038113032120501c0d060101d001c00301141c01020200c0c070030f005840c80c1d449821a80b00c2c0c1000301140154036190050000071040c007401c0c1c850303804944105031100483c0c6000d80030440001c1d801d0307400c2601c1003000c8080008003411896003920420130303038040c186c031595454200c075510380203440164840b05241015040640d0620f11000074075608 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722949226 1250 722947976 722947999
    0x109020d0e061602150103050a030c02060c0610140411070f050a0c1203030507111e0102090d0c03020a06051c022505151602030319090f0303050906010b0c0a0f02 71
    0x14241041401c03075007000f0034100d940d196041c1682c144140203014505a0b0141c101d0350564641d00d44d291580c40e4020144002606285d00b95901d040a480c05215001c00710354a41c075228a81c540c000134a8400d6520034060034005010b00d1034030380141959405035001c06410102c1c01d4071407040d0004905003d44a070b002c0ca0304610007050750044c119020b0042019143c40502c001d1800404885008005204120400000303480405010542c0400480f509042510342401d20005078028400c0708034469210060280c031104114888800c482181c2c0202e40f03c0301e08540c3c8090580b0103200390070140b2100c40401c0741c0c1c3c0c04045101c2d4054050f4181c15411883c001001401c00314408103503000a903a29800525121f00b01c1c07541c158513540c80400c03485500440308003164065580e01000c1c007100d0090046402c224090001540501101a0003000215040e4010304000e030080c00e0598103c03810380200340020460412613000c0b102424070020007060985003d0712036202c00c441c1c119007240e208aa1505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722950476 1250 722949226 722949251
    0x20613031d0d1421040e16260906011403030406030207030c0c060302120c1e03062808060c030103020105091c150209090f0603031e070f030e01110c090109020d 70
    0x22801c10f0110320b50080c483e144010389094440704041d6814035400c007040105220303180b200e0410b560898082080d50521040e9001c06580d501c1c284a941254240d840f8581c0002d5031042501d24010110501030301c80c0f603602c444c46190000e40c841092500b641c000c000400200c1d00c03c0e4001c2071110700a18040c861102141d41c1c180010711258080c00020360049038a85801d070640400c0e60704001140021454060b041070010102009800da86410b42d1002c000078039503031502c0d140003128000c07440d2a90140303c0740202402a04c5210b005050031481484c00040003d00306008803130680703405031100307070074000144104100c6055403150001552240c6021000060b10880c800c00904105400035031981c0701c402c14807014060080404a26202820078820b1585001c1304856540080800c000da59441500c09000c1d01d220320b03000101100501d01421080c5940000d5107801c0000907660002010038200100740d44a05051070380703512031401e800410034a05070b540100110030015001180340c4620340d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722951726 1250 722950476 722950493
    0x114071101090b1305010c0c02090a0b030a0c1523070602071b060e013203090f10061a030709060f0207180606030b090f0a0b010e040906090201020613031d0d 69
    0x44944d0036400c40280301ca400c1000c207005003400c1c00352038070303001c1040716454001a0b0010b03805810a86103d0341c841c002d1029031030500103130101a40103422100f040f5030359104850000c00c800c51103000500c0010098241c0311028601920311010502c0c9241012003d88951000358010b02d02201e400c0803101258410580a4216000410240c2c441d60050181c0100240c0340c0c50341c200f00020020702c82142c44524620700480d1725001002440c0e030f0741c0c8a40d0b864410900c7c1541b4010070052900c10554420400034064001d0400d44003174203e05914070290348031410080c001075030000c0210b40a0b65090201d00c1c441e80d040a0103102d10320449041c0e9a0322201c0c074814513001c940e8400000c1d2140e9041c082c4580500404000081c1a00d482000d803402026407025081c000e0005401582c4a4040a400d681314040e4154240030092003041425110300e84000200401d000c00c030301500610002508030b10421500103022909611900c2d0b046030b207030000000300d0b43d000004580c0260001021800300e403c0c0f2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722952976 1250 722951726 722951731
    0x40c030f24092c1212010f0509040305031602070506270108060d08090a05040204120b060f0109030308040c120302030309061f0506030406090b0a09030e030114071101090b 75
    0x4184840c2034001c81e03144426980c42c0d0800b4400a00740b40b01110f16004a680245107070381d88043c03402580c00340c11140ea080c522403203061001070102159032100300800062841c1240d8290015810555982042c44040d000071100900811400c1c80024032041242d0b0702a084200c440c41610340807030721800000c0d03540c4c02211201c81c01510742c2c005002d503000064910000780c103090a00d6440e924100d8000b908000110303000600158021807481130030380f00c0903150009064003c0055480d10348440300c0716003a0390b04400a0315001d2480010a20b582000443c4881c07400041c5c1d1610030b11401d64030151003d46011300100c0b408070410000003400c41111820541d814426806559242083d80303d00e860160050700e83d50400d0031046141d211a5a5110702c8800c03502e050b42e8a68480e07965040c02401010b24600c013030f0041e01c0400c01c102c1c0348005940a110210300c60303100c01840c07869100c00d01d4203c4480380c40d200062851540814011406118840b50310f00e4010004110700040d070b90780b518070f45801d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722954226 1250 722952976 722953001
    0x801140a03021c0506090705030c012105042f0108270a050706090819060b030a050f030904110708032a0c01050f0c07050c0909010b060408030304022706040c030f 71
    0x103c0492080080500c04c05400c01c4181e4000c00c040703410000001e860b0340344880d686050001e25203810814402a1220304661000408100580d147c9410204ca00c5c007490f0541030f004d040c4104061401e1034240c00650511081070303482c18603d907500e40b810000d03030a104d40089102c41210a100c00b611400300f11542400c0e1150014010291804802601c6542c2607001840c007904000712001c0048508010082e107a50050b001103000060030340401e0411100c000c01500c0c41c05002d24031080d1903000402080d5019090b2001c2200d00c0794420202c0351030149420003490604100042160f880b11501c00035403204240040020031b0340480d4105009134441030742c0b010f0310707515941004441b0b0001c01e42c0307650200b000100ba910301038859903070320b441c2c4000645861084c1000b1020650344202580a6075441d603010303110703a0769141c407540b540d507036604202d03003c1340b103040341103000d14600310040c0080d0300200c111070301d100036601c90908100280078a5500002003680c4e5800045003503041c0d00079121803d85 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722955476 1250 722954226 722954269
    0xb010b0c01140c03150a0305150708090d20070b040f0303080106031b140f040807050a0b09010903060b2704051b0a05091008010204080303090f0d0801140a0302 70
    0x502250a40c0d66240516000e02d0074103080040c00010b52040340c0d40b166803542c0c400480d4001c10b0001c0d02000040e00043d2462203400080c40a052640c0c130f10a000383e07401d031524402603031050f07142681d071004500d00c140000d5030300c1c001d030000d4805030a0100c00c014213042502e0003543c43e807030740219542055029201c1e03203000f0b600410a03d82c01c40e5159015142c185024403107100e0020303110b509003a0482c01c4c40d080150302285012011003071000c0c0d96003400c03003403d081d0741c6a9858000a5903801c0c1401000d1048002000c00941920302c1c03004c90350b03c1207041c3c49503c04140307161100d4006005150204d504012040c10480d041c05954490b01802da440c010940b4140c101420f100f0314240ca0343c800003030200f00c1403c00c0c400d1591941c501200701d4504450b80c25496940d800c583c03885011592001903198000b10340070800e07030004400340d841001420f0841e0040260440318a41c1c0790803c9611802040191006010f8000345184103107081801403c1041d13083c1c1c3d29404560641c440c980003020102c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722956726 1250 722955476 722955487
    0xf05070c1203180e0f0609040303061a0c07050a050a0b0c01090219150c020303030604021e0309210403080a0302070501090b271605010f0207150c02041d0a08160b010b 73
    0xf02d8030b909240280c0003100e100c4d20249070403200201d00a6015080301d126042c000e000504051098010402a240c41e031304807035009403100e55814864209e41c0f03208240380070b803510106042c10494501c008640008003520442407408031284001d61001c502e42c5403079500c64030307604c004d600c4041600c84c032109440703c1c1c0c40c00c50380b508145816802090003145d0400113030b8811403015990010030b40c0e402440407180165180000200d0280595014160b03210246000c801c00c8180c0e07102190600008a16968082c0700d410a20404001c0d44070358003000b070488200f0301a5900c81d5109901400f00944600c00000d0004003648410b40031405c02c40e0400ba1981c030009161141c19101c83c00d50007020703466002050100709168007a0f80100c1c0e00e003c0c080c100400c04050058071361080101000030070781106800e9503c892070308011b059a43c5a11f09038051070404845e15000c3c000c48100040e0040080c000e0701d03481001e075071110030641c8403118502c81006071004200124100c000018000c3c00c54620041d80c49 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722957976 1250 722956726 722956757
    0x1908030a090501080412050a0c0b0a0903020d0503040308013c0501030b040b0d0b0601030212090a0b061c0b1b040e0907060309080409110409020a0e1206070f05070c1203 74
    0x120075401943c100079010080c400094401a500e0380300c0e6946041040d120580701004036102d0a80e010040c114074420f800b4054083d880380c1c000c0b0f500500a509440c5104420081900c079840295401000584001c0c010051400150f00c01141c040780c0c00c1d5810901096411000240302e20021180200e05030240100604d44e09486000d5190340291014046000c034100000c010425640000c1e100e80181d8000a64680c401d40c111090781c04468070051044c280740740f0b420750361450400102c503002c14a2002c01c100307180c10380e010601c0c03508000e1240010846590f03040003d03500031f03114043e041c4a00000340110b10b803220241020300032400c449851450b01c510618a800a55444007040c50700c3c20b00740a001c42d20400071101030354880c11700840d1041035004030500a10031540202c80c1c491020514503012540700090041c240300c11a0700d014200041902c6584a40c01901c0340350202e580c1c01804004d09000314041c24546000e0b50850018a80c0d818524001202d41032088000604c900f4034046207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722959226 1250 722957976 722957987
    0xf040606120818030c2215030c1e0e400203060a09120c0507080d1709010509030405040b040e07080d080c0c2a130b1c080909061908030a 60
    0x80d01e012001030200e40d801ca4089403ca4416041c0b10715072540c1c098891801c050035030000441d0426240505105581c0c0e409c01c03a41c92041c5000700882100224a09610714a56220a60590390300700003a03201d94541004404c0075500110b19000a003040c41a0039824038a00140e0061a10702c2003a400380c0010b8600c105400d00b44014800f042da2480c082d03003400421603400c01c0c3c4070083c60314108142c0626060030060720300704665000b03011500c11407004e80f0a03d9030050080300d940707811401d10f48098942c40c00341404e07600d01310764400c00369100f48010017046c41d20343c0148018600141c0005030301503500c0e100034104003194108400c25804803410300b216a52001c0c1240d40500101c5149042142c02e00d1525140e0085000c030055000210340780113440c2c040e654485020002c001e2400181c818007060031400340c054040d23000c1c41440283d04860100400300108654168480001450b1074005010800500d0f800b60980f0381110144e000b458803241d0016021003e03008003c02141c940742141c200411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722960476 1250 722959226 722959267
    0x906050a0602030c1c02070b030a0c1b020906060d021b03220311010c03050f1611060c06061e1c021f02030a03090501020d110c07060305040b0f0406061208 68
    0x2c5520400440b90b00400c0031603145103041030800b1000c40c5a1100600701c3c602100340d04650070360040001801000d541907030180209030950344800011482180c040d1a208900b00c80294100c1c0080c0002001440e00c40001c02104140280041c10700c8070010302c120755840c12071141610341c1c0c00000c051100841001401100401c500e403006903583c03c642d02c0540c018820030880341801f1110240344100350244003030f6603000081180c13070b0b034481140d8610348154000340c086c1a55000c14409502e50b05003003520854820000c0fa0004124940f10003062001c4540018035407400c2d00d101c03d0000c3c0c450359a4007042000c0404124050400002c640100154500f2445050456044000095241c25008815103000d040981400900c007500b904009001e0710030001070130a80c41c40c09811070340c4201360030068045c0440410071580d19a448800c190700b110f5081e500600b01d02403000c00506007101e00048264441d115900c0400c0b421750354404c46411500100e011107003000c002c51140b1034007402c040b0280 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722961726 1250 722960476 722960489
    0x606090d11130908212205011b021605030105071d030316050a0b0606130504020723033006060d0608030a081602010908031305120c03040e0708040309050d030e04060906050a 76
    0xc0b481c240041c5140160031000b241c02001b04100d41e482c01440820360142c1c0f1040e0016411040010792250000d44900c580818041c08540250b0089040e00341441924818490342d1200c0207449103181e5260083c556000c2c3c03080d0f041c84100101c1304889000b5100000540c0700d0300040c82c0d070f04140e14001100283c020155401800b00f07100110304240600049002c54a0607200142d442c540c5083c900048407000d50b01500d100e402e01501201c4070342c0040104503205001e024018903244040d054180c0020006c210b4103115000d1021071030510b0710308000c0c025945035000006285a44442c0e050075034005500100201c1c514030200001424020b800d9482c1a503684000c03c17104c600c90342e0750682c0740006072641c03000008520001c810000200030b00b0314106500c00f20940c9070081d1080a9940c2c0c2d206009254004180e90041000180a4079059000c2ca5141d1108103400782800d052100d180c405540603030030400c8151480071503407641d11652005d080c440c0310100f005401c0c141403001603042c560026 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722962976 1250 722961726 722961787
    0x50d0f140708180f0d0c061202131512050106020309150309060a1518050a0e1b060711090a090302010b01020a08090405041109070807080606090d11130908 68
    0x100180c0703400211540a040b09080b011100c3c803100c0480c030003003000102c107a0031004034001c083c1404080d00c886402c0350003075583d42482c034021080744804d0780034001001100c43c064241c24848241c00c040007280d28034603440c080800034401400002584c2c001c1e444500581c0000645203103d0604c8406050303851040d080161840c1081d0044a58035940100f414030000c0c1d0b41d11540e0079600c200782030740e4014128207055101030385030103091030003d045c1600d484030045c1c984a264070a0500100d82100c1c00340c801d01c0c10707280c1c080c441414044168030100c003c0710142e03c044514800d41c1d0710340d01c146008400e507030400101c00c0070074980030342181c0c8040451410340d44010a4078000800c4441201c0c1c02510651313010829443d5481e029a1801d00b442699521680c0001081020b50340b10366850f114030302d240d944c0039031a2101001d121051155014184e084582c4036001004150a0342290f0b44036a1b024040103141d8109080b01c804484103844200e07007003007000445500e2071340d440d61a821040003c5060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722964226 1250 722962976 722962987
    0x50f0601050f030f0702030c120d1812050304050c040c0f030c051312111809010c0807080c072102030c010f0506030312090102070f060c1d03060112020a03050d0f14 72
    0x820b140c500004000b10b14104000001900c081d2090007510a0b101143e402c07901c0410402c000c003400d6801010710901003500d00000c0440d04140a0002d5a0340f07500840b42002c1c0442d4484210740603400108203585900c5149107541c0303183c449118008007800bc03552031803020640e0000003800d07600381c0c45800d01041824007805010080c5c20b600708003114602c05d400c800b0b80c4144d20302000c10700b060b0344910350b03c1900c0c903485420340e80500001e9031048100e0802041508400c0da03060b9030701c800a50f201000030b4101000560007000030402800c589000d01e400e0024460081c1808108419410407030006800c040340d01521100c090040c00707060445400240510301d07080c00881e40e00c0c01821221401d20162034041045100c2c01c0d8121800c0c3c6421100a000d51101e608140c005001d600c94828009242080b102c20b0030034807030412003896540207000d02880d9181802c801905030751282c007a64440300c811800400500200048030318580c0c2d548500a407050316690251030781c44500b08294020780c04228 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722965476 1250 722964226 722964247
    0x4030606030b06010e0307140d0804061809110702040e0a0203100c02010e01060b030a0507090806070c120201140424090605060108010b0a02030307080a0e1e160b0d02210703050f060105 81
    0x1800703804d483d00c5106801098800c41c1c000ba003c2728010f02c1c0a4205080000c022401036408076050740c8400060106549441d560300744031080764451410244010010f0100c8001840c0032b0b045001000e82e0300d0110348030040f42d600000e050440500c0d507802c886942301005903080fa020b018003668494448000c00540303140c105409404d100041c40c00305a5a0385100281c070749400350b556030000c0c1040a04030340b0b00e0301d00f072403003d02059000070341901c5003654000f10320340780d5105018080d040380c1840040d41c00b0780c442c3da5509252800c0c501221741500303075500000410029900c40c400c441130103608007143c1401d04000140902074180c0040801110070040f014a25800004030780e0001c04600d807031101e66543c2001500240700982e0084850701072640a451015010800011240c4002d801c3d00c2c021001ca0941b8820400b1500c1001640340d401d1000c00d003004503560142c00c1c0514040c0c081a101001c04030381242c1c0c00fa04403550310200e507444c000e1007809244500100d510400a0901c5442e103290b404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722966726 1250 722965476 722965483
    0xa051b2a01060608060f0117010605040e0a0e031e04150305040c0e060907050309210a0e040204050a0902090d0b0928020109030605070c02130b01080a060506070807080c0304030606030b06010e03 85
    0x1081580a070f07003040e4807205180d204854188c0c8012001d440c02c0c180703503141d50703000708540d00501c520074002d0440c101190001c2c0140c0b0540c1c845038603040c011440c0000c0c0003501003071038207866420010a1018000000d809000b100340c141d103241c1c10f80c0c00140502c3c1c03d01d04042148216000b8101350606c0700100261600d40d07030301c42604007086003002c43c4c50740c0e6004040d40c07a242051068680d80b2050002d10f0641d02c0c2160064a02480c16460381c84000c004801440100e0280740321b10f42d0b100d10744100403c0300e0340040c1d00030309040c00068000600c40800c0c0e200ea841c3c10105803540d034860b42c00b100f060305905428884007070150001850b00c28200c800307a00002d0110001d404040c001c1c03a9154040380481303000d0900b180c3c0300756000c1d01500b020021001190010b20b1082d08080c08244904001020416180b0603101510002401d1038100102a107a0101680000710112120102004442c081c00401c0001d04001c61242c0c0f008540b00381145800d961030040a40214140118058040c0c01c598010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722967976 1250 722966726 722966731
    0xa050303060904050703060f020d0b0906030709091401020705070f060302030c180111011b030c0905030a120507060f0203012d060305220c060f0503040b0a051b2a01060608 75
    0x2242c154402c0d403168107106061031019070005110700d2928854003a000b9203500a00000081071100b003202e5000f0000b805400501250100d0b89500410750504c642e20b15035005003000c074000d0701d00490700e2450824031801ca901c01c5005a80b071340d2107014200100d4a10115820140c00545000d50450401d042004594012003250110040c0c000e9426856a482003000075034100401d0b0080c06105020162144201c1140c51008000382c1050009410580140e49500c100e8002900408102072141c45010300c009043d4110300c01c22a003001550f000c5089030141c8840c82103250302c01a0b49500d40f00b44481a2004402c5000030000088170304001030b04400c1c2164100c880c2030a011034245d8450102494515107000c1c01400c90030a955070741d00b0700c12503031100c030180c0f0301c1074440c0955400340c00b04c10b4449010448006104403100400240001c2e065000b050700310140008e6503c1d0f0404110103500310381c100c0c05040510995104008206241240c1048503695149008020140c10400000d0085100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722969226 1250 722967976 722967979
    0x9070815090c120108030c101a030a0f06060503071a090f1f0e09060619020c060408010b0a050102010207050a1e0c060e150c12031f03030f02060603190212070902030c0a110a05030306 80
    0x101c3c80d0030f01c6548210b100060118074000cac10748040b50a241703000b01840c0143c0c001564014030340702001c0703624180042c44205a0b0030154020611b01030128180d061540401da41d160469054284003c0d039807104c1c0003480c100c2d05440c2c803580142a130304c54020b01d01a480c0134524803a41e00002031046540300e1004489201440b452010640d0036030740010392038078080e9014681c100e80b00103000184005c0640c813524402c4021609113180c0303075803480128241e0080c040042c0c89a0040405000000c0c140890b001501214a103821032010240d1118840b024956000c5c0002c9582291103003a503203046030030341e502c4000300c516007803c104403d040c0a945442045c0341d03d08468001000c00d9201199412040d02c3c626088034000146c3e0301c1e0729000f040d003644503041501510504000c54820714010540c0e08000007a12040e0b0351004160b000c103c801950100c401455018203900800c01120a00085103c4c0740b01c158010341d28501e80301c00500034020018100c46541040d0042d0b40007440100c200c0350050710 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722970476 1250 722969226 722969231
    0xa0515040305071b08070b0405150f03011205150c03090105060a03030822050f03070c060504151b12020706320708040f0801090b0a020909070815090c120108030c10 72
    0xc3c04400d415130f01103d070000760361440380320710000d1002a80e4005000b0346000b511000aa03141c54025600d90303029040c0744161203101031006012080c181c4070000890f5024808503030030b07001101f42d0480c16880590341000081d0002040007030381e6801b4003506030480300c180c80c0710711003d1860f03c004140c09406400c00c00300d098091407244134800e07402d4003074000341e801900703035103041140c0794000c6d5981d4003841c82250109110800042c43c640182c2c103903412640103820380520694084001c4500c1031200790b80c2d103501c2541a2000003c01d15216151040e00c09540080042174201320005d40380d07881260140040d88001410380080081e1580715917142c104410506856071070314070b8021098022604803200c150601340001443c114150441c000507401961020300700e444207103030001039100321511103800c0202070004c0340040d486042d411f5403080082c03a0192122103880d000461b010700c2070f21006441507020039070000b0043c1d168082030040205000440c6002e4003000c40c5911210600d02c0801103e9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722971726 1250 722970476 722970503
    0x22032f0d020616080d02040303231806120f150415120309120c05150909040f140a0605040605070c03080f07050409020c030315150d0213050604080a051504030507 71
    0x4100f0110740440c550700c201e00c1501d6160b1814076000030740003440180c00040c000404886060103468580e40344007900b1b16030380c1c90208801c4451058044014081da008041006031010980c1e003142142e00440003004440203c4c01c100300640340c0c05054490f500e1003640707003003e040b080b1100c2c10107070002ca89203030f1078003024400e141c24190b500344c810740c1c8048240320722061540c0400041060500c10b5402c11101841f0035040d25840d6100e82c0101c000b03090f00501c41c1008035000c20350204404034054400e0194a0398000c422284605104400d18202da445803590140003c1115900480e54045003038980806a0700058034010180c0201424a2000440304804900c4507881201160050002481d0566591451414840c0e881d80116502c00c0c3c022082c0d8941c004a2601c41c0300132001c0340d040e130000303410441120030440003507010420041c034500701c401d000525034940f00050300050000f01c014000c3e86030f141c140b103420090301c04d01032078001d0608420040044d8201040e41c00003908501b0100740b60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722972976 1250 722971726 722971747
    0x4050402060c011503030306150f050306130629031312030e06041109100f051e03010905150a1e1d0f030d0e0c0d030522032f0d0206 58
    0x10300c6a00c4000002c0d50a0000514219943c2d188400c00c6034460782c1c0402801e1741c1d0710850400e041602d45114001441c80400500041c03284010f035812000040c111454034558215241c200c601c03503401710008100c240c0714000d48510365031410720781e072030a00d103d10b1071440c2c80b5803000004601d03c140107003040c25036a00c50b28118400d6001c000c00480c0d00013100c5076800c00d401d05c1001c030303144c80c04100d10803624880014580703030f10354065100315404d2801d2998503504080420a500905602c2c0240000c0c0680a69540740c0c1c0c02d000c0e403000940540c000d41120041c03455240b009520040c115a20141072540105501c00c130280c0c2d00e6580c104541000500040c1050001e0480c070100300855494403521100d035080400200007042002030340d5000300890700094007195120210a111b00d5404400300c03c203a00402e010380e00604d03504041440d0b4496030414007031050302e240240d40007900c02841144000741400c00004149000b10718810300703c107807444010001035140300c20300390007801004042191440b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722974226 1250 722972976 722972989
    0x5071803021c050a0c0e0114010c020108071d03070e150117040f02010507060e010c0206060102010b0d11031c0507170309032a0f030720031009051e0a0b0a150504050402 74
    0x2090340c4125003100307482c0d031b440708070340c2544083c00f80f0000094000d070300b40034179806090741a2041d9410b03161100300f5a6a44410349210f900190b014000c00c50650700c0311041e07a824070100001e041d20039801101410b0015013041c42c040f8803c60b041c14041c02611400741c40007686410790f403280c0d000700c00c2c548503001c5d480100d5140c041c13500010b01c4242410046d088030792041d00710403442a5a030382207800964a070401242643c2c2c0c0ba5031901c0d04551050300960115460042d140341c0410041c0c1180c2140d100b200c051828071401d0510300d130000f50007040c071a0401505190008042c007900041b241581000003080303440307104013008442100c20300300c401c0644458112811903540c1040d004d549200551940554a03a442003d080f00c07889010450381303006000740c0e8588084c1d0f440140003004504000041c0c00014001c2100a5450703200d01408602203669545e8109060f610b1580076207a000118a8440700d46d44d009032507140c61030b0400043c069000c04062000d011580c00315000700c2c541c0c41c0e90022968 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722975476 1250 722974226 722974243
    0x21c050a0b181e010f09050f010b0a12080309120a0819051b0306130c2a0b040f031e2c220f050c0903100b0d08180d030305071803021c05 60
    0x1582c1c2050b0306e030020710402003001c809140707400c80240a039030101401c0055200c21800b401143c09034000645000c640104091070f440501403085a007400003442c10703100c480e0028100071000940040400600c0011322200105401090780184168141004014544580d6248807003090781c0c04000100150740d200309418502950710000c05c500e003030451000704080c02c9034040d5507403400c90350020041e0814804141c52102d4100e0100040c2d03032030340e503100403841c84002d4084e0200000000403030100104a00040e000220036200c514030410307800060318404c00c1030a03880a1030011084603421644402c407a00a0f8000c81074041038400740d41d9032a082c001d0481c0005d01e0005441c0c0020461075144c0321700245401c410440450310001407600101c420f4440003404582c102c00c481c00b01c0400100309102034010041e040000b415921940d60100300d6021034024213900080e283c0c02888040ca4101040f15002d40d05680342b040d4250464000c1045110b00360f140c00d040254407809041840428040d814 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722976726 1250 722975476 722975501
    0x219060b190e01090606021b0616050d0c021002030c0d050306010210050f0702010e0f070e0a0f0e0a1b0e0612070f14031204060c020409021c050a0b181e01 68
    0xa101c1d034540b40401030b074000900841c1001d80c41e040011a0b00c5000141c1c1c0d030b081010b02c00e59070803110742e44404d0003015000174101181201108540c100056810311002da002602a40c500304522190b0040000c2d105102003400255001000903040c40c407004540d6901018407414070030380d00d84403203004030700d07100901026040d1180341509002d00d2a9164422502465a80e4001d00205158480917030700c514032520303108141c0d84842010441d4601c18001ca95001d0148070000a01440c40500c05090340c450300140030740d540010341980c08000d00e20406010080000700d0300090f99040040d0032060700400b4010134031440c0c0040030302a203540100407010103404100156603180d60b41d2996141040320342e04138503100340240d14890300d0703003040c44c002d9404841030380e035800300394107510740900000381500681603810554005191001c880c400034800300b0315115a004010742e05482c244040c10f44c0c805003103c2520144003a201401041c00101581001c0001c070301a14606181c40c3d901d0b00524000c00c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722977976 1250 722976726 722976769
    0x20303121504090b04260a030f110412140304080a1502070516030b07020607081614031f0e090a02011d090a0e1608100209040b060c1c0219060b 63
    0xc080102e5540c0d46801644a6106072035000886c24508030088105078000548200501000168074031079041a114102034110024003020009900001a44941c07c0b007243c040d85203240790308000301041c1078000d2030070020185082605000005407a8a10003070040d00d078a0880003500c5182410354100d90416520504840600c285004103041c2d5200b14481580e201c1603280000311407500100301c080c403400781e59440e44042c4e0b50b251343c60b182e10007071007003504104040c4004070f07a1000780d0000158002c04141437007042403041200741e15064000b0b90402c00c844600700341032282c647e000140b05c01002d81e09003003450529441034110311284041d802100e50041041050106891a5030711503071249030804240d5442051000400302c500388184942a440d0380040011041a603156003e000180001403010680c6280d610000e403054000058411080d00a04056166074511407882d1030200b07000d0024102d40c003442d441980b1607038411040640042d44420492102c2d41e00c00161003214240001030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722979226 1250 722977976 722977991
    0x118080606102106170109050718020d06061107170d03050c0d0203340801030204020c03040f03150c1701090209010c06050906010f3501090807080a0f0c020303121504 73
    0x203403400781100340b1030303000c1070b14117010780062480e018001c00b5291600140101140303854001464240004006640381880e424030098501d61050300800005041550b5801044030840b8042c50600070254040d01c9600d070100b484007032a06002c64248051841c50038001600d54803803018040900c1100c035038880301480041004102a881601e021020031418842ca0070013144405418804044801400c08128084010001072400742c0041900b0b04a0505903414196159490701c13002a0070741080316403a10b102800503003c04248559090403065280000c071400349010100031a50041c024070f041c0d50740020702e000d07499000305022080158407040410907440e0900c2601e4a0350300a006141c0d058080c5440010360f4805a54a080a07121140002603030690b91403601c141440e401d01e85042a5480b541e0741d101181c180005850418050645c80365100500d400017014070210b86040000e0202c22a00007015880c00010381e000700304401454501a110940c8001e074101c1c1540d00594010300f819071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722980476 1250 722979226 722979287
    0xb0301030503280519030b03071d070201020f0a0e0d1e11030d0203121e090a03021213030b0712180201030b06030c0702150f070b06011808060610 64
    0x81680c07900d818204612290300d041100442000f008050000031000d00c420855150014032004072211181000151001108082030404442d948111240140307a1642420320285400c21a8000d2092000b1443c01604d41d44c0e2074500c0c011121581c04100640c01c0b6070f04e441d1039904c41540b903d030300514140d460320100d95148070040035102c0c1c1150032440f00200084d580c200007800d000310349245d070040e606001801c8419180c00f40000d15000c00c0900d400004403802002900081c0203003100304c098410102c6908020b0b1030412035642d526112041048410402c03c100e21695080c2c0c0d500c071604030495140d0b45000c95441449228441c4180e107007402c041254070800c903150000074401e80382484154100000c128450004841c442c4420703204005100c014075007003040300400321180d8622400e040d180c8058000541107040d0407100c10401006000241d031304000c0103000980340e411300b003201d02c1c10500415154a00941654001e02c2d03003a041090003401030b8078211284c0341982a00f00301c1d0500e000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722981726 1250 722980476 722980483
    0x14210c07030e041413020a0e0a0e2104060c0515071806030b0f0d05070b0c071a07050d0e0f180a0b0d05030a210e010605030c032a0a0b03010305 63
    0x10120301180b45882c1c0540c10f4203250140e010301c4100085110125038444000c4921086504d400300e9000940341804070b8991402040a402001c1c51007000079000160010180380c914502d6043d03c800403004071740070500454004440a54000346403100440c08686012482c0c030302c24000d40321001c01c400080040345a48440040c030b8102201d1310400f5066a0781380b0980444085c00626500300000d020020301a00701250a114810f118800711402140d88142040e141e81080c110300907181c000c1e110801c005241c0c25450389500f01e0b00c034091403404c08039a0303407195102d040c8054074085c02181c0e501c2c030040340c1c1e4081c4607009165014020016045d1845030b60003844004444100308070340340c40c07201301050601d0030083e44210b038014019031030130840050558065000b1500c61412001c58031600c0e101d1031603802881400c0c12410004900b550400e03040505110701441c1c0c05001e13a000440320074210102034200703640784003641903a40002a0010104041803804d8200e0041040000000800c101c0d000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722982976 1250 722981726 722981737
    0x409030c0215040605070602090d0507030f060b06040506181f050301091d152d09100b0a21061509060b180f0f0405090d030e01050103020114210c 64
    0x1c41d10304032a444114020402d5014500400001450510101d000982554000c10b09c80c1030040c1003440050040c0d55280c5005100d0b00100c0f2440780944042d01000318500070b540c1c07407070001c40d006030505060001140081c002c06107005000101d84041117030300e4569940812031942d107420262160001c2141c003400640c002e1245415991410202c201c400720084d04240d8429900e0380503110300140d01e00c80e180c01c040b01a180184181d41e28421184801c0700c511074514401c6460b801d81101d241901100d414440300816032804542041c00d0705000d0f5840303410a100340da900c2c006a0b01c82507064043c00c003c15039140390040001e480e008030820344050700c000f04800c03208044014003c40361035802460b41c0740503142c44204184564180c4003e1454150f1000c6007001c000341c0a103c582400d0400541034420a454202e942d030480345002070101e62500400c02c212410fa80280b1480d40f40d130780020305044030641750303844203440072849a020844406100022100d4800100c2e000e08000e440c00d4001e0b03016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722984226 1250 722982976 722982979
    0x60a031a0916021506030c061b06101403210a022d0d020f060f0703090210030e0d03230601020f16061e0e040507050f0f04050a050d0b040201051303020409030c02 71
    0x14400510413520350418094403a80014000e0704414208805000058100b080d00c9102140e02820001c41c00c0c00421001e84500b0300a1003d1160501c2c0480700fa40140084036954000d400520300714850520032103184c4100c480c0300e064981e880d4811107089061086600b1080d138800c00b0b12401200004a00d100240ca00328507509640d011410b846081e6506c078003055091802d60400e00c00605010814002d45500040318100441d090f082a800114000100000280400d580e44100324070f03030300204104140e00c2414101002040003440020381c225289581803528006400b00255280c0d1080c000b00314411052404c681000044405030398002d040c2d4040e4500003140d40101c00002e00140160303407101245510f50680000c540400d03c405000000c0150b002d11004101c004911103449004103604c80124455603143c6041c0010845041c41d5503000f01c6c801d4654454400100340034041d01a00700d542428103276075418081d40080d4001c1e070f01d1b600196000d8030706641e49050540040c4a0301c171140c030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722985476 1250 722984226 722984233
    0x6050301060608070f0c030c0506090109060516020703023304061b021f11070e0a0606020c060f0d0902220b0303040807061112040f080c0d02060a031a091602 69
    0x1119041180d0070f0340101c4c0da803c001000000d81d2140c2500800314648510b001c0d2525203000049919407514081090b20180f00c40d0b0764500414040c800742c2d11526030010100404c810542c0503884000b0740d40c550358000039205118101d00116064507105150154254100554a01d0100500b540d00d440d041403280c0e8010480003250405042c41c440c2150340c280d540100804502c4810304403890100e20340400350170501070105c101c01c0c2400c80800c003a100a2a11009003000e510745080d902c0256606039121405640c0a40591034440c0ea800381030b9042c202210454a88800d4001300b450003400c0d010201030b400400000603034400454014a180010400030000d019000070501855628803440c031078422590030400080c010035100d0300105104150180444608844014407540f4550056001f2401446c444004024484051110060010089406401190091300403d440b48910707400e03d400c050f52101002d4098003107840d0b02c020000c2c05084a02c95151800031600c4e50341000500c603002d8403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722986726 1250 722985476 722985479
    0x60604020403020d150e120d11120103080f070f0605010914060a09091a0f060a060c030203041403010e0a0321050118020a021e0a021f140d0603060603060605030106 72
    0x105030084504a07076000d03040e0541c0d4001e94517200e0414a44200007100720f40c9944a41d658040c0c1000090103504034082441d42c1c43d02d240c45c4d0041142e0312624590a092810300074440035144280342c090444c3c0c2c01003e0305540ea20b0f502c00f40565032040a000401020111080030280b040036880507040c0c460b280c10402100c04003800907080c030301c022103c0302c0d4404000709091080d90b2094101c4d42e6214483e013059042c51b085003000340501d09040300c02a170301755585407c02c00b680ca000030090004100505040280343d95030b132070080d140d104070b008500d109940407031100500c1e1405d40c002c015101000060340c00c3c9000b00d02d4010040e00c10301013030442d505058054511000050700c078075070480c1c00102102c0c000c81817005460f4080d4010001110a40c081c0418810031440d101425a40310304400025020a0801e8410000c0c40960540d241038943c1e40159035400a0f03400145280305684104843c1d91100750780400c4c1005000395400040400b8203040000040140c9038124000785c0350700703d0003800310a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722987976 1250 722986726 722986729
    0x5070503250e060d0218090c040608060d06022107050a0804060c0306080f0a0201120504020d0b040615061101060b03160c020604050a0e0609250305150907050a020606 73
    0x500007521101460004040c406001160001c02401c1080c030500b002c49842c80340d000054030540005250265040d00043c1c080034000200680b0b02c1464421500c0c203045050007441002c482c0100e010302d40510007004003082981c4e031400e0040400c154000415940c48441c82c1000b41041c40184800c6190201d61000c584d009000764140c4512401c030741e03980c2d00c02c0e903a04c0d1901130150200304659403c3c1130369114041940030003071101c03616001d841002014811440d20004004816402e5400c0e00d03140b410051000680d100740c100744009420202070002600c135410060300038480040a005029101e40c000248140c000000690070f0014900030800103a55000c442c031940301c1140c41c18040113209001d0700416002c0c00103a0340340c2c2d001605042c1407945400c08500c650082c5d400844d2071901a5082112520304903605950040308401e41510080c640040ccc3d000c2000310604507000d150b211000926090f082c4080c2502d01900217102e0034050030a21405402035200829400042c0204400600c95 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722989226 1250 722987976 722987987
    0x15052a1209012a050d050a09021207081015051210020a020a0309050a061b0c0f0b09190e2d15150c0a080d2d200f071b060c060507 57
    0x14201c3c103882e0b580c40d24803075100560043c90000d100e01c001550317503141300002d6150140003a200c070041400400d40d003800d00750043e10b0030301740f0021403075141d060078041540c200c15104804100c0d1810785001a90440108207a4188051800b4404001c0c0c40802d0a80041c0d50010782412071034001d03190a200d641e01c0700b060048d002614014040804c1c880100c0c400482d10740c64240041501503c00c0c01d01c419158410014904c000b54006a2142c10118148250349003c0d254424450540401d41c2c0d9418945152481009030003840d040c0c400212400b00303460018443d00342c80d01c4010a100350007452070070321490755480704800f640c540502c042102003885000c030f0100f01c60054401c3e0f0010000950550303107803441588041c1c40d0704001a2100400e507070f11000e141404140b00545c0304aa01c1c0c550400c04a5004c40b00c644107864040c00da110340402c8102c4c02201214820300014004a039103078030b41c2c1801c084c9000f20100310802c21000800010311164884d90840000b4401c44c0140495140c6a5040740c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722990476 1250 722989226 722989301
    0x80405041109030607080408070b010303021501120b0c1b010f050405240f06010915030f1802060904090c0b04080105060a0f0506030621071215052a120901 68
    0x201a480b50001c255082d004441d1164004c0c808d1410318640b455690304d108080d2800c4e4003c0f00076070300090080d00243c0d88070207400e01500c90106090301c240165284c0e44504900500310841c1c10b00300280031040b202c90907141240c6100e00c1030082c80701d003032502c1181d0010482110159140d008000083c04441035620441c10286c400b03041c1d5036042e8070341c8290b690041d00c01405441c1032040e00100020752082c85044c03100481402c0c3c0300010025a8030000c0b4013038506640095800031140a41c0000503580c0740295500e12200f03940005080d4418038120204a9943d00688c145210225000860600c1500640c2c890341055403034969503903541215000030f1340140030789980124240000f0b003841c10203035024901c1580d500025200c4e82d0700c41e5105800c1c54025082815150920004038060100c0460000c91952000c00d04100368030705508be407101c25141c8119001c46610103072038014030307850841c295005a41544030020030b506220f01014000d2040020f0b256401d081c24510851014a9910104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722991726 1250 722990476 722990479
    0x6130e0a08090103091e030e01111b040204030b04083c090a24020111040501140d060509010906080f010b030622050604060e0714030a0602090f0d080405041109 70
    0x40e0515640c1d4480503040540c46904140d55800d0841c0401c2c04080d49100b040c0100301d04100c0815079040c001e1008050006040c148003000710a552110700c00903c0c001208501e0040c100140e590000240c064801c07548064109041c7c4000c1c030060100c1d640c001e2280410540b842c28603002d07451a401118441e100c1459040c4020b16007004841c5d01d01d0004000c10b03034004088800558403029070031115076151004d01001c3e4032540d0055000c5c0d0702441141051120038417145d00f064903000000305582d024071070541081001150203001c039a159000354002c1c100040c81c0e41c0e403541c3c403008420010320140c0309114a03032260000002c000035040c03041c05aa10300144c00307040b03145d0f111410b1106500d041c440c40342c000c2c1d041c501c01c400416000d001c03403406a4490000414010241c03012a4640345a941202c00315803000c030f6200e840c03a07400060b01e000d880e038007138005a21000240002000d00748240c0c002900604100c00410801c040000200300b0340340708980070020340c20500c06901c21405070b0424103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722992976 1250 722991726 722991733
    0xd0c020a03062406050c0d1b0206072906040f0e070311030c04021c1b020307021504090216050d09060504051212070b10050906130519020403080306130e 67
    0x900200b1416003083c03030b0b00b400e00703194800f41a5002076600c01c001840d0b030007000001c4000c41d80c0203107a031080c4101504101d081ca02005600e0111003a0402c80140d10002840781000140c40e8040000a540c490302d04d5401c0c4c1c2c2a0300d54880040c0071180300040072650f082c400c918091052440031494420000100310010040200703500303580d0350091003c42c00da0050347c10b10940184072082d68441c0020300d80d02c005802040743c9071080f20307440000c0d101d5802490100155000346002d403503074000207640201b41c0445081401c03001051f1510000d110300e03040120310f1800003490303d40c9601c0810310ba0390064400c03c1112180b00505c501103c0b41202400349900281003040308214906d8030007403641203866240156940485030302c5e030310780f240c0c1d0046c07a080759019184408c0281c20811681160010030081d101c00d450303850048006440341c18445540ca002940d0f402c04a03925a0080f1001d4003600b200b28130441d50349842e820511600d03001100c94903c103c402d007010743d5100701c007030191181401c0302d40001d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722994226 1250 722992976 722992979
    0x303090b0f090405310c17100f090b0103030f0210060f060507080409021b07050616032d11010f02090d0209040f08030a06030210030e0304050111031b030c0d0c020a 72
    0x3c000180070041c00284411440902100005110070b117851800d030b07201142004140d40a1a00201d400c0b007950004d8002220b45441428010010416a4806040410004504824480712001040746400240c03204141c0f4001004242e0040805015050550200c41811400404e42c0c000da84050060302c40720140c140041000e140039001034504540b190f10803e09150b00c81840304102c0e000b8110100311b4810b4007981d6000c21109005035030240c601034030580d147c140c1d220024500075183d0314000f4104014a444917802c403514640c450f030071000a01e0b10750103004401000134520300d00c2c1a081da045510304a19541a80c29510072200e03190405003220b07491480d56000c06c007c00c07030010000c0c1d030010f6505210400080302c074001035102d03840b00c00e40094154118010700c200300d054441400d017070510f01601d204c0300000000c2500d08072802480d044551190f031a041c02e045001c2c855010309405050081121540030100141c0150303c0010b003251000d099601c003ca668155041006e500113000040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722995476 1250 722994226 722994229
    0xa09050c0d05031209030a09080c03070b07051e061501030905190309080d050403030e0306040c03060b060405090c0706051f1404020c0d03060608060d050c0607030c0f06060303090b0f09 81
    0x220a074072580160181d07030808001d00109060000304603000c070314075040000e00c6501aa0080300301030141c440c080052080c4804030b404295140c403c0d024159160070041020b1080000802200703c19804145000e400304050703192040d42ca14055400301b407840d24140740c0300750951192080b030b800103803ca0010302c0c0003c80c00708000010b1107810b1059040000c0f0010114018201b0041440c0100c90340d40d899a0b5103107107040081c826403112803858403d8011006110101d0318540c107007402c1d0303a001080010101345080001d8418496035100a4021341034400f00107012950074064080d0f07500414050003a50b5134000c403c1800841c0454101c4001d034428014030103c040d11310500c2e01e81c00050b00c0145400c4007901c505240410740c4040740d0000780c44041c144030560b4411412604800d00b6226202c446060b9501c40d91601046172500b0f0103100702141c02d5051611607050901d0b01c941080e10104030028038182000903001500081d00861807905d400507030908184211003410030309444442c01c0129800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722996726 1250 722995476 722995489
    0x90203100209180106050a02060a110a0f02070906120c12030f0e010e06040e3102130609020f030709051e041a04020f0a1103040f0513060e0f0604050a09050c 69
    0x60b8060700120038040b500b2a8500c41d02415000e0161a110070703403180f1280324000d181050050030150464108648801c58500c070034142e0f003500c0640d00344a117190406041c200e1400c0d400d80d004104043c01e0040000b810804115289100d43c02858400d41c41629100c00c1c21000400c1c8000400050004009031002e1303200d800c1d44103580d030341494156820110800014031307a410a400001140015030140940f5022018109030004a511603810803a000e000c00c5071880284510080c0c085c00103000844881041580128090300000c482191148200074422415400c100d40c0c08002c10b81c0e8840205591500342801210402104807039146140480c0c00e00026140403c2d58084d0003880c500758502e0313903035980003030440742d0600314809450b100c101000410108408101c44601c1d00200820300505025141d42c2042c0d83c03040c0c544004540f4540070310b03c02000f550b44079201c030303c950700c0602140f075814100d80c07801150300300c80502c095260000d8080071586031000042c0154000c0a444888ac182036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722997976 1250 722996726 722996737
    0x6090e06071107030209070f020118030e0409110603040507050108090610090905030702030a1b0f050d06111608030a0b1905041112040506010e09031206041a060c060402010905040902031002 83
    0x42c0c10f4820b403560b81e5011600809041ea84400820540407800c0583c60f130900c80d10f904540380c408000b1010158ac0c9000c1c0c00c0c102201101030140341c4460264052002c40c4030001490500585035136603030700e80303414401d8558605024140c0000c0e601d0300894090640069a64083c940140066064503e004546402000042c000f20350318081800040b0141c0e40600a10346c09600500100255074014480003120720059001001c6150801d40c0500042d142c20245002d50745d40072100081d810080d80010200d0300502c01703001c940e0340f50740e07900ca030400014101550090700341540521407203182c882000070806070040f2008604040e0802080649860382081da4800d12030342641d49801e06400404c0003901007180c0c20380e1990f1203240104540e61141402591000628019500f003880e40700c5000044030303000e0811440303039440304019030008000c10542000e4510007043c15580d034562a90098460204aa0903404900318503030004982c10280160f25503103a004029015441c0c00341607840007500407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722999226 1250 722997976 722998007
    0x201021203150630010504050901061a031008031309060b07050d230408150a0905071505090d03020c0a050301020c070504090c050d24020901090b070204090503130906090e0607 77
    0x74101d940c03002e24842c565502990941d042614921740c1002c05000503075101071702e21185a03161000401651b000b0a1400c11082c21f1108982e689440f01d01e8001d4070035140342c1280406000005005900403802c410132001c6442040b014429549d40740c00329070045c0a0017401401b070b034000e880c201034400d1107401d40c0070018641642c0018001c0740700000c0c0100750000d0b000032007107920403107010255900d1824010b61008900d18203000402d1310340c0e540d0361140d4030b504c501000040c1c80241d003d0128081d0041d0b03001000c010b4074061200c0b44505009640b1124200c00d207000361a11100410070f0b040c18000c4a22400500e4021701c2c02a02d0001888004c0c03456500a0700e0b1007201d05004140c80d40c0c2c0400f40c061182c01103201e04034800744202d00c2b000000200100c6282e15104100f00091a60000030f08012100c00e081d60545170780c260b00220740603103586240200309010001e40341c449110554400401e882c1e141e02c0402002e41c59420070000c031150010302500c80d510000009044e05e21691500540e02c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723000476 1250 722999226 722999257
    0xc050d050142030201140f07120c02090601020c1e010507172101120314070203060103060608120f090918010c05030601140702151b0601080a02010212031506 69
    0x807821000c0c1c0c190040c00341c02100119008261242004032003aa1902c1d5801008480e0307000d403850380041c205640c49121560b00031030108800e05242410010b4414040e0000d9100d42d141046440041002000000413846104804041740380d07540b0014140100740800740c48010088a01814404a0003401005904002c4100700c2d032800103c0720f2031604032842012800700c2d00c1c0d100c05013214130b036074084510400700e01100400412500d500503420300c0e842c5030141000c0c83c0460681d000c40b403051080c020007035014410320000104010071130303100d08211540c3c1d900344d0712034420035000141c16101c1c0803d81c5801c184103010403000d5103050045d060f0884100c0061400c40395000b6000c0382582d03d0741d40e10034003141c8080200440c551300b003070414012101c5c0c400d4291030134900d41c1c00200b80901c106401d504544000c603c0861032184135109d001640c0c000c1d01203a02035a9140e10196079401e5440089005015111008084a441105503400341b800f80c0e00c0300000703081c03031340905c4a00e0300705005068a40c43d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723001726 1250 723000476 723000491
    0x6021c031d1005090601080607020d0c060f09150b15070204110903070b041e152a0507090b06120121150b10021903080c040e190b010206040c050d0501 66
    0x10020401d002d03000030300d5000482c0c2843c280814505002050f40854901e412130b808004110f036000c29081001081c50600110312003080c24400300401000c42402c20341490b01014205120501c0a0a141280350b0a03060142110103014003941400c803c185ca040703c42c090001d0001031800b034110b40602260b480086042049060010f450211994480310102000140a00040703418040c510402503003000716100303088c07a0040b16100398100c81801002c120110740f0310318103000528013000c4c84003c2089118424080c3c0e0920a0316800a0700c240c9122030301d0030040143c2c60030100d06440200d6070701c44039864284e107000c90301c1307811580700b48218851201c1c44000c540001c1e845d1007468100c10b071001c0d00158020b25001804050391803155030009550002082d41400c004101e1400a19503161501035410b4480f0306180d0f203140150b40110b03829410304800c208410042d03e11000005008074405d100031740545005984a21050354040c242848199003032156007400b070343c203581c03080c42030f4000610f80c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723002976 1250 723001726 723001781
    0x10503161a070b0c03011409160f0e0301020a05040501020c09091e03160f11010c080a0509040b030d030c08100e040605060609090f01080f071511150703140106021c03 73
    0x8180480b241e401308600440140300721440c14504080950040c0c501101174140500a04401c01d4201c00110400c40b80400c0040000c3c802d1016041124001c0e000b552100ea400e0f40c040d10a40141c00f488d40188102d0064600c00d2900d2034020f805006030388068801c40f841000c00350320a010101c400c4049203c00c110545684076000b10707101c00ca50050103c500b81011030306e40030100300314540500e070412a00703009690204080e0f334115000040103040c4141c3d43c0002c940480d019041090940390706000d2016060402509500700000004d07860b03850b100702d552003c0300807403040ca50307015010301c041461000500042e400d5024542004002306014100200f02c400a0142d100c02c850040c020384540e80100903c50b4200001603c455207031004d8106036040c0350071548400307116804d0404100000c1c1d885000c138032007448004401091024110000e1904400241c0030340a80e03255030041c1440030000089642c03000c00c0b059401e031031104040b03100324104501100948006400030300003000346040458103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723004226 1250 723002976 723002993
    0x4081207170c16030b060f040e15090a080408010c022a0f040e0105070e0f12120a0908191b0b0313050f0d120509012c010f06061205010503161a07 64
    0x2c0d0700c074918109041c86d10300144070500100c07041150040e03040140b808044103012455161390000c51131030f01000d0b0f4443c82e1592404c1d0000101910300000000e000c210060306402c0030149000035004c1f2040034481c00140078409130a900030b507003100f06034001c5260300e14003040e00f6200300390014800304e184510014000e003110801da4081000c10900c0d407160b101c602b800500c0910710041154182c0525450942541c0c5484030218000d0301e020000138002ca60600500300320024154400403941a4916210407074400001c1c000c0a0312540c0c0c04c41c1d040d40390014130420b2801584d40115819085440303020b080f08602817800f80440b50380c05038018446030240304000301030003c960380da1358000040e00c0d03043d40c104680010384048000d905240c408076072021401d800c1c0e08403114000031700032890026501207006102c49400c18908500b050000100c02d9400030f41d16500348038229081080c1d981c1e9904056486e8120741d14040c511102d6001044680030312000364440b08207d81c030312440d01100c1ea0f282c01c1e2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723005476 1250 723004226 723004229
    0x51608070b07060f110a0c1b0b070f020316060c030809241305061006031103011208070302030c120703020123070e040207020901030305120c04060e0f010c0c090204081207170c16 78
    0x144200b20110706110704038001a0009200901e108e4050341070107400906e6108050000c3c010407580003009046490400543e50a908181580160385450310001032070040342d0401980050020000b00e45011000702c0c40c0321443c810940d000250707a44101c00c40958040050100400d0721002410b4800305400f48a55032040c1c6441d01aa0b0000d4100755000d011a030600c1a042d04140d0180010b0002e103100c0d420400c85960802102511040e461800300d03e10f115000f1002418054281e1441c0d2411a040c050a080c92094000340803c1542a80142c1c1c1244100b64002500400401141c9002d00884214014101c007030405403504000b134021070040c4c0000e90088000031700000f002d194280c54807001c4c030f0f00103014901e6039140902d091801020070140d102502d00ca0703030302001c816045038010713040c845a46501680d40040b166541c0b41c018005c0d041485121000e01409040280d001c080c0001c5900c220303481980460f83c1d00ad0216503290030b4004c801107144500c140f810100704c0c001201c0100c070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723006726 1250 723005476 723005497
    0x912050f0f031c090503040302042403051b0103020307020c15040f171203070f0503130b040605040204050a0915111e19080f0406050603030d0207051608070b07060f11 73
    0x40d030b03e40c40901c22815440110303c16100903840c03ca00d0320b001410110450382103903012100030038104800403007890381c41c422230300d51182403100c4ad100204100000c1050381c0e80d07007400c1132050042801e00c00150280d1004440b000c0058104512041c081e142881c0100041076042254604050711040420720760015908a922180d4645e0b2140313116290410400350b040050030403081c21800c0002025151a410300ac03403100340400400000d1009548045a51140b0b030080d028003824100350609200411080d54282d0241d8100000540d11741d03002d004003281d482c0e00642020303014103401d00d40c10042c54190300c210f09480040144502c0340d0140304080701d05440c4810800d9030303072080b014072880d03900f1080044000d00220408006200714154181c80c0e0050f00324002007a159102c0300040d08521441c02840107045c4041013070018000002030b08444403030262000110703644c4420340030741d51313a1051103a0070100c2001c001c41400103116402c100c003441700303803140440e401d2081070b50441c1d5904914101ea = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723007976 1250 723006726 723006733
    0xb071211030a02151003080d0e2b170c0906030a0f090c15030c0c030e010909110405031902150705010e070b0c15060f06070215040b03010e0a0c0912050f0f 68
    0x2c132282d80c0341a10203900085c2009564440301d20796655541f01d07004669410710f90a1350b5104000070b401c021300c04203540303103d10000b502c1d8914030801450b072a40800c0320900d0014a0104043c50300e1049681154002c010324106a41850521410000aa0310003040c3c101c4098036660440070f0050140102580c3c60311407010700d405203080c901001c04c0f128048401000b098103203095140c02c1c035007080c041d141050b01454400c50b24510007005031500b2055038401d405152601585c0410152142d001e041030350000c905546040041200d0080900c030b50b04806980f2003940205c60465030545401060740c1c5124038004180e401f20001d119007400300a600c01c0b460110300183d12000c0300d50034001c0e050f02003d00616100c040c1086000304408035103030041640101c00c0081c40e402955201c18101d00485100d028280d51552a03c44203400ba4101b803094150450340b81003c50440591405810708000c43c0b07907034444490345400c120881e40b40d040740c01540e66000782c0200800701d80c4240665454060442e004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723009226 1250 723007976 723007993
    0x20306010f0e0906010c03051201090f060807050310090f1a07090608090619140c180603040f08030a02040e04050105100501020d120203091609090303050a02040b071211030a02 77
    0x161150366114076032001c110031086415100e80c0d80d50320603500a5000e02e450440c02402c2d01e030680f130b01e1040c212102d24010424000050f00d20207500004020540e00001380034556a031403620f607030703400780d4001c056240c0c1020b001c1c4040030701f180e40b00c00070190040d103060400501c283c46280050881c0244001600320882c1000511508050244014002c620707000c407480c54411501621043d001c0e21140d04030214028203081c4243c25080518905982c0003041c2c10380c2881e03c00b54603281e004450041004000c0310868550340752090503a44200d800c01040300305a10b60b81d41d0000c440d400184515081d5600703101c0440c00310f9825a041b4030852085000180c14100005c0c2485051a65400320781154441240ca080d00e5500030400e41d168000284056143d448015a0714106102c0301c0c0600850b08880b6400603141403150001040e183c000d0714100580e464070380340b030400e0380f02c0c0f4020603280100400c2002c00142180c481807070611017a14040250f01d03052008a0f06690000d00c0070001a40315100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723010476 1250 723009226 723009229
    0xe070305072604152007061109280f0b070204111809041a0c0322020f0d0309170a0b011d01060c0c05030102130806070212031b09040c03020306 63
    0x1180c8884030015035200e0304414420600341c1c140310000f04002e103c003015003c1c2c0d51281403030342c1020001c0c0d001c1d1800070034003c269a001d007240c1c1d000791005070b801e941445107055000d10490105c9042080262010800c84d401e00140c040d0b06d0001019401c4100002400140d00d46044c0d00140207050b41e0404195901450300422040c0c9864000d0400c0c103150400818135810f80c800034030710f0011070079140c00d40e0742d80c0e4504105841c5900c084894907468103074820000d10680d44c80013140709200b041081d041501c0003844104a050108000941000c80d140382c0f611140760000c100300380700c2d1083c5440300c1000d807600c5205800d00102d00b600130543c1d000082d0041046031160b055409002c440c18030085001c888410125031540c11b1044c0010302400340c07021818003415507000381c081c1202500a65a070744070000d1003140266148034400e10b03030052030007142c1014404549584030310f0700d50802e03900f151030b09404541c02c02c00301079201c540200208803a02e0a6143c82c051290751008030b07200161a0300d003030380 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723011726 1250 723010476 723010487
    0x170a030209010e100f03090f02030a121b030f05031f031103010b010318140a0f030915022a0d06060314070f030b01091d0f06010305160602120903070e07030507 70
    0x1620301e00c2024800e0302c6410744c581c041028456141640341c0425040841d082003030140c01c82d0074010307406020b2034003400b05120060103207241500c034560301e003103e803000044146260035080300001d002a0380000e2580b4014401c02c0950340240740801c0b11500303643c0c808941258203185500840e001000c0c01810030035854213115040c5a004282814030505000702c0201220650300d050040001141402d047e40f00c807000c0101204560740807116020010312401e0140c01d800c00381c860510103115402d44220524408501d82c0d42a040c00e480305901c50f15039010070404403c0311200c1c1c5410003828441400421030501820b002540980c3d00381040720020b580d80b509110a6401442d00b041c1d80f60300070000550240b0f8072904441c100c1000160f1100b00c05a440040c0626a40700040ca01c3380d602840503150f00400c159040300d00c644200c03581d00401407414000300b003013881a0009078120703150003a0b14910b0303000100540303800141a03072074035a120343c8030705002102078401c000042e6840e420020081d8104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723012976 1250 723011726 723011747
    0x207261509070f120210030b0310020d050a1814120a110c0a0f060f03021b16060305060a031b051008180703020d06090215030702010e1c0c020904170a03020901 70
    0xb40c80845090025190000c150130360001d0003161045501d00c00203100c0d40c002c6030b000c0c2e4010107540c00e185440d0f81320390103500001070f10420546020045506005c180c4100c2c58108408c1d007000d0703e20b00807501c0c0c29000d0400d08241d080c080c010056032001c40c01c1c1c10f0004115840c2e442d00c0d540559075a00030501e24154012151901480c0460403c0c4403444184000c1422076840c0d1611255a4030501c03130490180c001c100c8009520070101001c000d40c2180410800c4040620445d2840f801c0d5488004405030f0340140c0780542c2000c4c2c001002c1c00810748900b00030701601902003225501c01c3e69140807841c0501e0098411000030302203800d0012190b07910107079040c8211079000030144242990001860501d5214000f41900d540c2c400c004110740b950b44042c2e60359009d0710f101716204d2030700003000b03030103041c1e10b2041c11354078005e01c604030101c04100c00084030883c1d00c5586040c1214016802e0144c0703000054819210300600011052104403541d0007004029003680e409078441001200241105254 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723014226 1250 723012976 723012989
    0xf060f090304031511040f0602160b041401030605090a05180a03080109050624040f06080405150405030f04060e01090e0906190e300307020726150907 66
    0x10601400305015001090300c042c0e07030304036042080c0340b48030310203078002000c9992200c440307820301040000d41d1400da0082c0b9412111a034013980c41e42c000c40c1d0080342e0388003c20b00608080107014441805522800c040c04450700038103050004000d91100000703019520304403424010584c4071810030500d10030250b1012102e280380d038002d12801a40d0350303002d0a401014050b80a040d691000042c0c6695104102c100b0304c3e00c0b41c01080d581d0404101c0025076142c0c428050550380007c40318001441c5072155081a101e41d400c00b0291060442215059864103005402961548030600c070018240c0c55460003400102100e480da0300f04401410005000301c0b001d607002485221081d01080f580540114015a00c40c0c01c0d00c80c4100c40010501a0b03400030304211250701e100b0311132140c5007000b402c2205100c0701045050503a007100182c1c0003940026512040711803000503080008100030440b0042100030325100408411214002c1c101e500038036142804c4800034401400205001e142c482c10302055015044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723015476 1250 723014226 723014251
    0xd061e060e012a0c061409010e04020c1608010b01030501050405071b1e030503060306130503040918080304050307150c090b0c0f0d0206041401050403080601030f060b0a020f06 77
    0x902680034041546080100d0705000d80070200420b0300c2600b00c000c800b40008050001d0030703e00141002e8020803160b000d280d01145419100d82907041011007a543c500700142d4074100c00c02c00f90402d10000e9006001c01d40e600e03100d140d42140c0390352040a6a480540210000042c08580c82e0340010305444060340900e0080c1d01e0002800001d6038409030300c50a1001d03030f501c3d12a41e0401860f1440750b80d000d10011406000315040d040c810154420000c6000790411011a100303600c40904481c4246404140180a90710822003000300c16456041040000241103080310340400548404080e43d000300c808a5440e08001000401c100050106508110140604100d0000d8240002d419820349015001d46010041511840302c5810040400c001c041442540c100001100010750394030800c1d0307000c45808180e90f1440003c0d071814402c0038417481e010b40d2940e0301900c4d644015401001d165424401d016212000406c02d4210300e001000c0706c44959000b00641c1070303d801210304201000d04003150f11031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723016726 1250 723015476 723015479
    0xc1b03053703180809042f070501050603031327020f191107260f1c030c091205031207020d03180f0b060303040e040c03060e010b030a080d0e030d061e 66
    0xc0b81c41043d9102c0700d03011b03a4005002c5054001d8004031320b02007100c07851240b0140148800c0c03444004060000c252203a0001c0c4015141d4801f0180c40c0d0040c00404800241c0180c001c2050700b8a250501c030250000d801600002c10318044410180e0b03005004440c0130794400204e0180070462039041d01001c51092409110503256000b02d0f68452415100b0680d41c00c601959001903403007914000e20000309000203d0b01021011040e81d81c0b10f150b54681d41d41c07005e0805901010190103370241c50901c0240c2d50312201076604203520303460f00702d0302040c0c10340e0648024443c18880c1e214500c5402e015461580003405100c0e42904024241d8036021246100302d50110403d9001a00c89007101c0002640704c050070a0030356596000c40c0c55406980d006020396482e074010b100034410502d501005880c00b44405001c00000c01440c0d034261040c03049000c0d01079005042c654003148140004d4030001010b040c2c00314000721845c0409185030000300c40d661195543d010100178a000c80050400340c0d44804000d4000d06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723017976 1250 723016726 723016733
    0x8010503010903090b0f040512010b040b09100306180b0a140705040806040206090d0c12030210020405092712040f090507050a080c0714030309010c1b0305370318 71
    0x110304c0d91068815882d80840c1031244a00d03500c1c00d480252101130300d09060440d0340004d850203003d011000501613881c14001030020b0914291040c441c8400b440004401d0740340d81d4170b038802040503507203180041400703404100c0021580c3d07a24500031220b040e004540d14440003112642f01801409910502c10b040104001c06100810869801030301100c0d056220a41440411844001c80078000c015004c100d81c007048002c109441c403800780380603600301c8002074180704e14001248254028607074801302260019545d049100446082d004070029442c03280007084150034a800c0c684940504405c00120b41030103c0d03510509038030f008240e09401070206e402d0003000604a441191448000c001c40c0344000794240b00d0106c11140005d80c4031513405600242c40e003d198407a0402d54100400d0750a000b00c10301468807609040308644d2030a12400301e00d06281c2d0703055900b94444041c61034104031002c842e190b500101c4115084070008201031002810025000501301d0384c1b001910300c07050b444961544040b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723019226 1250 723017976 723017987
    0x5090304050112051504020c0f0706090e040b07020a06051503150103031e0c12090618030b01060c05070504150e0901020f040501030f090f14010e15070305060109030807060c08010503010903 83
    0x30843c0c60f00015140c489801045a645000c0c0d142600140002102003118a000070000f0105a07040c0a0b42d07a00c5448050441d8580014451b140c0081d030b9110208002c102503500d0245c005540c1e004849580000ea55000195a021034008540000300705038101181003c1c0f008402c0308480d103805101660442e80c2c054224141c00c10207600101c5058815507105008410f10750078950890795504011504480060030560a030041d0000183c0141c910888101d5400d65081501d500002c04d40f0145c0c03c000c400c90780100652000d95a51080d80d0f00000c0c541c071617101ea910f2503500e200c0584009824111102000700d80540010520780c0b040268003400d82c0540251030686c1c0003481c0124440c410019041c01800e103401c0301030004003210a80d041000f2041122400301c02c03030240244140c00c4401c81302c9841c1d164a01030340402e486402c000a025510075403216500860505003d16101c6d00d0791561002030300941c1c012a031441e030791816420000e4000c0c00f82ca0041c042103000344080142030342d00821 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723020476 1250 723019226 723019247
    0x90906130f0c03060510060c020d060b010c021c030206090a0f020904020109170604030908160b09120304090b0f090108030703030c030e0d090f050609010504030f0f0b0c030a050903040501 82
    0x4100900092800c104641d440c25034200d40000d0b001c60901d0316400c0290040c142030341c1008403550700d0800060014000e41c2110b01c1c06800424080c815038607a2074800203440812541410030650541d00001a555000c000c030810803601c58582c2e034400700740b8029242c103401504800e225440042004e001403180050040e5041d41a02d00c840075454030300c010380e48401e182c0c01c0070003030030050003941c5110080000c10a11560199444075000c1c3c2e0350785503560301c0310200d0f2841c0c00b2019080d4028031500b960a0010a601400609500381251100c003100b425500143c01143e141c64440c503a00000d40b07080d076141d40078213030b0440b801c041d154542070007e0380d030b4400c0c2d8130014241503d5804209025020340d00c115010708961040e28000028a54010803030845401210501041d400f0041194103200c0166510200180c40d118074190640d2034680c0001c807049400c48241154000c1140001c2c503c4008901412100508130345a06017201613206031b5200400705002ea42c01408100071681e880f902030f16 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723021582 1106 723020476 723020491
    0x60903090e010b0f09130504033b010e0f0910180506030c240a05071203050f0c070309050a0b07120801150815091f05090906 55
    0x8500000380140c100f400810310102203d0498507000304160803000780125000001050000f081c1c98084031300702c000030611003100564594608850220b501c2008140d00d402d80005c80c910f05143e840318440e41040005002c5810a880790303100160481005420000d031072400400d03281441d903c0e48550035440783c220200b9000383d00c192003018081e1500802070304040b0f11907001c10155981842c0d003c00341104141001241c8003101008000f24029074a034952100b80c941880700000710000a0309043c1405c0c00100301c044140f40ca0200c1d8004d104901e15038403920a41001c071101e2480d600520380141d03200303401145600e4841c01802c030f003a11922184d514480101c0d42111204020f12070740701103c060408421005010304402c1e42d20a408015030500e9000c03900018813590001da07440b402401484084284440001300e90b000a800c2c103813032140550503c19590340d41c4410080903072 = true := by decide +kernel

theorem cover : BRFrame.Cov 722841726 723021582 := by
  have h0 := BRFrame.cov_init 722841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 722841726 ≤ n) (h2 : n < 723021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
