-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0892
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:31:29.916985+00:00
-- url     : https://prove2.me/submissions/6e53c699-976c-4561-ada0-1707a6a7803d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160251798 ≤ n < 160431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160253048 1250 160251798 160251823
    0x11100c020c030a030212070503120f09010b0904020609011d060f030a0510030c031712130303050601020d0f2609030a02070f050a05040b031c05070c05090f0708090c09040606080d02 79
    0x86c0000c00a000d098205031300480300c1203410780020006003401041c00780e55503008064010540107141004000e032421903490032101801602040c04000240e924131050b51803000c800e080c600131151081c0c8840e00310310102c803141c0354401ca001c01c8040c0244141030107544502909841045030792148044c4642c80d80071444000c100c0f06102009000049145c2482c04405142a248a080a2403500302c0c1002c00070884140903204205000c08041c1f5034140601604031034280043c2a0039520180b0081501031900290400d200c421024024540c1c240c1c448060454a0540810001d041c4452100e880c0d41c41903016174010b02c507002e00031134040c1c03081c44e140c0c0032190001c001c6400140703814184400b80260070b45281d4140507288402a003e43c2e2500300808580403540e80c15030391030851400004210740790300703700d00618001d41001441c10901403916040402814440c419a54030710402d4a810004c280c2c080d000350200e800d000c01c000c110707000351003914129400d5a200401d040001c980d91a40e4034402c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160254298 1250 160253048 160253053
    0x305060f13080c0703020a09021c0b0f0f0111010e0c09101d0604090f0c1e050603060f1c0305030a140907060521010323070b07060c11100c020c030a0302 67
    0x10700e00050780c2c803004062243c103980c01c2d0340181369250009110034510b50b1000f0740e5550001081000410400c000e4840d000c1c1002e02000310000410106030030441d461a500c3c06006100d031064600d0b0f000d408210313180d24000f4000e000d450100000b031500c5038180c07130b100c170b00805249010455030310b0542108000d031038a0742003030080c980000c02007020180000d03207800c2d00107039921145004100310f00c40c803115041c051140c0401e411300d0000c1c250100f2a00682044ca402e01e801c40c05d02a5039a21000c40343c0108003203e400d2032074443c90780020f0f2030601080b03001d001d04245040c0e00f002c0540190180d03100c0c4a0141c810800301c11341e4290646c624000301d40780301e01a004104140710380c50084014005101304d1482004042c964000728071340c40782080c4c000b940c4d1100c03401010990b801040e01d0740c1070b0b445492005044480d2504000584078054800000d0a184d200c0141d4061a88204440ca000103002c2048034042c0001c900c1c40300080401032014001402680007413007190030000b95007a40150300d50300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160255548 1250 160254298 160254331
    0x30a0203070b1003050d0306080f0c0915040b060d050f160e0907090f09050603010b010207030b0f060613060c05100c050901050c010f09201e090711010e0102040305060f 74
    0x6507450084030043c038942403d600c9400200118404000d40da4500031240c9002130510b0410074803038a80014085151101e502c00c0103096090f84407501c1d11500004105c0320000000d803c0300000f00600041f2070038507000800400c00341c06960003034001a018414100b1041c189440e2401c0c4000c50440d05401c803801318280c80f1030099a420071a82c415844441803400c030f2071494881170380140940d40360f88107084407510ba03014080c45240070f11542c101124240000c0c9485440d42d6a032100d216001811781840342002c1f0b001804a88500b01100c140841411440100c262a401d001e405d80c003100c001580c1c14031684001c0c103101f465600c00c0c85052603440e111107040c0032410740116030640c01010140015520740703511313441c002c000303003c0c84859501c00c180c00d6118406c41004010107018603003a0900c1908814005580c0403042e041118400308180d890381d03055541c00b00b0a0b12803005031030200906618007180c584040d101075001c0c0c02640c1c030030300c25104c0716118920020340500007615030500c9046200d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160256798 1250 160255548 160255553
    0x40b07031a060a030b0a06030c110a03080c130803041d0a090215070203010f060e040b0709050105030103021e180118050c180d080a0512010603020304050a060c0516050c0111030a020307 81
    0x801403c1030501514001c5204480600850031070506a0320038008252a010840e40c190740001c03941401c400558001c00b0385441344e807402800c5d001c3c00b501b03880c81140300040d0382c400c07840c11103002d07030280030188200c95490380c1d5000781d03050200b0501c401145040424011401328449070080011290f0000c029849411140d10740300c5859000440480c0e2540d60b9581c0b030880e0b101203004001c000c003001d012455980c50030341010b800d0402c0041112003001000740c0188041e80c3c10100340c03810b481d0155006000c00102c0850302c0710b1800c840e424280d00565000346089000304040d003441c1a10000c403481d50751540d541c3c256100340c903001c2d0380070240000c4c10300c00e4000c0c61b00500b107840100744c1c0003000040400c005845005081d40854145d900092000030806a643d04481103140100620b02d0114a90325003611066141d2900300700c01031840fa00d030440350300541d106900b5a042e0b050399174540020040f40340351295445048000460100d5181c11010340c0c14603010041d40c160054a801941c44c141440c2e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160258048 1250 160256798 160256809
    0x304030c0504062c06131a09070807090b07060f020309060604060b0c03030402040f021e0a0e090402030a14010b030d03020d060905010b040e0907173007110f06070803040b07031a 78
    0x5000c41d806c4903420340c3c50340d65141140900369212426110700c00b080072115003484082c00c0700400b00320500110310103001c95075900c41c0ea548115144544195100c070002d103010b4019028030ba00c40c044850000c410310855a00c04110079000b40b5040310304000701543d52400d00454002d24074045003503001400001d0140c1050707084900141114840140b0384214820640360581d4080e6104280d00c801066034921071380c1041d003840302c1010880d941c1c5c0c0c881c43d160f8002540c841906c10002e2104551841000c91442c00350806191080003c3c207880120305d0f81c0c54000d000303400c00031080ca50f00b8104980019004000c1c860b03541640d05120040e4030745070809130580301103140a00040300920454000142003803888e603101c8400141480540448965503080e0100c000c5080041d03d90b01170180c04418850300c502003101d01246d0f00611003151180300b04000740034141111041e58101100055240401412800540c4524411039507016542c8900720100c0440e98000b051036034000c40284906210302d0031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160259298 1250 160258048 160258051
    0xc090105030a060308031f1a0307050901020a0209070f0210020a080705070c03081b010506010201060b0912010b09040f030f0203091008061c050d020106051c02010c140304030c0504062c 81
    0x1041c2c4007080300b0b5a203980d0f455213588101c50658041c24284642c1540d5081c14940b44000d0407150b204041d9101440c070711410074032001c0d000c68203001000138081c900e0b900920074440e00781e400500c80201882c0c04940900350155501d40740f40180250107590003498a00c0c800d43d50b40301c496940d000075603510140151042c0c0d104600903200381105500006c00110650010030f45444002c1c40d0000304119a654642510710190409055904080d42031100e030303080d00141d42040b0300880750006d40360074042c42c4170300505085032130a4010301c002080105102d01c0315103400085210f584d901c14005c840040803038aa00030f0140301c40e4001440e00881d001c06228566003034001d00000c10070ba07100d82c0e40161070321540910200440342034100c105014031958080c813501008103015aa200e8488146856034486020040e20080c10b016010008405018500c12000011040003080b41e60320f40c0c40741050151420b4603c5030b83e20035410503502248449440c80004c2c1403180901c1600c0603800d0400c00540d29650 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160260548 1250 160259298 160259311
    0x10e160311130614120f060c030a09020307090b1008040804060804060209041805060705250602160c03110d150f0b04140a0605060909010603230a0507080703050c09010503 75
    0x41000c10441c4810b80e48500802050345000071041d0210f56000e00045c0c03420524040351540090124456006c000320f40103500820713040445a0b41d5a440d031900005258007000603406201e20360700411000c0c290b40c890041d0600c112003c6080140d0b0b070000300da00310342c101c23402000c0e640107210400030325018250b40d07a0000d104180250a004500011404450110451801d540c905074000020b1080a01150360400098035100e8a0031500040d410080740840c0f402d042044601e101803010300095a066030b030700c104525022250341303c0314104a800f03241a400300740c03030038408064201e400d0715080720030008c100e03803200031443d42e0a06080f81d00010080c00b56000d0110b0b03102c0714a24025074840c0320707040003d0518200c01c0e021f03044c0002044201d035119045140070b02c10030000e0480c41e9490320300391411140c0d5440c0208030250803a84448001444494103040d20b80031074103214a0140e247c111b580308901a6556200ba5a2a845e0807801d03118166582c15280ca01001401046d52003000150317031100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160261798 1250 160260548 160260559
    0xd1104020403061406011103040b070f020604030f0b01080d05040e0604050a060302150a0206100803040314030d0501030c170c0901090c050c0f010b031902011b03031506080108010e160311 82
    0x10b03500d072107001c1500c8119404480381d040300c03020803142d5a040089905c840c81900015400d00e4201030b04120140f150000240004020380741110031556600c0490b00950b0f8441020318210b01945000b12800b5020301400c2441c0c020b40300e81040745803042081c1e9084a511000d0700203540c4840061100804018101000c1b494892001201503241e00a40301e880341112000e20b07942d5035849070000e061601c050b003151181d050041c000c000c3c1e41c400105440503030350456440100c0c4e210729650185541f0980300700c1c0315001e05000c00081881190a00141241d90b448841c80b042c00c4446c2030b480d02d501200b018582e00402e400d00500c0580303400c1c1e02001e456019405c01515002c4030180d1a45043e0764200420071981d111407244c0b0090509011a6403180034010001c04180d8043d40040c14000a1358502003240c11610040028548a9000f01d480c0c1040740324010715094482000900d00c90090240c044030350f0828164161300c503000903203940c10003410701480c0221804d582d10002040801e655096104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160263048 1250 160261798 160261807
    0xb030316061404050303070318111203130906050f0306070c2009040b060f031603060f0221010905061909020304020102120a030e0d0906170603010e0102070804050418020d110402 78
    0x24071140b01031400789002e00d008585134648080020151181c0c0419200b0294007100c03810000340180d441064900b10444000c3d407448249901c45185000300d802442d5141210280042c2031000da5100d0010340d5800d483e6050b801920034107255803500b0030348805001a41e800e22074004a001e0380b0901c0c15000c04c020806d0010500c0300005200b114041da0299080d10049090010b10701d00714808002400064014200503441d02091071010401c80c8005440f141c1c503008035120000312a8115500c082001c00c040c0d82d800114451550490001d000e10740c3c40900d85008644945460340d00c080403d051004405000d50520031040301a410240040f41540304141d03003111040340030350140c40e0350f48079a0b800080388901c503100c052820300c088a40034103100180009120b41503002110300c1040034540f00083c0d15403125008240100701a50b0306242a51000c5211010044090700400032a10b003110f042c800044c02104a840040481e10020350001c41c54444000051040c030f00c50300c01c11401800181817 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160264298 1250 160263048 160263071
    0x2010e040f02130801090f08070c0b1207020f28170714010c21180506151306060f080c04030f06020415030605030705130608070602030714010b03031606 67
    0x2512122070121188503008907404800c0010750600800a1480100a000c810000d88481903000468074025203140d00008210b02844100078410009156a40045644040b600322030b8044640517252180140500178049540d814001100d0400c3e2000800f10f82803c1c508546000003440310200464031030200802900d185400140076040d024020035440e100a15030410403401c4840202480d402c0c0038100c0d8654030140c109258024490383d11444c00961b10399000c40d40b42949807142d00041c640d225100c2000421040862284125072040d10451440c1c40906907070002e0b2101401448000b600b04900744200c28410207c00c2d402c0300c1550b501c0e03480c09850340c07910900d0810712007040e9005900090b0401c40b0401c04a43c1e1102c03000e40b0724040040908020029840c0c0c0201d1084500c6107181d104107401d20055070b4416001801440c04844800d40e444178042d403130b80c0282c07205641644a2440c010318508041c001c2c00a6280000c000c1e42c505100c102d80c0180d0249142801d030781c804d0b51000925013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160265548 1250 160264298 160264301
    0x90f0b0402070c050102150f0604090305070f0c0f0e09060c0313050a050d12090b0c0d11040905040b09030c06011a0f12040b0a06050604030204050a0929010f0803090d02010e04 77
    0x8540d01403155140f4850500001901e8610640c0305860300e40080780801c00d00010a40145170000022039001c1040d1000d400c04807024001e50101a025180010021042114040b0907808030340e2182c000c03014442d5030304007040111508444d14101c0360400030000d450101640d0043d60b0040d071120185000928a841d583d203001ea0883c2c0480b0f1590040c0c000c1401241c002c100040701d22508a004c2c80342c010240e40b01e007241d07807014140b021095000709074100300007420741290720940d0f8010101a1030b99a070f4411100580710981d400e85010b409074001c583c500710040102d070800d6561400410450341380445400f080740d440f1440f100800410b125044910f0200700c010444508119210003081c20b06e401d1840c5c042001420002140d40381400411058880c50161012603070116000a030aa54000c4000040e00c000600104181d0f0320010031b4003400805011070a201c0b030172151150701340c0c0e22680004c00303200890103001015030040c45250305500e0141180b1035254810b02d0440903190b01000800d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160266798 1250 160265548 160265557
    0x7080a021e0102040e0114010e04150b120411030303040b041101020c040f0c032a0c0602090909070602010b0402032226070201020c0603040201410d05100609090f0b0402 74
    0x290594001408021484451041780d000d8511945124010340005001070300d81c403207141025003c2c0317480e90104110400d010034040028030900542a0b510007601100c07061034201194120342d0440d81d8054800c40b4100001030b40d00c500c2c0d000c6840780d140d840e180c5403a000042072400e154114880c0c0301e101c040e00d460324000c8801003070790710300d011681d01002000a01594040c01819104100300151008103035036440700e080c000491410714101352041428890043d218110741c1c0d54208207488144181d42000040d85c000321811070380200440c4900d502040140d1105590318842d00c1056182403001004042030f1900882c030500c0e4a2103005402e880c2c00340007542e82070035181c143c440456048290350701840403000552003120304910b1031a1560029114100318801c1e00d01183e00184605581844503a40c202076003165900c81454200b074650044595002ca02592413441c00c2c6404105880030004e10740c02528040e4540540060510048800a002c0b05400f1002c2540302e2195031020b071107505c01007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160268048 1250 160266798 160266853
    0x1080105060f0d2a0e03060a0f0e0102310302060301060e03160602061b040e0a050c1204060c1b051f02040f080c1f020c011407060f150f060507080a02 66
    0x505103a0600f110411403001300070800080c010056070f000580c1c1c0c1c02007402944001c2030308002401d6207540220000800e40703910107505075880081c800260003401882070254045408a03828454801c60300c8040c04806c03884002c1d04400e040c401800f060b0300841c010841e503035010382140c11100c2c0c07103800e00840c0040344d445040581c200e00188002c030300d8590085078100f458030004a280c00e2414020900c6000c0081520000303999680120f0207102c0f0040480c2c600d50301d074504078040b40c1040e062180041500d010b100d000705000c1c090001d407036030f414a0a030400a4000300540110400940c2c005488024880304021051b400c110100b01c00905000301c201800d4400d0003001656004010301c103100180c04000000c0004400d541c62031140c0c00a03a181e0032400038640300007540e420342d5542d0141c0c0900c0300010441424180083e030303214095400391464103140c80261000b02d9542040c0e600030300890140c00c000500400440005ca880c00e070040114000c2c0d40b041b248005801c0307072440840590b0b004070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160269298 1250 160268048 160268081
    0x2030604290a0501020a1a0402060909041208060a0311040906020c07171015120f0b010803030402040f021303030302130909050604050d09060509091f0b071a01030201080105060f0d 79
    0x800c8050030140102c00c0a004203000030040070700180c0380c543c0d050185220594401c09020006011900c50b00165001801c02400c0420f050403c0c0c60885000400c080c80a40012411f900145552505041490803a60080d50020000200748107100c040c01d000c11301502e4068003080880365500080141c01c00031316400388003c1c150300081d001542403218407110740c05514148030b4070000c2d11407010046003c071801102d848050404500c0c100c60094501d0b0b40142c400e002650000030f07a6600800194403451003241d04000310280074a80c0c00490103501d581c00c0001401900a2001a0084e8003c061540300b42807180b0b542982c1b2640401940e02c0088220360315003003402070008100701001a203422511300e08040c0d68003803e2000040c154000c80da04144035010305004118211081000c0118440351005000c4070b0580341e94240c4442d81c02200203c491411500490099564415599042e00d50596400c0003692030641000a20b410803001080603580c00c0084003d035800c80d100e8000700990202d039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160270548 1250 160269298 160269371
    0x10392a02010e06070203123001080c0901140f0d0503030705040f0b031b0702011101050c0a0f11060c090312070309090c0f121805071e0501180902030604 67
    0x1050b40a110b032269000e06030501c0754800580d00842d421401c20a640c0c40300c0d03110811400f00340b044d0001e0007040c154211480402e08815008a42403d0690384040c04846807a00c610007070110b401800d200c2c0d10040400740c80f52807890701d44118030014072840117003850b400c82095202c9a0640d44240c1d404000b060001a0401810020400c164000c04c1c014034010709518081181610742c007200341c0c850b00001e6002039044210380c0140c5011480820700d400811542c94040d00c0c0d605603502c043d42c01804a800004241e032014490b40c9420001d43d414805400d0a803642c43e0414110380007000a240d250082d6001c02c04615810750142001d14000d0752100341d10f51400c1c509000b102c40d1784007040c1c100010303851a001c480c0d40010b4403200c40704011500240c01e51100860301070880c41040003d2a80c050400f00084510312036201e038085141c06c4010811060b42c90b401521500a0451072040100491408001c60141036014650069000d4000b04400c45c2c6140c0c0d06420b8408840c00003d006038480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160271798 1250 160270548 160270553
    0x2150705010f0b01201c030f020a08060f040605010c020d0c0305060c0901030c030e19060b030706020124050102060f07050904020304030f0f09270905010c0210392a 72
    0x248000f080325034210022440d481740b07802d1a4894669204100c050400c00103e01d4030745210754041822107a100100715210b041c500c02c02803203501d00f03442d0305100309040d6126001d145001e2081c10100c1d0740503102d846d211821a801d001080c040034405650307140e0740c0c082c000301255060260074861402c0500155a42c3c3c5540005811542c2d02c1c1059400c1528100041c5821500020054140c0301c401e00e20b03502401e001d00d402d4010301009140603400d405000c000041c40e680540200e50035090b0708203400601d0f40c0713540e0220311507c154481e00e4010707402000440c0c442c02031318402c02c0c0c01c1507040c80e042e0f1500c1c52060100d02a89c1c410741c0c007180001c6440c1813007030190390700401c880c080c0e10141c94803040c07482c641202c0b004c00c0c01c0113000f4618000000200c03403401542ca03070b21000840d0341c007500a000c004c070202006520b031306e840452074002c83c1c1062a2071080085065030707240c028400080a0304000f122503842d002d081050402e1005010000c8003003440d820345002001c0480011980c4807810100300e2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160273048 1250 160271798 160271807
    0xd03051b040303081b030103200f060d060512030903060c0714010c05041e0b030a0209030c0a0905041b0308030c03041412180409020a09020328060302150a080402150705010f0b01 78
    0x511408421034141b006000082a029044142086a10602c2610301007d4001000200030a203042e920010000d241c0c142d44c1c1260b0010800c8403030465091101c04201078100781c0701e00c681e24140f41e00d900b1800c0050071100c8914040d02c011400340041e03500c420b41c000441c5085540d4542c2c00404900e01140411801c91000c0230a442c0c0c0c0e0041211020440c80c25880c00c02d54040506030107141c0341c021030b03052640d4808011074a42c0031001014482640e0b6118180c0c1c0c01010302b03035000d8a200700c010b49040d00070250034004100302c0341c0c8201106e246544a009035031942d007001c0d104440b03d040b03544200402e00c3c001c00030140941d04503005150f03034510441025118045072103105001d02d04095040000da40c0b0b900d14034086606151000d43c1d259182000145d04800001940711061448013842d40c1c1c900d103981c0242d00392442901c400f80c4107000c2c80b4a110060003501500380026815800150050402e40c07442660f000d00e807940b2070b0400c04a551018256407004420b804540d42d00d0141f0300c0d10b90f900c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160274298 1250 160273048 160273081
    0x2071b08100c110c060309100f050105040c020706020a03050d0e03030a0e0d0f0203040e04051c020a0c051c0f060b0d0602190e0a03030f05091c030314090d03051b04030308 75
    0x20f042c01c02c1c581c002000041e854207501d504691250001100044a103030081c001240507810783c1c80100040740c1c2d000d299074000d01e020702895000358980100340610340c1c00014070605441007034000700356480803030b5000c4602c0e6011982c43e00809440f402d65000020f001c001660241800340300c0400d20706076a18921307260280c84040303401004001c0740e00e1070f05075802004a4080c6c5400480c04590341e07850f0f0411502d0a04011000d103803035111403125a141a901041140f1a24801c0442d001e006035680d080103041ea9101850801603d44021210700048680540c406403a20070740020824440580020b0302007120400d043e070f543c6400203214002450554140c07800b844c21410020440c41414001c600035004c940802014030198080c0b4500c0c103401001900d401d280018402c0c0000f0949607000c00a54480c504120701103810704402600720004c111079540304020b12001071124541c101d030100c02401d80500440c00542040c120a04000aa10000c00195000b0b40b903020490074001d840b10500c589 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160275548 1250 160274298 160274321
    0x15030106050909150a030b221a011e060c0203010f060f050a090e031c110a050c06160e0f0a090f09170a020a020f011b1103010c030b09060402071b0810 66
    0xe00c0c084c025241d55a200940040e85e400200740407131582d4154481c464003140501d08004440100c11180c20810108044030300107002c0349014800f0303681d42c03508020a1100c0c075030089480c100c9440511519100d043c034580c1240c0000c00116203541000010b0084807015000f210000401c03000a000900749038003048014030000408215107402804090340302e0040e0f0241c800a541e5070003003184441a181c005060360049846116507620075804094107580c440d503e00c210b203005510008403011070140601e0020715040e2152818100d00c2400c1001c9191000480e90380a0026940801d05120740d12a11083c0e400e00038000582101c1d50606440c043c4504191040e440c1042100b200c0a035808540029425415550341d83c1801c0e484006907050718204081003a184640301c4042c007404011481e100c00780009034000c00522004400c02c074242d5504480c00d503008200e02d40464418240760b801882c1a038010744102900308040840e0000b0b2015560083c0a942c0c00288080c480314198400c040300d044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160276798 1250 160275548 160275571
    0xc01030c02060c040608040c0305070e040605011203020a030809010f0e0c19061d0105091c030306210b1314010608070b042603130306060311040905031815030106050909 74
    0xa0201d0103244113100d1402210308105008001c0307410400408506005598010141c1e00c500341c4a14200c0216401103405503603007030030075000086030540c0c440101c1c106501540581142101500c0560b904000a0820405990381d140000c550234118403805040b01109005451500760034401c010400115040b0030440c1c0035102010032500d81c224201940da20b0810804000804120005940c41d00400070055040f00c01c0481001030b40300810180c101c214840d80b000c010301078582c003182c0702c43c048592995180c000c41fa038503200411841d0783c4007603021030072408007515060740d40da03106038408451207012040c0e134513410301b03100b900e200b4440c9038054150444030070704092030208442102d10481292070130b0380d00030400c00f80d4043c1d0140110740001c0074004800c0b0825070340707140c88030007000039110550301c9690441004050b4078050040184558204004600742800b107034000c1c00000d140e200e4198482c6540700300c40c129181e0100903500801c07190700c825864441a005010440070300426070740c0242d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160278048 1250 160276798 160276801
    0x70f03020a080325150207080304060609020a021203041b0e010924210204020c0706110102160b1e0f06040b0a0f060e0d0605040507170705030a030c030513080c01030c0206 75
    0x503403c402c2e08000070342c132146600c80210050a058024022500481c90302c2030002500720140186100194021445180104000b039a9514040200d0141c05161401604041d0b0208405c000035405075400074014021001e40036020704c0341da203045a45034030156103941c900d00104405603842c82000307046e140c00c1c0b041e0210b4290144280d480c146a500540328500b4080702402d842c18501030112694940c090011540c904440c542d00b655101181319080010300c4e0144185210038060003945c2d1100c01a1850044000003030b905d40000000042110903a42d1a10301400a9044c0308400d160146481e1440c0d40c505041680501050f10701d45400030f130142a03a018100b05154030f03482804100d400d1460158048541c207000110022041e40010b0400c90400d0203000c140800801d1940031074000d401011407580b06416540e448080c648a05589900002c56603408a406030407521015446890414075108503401840d01c1c6007420740020007079501c00c00d4402d0b020b58141c030820390b420145000030140d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160279298 1250 160278048 160278067
    0xa17060709080706050706150801060f0807051806010210050408130501080f040b06010522051c12050d1b0e01110111042102030304060302071b0b0d0b060c070f03020a0803 75
    0x4a403294800c04c2c0030498009102c4061020310342c80080c00520f040032021199942d0b000341d6020784943d000b0800003011384c0100041103040060100d0445c1c1014081e450402c404120001801000410351810740c0035440c028012410b851250f288681e1140480a40b41e103000309000f08000e038190801e6041c08254001c0c420708142c4810354542c85640440103e400e42d503640e0040304c02e0700403440d2509074020728410394000014002d1090b0151082500c02107030072801e00541507160002c044001d01441d90070403480b50700601c514022702c640217600502164012114450080030500101a200000c0b90344c0c08640c0a9030340040700840c07240d01080240311041c0c3c100c0804881d44118405c030150308603481140280c041c0e04030442d490b81c5030000c3c15240c640e0f50300c110290207580050400c99103007040712500c0c601843c0000c4c0880c246d401c4d048295041484c14082100100040312220f54405824401540410b40c00c01c0714502600803041034441c4945944107001080b2880c0d0040002500184016040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160280548 1250 160279298 160279303
    0x606050c190311071d061906081509040609020f09150d14030406020304081204030308062101050c09090f01060e010807050d0f0504121403060d0c050a1706070908 71
    0x2030400890010800201d020325003a00e458442240c0407205000703410000503003c6400224646044000c4203400c0c4e03d0391071000b0001c40183e4400404c10080b604030701408854841c03c0002d50040d0215041400e800c441c0c0f001480c0860211011110031740c0701c242c820114189139244c016042030641c1e00e04a0ba0501001230307185200c14030032107400b841440000c20140101c801c44024540c6141041d2984d498640310b00a4034ae0340316028500c2203226406130442e400845c41c2c21a07040300d80551b2004020345542e000c0020b030980442400c0c02000d400030700c20759000c0c028850380e4002c0d40c1c00d8a880740e80b810741340c0c01c0c80000c0c88010b01d92a01c40170504010091141c0050641060312024a042040d5948510083d074113030081035600c0c0d448070305e01250b40b20007000c03541c407081c011805003006002880c0d00c1710b001c4038400c0301800d03005031004051000c0303121030604071340c0c0621080c480d4100604d038a071164046500c2103034503840001b400c284288d900d804001d0500a00d1b80080c5207180101d00745040808a82c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 160281798 1250 160280548 160280563
    0xa0e0f0a12150c08010501021c05030f090a0c0608010501030c030218040506060d050a05012103020715020703050102030915010e070207180b0409050f010e03090307091a10050c010606050c 82
    0x8802072019500003041101800300d40c00c254500d20b80800c41c4043e94140285901c1d002d003c1c10380540305800981ea130703240c54080316146c489a960394803803851342c400e0034000d90040b0141030248a8884c0030411000600780000d0680a0107213540c0d845100d61400c0001425502c2804042c82031600c100600b440060b040c896011040000351008101610340c200811554803450341c403510b20b54681000d00420402d150811412503100c0c01c1d10300d00d151021181c0942c44980100d0080150b441120700300050000101c0883e601105401540c000340d07030f61b031126400c0e03a1046447e0602e6401004440c442d48180c182a01d01606500510b18078034607201c003019603562694010041550f19140030402c48001e2608000311201e4007800901c00b004503803518540d9414801084981c6509002001d04003d200109903054007034010000e00d0300600d01580400200407104401c216a10a06101d82e55034a0f0702800562100c0e095680750b80e0707401c201611900f162144e4001e80e081042c200404003241074006140c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 160283048 1250 160281798 160281809
    0x1804202707082a07052406040b120303180c060408010e120a0207140a030f060b01021015030f08070b070503040c0609050d08031003050d0e0120060708100503120a0e0f0a 74
    0xf5a8482e61414100e00c0c1464110210f41400d042d0b00542d10801d03016141940650002d0f00c00380b0801d42c40030304029600700c0903013030086d03103500034000240d2466509201618a0040806403580e40c0110300120b41203901c29007201c0c1c07a5030745956099100b0700007044603540c1034220b04007036800e0400c8604000e407100c0c1140f24800b80f114106104591035980e48400500440e446406002945800c5ca403e40c00391500560050140c052001c0e034103c603c1950162154038007111608505117821a9a2003208072400f50090b20092001c0c450040040d0b400054140a00701b00e071186500c1746014a00700c07c0d030103000e41143c1c1c10000c88c65010082911061480360800382c1c402212038813541c0740d40e58240356458a50000d030071445000171041d003042c1c20810092040900b80e0350a44c00c0c01041c250040c40c6c4003440034070b14995108030300245c1c0341c82c40380700015001581d504d85060800c4da500000303482c120006203114002c2400141c000e614a411100c0b200b10070300180c44e1710307182103000700000d40b0300030452003503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 160284298 1250 160283048 160283131
    0x40302030c03070f0605131203030c030b04050f010909030e100201060302091803030703180215040630090305121006090608070c03050c01141005180420270708 70
    0x419014103c02c80b0014040c14900000e41000700700381c09d00174050f00800450001003450039840d0308407410709000da90b201d0318504603092161391804280d8401005158401e03401c00215066840e001c0d0744081e510f403801900e070b90001c103085065004110f015600a04040164007214a078000e00c8034010003582c0e800300b254100007500f00e035524400300080c030128400a40c00940c0d4400111070940040241040c1c90841d80c41444800348080031008280c03d450318070f844015028104114440190015000340d48645412802c041c3e0400700300164000c143c3d101c8402c00580c0074140541c50307000e040200100343c14640200303503040002d40680a44100c0801400304a000991101030303400941040c80c0b100070a40d034400c07452500202c4001c054145000e010321442542c2030040907600005c0c4810300039274028403202ca40c15004031f440c18040020204644d041850741904541e43c0d003000303440e1901c9403040b100107a02442c00e094010720781e40004040c030351104200d0321326000c0a07103401c1c20518134102c811031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 160285548 1250 160284298 160284307
    0x6010915022a040914070504020702011209020604030c0902070215073906020307110f060a030911120604060506010212091513060c0c0605031510030e1002040302030c03070f0605 78
    0x142465003205010041d0b8101307082181c00350402403060700318000d46201000341c0c0c0e240340d02c1d042000141e00c01c111010b40041c9000c80c00d040b00717500c1c5500100c130440c4010291441c280c4d49548031001b044442c3d0002071500d9000c5141001e500b080d0420340e2402240c101c250b860034003541e552510705114a03c2801003405e8080c68070420385500680c100f1100c140c0642070403104e588490080d034075807040703008403104900382d00d4078201401e1481030328000107002400c843c14020f0b5420304900038405540c068444d032001c2d50759a04552180700031810700d41d00d22405850186083d0800005882d4013400644c1198041500c0040000410040d1000074200311418101001c1074001070020b0b001d0701c0c85602805117440400542c0540040c4844100d07481081e40181c0103aa5080030380c0e20740021140e55040042c014001c010500e40200010008581c07400e00080c18a0741341046440c29456807011142258009401d00a44c60204100c00720b06404030028010f9508100040080100902c6404180f000206 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 160286798 1250 160285548 160285603
    0xc0a020a0e07080a0615120e070f0317040807230a030c031e0507180617031201060905090601031805010501030311100501050d0201030b03120703030510050118030201080a02070c030b0601091502 85
    0x1c00840121410310111403010f2b4940101e00400d80183c80704440468550100c00180380c140d400362421107041901404001d403501e12440c211200c940d030354038002a8010b40d401c0c403a5565404410145015041510241d03080d4600007009000d200f110207030a002181151002410008089050300c1c8910403040100f6490a048800381107903421907410002062814411158004090400070001d80d83c108196641d415081e20542d6142c00780980000c031070400035045502079081401d00081d52003255031001160346509003121030a800440004403800d00b1303124003a00400007021940072100040015500d0f0400142c025404004020f051503100c1055103a0741c1c3d03045c480c500340d2000010440756140018034005004080403038440780d1b580c3d11108041a40d5205902c0941c5c0c03100591407948400307046030015640240000d002d501010b400f00f0038200000c5208039207000440c41055a08010300300240007614444140d000a039403940c4010a1000c03ca03400144004078100c1c061040742522a01d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 160288048 1250 160286798 160286801
    0x1020c2407020612070f1107030b18010c031e110412020303090a03061b0f02060402042a03090b0a27020402040e0c090a06110d050c0a020a0e07080a061512 68
    0x4502075801103000c100c8105130042c08500512640c001c0d9180c040104074501b0940d5080030021642005138031041c4113100048d81000c800b60001c0400702406a01070360380b0300042c00c0d60604d520510000e6103807405003080c0840b081c0b0346020000c0e0300e5010300c0006c0702c7c02d90003190f40c0981c0c0716000d1031484043c402d50541d2404d0040710300b56240a8084c11010f503c84c10f20501511005103800429014001200a80c62041d607039410440d1059002e000c3d01d440311740811003c2e00d80c3d0f00400b5450600d0b502c01c1e0580e0040141550001c10042d01e0201d00d5182e1801d18444109000b40301b040d100f8144509040c00082050309103480403180b101c2002c5c0c1c01000d001040003402160010785010015105010b40180410302a03c0340b01404c598080300e06465650172603404940740520391055000c40c4a508403d80a03c01030404440c1003c200c480c0c016464000031119005540064040542481804046544412615401408410f0606c8880e103051810f060b070501080c0200c1c1006604201400d81ea0405d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 160289298 1250 160288048 160288057
    0x60801080c061e031e0901050f041209091d01050c030c040302060706020d050a0f0e0a0803071b08120103030206070503060112050712050c0405010e010c0c2c09011a01020c24 76
    0x240b4074295100d01d485104001407104010140c41080d030700f0302c0001c6c04074005000d580d1040700394000c141001c5e140c42e914446014031100c0e00c103083c0004090080360120880c4103050740c0b00500040c0d20980c0c510360348000d084410191a0080072907042040001414122040310b045990640300650355810b80e051900003801101c030904d11060a000034000b0105060b084910b4160040e90204110400707003d00c0c0383d40d4512444003c203000c0c0140000395a050003851905507007e4a441e240c0032902103540c6080300f0380e000300a0b41221b516942c0c014820700d64100900303513100115003400340c61414040d0000e004c040500550349411511000001c180d94451030b0310007900540c80209001e03038203144440c03072516006401054001404007100305495032180305280941c039000f514180000d410150702904c01d9802c5032100024100c4400a0003210688110052190180d0000011181c5007004440c12501ca542704883c11580600884900d9558001151401160f00060070320761a807607141d128118002e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 160290548 1250 160289298 160289347
    0x70623180303060f1021060302130b01140c07030f0506040b130503030619080a0501060303030e030906030109022109211c0b2d030d0804050a12140a0e0307060801080c06 74
    0x729481d0900c0d81d0700d03240c1110062343e200700c51070181182e040c0384000403528111016800502072205040b11051003070018114002140c064039400d503103a403a85254151038400032500387e80403000304070500083c039901640185080c460240c03a564140c5070a6a00c0c0800760580340305081d00c0740c507810018be00c000b900c4010262001502c100a0031810801d000740990700c42034000c00e040062040c43c0791004011122009002003015082da4206006039000b074201503c01801b543e0640000751b8a06100c1501a12031403180009001e49149086846031504000040e06407078a024070001c0c072403048001e03c0803810305202e4800150912614006424060144218111510b034444840305a10841e801141a501d0036012282e070748010480450344030404490281298200001c075a000555401c2c40e200740c3c510a00e8044030481d001400e000075135101800410105503e841a12402e003410f000c207c00403c094205080c1d6585800d00054840c40507180e8240314041c006150034410ad0001e081015489 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 160291798 1250 160290548 160290587
    0x31503060612050714030318031002070803011409040f080c070b0f040602060105030c030a0b040c0e011503290d03050708030406021b1c05070623180303060f10 70
    0x5649012404180342d81200075502e50054042c041100ca0703001912081c00d440c064002d524001e28118003211000208602513031601415440c1c203e007511074009002500d000300b02040d0ba13035241c4076000300c1c4a18271921550003140d00004100214001d0b40200c1000d54000f40c1441e51003101c03242e1507003040b01035001800c0c0d440001c515a0039031240303040070b00b003901c4c102e40840d01c3c1031342c0740d0003055600e202504501d641980004817000c0080d009801d03081c0c103e481210150304580e107410302441c0b020b509030440c2c1d0500306508024520780b5410301030036046040700540d0b02c142680202c0c008242c403208400c1d10380a07681210380740c3c1c101481907044400071034000c203803e0f03260700b481c0ca400383c081e500000105449000d000006030360004049400308610b050b0355034454142c00c0400d410350f15504642c80a407803c44c0c2c0c428082c038403554080300302076a0880d680501c0c02c0c40e281038980418000c06054020301194420700070080e058a03501491100c090048a021441c112400c008031500c0201c041142c9014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 160293048 1250 160291798 160291811
    0x7060c020c031006030c05042004140109090b0108010510121d06010f08061f0302180901200d180f20010311030f060102070f0b070b0901110301030303150306 69
    0x21680070544070000201182640c240c8582d038403001c001d45185002c054000c0950a008006500d850b900c0040410811000d001e039804040954591580040d80700d0b581c0074204c0145201c2c07640e405a0102e025003292041007140300c81d0000001e00040b014001d060159440c03182c14030b0828010303150745001c025140c2003031258140e0407800700000c0103c0c0714170358002c2c0324000c0045400a048c60109042e02c0154000701340c2541c85000b505c51007110040180c040896211002c005615407040d094032203900412183c545082428040d03013140c00c484100c44282e401088a911090f0303250342140d180ca4008100411010001c2c1114140c3c9880c0c1c0d44010302c1480000303403090421415207401845940d0300304456100c2c020403001542511410b442c0707070301c0301e043c1000002d403103c2c1d200706840c0e040300b17040c0304072182e00b611144400b01ca00015004240e81e4100418120200040c05102940c0000b9907030003071003003818680b010400c0f4081808000e09040d11046000c2d80960500c0d00c2d04000e50f0805424083e9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 160294298 1250 160293048 160293071
    0x9040c1e09030b0108030306030d030207030e060406021e1f0f0612050d2a020d0515090c120106030222020d020d020306031c0e010f051c060512010c020a03050903030706 74
    0x200c0c0c0700e480101c03a08000800000b81100000c000d4a125040260180c014061141800c40080d0b011910071000e200103402c80d56401d444040181001e8403190b0014010b822009001c480d00c9107180355a0681d96110000c0c07030b40310b2500c0703500218815605d010301046141c00051180d001e80440c0d0040c0e03410381080c0c44a64107108000405070020100b9071075112202080240079546e29010b005001540c40090240740c006003003151000020078021025250b03507d605a0020280d00c0003558407007080d41c80188800c0380340c40c04000502032078800b03000030494545581d0101d011000b04c0703030428010480401c040143c0640503011603c5501d24484e0031540c803121071003000c00039017003918182e00038827408608100c00c400d20f074940c00050f40740c0d03200ca0307090300100401150245650140d200800c0b00504c850404251032000200040c00d40303140125416040909000c0765054180d42080643c0c1000381e01080c5e40d4004c02c081865a03050710b4201c3d034854101000c00d04d94801c404004010500c1e11030382050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 160295548 1250 160294298 160294307
    0x309050c1309020a0e010303080105060a0c23120408070905070504080d0c12080f0f0603010207150e060709060f050d0b06030f04170c10020313020d030c021009060509040c1e 76
    0x440c1c0f4030031210110f09545440c026500a83c0901006001c40c41500040c0f20754a4444040d0060030b40300d2138800414020341d603075125a0307a0514101400c1c2c00c0415000001750200f0710401900502041820341440d1400c207501c2e0342c40d08584201030000b80d4480103c1d003035601c100c003220040c6c1681021034516240f080001081380140302000e41341c1a5500c661060600c0c81980154040c03404c1e081c507405180c8610810001e074403005020564103642c20064000040d070400c104004d88003d442c03001650748440421030303042c00b00041600c820002d00300c00034004940c0041c5c4001030002c0600e4203580310341d0803c1398080100a05217040c2c0d8040d0703000c03003042408000c0c10b21240c031a611070007182a100854543e80340c401e0092441c000c08640080e4801040d0342e100d9405141c0c01041e82105100d0170701550041210032400030b03c2038002825021541d07040d401c24014018218003e4540700100d24a03150005210740a0705c000d043c4590340f105c9260700307808d11078900480781851101403080310455410000d071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 160296798 1250 160295548 160295561
    0x80f0d240f050f100327060b040f050c040312021e010509011d030913060e09060f13021c03140d1505040204050609010507060f1b030b031c0309050c13 66
    0x803074500140c000480c00c1d00300fa074600d860072000500484c0c1484a071280580180101c421302c01c0000d00b140d0280714a2203000e101b40c0016500410002034070308103010078041a00d5140b602c044446051105001d85544002c0445088030303080b581460740c000c01c0c59800ca0070001c0d10105000c40d0440070005501e18141948518000c6c200b80d002006040700748940d4507103580c03042c904c04200340c000348108041410030314007001c0030741100440018015210484110011400c0e50b02503060703844038040240124000e010349030403038480440c0505800303445d4001160343c01849980941407c10a81c1300d405c041c084e42000c0f40490009000d961140a1198294010440c3c1c14100b006018540740000e520304ec60b100319800e44202921039450150a1001515158425007084412a655a03402c9034201081c1c400c80501140c020f010b041000003c3c1402020f98000300c43c00745c8a80c0003c0a001390505141c01e031039035401d00c2c0e41030115400900342841400d0402170b81c2c81c9d58102c103240b218105414420344c40310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 160298048 1250 160296798 160296809
    0x703111b0d0816050c0f0313050108130b010902070206190f0e04020304150b120a06060501120509060403180504060b1e0f160c2d050607080f0d24 64
    0xa80c00d1400550007114044030a544100310322030f800c200e0380441071240d0011300141d840041160441a0780b0305040d89554400d030310056000560750402d101541c0d00c0303059180c102e04560600d0000e05d200f511800162081072041001d02c660000710320b821919a44141c1c0d01c03e01e05000700e121103540045010301004550700c81c51000030113901c05002030703103020f100742d034045c6412030248490940c0316417456004120f116551640203503510112100603400b00329041425201d0f070000709d241480e20001420b0340c04042e518455640c1800d0401465010016250340c2c85a018942551550807403030034007207074079441d80000e50003508241c0086000d51400000301076406550f034200300f41c0c540c8800510464000d0203082c141a40c0c00300b050304000107460820345140741c056412101310907134543e40e05003603d46040303450641100341d40c4015504840c1a04800051806450140c6081450340c0ca030112489400c640b481500c0001c20700d4420895540d11401842c90001d5544681c04409128140c50f06500c1c1b064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 160299298 1250 160298048 160298053
    0x1d0d050d08070c0803060d02010e130234030c03230403110d05190303020d0e0f010e0c1503270a0b090111030c0d0b030313060206060609010c0b0703111b 67
    0x4102190302c00d815003101e80c4d410070f003500e013035864460403c1100c02c2d41d44401d0303041040c1100204905d85e1101140c02c40e850031079100680c0d0351422190b00312140d4103561302100c100b1700c1f080d03400405d002c48000039402c076916140103131240d10300c1e240030b1b00c90b5402e80101c040082c22035a85a4418074400c4010000e99000e100741c06da1a081d031608009042c070a2410040a94220f16400b13140c0281100e02d110740e0a00c681405800c20200c140340008940982e280c054569200c40e4810307561840c284552459040528064159800c5080200e4803100504d072206400c050000300080600880d403c20507449038410607402d080000d1000c0e09030b13441c01040003d9600300c2248001c155403041c14401c0e0300701420340400c100d08669869002c42041c1d0003400c060908180c03103000550b41070342d0503c024440018241c40e205819820020020f00d01034000303014234025002000070700d0140c1c2e000030320007180e40d9211003445416900e954080b005032514034800e0308400c01c04035800799081c20021010845c3c5210004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 160300548 1250 160299298 160299301
    0xb07081918020103051b0910030e0102070f020108060321181201051b0901090603050a020c070b03011503050105030309240d0f0c020307030e040b12121b03070804061d0d050d08 77
    0x4800c5100c060304401c4000d1002000a00d41f28100803410210280e10381c10001003c0e00d0300e06141d426a80301c003100300c1d0100c0c071040c600011507070414441500010142c00070050085400070500d44840c4148444541c03a01c04140040c414200e2442e0b10304203000a0b0440072480000c08690740609070903a541185484030000f04603510103030000707540480c241603507204103852600c0c800754003c21000d0700681d032040e02007204552050042003507500600d61145030598030f40c5440c0c0b07003502e840f05030103500c1b040509207001041150341c000140d40c021300c403c070383d0300481400c2c1005106201484441c030903440c500100d0712a83c5051964441210980040c00c1441618120b0383c049031644600a0010003044020015100324180350340301007000341014012420f545000c024042c0741400703070204020302c03a100060021946e07450301003109008100b20011410a2856600c00b20039002d20b0051404100030707046142080c22100a110b191a074020305841d84180e11381c01d1141e1501c8a18040c0d5021511640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 160301798 1250 160300548 160300561
    0x10f0c0206090a392103020307020f04060312080105030d030c23040f06030c031a130509030d020d091b030210030e0309060a05070b10060c1b05030f03030103030305090a0b0708191802010305 83
    0x2562171018961590185280a101d0b44c2002290078480d02000e4101c0c3d9501c0c804400241c250f06110788103011a140c4001d03a61522003010329020300070070700600f01804c12a8044c00c1c141c00c02400260f4034204134046007489032010000c0d80e64001e81e8003e880980700040005489601b680c1302c204140340c196004e011040000c174a030742d4401c0001149540000c00140703088400d025940c085a004030184094074600121201100240e0b048010180c08156440e82414200030203103070600f18540d500b807814200d0901e941c0004980568555039a810b00d0b48542c0004030902050003124030044000302841c1d11008503a00050164000d080201d40d080381140c08a001407603462240812034990b665102078210240d83e80c12144002040002035034445000c0204c0c10756030502c00c1034070034464800119201d40c510305008055801c0940b0700080c42c1c01040c10300c1d011031000182c4a62007012810011a29290540f02001100c102081210707102d20305003404044484840b00e4000c258001d90b401d024648401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 160303048 1250 160301798 160301849
    0x1a06160c063b091e0604050f0c0d0b0405010b07151104050f0301020405030105010e190c020d08041a07020115081f09030917010f0c0206090a39 63
    0x1402254466800904500351114107401c0b860b400814864400360382099a001c569900000d4a0407290f40550040c04034202048051541e03200c0011a01809a800c11000c803c03003284000e05445010413000a1055004102d901b003000a003001138801c00403980d5074820689160010709040343c7c11104030b800860602d03454004c4041c0343c940c00210500c3c20b03140004000399041414403054142d5020703c0009101c0d0b4084c0700301d0b0300a044805000805203042c00d00014112408603030481c04070f28044260002c21360010304007001490509182c4843e895500340181004c04041c4100443e901c01c000b0052041d40c1034114035021072034801e01550306030f240c940854550500800d03000740c4401d020415060603d1030b4101c8034815005e03040c841c2c03119444800516101402d9481040b00b07a44406800040c2c5141c0d2007090500c0483d403014183c6c0e81400c1c038050342c80c0e85008030050000c2040e252001d2485804c5200e4969580c040a04015142c141c16412410705d6024450402c0c0c3c3c01e58001001c850500c01c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 160304298 1250 160303048 160303067
    0xe0901090209061c200f0607080306010e121b030601090b03060a050a020405090103030908070902070308041202010f021305100203030702031207020106030c08010504021e131a06160c06 81
    0x701140e002e66240014840d584180340c484414403a16140326402240001481c0c0c0081c00c0da12412a003600d40c80414040703d090180105801b61400b04490808294020142c940000d800d01e88903250100900000d075580c54076070703c424900d015a03440340760f0100d205d41c0d405840240503003e440d1756030b9070303080c0d000e00712414003a0480e0190000400294450256481582d0208214500505064845d004191580001d0704100c0110741500024804440d00700102402080c03886015445d19041d654010142003010300010042c1410400c142e034103134000e4001c4800715025120071500d4215407401c1881840382482a24005d030403a150219406101000b124031801030703034000354035004242c0d001e1950018014689401c40d540e07510088001540408100020000d1400109142c10180100045603102c000c5001118201554000d842d4903110010003003041d00a03800144514004541c03900d20781c641c8056507200000003090700300c1c1081a2007035040d55004201c0008601d4541905460b018403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 160305548 1250 160304298 160304303
    0xd0606050d0b03070f0902030a020c0d20061b0702030c101206050f0d230303040b04060b09090d0302070302150c0a02070b0a2a120906030c0302120403030213120b010e090109 76
    0x1900171090160155a400941d0043c03226a001840c0031942d400040c01c00700d010800341c0000d50300f81e0404040307451040c4031200603080e03900508101d0030102d140c11601c04d1501480120103038040340800655805020103082424054010750300c0041d042c80040240c041c4526180030140707042e401244908044034601c0524202034a440344848681c0c4900d5060318800c6000c042c0e00440ca943c080e02554140003071400343d48503020504180c00c0070710304607042d6400d0401150203035040b1030030842c0414000465500c0100c0900300180d80d0001c90500704c0c101075003081e030094403c4407441801001c0031410000e12990300c05500340c0b515151a909128100e01ca5000c222000a2079480702c54009071802c0550302405140603d0724025680d00d41da0307000d214200d96014000f282d4402d004010fa59014014000451b101d46400c51809000100c0c0c820725260140000d010968045844680c4100b00c0c080c00002c0c024040340004070309072030301c1d00c0203401009000d41c50030120420089000d4a105000703511400390b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 160306798 1250 160305548 160305569
    0xc01080a1b23130e0c04120303020904320711060907060e031b0402090f180103330209040905031204030201231602011803030501050a06050f0301090905030d0606050d0b0307 76
    0x5162400719000444c1c0503060340c08440c01084000361110414007000082e9100c3d490141e00d0f41048000c2000315611541d552001c0f0034000d4400040031000300038450b03042e0340404810f01540b1030840454000b2621007140d11680f01d06400e218030b0010000e46034084512954a180d000d04001041c151100d0041000b13516007a13010294452a14140d0050030340c00001800031000007811030005040c0d80e5200854114500c801c0d0014814031494400c0207034610710314403403801c4041410344d031003da80c0e0b60300c540044001d80c0460341403070603521034010090700d90f0450222629048000042d4000c454140e5044015601c0d064040c040c0c030b400c41a0710150180040da087c4215501d180102240441d03241d241070844d541c805944089059108840a500f0b0213698000f44541c1840144403041d03806802003810f0007818020f072100340c802c036411a810745038002400700345035045241c414a540100c90448010f01d051103000704240da1301c44060020f90614000921001d10310100389034407020b041c0203c48600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 160308048 1250 160306798 160306837
    0x1f0609090c0c0609060519020c03070b09011d100b01020c0d020f031006080102070b090a080306100203070c06030209040b010306050303030a0908040302031c200c01080a1b23 76
    0x20a5a00c4010741003101d04020400400b03d0362484112441c25500300c50642d940c03424800350040d0100c080c028881c1020085140c1740611300c3c0c507980c0740102c42004085c0540100003601480c002e400c4411341ca01110400c04e941c601c00c0711010349a00e0703500c3c0d10785065440c0c00c1414010b0b41c0b0000d13040400c900c01600921f4540038035000d00c11f1084461034220740602c11028140501c05a85c45028010300d5010001615014245484041c0c1c540c0a0321046050340700140702d00104014004598100b50100c80301c0714220300d107510583c19400350705000340c2212907102c0d0010b03c0c03030f406d6001094803074021034040004002d40b4005500300ca03030030701071150142e1081c00000c8042c8080c0e401160042d0043c000035040aa076039000a14042409446105d075a0000740004074507030300000044256542d8060400043c8004070102c0da1311115607461504003c3c3c840007007802d4080f19800300c0160080d902c84040d0719140607401a1481c8038001d12101c00891030040d08000c01e0340c00c400e803841800d2207480764008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 160309298 1250 160308048 160308059
    0x60111061b251104140f011202180702010c08090a050d050a030b061902060609040f030e06090409050a0c06090303081303030e0708061f29040801090305031f0609 71
    0x99009900750301e00c101182c0c80803400220414003181d100a1003111140d00091059060205a42d5405c4241402c080c0f070000344150700c50f200c1c013014190750183c0c07154a0792235614000101e100c080b0842c45034031442440180303c030031503042d0800074010b5010f8445c00400c1e1600400543c0d1024900030140a603000008444000e901c02c1004015030a400d1402262041e0941c00085241d408044d0410284295003c0000ca00781c041c02850352006040320b40c0c1c1e50515143d00c03400e1030034a0820380103003005007204005086940728001d8443c020b0024104100f040712500e07103903a5030424060280e81c0305590100001d21244195584030a072a85540c4183c160349451300445404003100c0d200714285503c40648920000d0304200c004010310840005202c035040c4841c605080c2080880400310460070345c4414046106c0340c1c84200501032547c100c05c08490301d120781c40c038824025a00449840e5081c800d44109041d44540954000c0c3c1d031070720880002690b10514008104847c0c4180310100d0b9414204100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 160310548 1250 160309298 160309351
    0x801110c030910090f08010504050d1103070b070c1e11102c060c031c02040b090d02040b03010e0706030f0209010804030c062406030b03060c091905060a0201020306011106 75
    0xf03810014100711601c2901c0303c0e0808003101c41a0000d2035207070341d1482041f003030080170010100346503d01e081860054000e13070300782522440364460251000404001003079480d41b05007000c000765504480c004024800c0b6004c0b040554840c14015650394801032000c0d159498803684103040011940c840f0a02c03002007444406481c1c1c40d05950500001c503051104806450300070044c1500652140516034480c01d0303a403003840e0f10703142c0c3c044203601030720500c020312106114008481048a0440300c2030080f205920008000d0903010819607095401e0000c86a400980011000156a0300751814480c52510034400c0c0128095400124000f40b003403004900464080c10707000e41c10502580c00410a181c2d940d40c4089000402860040e02c0075891030304128142d890b101c3c2c0301c00c101c0220040d14040c100200b4200c058004c100205208400701c20100210901741d0f00704400818028141540382c02110001a00035007084130068085903c0d80d00307040b41d4040109401e072040baa0300700108a50a011180d00d82c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 160311798 1250 160310548 160310569
    0x8061e040b0a0510030b0102060709030309060e0d0501090302013201030f0512030f180120090325050f0a0b0d0207020d060e0a2607080a030209190801110c0309 70
    0x2e402c002e0041001c640c82e191a000441d200100d514080f80740b90303680c00024580f2100901590030010602c0090001941c0b28010b00100c801914008010300301202c00a01401c0c00320310010b00715031809030044200350301034103d000e000c000c4030000c55440d011f41e022080203ca140d18040d000c2502000107200284043c04c1d10319446000300112000c0c0600d8803084643c0b03910598034541000740e90340822004095000c464010244d009009000344580d1081d401c3c44903502184899080c6d41c0400d00e90700944080107121031000030101c10f02c00143d684441c050442e40640100e60154940c3d01c54030116003818079545048403880050240390542c00d03201c0c000250001c039130480c2e0208401c40064080740b454000e50001502ca0400340981000760315054200c4240d00c141110210b6441c041e000c0d070030304220b003610a0079400611540e42d4020305082203009114041e0301641c404101c0c00500401d50b68400201e068503d1980208451040e91030010740c50302480315880aa54020003004280c1d040514015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 160313048 1250 160311798 160311821
    0xc03011e0c090b070b0108010b0d122003040303030204050301050106051204080f070c06030b010807030c090302060d0908130315090213230c12010f1d091501090204030308061e04 78
    0x8803403141d150942450f243d8460070060318501002e10040c884400203104100c03941004a5560350800016581c108000304086010350070b001c940800381c1d00c5000c1c4030680c0b000c240d80e540140c0790713600d4480c5409002174115004650185d807a000000c2800c3c2c0c02203088032882c00d949000d82c4001da031943d641025a50107580d006c1100d220a01240000841c00305036a40503110b01e880c04920003882000041403140002c100d00100740c1042920f40115410144040660f80c05451142e9100041081140640070490000305020000141240c068514483d0601564400d145000800038460100c6041c0c0701c4030307200613600140c400f83c0800302c10b010703034070100720b81c400d5000c60400110240144c44595804840c04850501e0002c0c3c10300054000c808040d0262050241c03808806e420180e042100000e019500c10905110300003284c4a1302c0104011039200d26003a503008925a11214904080d4200c2d1000700c022070b042c4004250341745459114882010200c4440e00c1c5c0c17003c030640400024142c0d503c1c24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 160314298 1250 160313048 160313057
    0x4030812151909050f0103080405010e041103130c09050705030f04030c05160f0504150b07081201082a091909080d0203150a080c040f0e100e0c03011e0c 67
    0x2806944600c614058000e03844100b41580318540007062080d00c10050075070302000c0214006000045502c000d640c1a10020710302202100004e80101d0020200b01108651240c00841000403800b1000014144984039035a00306502d036451341d82c5001e035401641d00c14003183c01400042c11100c01a012140d01c14040d103040c0e01800700584071141800c00d0340580c507010ba510050140000300b461400348000f00380079201001410032011907003500300814010450301d1440050601d0034010158150303081c2d200c02c10781e4941256528003520796682c51040c81d52640d140a00c0340340c007900030720f400000c614500c0031b84413101a581c0c2c0b641d00313140d580748030442145240c0e5030302925000c2003500025003004240e4000043e6241440900c13007042d06412102c07180b01c0c0300480c409100401d008504c010281d80c050302c007c21800340c80b0404602400d00d10301c00829611543c3c4240b841b05585030040c14005116006545e05020200103040c00da59081c03020302c1750540b40c80c41250b110000765002c00d0030340c040e500d40b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 160315548 1250 160314298 160314331
    0x2070501111c1707230a140a03020c030f0705011112040b0c1903020408100b0102120903011d1006050109120b0a0e06041b05010c1a060f04020d0f05060604030812 71
    0x41c1c07407055102643e01d0800141c0b14171400e06040707505440d0b0240512074013105402c0a1400000070030015018181104100001c0340c11085c041c002d40646203c00e45c0ca10680b6104e1442d6160304500e50000501614107608029120041038031100c11103810f5204071103002401c0e40d80e61100c06c440140645480c003900020000c040c0d4000204000f2850004c0da55405030741c580c80e01020300d180502c0f10220410591825002c032025a8000800068414400c2c000603241c02a0400003801040201e2403904c4040ba2050f80720402c0c907010907040c941231604041000803940b00c100441e0001c4c2c41740034101346080c0c440c0380980402c14071305000c2cac2c0c005d0510ba00400d03862001d81d0b02c01e040540660701120343c00c2c00402c09510110324004a100985000e113007101091801e0f8a40381900c0c5000c10b003150302041d2a00125406440b00102c030410304074083c005540d01d24404800000030a815501a1299464800810100c2c82c0001c1101d08a98200da80c0c241401d1000f82c810b10110005082d41004200c440c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 160316798 1250 160315548 160315577
    0x140f0307060c05100516080408040e07030207021801270e0a0813080c060307030c020a05150610031e0b03070e040f0309090203090a080f09040905010c02070501111c 72
    0x3184040d080a541c0c00d4403240d040e180440c50078103203c0c00a0b038810f081000b004015480b00c0001d4040300d62070715003000691180e0401d000300e8420350300070301201c039020410403849581540060060324800d40380d54404104100490034440310a000399606a28080200e00824007038040b484a840c40040c0c00140d0000217064131890b29480d04c9d412501d0750400709480440225118680c2c00600707180c07010700aa00041800619240300092030b4000345950744c81d0000c880d42c420440c41901e80d0340007003201d85810316441c3c1c0b02c40c1d01d07000b01e40080c442d0b10040d1401d10f4442c8240903000c0d80c4800c1c0b11291000c50341c03088480b0003410182c24400e41500c038501000071401c50780c542850003540200d26050035514142402040d154a85c1c001c9810343d4010801c1c041c503850b00150161145402520140e15822034045030840c40c4505803020798864205007000b001e1080640c008107400101c0d80032180c109940343c2c01500c5882c1c0c1c85d80100309940100034904115043c80200086040a40c0780006034882d10a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 160318048 1250 160316798 160316803
    0x405060a0e01080105151e061303240c14180d050706050309011a09160e0303040b040f080a020919020f070b0615040b0d0209060c03042903010b0301140f03 68
    0x903401020f490f91214280b0241180240540c0c1e05114141c9249072080c8140c4000194000a4503030710b4011038001440320350798608541c00038091503020300140c040d908000940084042c0c0c00c10325000c60b40c41e00d42d681c40d5040c0a6002040d00b481c41300c00d1941070503485802016400010101c882d0813100d117040d0000003940a03c2500302911480d03c8464913820311561030303801c441000c5040905214260528a150b54504c1d0b0745941c008880c12400c0055402d4030300440300c04020446864240c400410007207450506000600241c2e09500069420300759214a5942c1d1511003180c040c0d0002d10480c00b254140c041c0e4066000c0d07003040b041000d0301d4054035040d2540345500c14034040d1603201400d070900030f035071800d031070390000000e403464802e03041c2420b00703400c0c003150322640b41c48245003035000440e1380054a034142030320341410740300c0152038850b03940d2254214002a44101901d0401e800a04200301e46000000c0d28113840809084601b181c0c20b10800b00c90620304021030962002010344013007100c2e0f408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 160319298 1250 160318048 160318051
    0x9030c0f031201050303070c0308030402010c02150a0315060c020105071e150b040905061609120305070b070305100b09030a200102280b0c0403050a0302070e090f0601050405060a0e 79
    0x1040290b940302540000b4501005068110500c04e40040101001160146030b00c0307810b803500032003c40d5482d111403006a407400c1034210000e420401d100e684001000680d006004425015201405009074000e0a03500d51020381c000e810129104404405c0036510078030181440f284503060b10100021450000d81841380201011903080081546911040396180a00c5200d08070a0b039051002002540c0d80d50b032100c0004005400c055928000c0b502e49501c10101e5030014155500c926440506070304000f8800d41c085403094509800c160b0100d05a64403d01c80c0a1150350701c1ea04820f07000e8205000d40e90554444120158544900350300c6030081000c8030007030a050383c0440e1280300703503a280350700182c00c2c10400c0b050000400da1100305400d80314062404840d5482e841500c4400595903148406e03064052900301508910840103035908040e00000c5242c2550400050140d40d503452440c2c1542da0070383c10031001c440d07401030b5004100b5401c060f00a90341284000300300000c102d480d01d4640340c07040b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 160320548 1250 160319298 160319323
    0xa0908030f0409060902070c17011e150f03031b03050408010c030b01020f03090a030204020c1f0603051203010501050703120b0d060b0907080631091b0602010c020d050309030c 77
    0xd0700b00f2058116214031340080000a506505000041e03c81c1c0b2601e100c07510400424424040780d40b0203c000c01c1d400b442c500b030244c241020201c200d03d80c2c40c0008000c501c02c03000b0760401d80c21000c20201c0c034101e545800ca03036055640404c80b102c03808161103400c90184080701400340511002c1034800c000e00030020120603540d030010301c0140c2d01000a103049500003280a03240c10404c020b141c1901e60002003001d803070701582c001d139603101c00340552450000c00c0e110011142a840001d503400c07442c40e8110030222401130040300c8003804603514128172403000713119427400305a003003241c034002a010300034110300d192017080d000444000344800310b00c0c06c15400d00c04031801952000d03c400c0d24a4069051500035a0741d142c0142c0b50f24001012603001d0b00d907211400340854001940c40700b6041201120300d003003c9180b0060111381d4840c9054840b0341804d0302c01c4558080f0811010600610521408142e012036078002d280100c920041983c0f5030348007906000d041c2c00f0800181103045400c01c18001d1044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 160321798 1250 160320548 160320577
    0x9030f080702010914030c042a05030103060b010f0c02090405160611060a0203040507030206180a1202091602060a0b0d0b0709051c1110170108030315030303040f080a090803 76
    0x203007901c00180001d82542010003031018120f071581c0c0da5180083d042030f501c44241c60000d92050900144c00e1031090504030300c640360110b03401c904e42150340034010714102c070f04c0390405001509075400191281509110403500140c02c04013810054500f00c070900782c00901401c140d41082c201c4d120b1810b0030140681112022074808440041c6d01001080003d0380240004000c500350304003030340e50756160a01c40c880a407103124081561a90810010005064190300400c001140b580d41d000344801080400c0b4168801c40140002a00146050741c1101031140d4980c0901000d59420300d00500801d101481c4c650000f41400c0c51400240c402c0c0041e9019103450384840740c8491810301040600c001202c158411504500751340e0001801e40c1089440e2580219521001482d40c0d00c400c64120341e001100c40070b60700000000180440c800b1000f10700502c64403803103882c83c3c4200024140d40e4801960020a9000d00d403420101241554010f001082141d141c494000755560300725510b0340e0440c031101d01c07401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 160323048 1250 160321798 160321807
    0x9090402180711100905120307021507020a060506030a0b06120102090d1104051b0403031416110321040b090f030a050d2312040501060906030f230a1209030f08 70
    0x24008000b40c0384200504c82003800030200c1a61160f89801d08418200b40d00d07400030000c1b0358054024060503a40141440a01d4542d00c0d050900941c1e81d119a80b054512502c0c05010810307900340071a6903a0055040281d145164892000b80403090b4003600c0750b0085554244001c600c030f81e440e855481c08060003050052914031046e02044104c0c2c83c0585442000701c2c851f202410703000224015a011660035060107159040d20260800e50b80c030441da07800900c01416243c0d00d0400c481c0c07000c0300341c2c89a02038044a41071a65206181891004030b8005105130600703000421400749181c004180c0b00348094118454818500b01081c40c1c80e040807800c85070b5400084480544540c0181c20341d00c0d05000203546e80c00f070f80746c0b000101040d10031000c416044000d4203001506001c003d4218400034090803504006c5250380c0d0a0501500324500003c03180108903410014a15038640c4010000340345c0540605074074a6180c0d1421071888592120f0360a201c8c61410000c0854001d40650300640c0c014040c66594 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 160324298 1250 160323048 160323077
    0x140f030a05070e01021213030b01080a060b0604050109050d0503070b0906160228020d02031b0a05040e0606130b0301060308120a060e010b0d0207050607020703170f090904021807 78
    0x1d56500501c420100b1008100050640c0c3e800070b40100781148491105550b4150000307001200e00c8aa00301a2040303003560000104000d0000d078000b0b03c14042c0f00104240c0c0450003c00605125500c106030001e0080700d014415072400e1034030380d45050300c200200c0785000307920799074001c1403001110450300d43e4204004204800d1641e0828200664a910241005c90b4854142038210180140351036441000c004c05c8808540300c120b80f1440c1d980c1c0080440d4101d0445480f5020840404112540504001d010005072418140a0100e9000e003440c050901561640140724400d051000000f0b0300075243d5035803403c0d9440a1281001441c001c18040e07660301c00081c3e10a14417000904403961071481e018040094004036081b00e415910784443c802d030f950148070092000b038040c03414081c1041c0a00c100f80b251494000400c02d0840f8403480400689041080f5004614084d18500541c015010030400742c0919140311031560151006014203201d03103a40c4c12511550104a82600100706038034105081c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 160325548 1250 160324298 160324301
    0x260420010908120c2d0d020c0a1404020d110901020d02070e0c03060102030409110315011707110a06061520071202012c12010b0f0409060e1c0f050405011b03140f030a 73
    0xc01b20790700003001d40c0c0c0c0121011440a01042c4214a00c50002c400245295035035501280c1d1000c405100a00005000754103605050380400300c0140035104241002131074500202d14501118084481b2071025a900c40c2428241e9000a040038110f0204100210f509000c520035000000040e0058035286d103070194408258000c00e454060612120b002120310404034000025030220076450080c3c1c0000164a83c6480c10038411001450181001d00c0480c0200b40000000640906661001040e11a008540100e04101a1800701c9500401c00034414100d49090385428148185080c44925210301c50504000c094813442c05407201c040000e5a40310702d0014407411034865403500070000402803800048200103804241401540c842c41034105002e140c3d032000440101800a44401c800c044440000b07103941c10800e200443c5640c03698000161092060f80c055400603181c20020450320a440082c500c010032080b0100402d1642e640d01070700a520140c0310aa0021001644030b09181d03907101e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 160326798 1250 160325548 160325563
    0xa03030807120e03070f02010e1e03010b0d02010f030b03071203020d0806060c07050d060e0a030210140f0705030414011803030b060c070501260420010908120c2d 71
    0x4a44504203da0b0107000721001c400c5501960307018525440b00401440141c47c021002c0001d254000c00414040c0b801c0380c00804410300b40b000c00c0340208000c490710001c220442d094400040c2c0007400b810101e10529019034051102200000d045a2080d5641c000108003582c4200c01200140c201c03201d41c00006400c121070350303080642241c84030300b000a02d0f40d007290b0384c81c45403090500c10601250b4041c1801841d5004044400324a0700380d41581c0582d003006903036410b1129014440c141303404403c3c0c15031818400c1c0c1c0c601a88403940c09040e1500e038060121801d401c0036109a03504403100306a44401e070000d209544841510303d10100c4000d0060901600b22406101c10741e000c0c40c020411541c50070004501031003591424206001484c0c8080281a0300b25500b50b000240454141c0030b1006001c00034402d40b40047c042504440000c485d8001118103880d075109020007903004080703003506800410060075640003401e0455014845401c01808400c1103617032141209801c8501c1280c0610060000c0c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 160328048 1250 160326798 160326827
    0x81902030c0a0b0a0f03090501020a08010510030501050f0103020d2a090f0315090311070803030f06030f070e130b0c0c010c0503100306020d020f031005100f1205150a03030807 77
    0x916a080c42d041e906190391090b00c11010410098001720b61049000307500541c40b0a81081c000c6465030410400600488803c1c040ca41c801d501601e4960111442401550b06840b00070700b120700c0401001c801500a0b4010018900090307031181c0001500c1d200c3c078412520000c136012004100d41e100d1900c00307440450503400002a00c800783c034060012070380c0802c15001c1900040c0000603240381e00c0c10700325130321520403c40c40c240b40074039900000c42503000070145028000c1511414030300d8a40c201011380d40c000b4803d02c0200d54201142c204200104004805e5202501800c29025440c0d1a80c94002c0a1811500b543e5840c0002c65845504442403041030422161420490320b0740c1081c81c40c0c0c1101e01980c2c40003c10940e0001201c01215140780c0680300d280c0c0e440c05555440b4180320104450f201894002c0d18000c0c0074107520106211304c24001988150480d441e0240040c00741d800c448040c2c1001400210344135a690100300c141c0d21010049402180640d1700c0024a00302500e0041400d250034942 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 160329298 1250 160328048 160328059
    0xd0c050405160207210b0a0501141008040b0c0d020703020312061014071b0603090611160b0a020c0706110d021b0d0c0504020f0d060801020a140a09081902030c 70
    0x81080c06030000346a0302034a10344601c01d00f01740c0c1e4150324031002005e015001070031520030b442032080b81070345504014165894191120b0310140c03540240701c505c1c190400c80c03a00150000f40070901041210703812a4119020724401e52800c0950400d030006c0e80e0049030704400583c0002002c40f4141c1c40441c003143c201034104d583d03114112440c1740003042000c054210303044130000003501804010783c402e01c010001c80300c0f40d0a0750f08a680e4902c081d0040403241019540f42c0c0c2010b018160700c00308203040324101744094601105150a64403949201903000b4025500140d003004000303c004401c101c540001d0032603076a039440c06800c500700c950804901c107400c003003550b10503a40100d00f4082d0001060140c20b007587c5241700c4118508204461601da50700241d0070900c0001c40201007611000100b14040c440032080c410346070342d011050b080f4810710711070700c0c0052070740b03200d40c404404010024015250245840d80c03179280c8039030036103051150220308032140411084042c000c6080038080e140000104491 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 160330548 1250 160329298 160329331
    0x5030d020a0213061d07020a050a0c1409070206070509010306080303130c0803070f030c0204020d11040f080c1e1302120a0501050409020d02010f090f0b071b06021b010e0d0c050405 79
    0x280c1c212102e43c0e0400e40c2d500702480305d000645403031081200349100303604030040328141d240b6800d1107a5860414010030000c181146c0c5080f82d1810032041302ca004960550040c031441d40c88802c1100c00741c102d40310b02030415488100020f55020104003860140d07141503040c1c4507402d80c44c5401c0c0020681c9a0080c421a0000e010310000709812241e0100c2d0190541030000309450700c1e01c0007a001f48034001082c283e0916000c20210181d070b481e0701400036144085c81e151001c503102c181c442d503210210b10034150300c44580040c10b5210030800b404005003400c003030101c14202031508445d40603600240c08000403a006d8208000c420505402118010007082d00c080020740707440d80124030705000c00305000e814007421050020241d0320400213513004041404208254903143c09208000b68003142c2d06a612410580010f07140e50001c0303010508940a0b40c0050038651400050350310400892035100e41444042802c03101c858440302c60381c9801e10b1041d96040346640c1400c08000858102812006121b0303038450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 160331798 1250 160330548 160330559
    0xa0b04051c020603090a1202010e061303020a0512030601030c0c030503241e09060906030303040f080904050a23070512060301061706040302012f1305030d020a021306 73
    0x44405035101500c104526041807403500c00480e441078002500710400008120101c1000b181142c07a5500c84c11198030b440c1e8003a2800c80c01ea0304006e02c0205a43c220002240404021400a40c641e91103401540c1d0200190b0315007e04003000c01c0300129420000004020041d039041c4259440b90100f0f08002140b1712082e10002c00741d01005156a400c1031290080c100c0c00e4501c86070031030440c10014105a03c0c0d003490b50b1405607562440008074060b003800341c04240e051400b50001403003004041c009500315a1191202c5000084c404000d88848500f08415411501d86008882c464030b0041305c0400d11880168003072004200f556411001c8a8104c424421815400011100403401d14020150280c5440000a0050076070350321100c04814079070b00324030064001050503442580030350002c112140442811808040b03e01810101c046c12401006400000500c0a41b0701c0038816000c091020307440744040380c80c0648083c00781001d40e001e00c403032804510b86120070000400207041c007808107600d042c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 160333048 1250 160331798 160331819
    0xc060424021c0810030210030c0e03151f050907050a02101b031d240f15040216140609010b0d0203070b0a051c0c030c0216150c06020d020306010207050a 67
    0xb100280100500310010811004429101101440d002043c220340728001c40400b60007040701c090f02801241c84800d49080e10300d4007003040c07060b5061403000c4180d40d99881590340841c14100c02d114000c0750440001007801d0b11307a048040d2080d0603075280e0781d40d00c494000000e07141038004100071607103d0a10083c80019240308142408410050401240c1003000c80f9808084d00604c00c03000c8040d01c00c0b44000e0140441890943c08454200000c5200d41d40f655030078180300403401c484516000e000340320803413242d0419a006024001c6100c50f00c068180c03030790b82c1c1d080c1c000452010f80c034190380c41141840415072080c42400340540c4100d514084110003a4042a2600c10500c41d0041d51080801e40c00d1865010300100d03244e411990700c0300c10f44a0842c50024000702500041b400000e45010140703480d913400010081321417010885840044ca18142d1031a126000c801b4600f020422070b040c801c40020741500140c24103514035440541c40340340c01800245010310b154095840b50104079010821442d01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 160334298 1250 160333048 160333093
    0x31505090a02060a03110c0a12080c0406120603020d0302010504150b010c02040906110307050a02011a1f02010608030703021c090e04082a010b0a140a0504020c0c06042402 75
    0x1034035400d480e551303c060160018400e440d015150140001383c030041105010841c3c600581c40f41e00c04204445c004030044869400444003036182180422061224500034058202514030030030010540f55101d0b070100d01441c1031590210003503912082848100b00c1c10101c04000c03081c246c82d040091002d0703000020078180c600359019001d20303544d5104006008507600914034012039015025520704020030000d03e1680020500d00040d441d1007003603002d80d1441d20f003c40c00403900410300c91650281c0314a6110600c990149171003035645c0c482c40002d04100600103082c9460094018180104006000000304000d2420640c10004030303480070304c4034101d4034a00301d406c00d4100c203103a907e0380016040100c0d4180741850345d0b407200d06603858883e5000c10542041c03a4010003a14905811980c0b00000c005080c1450080d0364400241c9600b030040c0d00706a4068650100c4920072500c844001c074002c00c2d690741c00b070f80113281d1800a207040700160305c3c59400e2072286001c40d44018004407070300c0501d00720031410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 160335548 1250 160334298 160334303
    0x203060a03030c02120f03070303050109020f091905100504030c17030f0a021228020a0312150905011e12050304061b15020315011b02011407051006031505090a 70
    0x224403c0203004d40d1604110044c000700003404071484810320180c8107990741c00c040700482c0080d00700f0002051030200340c02600c8940b0b0205104030304015514082043c181d801000303046003841240800542540c0300560540001d074140ca5040d40c031410360030100307a4600d260304031180000400c01c0c2d018940030b00100b1a0021222142920740328030040c0340c00c0742400d47c02070b440c850f1094045221801800504520017a6494400d540c5420001e507207020ba0b1600c80148001d0f0101e20442000703154040d15404c0203030117210b80000c08900c680c0303d0808104540080e0410311905404010344286503c040c00000050850301c40092884c08681e83c0e165500c0c070542c0034102c100301d1546005030110450a0428501550010306080c0014000c00f0b440000d41045805203543c1201c42803107035155024405004911031302d48002e10640100c0c1d0015141c0c10342224050351520320402c80e800201e070050184000649480002140c100e10750b0138017044542d907145042801c0d52400051080840c400204c01d0107280d0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 160336798 1250 160335548 160335557
    0xe0f0403030b0a08010207030e101b08131a04151b0609230a030e060903060a0203090715050703080a050f16020f0f150c0304080a1103040306020712030f0203060a0303 73
    0xb91550108880084030380c030200c6a5800800d000c4101038015800b0000e14506881c03024480340c1d5000102c800b4500c0000f0b181000f4149240100810304000c001d041011102c0c03c01c0800c0707990b80142c4003040c0c1c59040c036007540c00e20210301441108a02c110200d14544146845002c1420914600c3c102100840f4014501d9965614000030405840c41040280308240001203ea0021464060702c41076590421400550301c04049066840c2850985081d20f9003c0d004222594078811208001d510140005060344070740080000e0400c01c00f40250b070403450307643d1001d881d0509481d014200036070140402c1038440c184400c0001c50340d03845d0311441d07100c0080340800c41074030640c00003a41080400310070305009005910f14030740d003c0e000107001c810110742c0f8505d6801943d5034404060f40b5010036280241450410417088481500c158030702041d01200e40c0941c3d00d00b0381d699031004202d9006400407500101c050b10f440d07aa6903014801c0c0089078901000c01d51941c41d02000107022844030340030060511 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 160338048 1250 160336798 160336811
    0x810051f17010f0f0b030f0f030703110726010c080c12060a0b0c0a0b01050d030804021212040f0e0702010c020d051b030d0504140a0b04110112110904060e0f040303 72
    0x9402150300e0090681c000c101404002011320003400e95407a245009206501403105003003400209603c00900c0c6030007031800c0c6404ca6a045682c0034282c00007803c0e511401202040840401000401802588160b4541604140c0c5c00e02e0a4444481c0e01d101484000e000300242d4268881c102e502410712180c400d4210780d2103400062001d043c1e60441c001001021a0110300c0c0340000414802c0740b03014400702c4100c3c7e0782c0d8008019040040e220700400181034040850300504100611000c00c20508058510000c040280911550081d6001100c0e24444540801184081d056007907001305045c4005d100d60400d8000c06550345003040d5800041140001d03165240a40041c00782c9110106038065a907030781817000d900d0014040c1590141c442c0103022500024000f0000b0700954519840400306005540710b80351900742d425040452810b1000308101459001424800e20003640c20400344070303482c0c040a0050004680054018034505038030315081c4145da0003c00000350317215a0500e40031852 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 160339298 1250 160338048 160338089
    0x4210e150c07031103011113030f030c06140a05010510020a0b070905060d05010503070b070c0b0307030f090c0807050103020f12060105040e1911040e070e0303130810051f 75
    0x118800e04070400554000c0203004401c0044150402800c894104c00034081e0032490305180300e0910408030103201440c8010300130800521118003071700c65103000781890441389405403035402c1924000781031403181b80407883c10450403035480d2041902412042c2ca51580c0168150170103551604500b901418000303072a030005051174403c803498000340030b01a000300d4403280c0e1840e40380301401c400e0007801d1090180b480007190146541c2c00b07551b12550407814120001d40b81052031900c035400078200c0e008164603504900244010340c06042e44d0203102d07213149482c49181c9400c0c3d906041e5180c000038109401008542c4076140f01e802944c40700110404924036580720f450040c1d6141c80789502103000c040c411002c05c001c14020b00c0c400904454101d10030702002064003400c0915100b0b6018010b1804440400300300030743d100f842100c80c004409001c0380d00d007041c1d81010140501c12940b100003141d10214442c0900b1004d801880c1c1c00130100901e000d642812187d42505401c9035020301006020500c1c40c0d100c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 160340548 1250 160339298 160339339
    0xb13020904032304120506010b090a0608071b0b09010b01022a060c0d0f030c052b0605090c0405011805032503150e1504030207050d080904020f0304210e 67
    0x10b803555600b1084d59565120010104664017403400e4585020782d900000f1050085002c4440180000b040e007017000f41406016110004080c0c100b00030003c040e00300e2100c01c3c250a03122600c0902900c40d000036854480492800d40320401c91440c115046015544464503960065200304604a803107003142110800c00724030640201e142e070320001c4c840e040c40440350541083d07102c4c0c10340801d55024004088403400c2035445100d12039071108002e0b00c0314030380340f034000d04094450080001c020002c50f80c0c5554000040f8207a4003030314259610346000408000540e00481424003000c660f08460010070314020000352182c8000e480c019420b0350b640000d6803044280c0c64887c000c2c5520004031a44001c4003c8540018a204000d29501d0301c030b011554494101c1c0848414829581640100022402e00040c840808284401142c0c0980c062000ca404d660b52400504898014190101e0300d03860203013401034044504a00f003009c1507204110050595911601c00a51400d01340c4420702c201c08002d007006d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 160341798 1250 160340548 160340597
    0x1050609041b03090308010b0c06150607050d020f070906052b060e0d08070528020102040503060a0504111813020d0605151203090d0611040b04060c0b1302090403 71
    0x14071200c007030b01681219070503910010741309000f903591000d1a81c0310a440405440b4000d4007071f940d580b06800044c6d461b802c03020084500f80d009050541420810340c2c4540c60600720b9421900540c102d541c2c1c0c040320400c20828500240416801404803500d44008588421aa0300c800c4514010342480491565001591244000e07030120041140709080c45450b61600034280e080000100343e040400c18151051081d07600007000074150148100c1c010102c6030000c0c04440079141595000d102c0090b0541e01408071511920362584045400c0c5413524088202c070071031691591090782c12120f035184001d0702c4072450307601c6142c4064105ca060700500000340d410606a1b401001c040c01d09007001881090500d55810600003a40c1103030184900701c050a840b4041e40f20b100d42c0114041c00703a2404541c490304002c0a0b4681141e80c00c1c60107407603080d44041c41d17100703800803800b0072801c144080030054040c1c00158400c2e41402c0d13a4040100760340c0015112407000d080903003008030400d40c45012400510811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 160343048 1250 160341798 160341821
    0x206070209101d04021809030a030504030e12070513020406050a0c060b06040603090510050622110301061d09070806120715020a2306160e030303010330080105060904 73
    0x30850851843c403000c1115084130100d01409880c1d5442c0c00b001e80400c40c0901400d8240c000e1818155941d10850050a000380240c040100d220042151a221070469075030030310740540a044414180400d01c819117014102a0072003a00c100010803060341d020007603840121061400000d008054100b0724060000c0103003440d84000300090000301c454040d400308000a02c114191601c0911140006c0100c40c0300711001a00084103c2d21b480360706d02d0502034181c444114500004070030310046522200b40c2c0098000c100030030111407608405200c60418110701800840e000c00b118035042100a29041000d801540038162200b25180307a40c0c010720042020f49030503032500759004d405010095603404076540c03d540c8410407545c1c5040c040c40c03811003440000b0f01d01d0000c0206440d1a86010894140403a012080000e603001c411100d40d024002980254010a42900c0c07004c0c150324004136401c159006804043c13805000880d080d80c1002c80359045500c11506541c031401d094012030041e040c0a20003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 160344298 1250 160343048 160343069
    0x3040503070e06030c0d0b150105190206040201090e041109090309030129040501030b01140a0f061e021b01030b030a17040f06090303020c040213122d020607020910 72
    0x32410080c046941d510404046003100d0001c440c0c80c0503c015502400d40190011040d07034002000a036006149023401c2406140880c030300410303981ea01d440c100c02d0851000060300b0240900c001d6680c40680080a45841452441c40e800c1582d15001d0500a40903450300a802c60f80008590034010300c165a0b07495009002400000403440810406841041c5886200700032a00740d0342103418140f042d0750580760303c5088241142d0130103040f40450401400541e501030700e6910b011980900620b50080100304a44404444003429600801c041078003201d810215400f4060402d51044402c4502c40c081000f82800140b8016000200307080c00e4081c0b0015151503030503080711114002107002007044a0b20041000c000945607030040702c00d000c081c880500140e2041507200d4041c6415402007401c6000000d01c1c61410b41d40d0503690820b4459142e06990100c0c880f1524040e0203801c1c000041e40038185411070019010640c00980540560003002e40101da40c2030000302c1090240c440035000d407401402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 160345548 1250 160344298 160344313
    0xc21070506150a1205030403020d08090a0801060e0606120f0901021e0702040f02040305060f1f030501020901031407050f07050106170706020d0806060409020d0f050c07140c15030903040503 83
    0x120256107071103086154020221410002007513070482102c0e050659200015600e000d103035400704071907504404800c4d24164402c002040300c6581783d450340341c0201142000800d0251a01070311064404000f080b00f4014903040140e1000703c0341e0071002984c070820510711044a0340700c41409500901580750b01445c000360245c881948c01c00440040c01c00c5900c200e42c10300181c0e00c01c4015405900484c0f00c010620323400381e00450341c07640011081caa8482c00141c51f4000b44441c1607549016610507603c2543c03d654001142d11065034580104251440d4003100102241030003039005003a442003803800107040f88041200010000203400840040102c0c014510202c000e94115507101c40182c03180c1000341c803501103002d00300340c0039a9001c0d1017038000501d024201440c0c4840407001c1e41c8070b00700c00c482d400d81c2c9944511109869224203802038104618182d220b01581c5040c1400349408001c24556a0124a00038100e0b61401201035058840d500d2168581e120402c036581f031401960040e603854082c490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 160346798 1250 160345548 160345561
    0xa0f020309010b0a08010614120118060204030605182d0706080711010501080706050702010c15051501020303010506030a1d070303020105070311091003150902031014060c21070506 79
    0x4204403d0303200d040301c0140c501580c40740021300b224420300c90714820009140c40d0f8605450130340f03101d115001e036420000c079602e00c0b1520301c4900c00403019000c541c1250702140034001c0c0080b502c44c0c2e90307200e0700510040040490010880e941d51016541d1b041d040300f4201e0b0a1464490510305030160502e5800896002940701d0101a2a0030300440b4240d0006180c1e860070201101e050040a04030b80d0700c030010703014540c104001101c032039102181c00d074180202040d40c01c0009240024012000300146000100c50406a40303051090300380c25011811507205000600c40d0396a100b003140d0300102c441000107142e845d1496560b1065140054100242c090014000189034064103d14410300c100c1c2c0d0100304503d21502208410f01805c0c00c103d410039403030300c4072078400381c000d6010302041c980e5440c0c605402990360040c0300503603004a40840510144000070011002c054140c10035001e400c644543c240f400c100c08041e80c0d81c0ca08626200702e480d54031010500b00d4188403ca926180d0040b0035201d86141c2103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 160348048 1250 160346798 160346801
    0x10241e050301060e1503030717070204020c160f060c03021504050f060403050c060a060308030a0c050c010903031401060302030f16050702150306030d05030105100e0a0504021c0501120f02090a0f02030901 89
    0x11a407041d07201001c5c052a6600c2c1c5404000c0b55480d90340952a07114291400302902401d406c13052040340c00c658208400410071400304096014160300703103032441c5840d041100e004201e810591050082c00400000d200c000f030b130049105114040442c40d00004d56886060a80c80d0001d01d18050781540036000030f02082c158440001e1080b103840500b116401e855080d0007400319640c610010f02241d0713051007c18648803043d0032440b031400c01403034410708000005a5460849840d0700b01240480e82d0742014000c001900000e06006100c682011411440e0045031410400e000501c420018141c400305000301c980180e00340c42402d50064140f4414880118181c01c0650003511000c2c4039101d00d0081d155120300c28012207041e92005409030640d003004007816104e4603010341031242c1c056500386001c965503d5600c09031644040d110614019665540410300403075406801c0302c80140115480d000109912a01421400e6410b80d01041150f860f11040b100501501400802d098000401d011010105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 160349298 1250 160348048 160348051
    0x216060912080708040320090103200102010f06120317010e040f05070305031b1e0c0f040605060721020c0f01050a0e0904060f0608010509150c0705030301030510241e050301060e 78
    0x4c0d051f040d120b80302c007004000c81c081003440300a084c4440c0c20031600c07102281015124a070311040c000032401740c0c400b21000082c2e0301c040d00b200a6020b40070001400380343d803099883c1d250988168181003103504109a040e001d6200030000780c8180488880d200c10400c040003808000c6401a0130350741c41752252008420100700102c0110540c1c03250031100800d10240d16441900d0310040342c010441141d0800501410628015038a46c1c4542d90b40c00c000b490791a15402452182e108800e040410118071501900000506a02400b19031107940003541c0c1d6140c00c0c034008510071003424030742c1d01d5010a03002100c02e81d8241410306d40002c1810b0030300040200507003003441c0c02d0580c0c1e00280060fa403940100341c01c8960858180c3c01c542d21216440b480c00c00d411a4054010039015070b1245011801c0d00c0d0545554000e92003154180e0000c025030100790403610806d01c13100da80c18207441c00601c002d41601c401c615103000d0010030a040200d0314403000c90000c2038500504000c0e0081c4522541c41c5491303c0700c03110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 160350548 1250 160349298 160349333
    0x2030705030a0e160302040509030d050a091b060801030305180402070309080111122202060a0207061e0804030e0a0503010e06040507091e0207031412040302160609120807080403 78
    0x2006020211501c012403040000d401302c4400d4241c0e145907400700800b03000c02512004070780c00100180d4800424600495220306a07a04011441d5042890000d01d20051011202d00c50310605006120640c0c0c0a24018112a058034242d9107903a906555201194180320000b0380c05480060190b08154201d90390304121100000200001180c546550640c3c2c0706006050500281c0c1c500001d404011078000950b100203418008240c0030f1080c0e010807a554000c0d4030007005640708010400c5020ba02010000d1031a04071011101115141440034040e40009407009040c44540111810542c40d1207583c0d80080c10001c1c028020b580c031214581e529044140e41c16601401902000b140d0303503d00b80211440030402681c00d080000d921003150009411040c02101000140802041040c190f0400b4050305448038011085d0b5050030314001e440d258500128400c0946044c10802425412201620464003240d208201d29040340ca400c502c00d2145820050140318085000700a121010414696400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 160351798 1250 160350548 160350551
    0x100813111215010b0a1215050402040609080c01030b0105070303050a0b030d03020a2d2a081804050412140f042d0308161113020a021203010f050d021302030705030a 72
    0x262034900d95981482070180d0358010408000c0c10111b03e014650007101412041c100544a690316400064103aa000381c0c040c20004008403818070086c8001d0001e0f904101090038200031214a810000e0f209003d80d04c401303028150b40e0030015000d403119802600307650b03500500341d500030720b00001c000e0025006145000c0000d4484c820111316411026440c903500d000344180d82c076409000074400c5800c40d0b100100340035402062070300c50f02c0500030040d040c013196202e002803a0302e989801d010311070760b1030642042a206070b040200f44008129a840c500c040d451b817510303040c2200300c44650301c2044d40c45107488034003001070300180001c0d00358159840c0003106004200503907008a000b440003e1104c0300c83c000030b0203c2c4802c001418113039112803103070384006105414515503911402c0000c0c84401c43c80d030b24204810740000d12050312981c18000300341001e24103d980f034119410a80e408010408501915004500400b440d5096548040c0e8020043c0001807087d9501d18000100410a402c01ea8070f12440c82d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 160353048 1250 160351798 160351801
    0x23011e0c0804020303030a091502160209060603060906040e0114040b0402010f02151504061502010e0d0306030b04110d020d06060e01090905030d0f0f29100813111215 73
    0x6441801c986010b035030014011810740e103548445038018800035008070740ca040760640100e0100d07124000b500344da03414a0301e813151981d460f005002c0d10485c01403045108080c10420070516030388030420741d0b030460000c0d075000441140424403d80148074000b02070300b038090440d040004219100855500c542d100783d882101ca52501e010599480c8900b0b880c45500005060010f00e110744000701503064807100a001045a61f40c0b040903001001602c107005005035114040f2a500d00c0c1e08000250700004a0f01e402c000c114a15110650130310006440100500710144044460780c0e21840030b030340f500780c0040114030b64507614900000249a41e110b588041c0c540c0754000204040207100700410303150408051481c19802007030300e0009207030001602d14415528107600300741c0749051048440800420004614520101c4044146e001d11544100c0c0310745a0003050000d640c0e8401003590f04108003a40c00c2002c1c5800e4944110741044d20256550003180142d80092607540004100c0a01c5003541941c1c0440e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 160354298 1250 160353048 160353071
    0x3010f0203042a0f03080c0705030d0906051c050c18010810060c030c080a02030405040b0a0302100f03020409090c090e0604050c060a02010f06060e030d02060105030a23011e 76
    0x26800700322409414100079441c9058140081549055107001450402d20050b44841842c480d800c043d40090720a0000841c0407010001c00f08a842c4c007401c4100c005188420180300d00408140c0540601c808008022400640020a08200c0e010f10704240f0b00034012072030078200106042c0c0080c030041a541e0540140ca00455000c0c02075603006892003e10189002e0400c80140d4107141482422010041c5110940c0c01044030302c00070f440998140d40c05190344920b0481004140c40c1008416441340300050070400050343d40c828014441141070821040d03004540b04182e0090046610103820305040007844010032a03005022001d4030100c1da002c000c0d0344d41c4407681640e00ca90844009080b40d228048441c05440c08001610b504100d0b84004581e010f0565614003c0e164035034000f1000c1407007160900080d14040c445441100c6d0706100400496162800107941d5035100384014081d00210000041d02e030308400c01e10f03001520342200034030511061f400301d151200341c4150380c0401c1d946000344080c0e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 160355548 1250 160354298 160354301
    0x1b06030b010f090b07060506011715040c02060603033a0906050114032a0604080606010206070c03140f0d1a010905190510030b030a0302100501090612030e1210090203010f 75
    0x15260f46411540c10030360170366a0400107040150400b4141322640c0007019443c0c41510f4034600c50103408000d600200c8244090105a807a01040d81e01950044001c00c0255280041030b603540b00ca0148107030b40344050540700d401350601c00d00c00c10a410650711656080f039501941184140c6440745d4801c0000d07aa0303400c10040c4111901300300541c150426038a1014420310100c0c48842030000340c848140c15003000c0f0020b10698080c1e03000300041d400040c02c01c00c5940c0c05001443e07104803241000c80c0b40142c0c665006281602c6810345217150007004c101d03525000c0804064410180032a54200941c80270700091200050184125500095120788007180714280807130011102801d00f5801589107041c039041111103d05102c40d2020940e4500300c03505269010003031344003858002d4001e02a01c0080144220136180140c2001d1840e034141101008220030b0a0181a51650113140c080c1204d010709000424410b600c07121481180304090926802d40499888410481d2084008001001c0080d0983c0b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 160356798 1250 160355548 160355567
    0xf010510020a0f030e040e1f0507090e0c0906030106020c0405091903050d020706111903061401110106090501170c0405010b030112050307060c03020705060a060302090606071b06030b010f 82
    0x140141c100c50b80c0880000e042c2610004118802d0401e048801d040c54080b608130b0b40001c4800d865580110780c2542035480704a4482c006c1242c9107410f00c030502e000c5c030005c2c0c08070880348a0890080c02c8100080d8081c50681d0a480701120014009540da5942e20700003980d9612030502c040c4120300d00341c0032500880780015441450341c3e4015504906600546056400c3e4004841d051800c540801c98480080d14501c510501203180c42444c030784402c0350030054080100361012803030030316141c501c0902c0707680f48000c03900e80c00000034038040090700c21001d546030141031268000f014040c2040c002194685500c8441c00300d00c00c500f011034800052000810060311820310490300c40540810050005000b00c00600892501400880c1d103041c0103aa030300411a292264a1030010303501041543c10480140641c0d5040080320780248082800c54000550041c005003e0b50b20402e0000354100401c010301d0301c003029142d143c4003000385480d92074002070b01034505030743c41d0b9000071220061800c04502480800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 160358048 1250 160356798 160356829
    0x8030a09081c02071419030633050f0d060f05070e04020403080909090f030301030c0609080a1a0730110a020604080a0c080307120501120302060f13020909060f0105 72
    0x504e206490f01d1855145003024200140e000b02e0038050360300e41c0b81003920070030006610440000403880c03000300c812428420904100144006102440f08030250498924025600203d40289448039040d0004502c0d0090110083ca61418411082c00c19401a8009480313899982c13110185100c00d002000100e1085020003044c010f014080c902090400044490f0300c00c0b009000c865140b40b07001c1c022499030300242e20450342c0d000149020700003c1e5010034600300400b815030003040384018585c1c4d41c040040074800d07142c001c0d8400000281100307206401656141d03030071488002642003401d9006558180c00800301d000386080c01c2c40d05000810704800c480141901e03501801864031a41d40b44103240d03001d0980d04040140c1c8802c004c0100301648015400350304540c0340c940c030141541082c102a130380305a0000944d01301001000c400b003078011820aa00898400f100455681d5005c1001e00012403044003940107c1d0100810125650000300680a030601360300400f05aa0380d001080762410408082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 160359298 1250 160358048 160358053
    0x7030b0312120c070203060103060e070611031207090b0a09081903140702031204180e010204120b090f031b0105130c0504021b030c0d0e090f010506070c08030a09081c02 74
    0xc4940b1a9900010341c2100450b96028908181500024035060084c2c00617664243c2e03405100403000740030025400100502c0c1000450081040c0c20662240a48070300c0d1103a20088000161525204040c24030182914415164680c04c0b02c6600170100240c074018508144944030b4600c0700701607545c801c80641036140c0d58051140c2d050070001e0002e9040f44504a802d403080c6800c0d14820001a4080c0018241844102400c4001c521550064a241c05e50710405640704102c24890300f45a041ca007140e16821005802543d11411009803401100380180e01040c0404115543c1c0c280110180ca54030b45500802845207403195408800c1d40650900c000b010703000c0c2c84000b04030031b08107600504800381c0441e044d0180384030412001411a8007251103e200c0307030404ad06400c1d40680010b42d69030f6030081501c5020003481c0034115280725003410300455200e1742e004200501001604110140942019006c2c1c0e6200c0e100068080d09242ca41d00441a09001d40b80507000c1080350741c4a041c055544e143e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160360548 1250 160359298 160359307
    0x30405061605030403060905060709081b060f0301080c1509060a030c0201090f0b090106060e0d02010c050a0f0b0610031a01050c07050909030705060702030301230112090b07030b0312 80
    0x30031203194046805007803000d501c0c68010011481c103002a000550164101080d10300d1103150084c1031074001003011040c007020035010f10a032880012242a018110704101e07640100b1180010014001e15181c1c0d105000d001002140c125004251005c07c1001034850b6a500818020000c3c02c5004504101341c01203003e000c042800303032094114006000090000090480c02030b04c49814880b0705074815640006400c0c244010810309100350402420706280c03225021003040001209841b6050780a810440c01040c80014000140040c44a090307000d80c010344401000e2a04240c0c0e004211a080d100d094261805005940203024800c9580b105220b0720b60f01c000790340c00642e05030308000d2160101e0310a142000c242c946507102514040c0c045007000f1a02c0340c100d46441c0e444d0401c01400c80003190030600040180e180e2042d500e030310078002c10864074441e808210048a502ca15001c04c810174a00381185034041c066002c08844c00303559030380d9052107c903e004c418581d54010311b1100074042c40c820032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160361798 1250 160360548 160360559
    0x6150905061204121b0606030201020d0c0b010509040201052205030c01080129040b040303080901051602070303051c06060518010305060d0602160501090507140907050711030f0304090605090f090304 87
    0x240f4a604c125114204080550b200c407445902450002c80215459070381e9000600540da010055100c12281510300044480403940e2802c1b030410040c86024044d09074100481d003103a02070002c0c0c41c60103079441004a511503000c220740329140070300d104090190080a6000c1e41c65407181d9803644c10303948031128128a8581d403104d1482100000d90514103403140500c404a060412079000f000218065039070081d050030f0501c9140e00b1244058480c100c0c0e04044031a0a100319008140c1c1400c890b018101142c48441001412644001c880b03018824a46051000700b09903802c800506540110f0780144101d00708400f006608903601a588641d03c0301011071640009001c5030000d0110f00d40c400e000e40ba02904683c0c03828255101c44408607201c0c2c1142c401440030500f00c2d0b00f50400c203070049991520505020300e0160080c800c48034082c1c00340d101001c04103119103040040b544d010300c0d03101c1102c1d40c0359541c440c441c000340201ccc000c061023194451301140240b140000320314020902d01000d1403070245880e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160363048 1250 160361798 160361813
    0x40b01120512031f0905040525091b110f061306060806011d0a110f16020907080702012a0305071206090203041a040f1101110106150905061204 63
    0x181000c85032441078401c0707076800a0280d0007850060511004c0042220640c0031201814000c90f08000101407403c01000301041000982d90300302050180903441180842c1d28202040e00180c0012042c1c44c1406d030803805074040b9034612082c085050f603400c0202c07415402c00944a43c00c4500303100b5658450300c04910424025032a000c04207100358400902185c2c5c504e4882d040c910300740d00000c00c0c44580c9000421003840a1300e09688406c600c84100403034501c04a5201c00c2c0d024030011104541d2002c01c070410a0315216481c0f501e510740003040b41c030f03407441e14000003800380e84122100300040d42441c10800340c000007000d05051050031070071841a0217150000441c01484018540345c100030740061800040365151003980090059601e002d640c3c1d141c07505121080784042940e00c1441c407950000c0002103009131161070140c1d640704440ba1030b0412400d004039400c0c16040156a0369510f807010018001c5030100c03000e01220320644500020568a00c2001960700035000454114400d40c000540000c210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160364298 1250 160363048 160363079
    0x122d0b0918160f090c0c1a041a0a0506030d1b12031407050703090e0c0d09050309031b190e0f0606250b010509060a090f09140601030309050306040b01 66
    0x140401c5450301c015100c0b1101c5580382c60f41c8500307140780703801000b88804103150007030740c0c069040b600303105504d150281eaa040440760a8000100300340110004602004800c050b0352202c000c440d400c641e01410100d410304024442a941c0c6031291040c00070052075103016480300b011900305444181100c103019120a000d8007030400301d000405681c2c034120320f501e0b01355000180c0500c074941d03206621a0102e25000d0003003c6503403c000290240c090800510740309480440e80740e080f80311400300c0c00e4211460503030f281d8000c00682943c14016138100803401504000c8030020b903181241c40c60582d5001000c071411004840c002c2030b620640c0b280010740044600941f0503002003015190900d004a80503080209003140d076080203101ba1102440c400380000c01d8140c0307000d41401c031014842c078184003000503910320a501c6014001500e03000d40300d82081450b80818400c41e08081095440ba50014615403120b509000803808180c3d03541000c511303402d0005003188210b07070195024607680d00b00721640d0001c009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160365548 1250 160364298 160364341
    0xf03020903100608070602010e030f0f0c01090c0b090a0504050103112803060509100b06180d0f050c01080a02070308181009060501170c030307020f01122d0b09 70
    0x1140c41012500d8803d00c962001030403480c010300780040c20b0690003404e644144502c444035078014001c940300c80e00d90108688110001c226815a501644170b80715025100358200504481b80b0141700184160580c002001d42540440d42d0300e12841c0c81d14100000c6640a01003d89107040402c031010307284c00d10f403500c58580c021806c200c940c1c2850b22414a0f51003803460b0801c50b00aa00c84043c0b01c4020010449180e90484444040c4a18134960b03000c00d45030302440844481c0c2e440315411145c4c0719101d030b10300c2465072500b1601000c800038150038840d43ea000514140f0f4001010f00c800658000d00714030035501c0f100d81c0340d030302e01200c2e403103d440c800090542c54011500c0342c01240181c0344c2990307651080c01d0f0f2161007000003103440e61402074280c4558007400d4084215800c6055010f82ca66000310031550031303907030445a00e11650705c2c01b030040340d4485103500e0314000d1034504070ba62010a00c0c00c0901d406105c183d00c00950100154121580582e40d8018000d90000f00040100348a0700c080c00110443c0756 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160366798 1250 160365548 160365553
    0x90b150a0314030d0605030a0f150b0603040804031e080405090c1b0106090c0e01020a080c1c0809060121020909030c03121e01060504060e130203070f031b0f03020903 73
    0x68890710b0b034602c001e001d500801c2e00c640c00001c0c01c005140c2e580c040c1d2002040214081c02d00c1c000f40351500030440258200082030804659102130703111280354441d4030005030181040f0703120318240c07400403455030150100b520001c0e40d00c4105610705d00951400760300b03d81e016411504243ca40018044040303800703042c45a410a01b0720007074010740b00e041900e240260100c0c001242991501c0004400c07650b1407054041001b103c003001400c0c60340c00040c08981e00340d0203400340f130f59403080030542410031043c503a18020041908070a804620343c819070040c004e2003401f09895199a81d0701028820880d9840a48081c00c480d5410901500e4500002c0f0341c80302941d41035908d005524240981503034000d03854040c6000c2e0752828010008800b0b040350fa0306452200c42041d41d5418100050001e000c0c6114000030001f00400700a029291200a014462400007096441e4100060b02a0540040740704100010740340250940c5c2d40c0c81ca00400354451500c43d12505840c03201010105d010390301c030189154051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160368048 1250 160366798 160366819
    0xf17010b040f0219050a0c0206030a061a1201060504120b0402220911060a02060103170d05010b0a120c0806060a0e060307080103030f030b0f0907020a0512030a0c0201090b15 76
    0xa4880307000d042c911a42076280180d94241c440d403400d80511442c101001000814440010401d8114000c2e44100c3c2c0c04582e91a226921b03040014060002c5412950100300c6511007440c0040c0800c000e400d00c0c02c0d06141c1030311540c2e07c881c0129014040c40c031802109029150003100480e020a1301c207600140081c000100d0b801c07074001c1c0d02e840b405850400303005440d5501e80f0359003070145203409241c03462803c6440300e107000c24406000b9aa004180006002d0140b9591207600c4080310300c00315a01e44529039010300c61503070f640700080000d400c06c0d0750702400319409031440c0707000321468411203803100d60a86480b4816141c40d0305018980e001116204240034401030600100e684040156210704001d5648202e550b0544c03500616a0000801110615091440c0c2d107071507540d11480c4484000c8151034111440e6070f0708504a240484031080900320f40201c0708014a421203a070000c0d03205888204007401440c15010f0103e080ba0031480001e0190003210340480c47e0912030410803000c0440c01072451040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160369298 1250 160368048 160368071
    0x16090302061b0f0304090b0307180b01050c0d05031005090f04061805030c0c01020c060304151a09070f08241e1206011e240306090908030108060a060f1701 68
    0x8141c103e06803032100d5400480c003040100042d000c3c44014a9051300078000480c40c3c40310382158054800f0b100001070340c4850b120416a44908280c403c030101040484070220311440028140307600c19100d0050078201c2080c049000c0c2841c00d003490103100b46d002103065507a59503c07810300a00c1ca5540040a0404400c102000b080040024041f200b903101c0c05021803c0f0b1507000685803000b002c044500a080500c1044003044042c507440303034a4140c1d0700021515465851485800f49101d4030902c0d44000050300784003546501041d001c801400d280c4030b50381ca070b48402500200700c840c000c2c4140c00110f420300141c185420415030020303283d914107100c034595440644c0000c0c4102040107880700b0583c80440108040100105000c64009983d0369441400d807d109032034103590ba101402106090403001a451294480d80c4810000c014803071080012141c41e10b80101ca035070013031003610403a201d104003007103800700c45202d140101d40030906481c2c0114581034850b000f0540d2411070340c10555a802c4031140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160370548 1250 160369298 160369303
    0x12070306032036060102060403020d05090102011d101d07030f020d02040e060a0c05070c091e0c0c020f040606020d080702010912110d0c02010905041d1209010816090302061b 76
    0x15043c018a00503402940c40c54080c03845040c0c018040c40c115840f200c10f002c00b0a402060403000b400b25803801c42e5541e10f0b00801030340900000300c8250440300c00820504140c400110f40d143d4201c030328500c00c2c040d002e0081c481c2031824030040034007a600e4105000400001d030058002c410b02c030348003405005c0315084c0da8001404031103828400148030340001c070030800d01c1846407281426101140c202682009941e8880840200b0203000380c0b21381550782e1070110151442240e01500d050320300842801039842c0d01200400444014030224043c04030301202401c98a0180540300680b160350740184220030003103000700d4204a028244030150b560b508040808120400a60845010389403581160448a1841d00d45040c01c100070f0381c42080380003540840180e91154002045030021200410318114051412442401150300582c45218000341c0781002d0440002800c458082625a60b8042c1d44030700c61144030305081b0900c5030008000e50018001444d142c03014011415036200040018195031741440d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160371798 1250 160370548 160370599
    0x1150306081c0f0207030803011a2b060b030c0d05040807080304060c0f0201020a3f090b1b04030b07030b031501090e0d0210090305130605120703060320 67
    0x14050b12510300a00c0c031598000c0019030314004a44000d000c050f1540d140e0b0011400180070b20080000786c1e40d051503101241d5005c0e28103160051140f821200041400c401340200d6420944100c41c0c2040710000300d400c402c0d8192031143c00d544081d146003000160350240107020050003181c61101c01d100c00c2020581100c041c40c49240302c1c14000171403c00440c000317400c00c0c0c240040301e404c682c0104880c04505a0200c0c141200c106002c04821054910480c2d0303120312404003000410380460003880c884404a950082d4044c00c0c081c805411580d2260080d4856102c0b411b42c2c130001c150000c10003007000414100c0400e43c4140c0d00e00c2c0014400040303c3c0003900b000e0103101e402e0014541d0304010b2080080501c650712420f0002307070042051420301c03503010307440d142c15107030b4035092a564000b481309042c0070f0011201e5036031030b8050000455440b0f501c00362040e0441c0145100125a8500160074540030384112001d494008400200c0c50f96107000d10340240e0745401a081e0000d00c400031601d8064582c0c0b5005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160373048 1250 160371798 160371823
    0x6030a0812010e1303020a0b06010e10030b1207050a0b0d0f0e03070b09033901060806070f020a0b0a020c07080f0a03030b0a0515070606121208100e0115030608 70
    0xc00746940740c155501101000a0091101054401003a0002a400103401480154090203503121540c6460040c0e5081e41c445070060b07009807031502c4055480760705911140758103004460b8030034a280550440d6948060a005282d040350100300c00707101e0103510401030103000d6034840021550005c0ca406c0f5106482000710f04085540c404200d081c00c028000315841e42c020b84c21001941410b0501c18241d80c0c00c8c2c42809a0b2004020207030001c0e03403503160070800035400030b1554002d120752039031008506d641d800e0844090340000d480302702d089841c1d840425900080350300315501035215255050444022f606c42484610700344110140010740328001d2200000c20740301080644002c9545040160a4442640c00c06216904bc0001404150b0380c21801c0c03000d40300b440000e1500c40d0000e28020f00207154580010b85035404201481c0704001a0000c030a059240c2c0d075880d04030340c0e110f100d12104010018015850150344410040c80540c02080d80485404594680400c0f2207640d02c4609061444a1005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160374298 1250 160373048 160373077
    0x6110307060207150b01032a0c020603040506101203021b03010e010e030d0b0609090708040213050408030403120510090b03070b0301170607050f2502061207020105090307020f0906030a08 82
    0x10000000540f041d8003000000303080911581c40c0d0308910107414184c00084500581088008c0c1c040355101c3e2800a0207a03501601c155900d06003800c129030756503000c403503641800d0b01156010071107081400d051446164590014520420350b415145051410310300751580666070ba001600c03062109015000710030529402841d41c03071050a007000e099820300545103015820401074840144c60740607500f42d000a4034602040341c1e445510010301602006171620745031031708010a110901a400380214011842501d44880800c87c181480003074545c100c2c0c00c20481d02c8000c3c401c110b0b8103c0750300841045d100080c10746a610340c0755081c00348260000c0c1c002040e82e005403070300340d07450312001c000d26034000d001d5060030783c1070420000e02508141708007000003038400f0119075000a20724400d0440580301354001c1c043c0d030701c03880c00d51083c28403a0805c5801900640c01c0101080c0320f0100881290045a0090300b40c1e1071040d5200c0501050210140a0907010b104042403000841e52903130103409401c119460703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160375548 1250 160374298 160374323
    0x206070f1407050102070503060103170f030705040e0f010e070f02160e060307050f0a060509040615050306241b120c150604020a050403110a0e0c091c05030406110307060207 76
    0x1a07603880c2407a660481815136000325400d00040c1e500042090469601150b11039860410544e00311642c010002d41000c8443e0100c00d102025820030301420940c0c0d0400340c0d400030b6070760790528400074410a229108100c220070300826200c030b1195000380c0c4110602e0045507480e258500349140951165444442044214000c0c000689000d00c1074174002d00d4120741e808009145000041d00a4001e44220f2003231000004243e082611140c00c52002046046400a488000840d0140565004454803442903d080308040449100d001b41c420a88084400700b90030842000c4101c00700802c845104200c0340b04002140034541c4c0514010b04042d004034015051110f080c1140048810000d8090391150380144106809a030344902a14216500900341d034402c8c0b2085808159103400c1d5421030380d210540e6000300000c0300f0514000b85100c1000f511220400c0c81010840b9204900e44400200942c0013080708000c9244140e00201c150060081503a18040ca26540d850482c1e019140c11106142490f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160376798 1250 160375548 160375583
    0x14011112011202031501271517010b0301060b0d0509060c0412020f030f250501080c0d090203060f06120703080901030504050f0f010f1413030f020c09040602040302150f070209040206070f 82
    0x28082c40c0c50b0b21f0003035418080409074599194041c106401544030202800c0b0501108110940200000460150003082910345440c0c2e409801c0d8000801c40c151182400040b03922120700144842c810384180101508240c10b251a08031034284a0f401a41c1c0507420303403248206690180b00ba0710421104034010a0580e503400f400f00c2c40c900e91003640d0a0086840c3c8010070890b40c1141c4651340c4031102e021a5681c1d103051100c80710050034580e90194040c80340c00c1c100100d80351422850350186e24119006181500c0551407070380e54600600008100d40c02c18800741c0002c0d40603400207900548144141c44103082c01e0b06030603140460410550707161760f455000b122144502031150382c0c41b225000760801039500d000390015a0014111400804210302901c01d03030107880c400c0c0841d0a1841c401403113856581000d08000010750481c0c0400d03441603281c221050b0000c80004221852050044103050904696408100706403400038402e0344c2144c02044940c000034100408940340343c0c414020000c1d10f0a600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160378048 1250 160376798 160376849
    0x1303020910060e0105030f070c170a020a140d02100f0605130504020f010903020d030c061b090e06010801030b150604170f0601060905150313020a0314011112011202031501 75
    0x5030fa05008040090043d650400300d80140d000318542401950100e0a12381125000181c2a00d260040400300d02c40c40039650105444080034021101c80d002d00ca20641801d844103003030040c14002d83e001038181100c40040d5000b01504c2c0c00c80780da00242c1c1035600c402092050b00103594103080d4039070342ca0804c0704524010903036401d44d410a02e81003040c0c41c1541d012555212040308081c00f40503160314406c0c10800113812681944040b0380a200307102100890151800c5100c1c040d440c40c20703212a0009042d5481450b120303040782d07000080103071586c490104440c6005400345081e41c00c040100000305460300c5003d1094160250309004000240100c1d82071402e01300b042e0402810002082400c000b955915420384429901150707003240d0300e440e81c000e00d555500225400035040700180d01c2c0001444442030054094101a10091000790100e1095032442d1048401944a64045000500c00002d1103014901058409002c8400c0101e10307c030910005002603000240d5044544211140c10255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160379298 1250 160378048 160378067
    0x702030a24050c0a050c1608070e0a0b06031b0f0a090e0702011e020904090c06020115060c080f0d0b15041d0907030210121b0e030a02010c0602130302091006 69
    0x18001c082101c0c2c1000d40680c0300034401c2040d43c0f400c003c004681802c1808041c842640b10288202c0500d00340d40d504c2c24803e403680c495118905200204000081d02c4a1542c00751503001c840060200e407440c2d941c4084000d40030310b581000207051500f4000c132400f5010b100e009103001c5800f602d4010b649850614a10a8090010645811641000300700751a00d01000803881c8000128480580c80c0c901c03c00224004003c0304c10007500389248a040000c000750198059441c264030846440d41d840c0e01c460080d20140c8401078020500001000f60503c00708540c0041c2c410455001d0010540360381c3d203030000c2e2400c543e41a00501c0b4540008003084480b149901c1ca07004c0b00c284454404951400c00041d50f2152a540b0002e0f00507210000c2d0003154a1142001811030032010038100052030b941501c0114105075801340001041003140300680500c3c00240341405668141d460040715841c542d11f040103508010380000c00f04403c2038000c001640c41c00c007100c3c418043c0d000012501441c0900c000c0c0403030f50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160380548 1250 160379298 160379363
    0x2040816050612010b0d090c15090e0702030d0903030b0d150606030c1205100806040b04170403020904062403030c05100908030112020d060207030309050609161a0702030a 75
    0x1c00c0103074004044001a03050b04461170011a140c0700c4412250440c068645418000c050031100c2c0c03000f0901007240061240d00ca2103a542d650076454030307292071421000e4142c0300c1001507441441040e034462201d40040d07081e20300c24034010590000b00008103421130412002158480011500c1303940740d03003007840396034001c1c022442d06114080120780c000e480d07114100850303d0307100d8440001038282d01c1d4183c0f0140013004400100c820038907003400c1c4100312200640c4c044600e0103000780202d8940c8039407400e403410750380c0040c1881859125580c60070020408a8001e1913041c5510814070030030203035542c10030003c5001e5180c401481e00c007031811714205210025000f0942c0e10b00b26850011600304010340b415a00c400002d5070902100313000180b0b1048002000070300762400040d00c1010541d040e007011403040e100e0011102c458941071710b00f54480a03a020000000d50315000204110360301c1c101caa6522480310031485d485c0621a40209083c03480c4190262240e4290041e660041501031801108101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160381798 1250 160380548 160380559
    0x9011404050f0f0d0209390a030207030c120c03020705030109170c01090213020d0f0b090a09030509030d05040602070807030507062a12140405030706050703120204081605 75
    0x60500e40050b81c90084140c64500609600460401945074451110383c03141e00209102034904c0d000e0000300100c80856030100351082c1d00c0703821a9150501240d00300d00c4003e9980c080c1e0500250580440094004101c15400c100c0e04c01c0482e00403c001032020f20301c0c44441d03903070120241e140d4140a403808402e0707404240240c0c0f5000861000c1000c40840c1005142403207442595000084125800b40080304400b942c000744901070759240c0b2921358010041040480d40038803450b1003001031075044855402c0c8490700034150100043c1c19009070350082ca00740784a07040c51030820544da070210385080c0501d04ca510101d400003030240049a01046188000d090410090044504580e507290b2548002e110362014001c1e021080e11a85080703030603464480000f00700c1d0f4641c01d007041c14490140c4480d13440c29004aa80317181e400c198450f80d0401c0714255480a4001c2c051a86403041c115507507444504207030704109400020400c40c62060000b40b005004010041460300754040b01d03040b00d82d4456000c281f140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160383048 1250 160381798 160381807
    0x160605060a1707060507080d0f06050907020a15020c2104080609120f03060d080c01060519120b0705070813080c10080601030f060b130906140108040b0a14010b090114 73
    0x41d040003032424144e9001d89026a100d00d20303441c040e0000d0140344000340c0c1076420f1000340d0755034900c01c0c1e115208807041156100403a072152582a42c5910b8a004058850840319004000401054008104003981e03101203454171031000b854402640d159141a05408200040412102d841001400d801108040140c079150414000030140c9100344200040c0940340031000540550326802e80c01e0a0a4004c4041640c413404d844601b4020905800390500c00d004a0001440d03103210f2503440d400341c40518000000302d01a13070300c5111041000400f2101005400c2100500098503140504540070024100c41002424503444a041c4018400e8980c0a11178108040c005c260f07010900c0c0b44c0101080c02d0015001c85c1814020014122640082d01a4440042e46152143c1901160002c40e46030103010050917440b40c01074110b21480241e41400a9141808940440c18090819400110080001031f62400c005906c82c6000801d03031118250680103e21418196006058074602240503d40f89180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160384298 1250 160383048 160383089
    0x30b090a050403031104150212091e04021b0d110d0504060f1205010b180607110105030a20040501021b2101020d110715060509010902070602160605060a 67
    0x40040140049005034036040403030141406035105c07a01d024015020a0340c0d46846245d03009910120071056401481411001940c9d600c16000380c840102004003035505060740c110741654904004600c0071f82c0b042d401c00421442448440008490f01e42c00005894540100314010305001212503940a02c1d81050003600005a801000c584c10340b26517082002210700702440c03c842d10b40302000c04440e910b24003000450030300108000303402c154008915201d5070300d43c500c050100074014030781e00400031306a00c2080075966024002540d0710074200d000c0007698401e0030504c0c0c0755481c1001c0314100c2088001a0611055074144030308208032114417203014036a5025070200d01e08808441c0c41d560350107600745000c400081c0a40442c0d074505c0c042c0c0818030000b40b0b02c4100c5030740e0741c2c0060b00444038104101200e240500c0103000302402c07902c00070001d40c00c980c03034210200e019500c4080c0407170b013066080100c501c0300006800701d00c0d4501d00035200040e4603d4024207200c5085441d030005401424889030741d0380ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160385548 1250 160384298 160384309
    0x6030203060a1203020a0b070522030f0b180304090c0e010e0901170f0703121806020312060a05030a1101030506030705061611090f040501050a05090c010309020609060a1806030b 78
    0x48500030b0000005000c00f50a0807070800080030001401a00c03068107110724213a101f00035100d201140502070f100d0b4206141c0d040d810300843c0c4801001c0241c610711690105095180695106501d40c440004142c801142c050950f0f009030050442180d4418178920610707030210b266401c1c0b603800e0070207403881c8164900081500c8030500c60b01403903403419502108141d400b802a80000d165510498038580d4803840e21340d0032408454002400105503612091903002e213942e1000844446030095803520b041c00d000c01005110003000d683c0c1040c9810400101520204000300c5d525004040e100e8000400310001400d44402404461007644803200522066407030100f11035414a4681410740302c540356241c4100c4282800000f00d90080c2840104000c80c44170b07502d0309100703e2003031000300966a40c0342002030403508169100c801903400200880c100b035000368130251750640003c1656003080140760005210742c0c0720000e000c0008510200d550a94181d043e0002c2c06000c2505080c000c0c0364a1101040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160386798 1250 160385548 160385569
    0x306030b1308070f0203030904060305060406050a051003120915030b030606030d0906081308070b0a0c03140708130501020c01022203020102030901081e130210110c19080618070603020306 82
    0x40c0a085411300503011550100210b43c802c0e50050024000c084d62414401d8442500303c400350395503400c000014041c0240c0d48600c41c41150014001e08600d03007503480d42c401c495505d1200006106100001158031604540e0b49218542c00741c2c0c0116281c0c0d000c505240c1050009802c0030700a50009d03001e455031030b8215590106446061510b40142c1d86c9030250a40090040070018200080019034001400500b4020754402e9183c42030a00c500700300c007401201110080c00712010344241c0b890114411074030072904690001312220701c0c4d4010b62807513150542281c0c4400340001c9269400600200424107111000709410302010102032000e24640010351603218044071076040001840c005003030400903840800d20115100201101d5162803004150b1403480006c0c26441000402c8603043d10621809417a0700c0d50f074881c000b4001642e00a810310460007139181a00381025080c84000c102e440701006004c0c81044110440c00c1840782a03c0040d00740000c980200d400c1500400030041e4684030781d079210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160388048 1250 160386798 160386803
    0x50c12060a0b010e0d0305072616020102011e0b120f100b06120a060608010b1c180f110a0e071421131b0e060f011e0306030b130807 58
    0x100b0341201050049525251307030300840c2e504c40e0146409100b4164424041c0900d01e110308800405400d159100080354100e5030004041c00104004801c00142a102030310354051040c000800c428081c000300040320710020480400c6180d1b9072084008500d007105140d40c600c840303030700500200c005542c0c0c0710380c5680781d075a4103021b81925919042c4031500c2e440308642c0400e8440280070a541082041813019010a100b1007000503421800400c288443c20b04403540c14042c01c10401a40d0590203090000d840155400080441134450300c5021800021103800c5a6110f41205006840d003001001802e01c0190440c0f9003043c80705c0204a0901d030003044800364007041012264640c90055410380f0004425842c813001e803c401c2041c0000c8030a210402a405441010645020380c030f0207014007d140154828001a0156603001c02c100341020303071241400718410300d001c20716500240018a407020700180c0303800002c1d81c0c640040051060080700b15030020301c01514580204480c0c0c455044038000ca0601 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160389298 1250 160388048 160388051
    0x1a24011412070c02060d0510090209010e010c0c051c02190614070206041503020702130c020c190b070f0b06010e01050702010513090e01090b0a0501060801031e0206030a0504050c12060a 81
    0x401d00e558010f0540204603540100002d58914202e60341502074a0113440c0e03841000340080300400c030340c030300b500a03116140c0c410380d600300460340041c0c01165280607000041c2d50001c6e00e10001320711a26607001600049903c1009001005464418040e480c0810300c407000312540e400d40188600da07400b00791440c514600000301b03611241035000042d420702c910b9100b0200040c000714948100b58154000d01a4203008a0724030000e14200301440f03041c1c40c8101081d9005030004a030180142c0340ca00e45012015030f2040da6403000688a000c0c1d01d0f21584030320020f68078071402e400550308200c032407075016921440a1070881c0d00c84010b0310018056008409001313041c024003103074806004a000d200c1e80010021030100f03014044072410401e0003070074030b1801910003070079040009a070119140249412134025603207003443c1d42e00e50b84910784130200d003d041034103007a20383c0912405a690000914058000c46100042c1414285001c0f0310305456041054019071404c500c000e0703020000b00b0b05551020a040c0c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160390548 1250 160389298 160389301
    0x6050906180402130f020307080108061003170a0302160c0e0a0e030301030303090302030c060f011716030602250b010f050f030a060203070306081009030e01080408070f1a24011412 79
    0x14404c014040c1008012003991020081007041503201d002c090481d018801980d4054440124410382d618080c0806020040c019203100401e0642c94006c00303072541c1d2494014140081b20b046046c0e014403039041170311100300790340041c8a800c0c117201003d42c01403000e0400300200800c801d5555103134041480041e042c0343e500d0340c20b50141030090048030401800340d800da80d054500048006001c1d01c081c05186171820b02141d10710315074000014205030600a200305000458610303070341c0c0700c080c3d40642c1c6e4010540004406440d410b940011003030b4039041c070078440c0110540c140005d894100040d0f40c055481808801c916201544010480448040c4c105002590303a90b5558402d0f0058881c50b0b00010a070710851240382d0207202643c0c00000482c0c8242d813141d90681012004648c0303450300ba00e02428410f4104043e600185c9003000110706144a046081030f202021032000d80550b108a40c8003c1c0003215200300c2c0d10304003440c940d03050071001c00d00b01140c99070f03d21004101d080c042c0c180c015075031001110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160391798 1250 160390548 160390579
    0xa020702010302040306020c0d0806040e0606090402030f031b100501051e060c030d1505010e01090e090111040305100608190204020714030a120c0207031505060a0b0c0106050906180402 81
    0x404a44c00f40d50001019940c950b5012100b44c0d07113281d4040441d002a401a02080c2145401d0280701d02404803100204040c1e100c0e0403c001d242c2e1400b0b00b04a903d071003204030058500c0341c03d0000d0b0a482c01511542c00110f01c03c20f201078103011030303100806800ca2030500140f01e140d40304401d5080211030702002240001040011514501c10b858685049100200c0c002d6920007280d0082c1549625a600c0e110343c6550302e50054450702101d50707140c0d020a01d80034050007002443e089650348a58120004543c2c1e01407208a18801d62281d00262001d800c00340b185620103c041c050f05009115440003041c514103c565640e408000c00e8000070b1045400103101400e0002061314189800480c0f02600e960301700101c0e01400c00c13081c000c030b200340f0142886220b111080c001311f1031000322034220b4507007500c060705030900200403c4010002507101d412004040345c241030707100c081d091140c210380001030544c4c20103003001305d5400b005180620440202c80300700c011242011302241c20550586144d42800c1012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160393048 1250 160391798 160391801
    0x30905030301290306090f10091b03050f0108061603230402030609060601023a03052a0910020a06050c070204050a0b1f09030b0406050a0c090303080a0207020103 71
    0x1000180103803101100101c0c4031204280c00f004501c00c240e000140989502903c02c0507070104981e1a0792241c4a000000c2651a40d12201640704512880f0b0070340d840d032a64684012114a10f0f20b86044240c00505582250303014410280c02c41c28242951440398585401e095032120002d06c007110840d04c801170840d181c0e00940001012140200840034107080300f0460088004048034243e20034464000428540720000c900c41740100010380c050032043d15103070030032001001c100000c0d28001c07101001c101444a034a00f400100300a055801003094101050710390040c04181c500b0041d01070700c2c118105a03001d9801d08482401501b40e908400c46c0803903182c00d81c200700b010000030304001e0811040090010baa131006000340c6108980403c000c2d21400c0780d10b000c0b503d9442000f82c0128005000d60b20b481260118041c0e81c0b520f0b8901807002640743c2c0e03981212000113a03012140562a10b041c0a0200c845020310305562500b032400190440c55921300800b03011010341510403c95002070302c0c0b030559119 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160394298 1250 160393048 160393061
    0x4020c01050a05040302120418050c09030307050f0f0d0c170c1002090301060608150f0a150c060b15070b0613060b090a05040e0c0402030924010f1d070e0103 69
    0x144020055890710b4a00700014001c2101c084006000308180f04201d0001c1806503401c0d2a086030003c2c01c60300c0d180407510002c00010303003002c142c82070600210046a904000038904d051003000034000900054032010f20b40707180314407442119000a80414200d41e4800d805401b4190044020154801403c0c4c0c800c91a10400440064500604907900780020f51500106403154064008000e080e80c2c0e114212640d0300150341c5492031150f0348440b0f02e103624018003508410341d0f0081010b400035950b003130342d9449410034800e09000305810101c02d178107009603442911042c060940d40e070b487c221180d6401c0600361051b5030740203213403080c4100400c4e01c3d500c4400318402d244c86110381c108078040d2500024809900b2182c0d0a0340709601e66180882d55041a010703c51180c5005001800320720b158208100294200401280a61060301b240b0007841140a180d01003680728440703c400c0340c2d410012880b070182072039040705c0c8001202040030220b6416900004d0341c04080307850101141c01403003004030080c184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160395548 1250 160394298 160394317
    0xe0d08092e02070b04050f22061d060f0120060a0911041a060a0c0204060b0901120b0108040f110d0506070e030a0b010605031e0112060e0303091b0402 66
    0x1044a1920351100303079020340aaa60001c20501c84454550000326a42d1046014940c102e80c0140020029403c2000414003144001041482d48080640c4584144c2c003020f0540007481d51282c0007008065200740308a0b500d0b410707070154451103151130804100002c0c0b0b29107000b4104007816901c0301d20700040700c400c035040710305443c00c0e210b0b503040200c2e401d000380c4006070b0300b134402e141d04020341c0d0994076007407180305d00d9290b4213000c0110600000302000f45030340004803414140440030b131070080140e0312403140c00d0140c024001c55545608940c0001001254081c007035500b1685000b011801d40da8004440d158441e80c4617205e844540000e25164100d2684004180e81000c2c2c1e80b000d040811a011640c40d00c2000d06d603441c0102e848a5404051360303148000c00180c032003d01070f00107000980c07046008540c007411141501d000540324003080485030b50240c3c0200b2440450038000810012503010344400c00c0d1544000394114107090458540b1030300e09144181900b00007443c036007083c1c1c0b115010b40e80e0203074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160396798 1250 160395548 160395559
    0x306011403070b0408060f06040506030601050118120c080c0612040807020105190e0411070c03120207080304031202010c03140a0b040e07062001020301061b030c0204050408090f060a0e0d0809 84
    0x41d6200301d01a506e210554801c0c05079081320002070a90300707040c82000d100e004024010000c0764030700350054031000c1e0100070ba101001c4031200d0215981020100c40c0d41c5080c49003500700c41c7c0700c5c54100c4c09400d0038107454941e4824101040014603030380429111a82050300407040555a500030310050320144079682d651b950408210030010005600845c2e041c050007800c0e03405000c055003981d400000361007030036801882c3c5404410b05202040050b202c252960600f401150646034032900c00034a540c210340e00c21208003498400c07204106a082c060110074841d0340c1401c2c881d181c0000408240c480c0010280c00c011a0341e02c180104035600ca4010001e01165403007920002c0713071121001450300000445246060500c45050f00c81100d051086030b049404540e02c0240f840c0c2481444c02d81100403d100703030100940030070040050f0380c60b8494070303000368480c0000300d542d805454140404103006881040c031462061100400151b00007194810b481c40403038652540c8441850400d10a0054850854014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160398048 1250 160396798 160396807
    0xf0c03040624120614190203041707080307030c050412080a170901090506060d02060a0c05030c0714040b0a1404020702190b042318131b21020306011403070b 69
    0x4181030070803a07510302034441440486055000c00c1040c4005903495801b0000e69540f10450390025400b848c1c005114410311281d64004a5100c038583e00150400d5542050000a010030560944034003000103140c0c1c01d20508151400394044040780f05101c028008680c0060001c080c070f4412140c40b4540d00305034262074003c0c01e190340228020712043c0d0b012111845000086822407418000103001c0650007031801d89010980e00c03040742d02ca41801012500c0784400c0c0401c0456400c2805075601030440400840c1415859408010588994644550240441010a000110050307050741d55a07081918050303a03402c0284040303036440c8101c01d2804103210100364007280c0a002e0500030421a00240d0b0f49004001d00c02c504281c9080010f440141e2003071152540c24049418070203416403141214030f00d241c030301c645034907240c00b400900c1030544080500c1b50001e0046206400075414100740b04030051540810b00d0340032940d41c101c18021010200d0818a4480e2265010455980a05407045030641c68 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160399298 1250 160398048 160398059
    0x12070905100c0209040f0f080d0b041107050a03050903030702060c101d030307080a0f0e0a0b100e0112020a0b07060b040506040b01021506040e0d0c0501050f0c03040624 74
    0x2a212034040e0358854003116103940070705407145142900c240e4000384655103980fa250780c0c3c040780d410304040845405845400180c01b1680d08005064400703411900801c01e074800604010031503808010b003450a01040c0101000b00e00000b4170411300a5150034450350300c1e5480c0c03000134031310300440900035841400000c580701520408600403160b910071500c2488510301c207891401040002a0345244558010b00c009248940b02e00000c5411005000d030010f060150008440c0603034007008036490a0707600a44941003013103a880d613410351041c1029084001207041819000000c00181320702c80c140401e1803040d50955071120151002051289061a60b401151519102404110b00c0c058400c52a0500066841c281401a80000b03c4141e010b483ca00c2c040c060040031002024110300d403c55a16100d40a00f40310400c07500d944c0c42c3d41a190a00b821910f80b03041420b491004022000300000d041c1400001141c180c1600d8005a2042000c20f440c030000d02c3c1d444060161620858100c1d40f000310000e130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160400548 1250 160399298 160399307
    0x20307051507050c01110d030f060f08030304021e0a2306131415030604090606051e03120717031803040b07050c090106090b1e04060e030f0607020606010f051207 71
    0xc85910450a0310150f02c404d03001524420001d81d800c003140c1e04076a068148007446035200100b811a040790015003651950407a002c620943c2d00409542c1d0b000200780015490800b10889036030349200958240b1707003d00c1000c1419900039101d504100341851205105450250042c09803901c0040e11043e1102007040005903010b840744554041450b000760004a20f0401030150301e07011100c0d8152234615140c640500005119031403080d036400d6554a004074499a61501c48102c82c181d075031440e07104500038802c05060a28100780003070110000c024180004101414600340e403003400e000c958896661140b17588c2c604040102604c124000002c001c01e940c14404040c0c2401c84c094421100302070030300c00500c15103881c02e000d1b000100300000b6041042c0b203c2e078401070001d403a01a03518a58103003c150f00c10303d15041030300010046241c181c08503190341000c0051142845005009160508014002944443c006004507042004034019010721600600c00c82c0e0262a034481007010920b00504001d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160401798 1250 160400548 160400557
    0x5190c0b0702011506080c1b0f011401060f05090d02010c0201200a0b010b0a020606061e0c01020306120601031203020d0b1801050405010b040803182209050c0d1e0203070515 76
    0x44120f55100c1302186040c400c0c0f64051107005220210b500e000d44100b00d01041111241d00300d0001d11940d03114000d07000081c080c0030014401e0201c2100d0304c0d418540080e100e1070080103441d0030010709001c100c581d941c0b214659130f200c580a08000079014180c1c00100c49203070b00a40e5050015802200100c0040d400143c032274034481c00307280407907c1640c9881780e4504611171105914016803280780440d1032407078004002d01c0d440c003003000078005e481d882c0100241146c01001d10041c240e507011040140c10f08000c041d440300342d11404013900c11581140e48200341445e503201440c0825902060455102000e544804a48180100f00c1825040c2490142401407001d001da01e000d82e00303000001905d4400c000581d000e40c0d0554001e907040501851103000d02d180c100e811380d40e001308400c01c0c201c0000b180300035140d0324104542d00410640d402c2d082952804100e248a18010042d2210950101d00341c100c100d00c0410390700d0f4207400004185d000080c0f6145151300003551200d0020302c52803080c030b603800052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160403048 1250 160401798 160401821
    0x110f0705070b030f0610020705030f0303010f0909081c020d09050309040b010201020c0c0f0a0905070203030a1505061c090b130327260303010b0a180605190c0b070201 73
    0x4441ca5902c41040d02000c0c0010f6501880c00207540000c1411842e2084d903810700c2110314812119100d58510000c4c0c078284511150884c1d940000006200000f810726048002d408801414004c110302c0e540c4422152040b4213142900e5600010203040d000701d1901121080c0200d000c0601c040165401c215450f6488102054410b40c9407800b003134013035401030003512502c0041c100600301464407030051003450a407507010300b40e001d61145c01c0400e42c0b070a036202c0d040c0110144d500442e00c0e071a041902d0b074200ca40e501d1500040c400135501c02c100c03139500c1100310b40c6030410108040c00ca4000081408000c3c000300c2c030300180050041d00c07c0050390591f8070001d2122b24000d54507a80004d51841c1d11031100410540c003941d42030342d840810310002d010014000910ba0003100340010800642c06d0386401c60f0402c2c1c20511071050009100702499070302044070103d44108102c500c82d03251030440080c00e141305510118030518102c15581900a02411108a0340b94000b40115054500010028024281c080c0304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160404298 1250 160403048 160403053
    0xc080702060f0408030615070602030406060303020709090b150102150103050607090905100b0703020a0512030105100e130b0a080a060204050907080f061e030a0609030306060c050307060f110f0705 86
    0x750011a051200301c3c06580c0003080c541ca107803034001c01d22110307820308000981e038031070208802400901140300845c0728a005181c0058010f00314503000f0f09000307050344410300550034080314501094240940701e4100700041d20402c500b141d200010b070f0500c0d80c09440c0c0207a0305a110000024454085042c1340302d08c40b155110b0101548514910302120015580b4107480b400594061250040c0800140308180c003d00484000384015a20285000c003030080e100b98105001c00104168240490810400f80d0b1606089011412941c0454890103002444030711568403040c0003a12600c841c00040094203110707003503881c04511418050080d520a10806004600c0700d40005c0c03c580c070a0303619500904107005100099291641041880c0c24000800c2d00c418140400b000e610390f60420115100f603110384004500060103040103001c54146902500c103100001300401c000403030100440301c01c994465800952070003041041c4d4010030b89500c3c17425003c5d10000c1c0d48020301c0b074442d0203000d02c80c2c881c0c0c08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160405548 1250 160404298 160404301
    0x70e040309080607020d140a02071203030225050111030f06130f0606030b0a06030603020d0f02030705040504061406031906020c0c040603051e0102090105030a0209131a0111031204170702040c08070206 88
    0x40d40d614601c108e21000e001a000610141300300706036042c4440013a4024640982003030300800c00d640742c107001d6070b203882e0207030f01d46040e50001c2110a01a00540b08201801b040c11450300c62440c01d5144801031000e84909804019641d05032182c0c2c2c01038804d022042400c0000c41e445904c090020025244413a1080b0564500040d06a02c6400703040d0940fa40070303000300c0a40089541d0300c64400703055401280d041c01003101c04140c42e201e91203100d06c12400390034085490b5030030061107480100046e01542c003d800c0042044803151500c1d0300c400c80958813a100680d504c069001d100d040410744070046901c1403d2100000c18008005450807400000d08010710366901410300e09401c0340300f00003110703010440034800034102c190300b54040e050302ea402030f201c9556030a0150b804001c8402440401040f640708110b06075407940e00800e41c800b0a20400300652038030700021200c40c500800240b0013402c11105811140c407148807401036400d016070103001800303200b00c0740350083d0010904894002c0144610f40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160406798 1250 160405548 160405577
    0xa1b0c0c1a120a02040306020d0603060f110405060c0102130605070507060816050d0902090a0f0b01020a2012060906011a0702010c1e02090c0403020a080f070e040309080607020d 78
    0x4246800060003105442e08400d40c5504091600050611480c035a0a010000100d40c007400100503031408242e0000380c190a5281400840f8404039840302d216242102c0d030103800c1191800c40d81a03590446516444500e11161303240648103c1c039504a20704107400000807459005005010741500c220b00352540f094890208903410b55046580d882c0558403800040c1c1c0311030044004182d00001c008001c905001c103900880d00300f500175201a1029540d81050a541c40b22521952502c02c0c424400341103420819168217243c0006400c00d05020064401010420b80d54155120b0046803824252403842c50131815641e120031092041240340500303c41d001602120840072118a294140c5802c0042e14098a5251104020f24034402c4a86001c0c518000940e444905151090240e4048280d8a03403e62040c450801040e0784060001d41c0a80300c00740a15201207490015201c644161543d150b032a428225034101050f07000e601c0601901081c0042d0503404615101246003d81b511035a41d0400d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160408048 1250 160406798 160406819
    0x3050603030c2107051b1203090109030209060a03150218010c0b18010e03040b071406010b071101050906030f040c060f120e011b0203040f0f0b030f0a1b0c0c 69
    0x8204030380b42c0c0c1100b1142000c0100b8100b011003520215040681018260740d2400d261501c1090704604803401e9080480c240e15041007440010480e20024504008084002070004026400002d100e8107584000070019101d0748204402103030444400a58120040340300c100951000840d590f21400d0081d02c24595405181205030706980102907404582d1410f044070004072a01110780f6040d500c0da061513084040420160024044107541587e0707595991074801e00d40035081149014507003040004000d03510368002035550031034210405181d00181c81c030040f0389a22500410550040d004024489624030241d030b281d100d036201c0c0010070b110b0b0351100302c190307646d4045150800004203904441a08004150440c90351481040004078100020000400741e00b681a900440142e201140820015412076a070b0401004401c1d0099030481c2041244056440018003122806901c4004101025003a40c0001d034010034885666140000e03a01c0c00500110441c0816030f000400ec0d0710100d101d0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160409298 1250 160408048 160408057
    0x90f120f030513081c0615020f0f150c0703051215041406030d05070311030a0309051006030f0f080d0905030301140f030715051c0c1103090f010810030203100501060305060303 77
    0x11a0340386003040c81482c0044240713800051400c400700d480300300007d10b5034030280c2241101081900234160740220f03000e08e1032503e480c803150042503610551503000d420142c641d92a82003168000042d543e07200f141404d0320148103008d807410144141800304070040b40c4007940ca50861350111028040030300100703940012100c0c20b66100e035158100c51100c12105002e03000904030103200e400c5c81c2d80d036944132980b118115000728811201094a4100401c10464140102c00c00035204080801c03000e0300715280d00442e0420070398005c0031400c0195200d806d0242c2c3e40d0585070044000e00d07050001600501e080340d1a50400c1c40344031940303041c11500c88800e141442d100c0c181e600700540140b440910b403c001105508000310300409004d01007014030350300d40000100c018202c4200502040c1884c02080c01810b2808812303403c0075641050100003056503c2c042c4403840302a0034a0420941e842d001c10492070489240d0001f50706100e200007032040300d00f040c0c00442c1222440c1d2400c120030758445060544a00c074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160410548 1250 160409298 160409303
    0x3031801090c170a080c0303040b070207030c09051009020304141c0e0904140a0b070f090501021e010b0a030606030615050303160f0812270d03090f120f030513 70
    0x2d40010f2103004800a0300010810003070044400440749074071101d4565100690091140c4c1000082100b03001c010b903403140d04040d9620040403580d20b19101e0740b20002d0680111f4000c40d4541e40801c141d0480460544040d000d074400465486c1400c1c075249090440020308962140980a0a40390300101013406400010382034031001105202c0504100e00148000c00485e1420340d031000040803600c0400581841ea44100c00c0110350b4248044080c108000143c00a000c00205180601459030301041c0310219a8614034844221200c076110b050250100c0f0400c2500702009680000074411183c2041c0104c0f4000d0034100702003140e1a050741d03400c041d036000340c40c2c05074410040290140f00201038040c2c01c0f4001e415103024044603540301205680b01040d2120744000c01400d112000034420101c1d14006000d505401c0c11240084210b07448290302030345c000506039504100300611080464504105500030040304c40120326190140060469078030180000389060005480361412260b090300c0c464 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160411798 1250 160410548 160410563
    0x5090d050a0e04020415080f0a05070c2333060d0b04151a041d06070f0203070f0b071d09061e03010e07050310050f0c07170301080303180109 62
    0x255200c01602e000c00c40050041e00180d00300000502c00140c0c640c4003e030444596140700c0c4505001d28000008403001d4200d041452908042c000d04d1600528038082c45c6500c2598540115866000101044041036000541c1c0c0a4182c40c212102e41c100c10812000c04103d41000071816010344428400008031195070304841e4840500011070082858980e000d03200380701c4510b004170b10042c40301c2a64100d5101010808401e0005882e6103802e0041103c4a00802000c1c80d049003510401c55030703114003511140600501119000d440c0c1d1081c0103c4a0540e000a519224000580740001000340c0440e2410000744400028001147e43c40201e5112088024006e08403500c90904010044d0413042c0d814003581c6420103040e00c151002e01a5401491010f030240003018a00f84c103260400e050421100c0380c092401e400c10061792210310700d46c1e0b001742503421710549615540c174105415a0110700c1100c40310001000009103054004025482620605410314502e020028903a080e40c040310001420403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160413048 1250 160411798 160411807
    0x90506010306150816031109040b0a0209030a051f060b03010e07120219030515040b060d02030402010318120f0c081905090d060b090907050307060e0607170c0105090d05 74
    0x40c1c2d02d0b040401c0d0340310980081c107482e6544030304491620b000c0b03202c0048006800d640800a108503038511203212081907411107542c1c07400759100c80340514018a20303060250f0114034204541c4080103104c00c5c080d403240032a5005940a90b81c07903501c070902c0300780003649403c003d404507a16403905e050702d0481e00394110301d00e110344a400c0c0a13241e40049104641d141c2c0da00b4059140b41003c04814001c60300c8044d20002074505000030421121a0410b021a0245041c01015407481c0c5a8a0881c0d94800c4000d05c010303103079141c910040700540080140060100550340d1240240302007602602e1112002d9222000705032854441684c0340540c0d00d1020700380e41001d1111500c40418985000654080e0f841c0051030b20202c0400a8501500107000303495096039051040c903582003064200d5000481c140041030054a04070002e03645080078020802044015612081c2c0d948450041d2018140d01c45001c203000012079114440640010741c80580941c20721010840ae0352009c22803555224183d696035151 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160414298 1250 160413048 160413053
    0x90d030503090a08030106031d010606141602041b02011b091e050402030c090a24050a030b091905070c03020d1103040e100f0603020a020c1315090e0d030905060103 72
    0xd600024014425400759441071000140c011000358040c0c201a14005499076501e00041100900f1448011481c3c1c0360420501240d0340004400c8801100c0d481c519030744840d491558880110134041c001d401c0390802c100241c11080503071030f01c01100c1789940200728016001003010005030400000c9030101d91280818040041015001c0c4030a00c5000400c4008942d140c0200f001c0340c2c800c60b01895600404540e0000615194010390018001680c0b000c0310914001c4002c02c40128040d02c40c0c0603c4070014510148a0103508400341031140100740820f40d01c1c00c15a800b50320070400f412040c0c040d10303000000f00103500800c015041d454255004003a050b90649055580000c10303080f61195120a000028610421205141c0b0500030b04002650380781ca04250308004168540004007414018803080308400d5000810b1240c0d000c048442d800c140c4c03005d6100c80024001600c910540740f020540c003140c000038982040e055102074104a90307805c030402c0741c110121907800c10010310a40105004201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160415548 1250 160414298 160414307
    0x1060e1f170603010e0d02030d0b09060a171e07031223030c270f030f03091905060d050103020f0d170a02150906040516080616030e120408070b090d03 66
    0x24060b10280000a200c4000341e0700c10302d0042e03d5424180107030310003d0000c81008050180d03003103c200640f00011203041c1103002654502c1c06004000c143ca000d03a003800801042000309203040b054580c00c4041003481805015200c10b01d9000036103050401c410110300d07040c498600784a001e43c60326016048907042c010050900d41c0b0140c40c0245080d02481001405880044000d14882c076050f501001c071a00d1201707201c1042c0f0300910591103034102c4200d0b01400c0a0110840380404401caa00310b1503c106055403140b011582e4014640003980400d210a03510340303680c450342c1039a0084840158580c0c2100030440b00c5045001c0092900c1d4100d000f9107820740240c400780801c9505401943d110502c188040c480800c004c030b8450000f64014401c0c0010b110301400011101030b44001c031100118289080c5d03695951340940742c0c84000d54062101102c143c03103a488500c1c0b008507801038540a02d0594282d400e01d4001d8000d41000d4055204006450b560020890301c1c000f40103050305e480703103d1546065a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160416798 1250 160415548 160415551
    0x2100b01051b100b06070f260c010e061f050108130f0c03150203060904151401150e12070e09010608010507030509010c02120d09150501060e1f17 64
    0x2030600c00203121414645034034201002c10701d0007031001081e00700d440700a2031040d1821142d40a01420f4208288404a420000304a03031113a00100c0950401400c0d0040c1d450401080180c01000301000c504210701220640158410b45401d00c2120501e0320340251040c115003104440b0002400786410400c140d501454a86034882c4810784151103207070b400c2d11200c040b880c203c401110350104c0e058090040154540720010031450b010008c60131440e15070b0100f24250340181015088514002d00c0c054174186a80102006a80019a4001550b034031000d41010b0b180c00c05140e00490003985c0d2071040e0781445080107001003c04402020a1860700065021a0788040c05a884954850300003241004007402031600511240d43c00054a141404c2c21608640c246100700c41107400c004040c3c05140917900940e80b000104030030000f41d80005e80303000580a0000e407400b030b000700d052000028516030001110300b4003d8040d20012401c4400c1320761114040b0b0a555402e010a100003c60504c1021401405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160418048 1250 160416798 160416821
    0xf010506030a1d070b03041704030c12020f0406090506180c040b070c0b07030e1e0307090f06030506180d080705031f03081308070602011e18020a0b0304060515010210 73
    0xf00070030a410002203041800e150868000110000144002c03c582c1b0b1802035a072400c00c0000f54101800c41c0e41c1e10702c0c8262180314042d25040c0d410714440656552000d0681d050400610401941e50340d911001c0240c1000c0311400c1c407031002c0205a1400c05120f8814500c140403203d882d900d05410000350650942160500b41c03203041c00b000020031070b808080018018140251100c8601d14480000c02c980d411000800301400c0c10500900c42081e00c000401e0000e84203040b101080b041d00c1740298800401d110b6101400030301c5076000380481040c00c44110f240400350070701580d0040200800640d6104003c1d03c07071340001002000040e11002b00b0007000110b00b2084040ca16442e6501c5c1c0300c02d07000ba00700d460781c8000e0240c0480204451181000700c0c00c02841c41d80028802007a050b040102c6040d04000305001d2581c0320020045500b4458020018156005000c11400e03500c8118290583d0001c8504448480c0762501040815400880c94481780034140d00038261100f180c1d09100141c0f82001c00b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160419298 1250 160418048 160418081
    0x204090512040623070b07232a03070f0b040c0914060f01141204050304030209010602030a030f060f0303051e030108030d0f060620030409091202060f010506030a 71
    0x400460071a00040004060a0344d40c101500b0b2994240c2010300740b400d4205500340400c0048030000b03502c0084050b800030217030500d41482c248440d282d8002c0200e0740b4082440e205c0009a0380402901510741d5414400c00b00ca007001800344d10014659240b05c6c400c000781031f110b5130b03100742e000050481c1c400c0d55000e032003045050301d40c1c2c2e594213050042c0c078840c270960104054000700f000350078180020600d41516007480e209000c1c0c40c21001c40482da02c00c43e04405400c013500ea00180038404100210740003560b004d0109542580d4a900094494000c103211200003414410804044e400700d00406040d0b0f503803c008140c1241c5540c0e401e5801e80c1c0134804a1041c600f8081c0381c1410941c946005d540249441c0c1d0185998464004c070080480b1010118880054a010070511655601c02482c02d00942a9805c48408400b604e500c2ea00c0d60003a50b1000c1105405d0a8070f0364100407452032040b505980c81e8085524130340307503401c0040110000b4020300d80c108206000290044c500c2d5004400c2c0348084841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160420548 1250 160419298 160419313
    0x11030c0711060d0516080403050a030b04020702030d02070611030a0f030e100905061603060e0112050304080109030e0f0928110403050d08011a09010e060f1305040f020901090302040905 81
    0x1141550304850183c00202d5074035010050000c800a140841c0340d0520725000d40e44d460320b90f4004d010b9000340301c1030900305030b50b0314090421902c0f039034121040550003d01711641c003444480029540d04a0b07018081c0020b00a030f18000c103441002040d0750310f2005030f0300e074104d25810025044005101100800345203104410b207168000780103206544c0c1c0c041c095000340c041490802100c800010340320301c3c0401003502d803203401c001c610034420405045d25118010980800c0607801c0c014a140116007003610103500c2c0003440c8080540000340508654021389a0300e000112907410400c8041040f00d1102000f419114140f84030281c90f018450b102840040c000b0707a02ea020b03145900d294000c0e8101f1112544045000c0e030b101504900300130300408a01d1006682c140c3c0c1e001403d4118007031300c032030301e818400d1080010941d551030350190b8a038110354035221901d9840c0711038410072205107031040d41c0c000d61800302144204400740c0201d50035a041a100d2041c0c561555080c0401482e800d03000741c419000d03507103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160421798 1250 160420548 160420583
    0x708030a050103502b08010e040204200711031506011403070e0409080a030c0f090b1c180501111306050c10020a050c0601050411030c07 60
    0x295006101204000410358154a01182070b04203140c1080400d02c01c0013000c0b42c1e404803140608910b0040012014100039030001da6403034080b12060010394601400100081700d80c0300c41c1c000c42c0070070f080e410300000c10113040d94140c0d1000c000b0b0240e0360001000600290141c24036400138041c4011940c0e1465500c00540050030031070704895811502181d802e0b005401a141c104055040360310004454400b03410148006031076001942a40d03d03101034088005806503024040b02040700d0070142003030024a2007441c00d0715080d80068621000320f850b1410600900340305200580e0300300c50a40310001024140f0105405940204059900034042d141c01d1400d800301c140142a0b00e00480101e414072589103143c000c1c203450311400170700042e40303060014450042c2071f80c54610031104681085540d96004030b44150030b1040d0070070742c200e15034000a070410f8040d0b8401e0003070084010f80c42c01d40314166280e01c20001996004d00e00c02889403014000301d0002503001009100c0b1038800d5010010709061344 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160423048 1250 160421798 160421813
    0x10512010509092503030e06040b16050102040e0106080906090c15220605030f090307030c020d3e04050405030d050601050d18120e010804060b0a030204060b0a0f2c010507 75
    0x20482e0130f0b8034250b403108100701030300580c4050b81084221441e83c18507003840e420310304901070200f11040300c0783d40c0b40707a42c424000e00394102e4018024000c000480e560f1a00b10282017441d041c1c442803182d1040800045150601040d80c481700c11001b4098003d00011281d400d00c2a0840e4000c2458902d1144426440038001c62544004143c5521419102c0ca4800c06604000318002c02248142e0400c020305d07070020380e101c03846000c1e1550456a65410f00014105040f50302c0e540ca0654207440070455030010b444a1400c6c0080340180c001c592409a030307210405110a5640580740144950700c00d110440c503c001c243c00042d8840410701d04682480c004e100d17001c0030b6071007001c115050010341d10050000d006c41e031040c0301524500d0303080041d148810640003c140d036000400180c0400d070b82e5110701034541e448a01d02d81c010b540082060101540ba442c40b4402c40e0b000c035109101245030301c45906005c1c2d0050340441d400211031f414001284004107503481e03002220a4103941007200c2005880000f4600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160424298 1250 160423048 160423093
    0x50d08100905091e0703050d03050417072018340f02070b03190f110c07050a05010206061e030a08070f020a0509060d110f100f090501051201050909 65
    0x790001012034181e80d20f4002a001130012450503543c01442091010460000345070100030aa80740c0042d05981d2401d185104982c1c400c00354500c070030700240ca8001d104d640c0200481c1d030540b106004001600740700c10405800f032a00d00d1548130320310b0307200012082e2103080f10350302d0704540c400b48200d5a054040e450190342da1500400c0c4000c1790701003c2500c03003603604008140c0603107145c2210a14509054803030101c8400000b00c003805045d15401a540c664801e508100207261803e030300c0c3c2d83c48140480b80151100064001c07e03025001c0000e00007100d6100180c81401420042c1c60f9020107800c1001d00448847e950346595090300c42e00e14103900150b0040000c2c1705180c091003001c0e2400c102ca20420580308a035602191144001c1020300080ea504c200300482c1450344034003460b0200741850003180380a116400600c2c3e1041c1150719540b18541c00c2506031607150101d80c9d810050507156401506c09026842042c00d256521f0801800242040c0c1495a00f000000c0110b81d80da4940601d0441103840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160425548 1250 160424298 160424311
    0x13090f060f0c0909020d0f02040b0702090f0c070b0702010e030f0301080c010806010f0e0103090602040b09130504030c0b1305011e060801020909040609021203030109091e050d08100905 81
    0x4004200090003040e01c50049215076480c41400121a0000300624264550183d010410390000b05c4e0f40d46415554000103460300c0c0104195120350f41c0d03401190854200703403400e0f8090404000003071303106141901014403a14200040038107000c002e488001c82440024041000c0d903680300c480b900c00501c10000b505042c142150103640d01c3d81083c0a40782020906c4003810b0521260105100c1540e0300502c801030903001900e81504c10300c4e40078004030082c0c10a07407800342ca424400203022a5006c08100284451740b0280ca1203800030304122186c10803150101d03000390020315000a0100003a0040d2006a00b2031100c0b5803040e91800b59031200341c21106c9882c1c0c0c1d03041c0b00742c1440c40c5518813102802030310010128840214148840c1501140d130b403807402480180f0b696500e840542c01c41d9100448003491b0040d10013166101e40c0c440500b0340c010004040300b96910001d002c03801080e00080340c101c1201c82d030f02038094400359101503c16240200f000c1c0a000589003511350102d8250414400e1a10a95 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160426798 1250 160425548 160425563
    0x711070b16020a0504051501050f0d050115020d090f0311041b080a05070903031e0201150e061c02180702030903010e15060904030801060c0c0e09030d0e0102040617061309 75
    0xb8810414840f0703166122038061403d107010400d0410201e10981601042804c00356035a0000540402c094800e101603080410301d400000310750003090100d40c4d0000030322a001c590719000b5000050360350070028494404030060120b0107000244992090003540032004c0d01c0803d01074505606981040da003128403038002079400d0f0030408010341600450343c000c2c4007410030914142c21601d0051400c2c91252000a5480e204e070300841e000c1d4802d60006a0440701c0340c1c400918181c60701c0c51450032807001d8441d01d104250200741d0381800d400c400748034861194010201d007a10420f41044c000c01c000d009003510305500051141c3c01c0540c03020f00941c14020802c02c0640740e1110f0051000403d00405441a80100041801c11001a810440e0310f41540e00d5820410320200345840e248114001d9500321040e91100042070100346036001001d0020300e80000c0060000c504e4802c5400d080340110304c03407040010550800001c055403000c1003550824000b4107103140068100e0300500c00c3e505641030860305403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160428048 1250 160426798 160426837
    0x50d060903090e01090218012105040507051206090c01020106061d01020c12070f0e0702061f0503010609020a08060d030207090b06160b04030f0509030c12150a0b030c010302030105090711070b 84
    0x782c40c102480304000b0909092520272a03480c180c401505801d0035001c1d000341d41c4d50200b01404810040c01c001414020074840408078022139650b202d041c1511842501d11840d180d1089541c018000c070702c01c3e86c2c0d0750764501011144107040030f084940060919815805640340318a1310f41c440b41e00790286500c1001c000c1070050701c7c0000b0401c000c1c00d21340c8507040c82c40000b0140040d05501081c5640c0044040c01c100c9205000051801c814030200e40c0099415880c01c000043d03085000d40141407100740307a40780c40a40356694002c0c070105003d000301c02401608a000c05005000700e41d4011400c40c0c070064880d5050a520242035403200122020980300d03003041c482000300b0141d110503c0360002c125480c00f10b0030841343c1c10210341e842c940310002c10310a151a00c110165150300700302076825141403405114240c10f1414490008200c400780050003030040064110300ea500a008580c100ea1000c2c05000150392800c0040340c1d40e181d803209220301400f4090740050f07101c100720b018182d2040140d1300484070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160429298 1250 160428048 160428067
    0xe06060d081b1c050906041703300108030c0d120207050a0b09071205030a050a210b03070b0403080306040c1e0807080a05041a25020f1501050d060903090e010902 71
    0x20f0b20640f00d1000c2002000c0046410a807035034002ea44c1124950701014804ca50221480ca0643c0240c0c0540780440356080305a00c050301d091030038030040c440f004c0c491104903602c1d5a030f010345920036040340360800da0203844d0032501c2c184140c5030b510051200c448011b00309480703640c465083c086841070640c0c00211440601c0440b40b81408184000c0120921b12132030800e136561520388a00400c00ca0300180000400c4510a0314084d204429007940c0c00c0580030f5090192815160040185901060007403045a4021a82d403403210200c40680b90401201c0c0c0c00d42d5502344c10000a004802603400401a8801001c90707040450700e0241c0300d031562501d0302c441a20b460340004010700e41c01401c1e002c2503403c040501c408103400040000c1e40c1c00c125020045a941e410f03150040d00a84c5801a08a08c003012010026607070f40420308858410604007541c07a81005900601c1c0d45078402c1c0281030b0f010183c2e070303040c00001e6110f61084000d50f111303041841005588158210a48034242e010a2940340c002613680e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160430548 1250 160429298 160429333
    0x150b04030b060619080402010e0a0806090d0f0509190801020319050a0c0f03050604060b03190e2e0e0d05030103020f1801050103090204060b07030c020901090e06060d081b 75
    0x20701030403c1d0f42d21410034402c0c0b107103c5409808000d4401c28080080c2c0810256440780e00002d02506014100150203503031950f50301d5403203600300c0301107a1601601100c14038162185d00c0a205c058699a1100c0c1010915410840c96a8060421480d138038015003000400d40c1084c0003a40c450203a001c040c003050200303a88a03400380e0300001c0c0300d01c6402d803800c0510081036410006007812401c80d45400280c0daa980da020500510241c0c021109500b80031003000007000704041251907900ea0703444140040726050880b965104000400c4020a040e80c040e8a620204406010400d00601000104522048522060901c1c1c40003000c2c2c80000d00c000014400d41c1444c0109606507041541c46244100280d00c0c3e0886030361060150703504040d1030740c1d1400d0555586800502c00742005402c0c4561380c0c1ca9901c1c0103414600743c4201207000d80b664500014010515100b07600d10701400350043e0150742c2c5c40c142040b96001c1d1001048442d203100340181380600740444c0001e0031036022040148901e02407a400181c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160431654 1106 160430548 160430551
    0x30b06061b010b010906050306150c12041d090303090d080711060112030305010b07110d0c15022d1b01020c090a23010e06011101150b04030b 62
    0x101901d41c10341c80380d8101e480988541110969800054884d0f02080314229070002407042c050307940004440c01840e501e100d020903581c400c18408542c55094110350410f01d000002050403920f1520f00e141d840c1e0304411943c0c015030861401c810f0382035840801d180c0078010040b0050100c1c082030b0164000003101e201010940b500d5603121101d105c0103202d5018294002410400006031071400f40046400030354101803ca0720b14403542042c050350010a5000f25109444c2010000c2e0541c60307250080da00a2060b070280031016003441403e02400b16a60300d0a00400c0e1418204800d041b00185085080c4800d0206043c2013450400503800c000c145025290030804240c200305024100f988002e0140e00824580800380f405601c802c00c14881c240030b003e4003100c11102080b22580a8110f03407601d076051500105000040c0c0004502c50706150307000d148840004a003e2080052020089 = true := by decide +kernel

theorem cover : BRFrame.Cov 160251798 160431654 := by
  have h0 := BRFrame.cov_init 160251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160251798 ≤ n) (h2 : n < 160431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
