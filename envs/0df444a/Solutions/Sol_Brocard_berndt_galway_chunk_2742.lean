-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2742
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:36:16.968516+00:00
-- url     : https://prove2.me/submissions/c688fbd0-9b4c-4035-8b23-2aadac22cce1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492985611 ≤ n < 493165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492986861 1250 492985611 492985637
    0x1e0801111c0209041d030a020f07050a06050a0302130906151404050d021201050a24061707020f062d130206251208010b12010611010f0f05040209070c030c0201 70
    0x10181126803584421030b01c0c01c5030717656590348020000303007900102a000c96601500c0b500c6070301d0f11004540f01d02c0350300c000080000c02006004000410a80600745030040c9401000d00c151b03d0300709810781090420650300c00090000760300d103a1217244150081c1c10481103045148014910034440c0e401250b000d25204200d150864a40815045030300da03071b0714000d102030b01c0c001c441040101000a98400072110090758243d0244824455909690060750340719041507400c2a44801a0b001519850842c42452100f540c003500c1370000300c0c0540014070000b0403120101040f034105003401621a120100000140b141c14190100d5121416906a54040c0c882034061040e40048904a010400a0030b0800b444c034200090006000404422521b424071241d890752200a06400345850002d000c1804400500070513000303001c0300440e418004004108801200050801c2d40c686842c040499902c580600c0304510701050001c0d440045460711007600c2c0d04a031001030002070f414034040d050140c1250090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492988111 1250 492986861 492986869
    0x17070b0a0905060c060402090c070804090c1101020304030905011d0a0e0a09051b03060a060303020a0209060a0f14120c10030e1005070f0905100c15061e0801111c0209 73
    0x1c001408010b288507112041e039401326480b980102c07012440382d00e040000814011224099804040c0c100f044603041508000d51000107101d464103110511002c003000c1000784409000030b520a501c42e075a2000c01a00c0c0c03a0015280f943c8a407d403c3c0d0181c0018011980d50b00c6034000c2004590b80c9800e007035040e850f600f601500400c0c00e810040e10358000e0340311190348550f00c00c40c1045501001d4045401c0c503600d010000c800c0f10640c4c0401030050b08401420405440c22000154010800400c00201555180e82501e0510040d501144911403160034400180ca0f0590220020300c110b42e01030b1042c10308100c006000400011000e60506581e401950b5208000b00011400030440001c10042400d0054000d0081e82010000341c0020350101d9020070301c1d0420007061104036041fa00c58081d00311680e603980c410b8039070807000d640c0030540c0c2c1c050014075030725100101e0140560001cac40078001410f14046a0035079000300540b50009004200114511601c0708201001801c9144016110a4014001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492989361 1250 492988111 492988127
    0xc270414011d0612122d07080c1516080c070320030f0703170a0c051c0f1b080a0c0c030e04020c0111130608060f060912030304061517070b0a 62
    0x40081031244071650700500b8040d02c01001800481084000c2100c201b04e40c1d41c00c00e8400b00400700032803c1c188650b00005030700b140a400340c0882c40095032403a440e81840a08444000c49010700303149000c3e01a01100b80d0090b08080c0c00140c80030701c2c1440c1c09120346020b84034042501101051200f40c1c1c0ca4450007000034025078861041403c88580d8641003814003c0462444c0c100c0c182c08096250b022503403c09061280c056960340c03a03254241003000e00c148034403028000030300c0d500486442e801034048010750351040401c0946030120f0908145040e000c01418041d004111150b618600780d40720f0406600040b16951860b417503c0d224400080380d20224019000f44402c0c8151582829004013150350140081c284009400718140c175403543d540d00840d17001c2400e44000d80c206038014103441c002e080100060a2004004e403150b00c10b01a0b541d051880c6a0044405030303001991640325402c1200c0c0804054020803080c40b0340c03140c8050350f02c0b03101d0315241507100303014241c40b0000c1d034244054065080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492990611 1250 492989361 492989389
    0xf010e130e011a0409020306060f04200d11030f04110a1d010302011215090b060f0f0705061b0901030e0f0a06140601050a09030b0c270414011d06 64
    0x78880d1040392000140a0110096442c0070032100b04480d0b00306080c03d1091108454004008120b107854240521444212000003140c000351039504184c02444403c0140341540d5601921a80c0c1e0100c0e90b1184040300d540d10281c1404546c20170504c02d520440900740c2c3c2d0090341005041c60f58801400c001400c049440d0b014401c4800c1e841c22804010b003440c4d0b44981240d000303894640d05103200c04000401c94940c4820b08031400a6624103100055595200d2941c15a0140c030080c5000d141040b403800f59000320030307811142400021f0040400c00280205504402074086d0f10b07100060443c0036035141d000326145030b4100b65a620104c6d807240003c00c000d14400c022501542c0e41031141c2e040c91405044290300215a551050000c200d05521800c04c8894020036942c0340c15110307040d0390b1569951000642229400403090058101c1c01c030032184604020400011600f4400041d001808192040803190071600040900104140e020f980c0700c281d1205683d00741a00c55075a041c000803c017080c00d941e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492991861 1250 492990611 492990649
    0x10305040812090115080d0809060739050303150303090a090c091a040501091508070507030e04020f07050f0c031906060f0f03170c070303210e0d1d0f010e 68
    0x4400100c56601040003807d108036035803001255941ca811066840b00142c0b0201d000941c131902000c03131640c4200419480a00c4443e405110801540e030075060000007050a803007541000003480034802020090040e4a10284c2c059420044100c00048091007a0320031800071030f455100314100c042c0308041c2c1d0700140c00751440c104c1c0c0044103a0200c44c4c0c0e5030481d005183c0071503001e60b00801c03d08440201031504221590f5480d5069a031308000300c0306504410800c80c2441700c08844105a41d03285c2c009020900a801e580c15100c558a0a03d9450184440620701c400d40005001809546000c601d04060310b5140300b040d0045176640c684000142500e600800740805034003008a0315004840105048038095440960228040980e40e402441401c0c92694907620982080000a00801e0101da0f201092280280d00b1884036440e41b00366454030b030400b0481e410481c204c1c0a81c0ba00401120511840d441e0240c40714603020b008510200c10410b820350500020715186002a90f60100c40314411091217 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492993111 1250 492991861 492991901
    0x80a12080720100e010911010f050705100203061804150506182412030d090c120f060c0512010b030a0204080d0906021525020709090b0a05060103050408120901 70
    0x800e02c1d511044050f90f0b100d103031420b040d071850958105024040c0c05580000750680c400503800c0040d240403186510b51814040d080c0f003031a01081092141c41c2544101d00000341e600e10b80b40c000c110a44003003c00b40f0480c01d00240910010560a106100090005200001e2591183d8002443c2070b451201c80c129003512210401060003030406000300450f08950750103240340b10f003000f001040040002d5500e1070754014010f0070068041604001d0003a0300882084941039100e801c28500700c80c1000040c1c800c0c05164020604010380d601c46c9030900c015924005040442c4154130200c074442c18031400c43c1100000c0301042401e425641110f0041517910111450f04054101c0900760905910607203000d40601804e210b60014402407451140101d091800012048074a81c1940c0c095842c406074114030800030040781c0745221348981070502d03015440c40c445528000c000d00c029550000d1515040600b000305001c00502a5015107155510002e03444215075600c1b00c0607401014034144c038a04032000b41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492994361 1250 492993111 492993167
    0xb01020c1302070b0105060a1b030912030c02031002040503030a390b0c03060616061b030f05060d03050406110a081207020f0f030d0e0f06150a080a120807 68
    0x10ba00502549102d0b16048065a03601c2003084030302d00400c9000000320b40f05a01801100101408051503a4401e04241215646514500401c603d20000460200c0c10340d031546025407070100540301280d411a142986018200b43c042600d070300542148006000e1342144481003089000f42001501507120846142540e81403841c0403000002441500d00140c0a004201403408140c00c80e449545c1c05040b1500d007014039024141c03103d140840543d519955035070881c215081c500302c02d02054445a9020030004400c000000c1161400703031885225085409440b400283c200d03045d58222655402c03c1d451588c00001c2d068145580500014100580007510248a009980c9042e01a217410350032680b4070080d00d60290b544001c87d030f142100e10340c0180220201c4a00c290004100c4c640300c481550040d883c01407201d447e0070001c0d1008030306000603a000840c0c070704001d0300100040a5180040420310165125000c0c24501c10f0030840c20004200001910f15001e01300c2803802020f000300900302c1000c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492995611 1250 492994361 492994399
    0x90f29061c0f1202160605180906060d050103030302032403151803031e0f04110f0612040602041a030c040e250e0310200309010e030301030606031203020a080a0b01020c 74
    0x10300041c2d084139145e0707400441c0051095041d5540d840003010700303003905550f21042020a8400a101c00e0b4018000c1104070200900c50144600962080d100983c882c102100300b04612004c8896a07040e0180942140142e0b5a00150300c521914000c02d41000640b500c2c01d84c2c4020001c1190000804d100c00018401c2e2201322500d603403401c0100c3c442210305d40c2c540c0c03c0801d418800c280c902802e14004013aa040360b6182104410f0760241e0001c03c0281b400303003032440d10100443c08580a480f105c1d408201000115101548000c2c41c800303002105155140c016400c0d5040d001714011901d04002e501d00103245110070641040310302101c0030311140c81d2100c01000134180c00740503d00600a0060300650810100c1e2405580d00014500711003850040901c2544a900e0b00002c001c6003056417141c1041c0003003031040c40214042d6000d100041b480c541076041c110105101220030300704240c230400c08514101e9109100784c1d000541c0401c0441c0132460000104e20700440607840f03541c4030194004404c1c074029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492996861 1250 492995611 492995623
    0x1062601050c0301080a14010b030109060501210f060c09170102181002030412020307030c0305060702011b050a0e150c011e0207050303041203090f29061c0f1202 71
    0x140400070300480d69412500c8690340000c5c400d0050a6002e0040c8038009468507024030205400740c00002004184440000d003500c1c282d16042c0d9a4a5035400180204043c1085100403131300d070b1000c846507260391580c2e140791f0302000309800340100d6a150712407469144101c8030701340241940180c08801048282d6101c0c003c2d8449244a521034556403c42210350418103442071000c0320075009141050310700800c0840000401500300c1c2c0c94001c032040400080d50407142c8002450180000700103514054a02a0840e0034800500e81c0d440300b85015040841d80c84003c03034803a595030345044400c01c40d5100c0859001882c0110001c0600004600b004400310f0540c850308205200041e107091384051102850202d200765840034185401c1000003c021403103035614064100541e14002403603440c00d8440c1106940003500c11141c1c54941e00700080c6070b40540303841e1030303480c01640308890041c20090005058000d200395112200f08600c600745090001548400f5003054000009540314400c50400946443c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492998111 1250 492996861 492996929
    0x405060d020315040b0a0504021b0303180706020a080304060903031b0e010f09080a080a2007060905180a050c0f0d0e21030f04020409082205032407020106 68
    0x7150f9408640e8145801d0040011404c1c010b048031041c0d90030401071101951109414226181440c28201c822034810030055128032840d100101758200c5100c031305c4c1e0034a00654044c0003154401042c5e140803070300220440c1d8010341c0c84000000c01c0e0545150a6002e07160f00a154541a21020420481c0c1900952407d00c800001d07611444c1c0110101c0c400d88180c0217602030760215034401c00b4049c0000d01000010541d207291030404103011540c003480990030350b0100780b0178640354000d0402000890b8026407628068042119070407101d0118910b841a4144001c1803005804c0d10b56011030608556442124800c3c501c0104a550710b43c2c07000e2502000c2c10343e40c07548400c544160b40340300c0520001c0d06800205000d020030030a1071600c41c0428421440701c09041603030f220b42c2e6a207030400000c60240c0240f01188071000b000c28031100070400c11000018580c080c034004d410045d422b500d040c10382200081901c4d20305440c0d0300a921080c07400c0707005241d01d0b002a071120b40b0301c0120030320503000c4403110380400d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492999361 1250 492998111 492998131
    0x100b0411070c0302090610050f18130218060913090602090d0809031e0a120e0907032405010e1509120604060b0a0e06060304060906052703030f19020405060d0203 71
    0x6c0e2205810f024481500102110000d081441400d0749001918010100305400c0c01c00c5942c0c40f884180000c0110180080c0b1101003a40090486502608900e42e40a0841d044903200d061508910119968400052000561a03903a42403071381000469410340310024400790106801618070b160070b00f91940003142c040d10038451100d22110800010141c2a1070b480d5a101402048565a9486801c144588120001e1140808200400da214034110300d11403041a50080380b040000e11015840b83c1c100304000c000240141740030f000c603980054030020102e900b80c40214003180d9182907420b0901074480032540c85540400700131000c0704001a110f01640c0510000c020014401d020000c002c0f01c00e114410003c40402d001070580d00d4804041c0d90b0190045c0c8020400e500c01da500c0808031a002c03140d0f080403500c402440c42e1822662500305002c041100000c501d14284412030200740346e0001c208100443c20512100c9808950750107480082c10b025000903200c8255648410103508119901c00f28 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493000611 1250 492999361 492999379
    0x40c0201150f1d04020a05060c010209040f06091404051b0402090a090608100b0a09050a0b0d050d0e01110c0913051204090b06030f010302040b06070c0f080d020f100b0411070c0302 79
    0x40c07100107050113010726030061070101050318000a00c24130b608034802940041d5820310015003583c40b031f80641034559580d50070000310075090803680c20841d81c1c11030104c44a03400020810000401c0010200b40841e102100004620b0071003000074064403600c1401600100d9064000400c04030640144040d1400c09080d50307500503640b2650000c40b51491003a991181141310204510b0202d580300d82d412240c28040441d10b240c0d0500410310400e41d07014110344c00c1d40070340d0888100b00d0b4172110807144280c091908004100c00840220307501d403800100303d48036001c0700012070110643c5000000700c4c160312000750f407101d114100c504101da402512900d8002410202c1e100380b1442d0100c11240b041d1980e6a9902840c3d08580070701c8020843e03001581c0d0810070402c002800301da880b403070042c020612840910070031401c0c000f41c0c0f803e10702d5001c089801c0d940428a4003242d51307800304080d42e403a020407000040d1003441b140018080c0807180080480c40400240303503002e0001d14154503054a00030703500c11007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493001861 1250 493000611 493000649
    0x40e070b210f0405210d09050d09090b0604090c051e040806010b040302030a1106250212010513080a050d0203090c010311251b06080f06090402060702040c0201150f 72
    0x20354504640007401a00414500700e040150340d4582c0d440f01040407170f200d09020885e03001404a903541e80064510754400392418980343e1f48480715030007501210340c041c40840f0000d00450494015030246440041e11000d4a4821038030401c2940c3e0244440100011400e4004444038600d41c001e008450240c0502d100104aa41c180b004079011240e02030014821b41e07490742c039065200d400c11003104e0303401881000841c400051a118015452040071489205091544100308204c111070040c01c1c6140d041900b0882224120620a1122600100029900c070f9008004996034400c2003a0041c1c464404410300225000001d40161000300a03202000720b0211000c1e02e9071180078507108110300030120322550005242508150f50064071440c0f4a0790b000c2030407481e0301c60900041d0001c80001d1110802c01190011001b882d0350002070503520800682042e40214507248100040030340241d45030b00321409100e100354040203c14692640240c0752548031000c00c83c10b4102c40c49256840500036000038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493003111 1250 493001861 493001881
    0x50913021e0c0a0f12020622060e070f08010b010813080906070f0b0f0405061f06050a020c060403050c0118030203030a271e060203090618011202040e01030c060e030606040e070b21 79
    0x1d2804e4a4448102e40701c0e59030380d54409042b0a007081c1100b800703085400510301100320a520050301c495000422460340c2440010b0030b8420040c651342c2d17800085054540411100402c0750380040090f02c0c0d00d60386003c02d04003000b02d02d100d00c82c000d0040071040100003422014000280c065441b038402e5549940300c02005800820129001d0010382e03108684c2001114021401007800381000d00503a0034160031000003076070981190384241e907503803c0030032140c0543d81d00c0582694a00d460540e050101070954002c00d542e401ba81c00c0300002e00c084078051100000c140201c0d43c0c8425000680200b400303407180d105181c0c0b001290780007403100c00380e40302c0841d07200c2c0013105884030000050001c038149031741a20401341520400200c01c0c18085445c0c10622200c90300d00041c0050028500c514105515514100711802c0065101000b00f1507a008220095500480c880340c22101c1203c020071500c1c1c0707c0e21b195007081e5081c1d05c80400440001807040350b1145520000c94043c406d20310030b04043d544d1a0703001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493004361 1250 493003111 493003141
    0x131e150806090708190614030f030c0c01050d060803070335041211030f0a0e0604030b0609040213020403030809060105090f010330050913021e0c0a0f120206 69
    0x1154460b140d54001510144103c07030340d40e4041c5101003880010100c0e02070210440700e541e000303c14440840042e00806060410942c8070016000e001140380010711070b446600c4a400000d12410442c001600880603800d58000c1805071110000740da50302d4180c1d14029004651a0f41e0388040590300d040701c1001d450b00040000100d104000c40240143d03a82c1e42c1d542040014200c80b40280030540607400c520b0502040035007030035581c48214940e00d4880380001341c00c42ca5001c040a1003000108800d100280301c0c1ca0217690413020581366041c1381d40f075500c0051400c000c4185201d4802e072000c1000000d040e846980039004065201c161006640c960742817100a410858420b21a00d010300c0040002410210b01011103000d00d074452030b040c0c1c240007011140400d022600c4c03400240302146107c55460b210b85034213540d06401ca011464180307106069481d400c403000c80d01158801c00b00700b0204076001440f42c03491181c2e01283e6242030f1542850701c01905400e80c00e099005100e80800104001400414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493005611 1250 493004361 493004371
    0x702040e0d031a150706021204140c03062509170a0209090105060904080f19050703030e0706210906050c030906090606151b0a0302100c02160308131e1508 68
    0x840302002d40d031554480b51310740c45040102c850682c2040b5059801006100d9140510306c80c0c41c03e5461012080f1256180c1030007458140d1094001d4000d00c513518003c21411581c1216024044455080c0840f0940d800b800d1a40408805218501440f0005030f010440700c2c03020303208440e10000c1e0b4031403481450803100110791550300091075001080101d029580902000e040e205c141c5443e00030100600c100140081500070080b41011070314008254050040300802c0300e940d0000c102ca03170702c0c0007001407545c4100840464071600000c0c8000e03044049130022101140c00107418001c0d800e00841002d060380c41180c14000328042c81c00882c10444007c00c8142c0036490040805482c00e95031034000038164009030710000784a80d01404403c0050050100c0003445003e500030705108000d10a0080685001160f4101190002c071118943c00ca5811620026281c0105e01d427511400b580d28948240071300358001c11640b04041c00e521310103880c0725040700151411490888401c50b0b01400c01c0d1070752003060710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493006861 1250 493005611 493005619
    0x607020f1506091314100f0c090b03090102040f1509050307270e0d1701050f011b031106040501021312080306090a060504020f19090e0a0b01050702040e0d031a 70
    0xc04503509280a40030030350010180711024104e030345075035030f031400d041c00030b84c50341290340c0004080003202c0401d441801c91018941030b003031042038407500c8000e10b000c4c0580100041144040042271864034258181c4002d0b0000004c020b40160312009058998076440c80241c0c0050740d11203020601d41070124002c400ca502243c0746c1c44070298000b045104451042121030015503641e20414941e00d0100100400010305031100089103104a5680c48100303016004203001d012f040090041e2642d0003961001c81d07200401c1d8408040300c640c41c04441c00117000c26030140d1031181d9010b100c20b006040d401000c4a5503541d04001c040ca41e00c42c0c21a0711a540464094081c0c40c2c00d000082d0309003070038814180e000c03041c2c2c080015569180d500003170480c0c2140d615040e4042002c035403a110342032032400943c61891542001801c1503d08a42030414400040509540940b10440d400860740207405507840c0382d6000f0b009018604107480e100741d4413402c0020840000e0306100441c80d181c449050421000c08000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493008111 1250 493006861 493006903
    0x140d02100902010c020d0b04020a05100e010309060e070b13140d02060c0715120e0f0604150e070902032203050d0c021f09031e0801061116080607020f 66
    0x1480249041c1c0800d0341800310300d494500046c0c0d160604007400070720903c4018401d062a0040c05a00e072010781080e4001c4084c4500b1302c0d090b40d0801c03d07500b2000001d103000328540040f403900c5805081160921611840340f244046515407041000d42140804802030759070031070f03845144000380000c90340c00f160843c0084440720090706202c002045004045422901055034560b50002003803002010b902c00607525034107511060034280142010100e03407800803e81c4040f40b54085840310b10107880100000b0508a80c212200580d8001c000c126200d0011b44103016039404405020394022a0205520303524043c601d101e91602a200003181505a61542d09000421814400606820104c00103502c00c018440410303210b00c031102da010b43d90b0100c020502142c02e25000d420201004068510f48600d20f40000d0020781c05a5028110740c614600003084a0701d541205040c2001b0451410f6000142038004c120f072400090540d00030790645d822200e40a003e4401d084d1a0b000d61410f07000070268403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493009361 1250 493008111 493008133
    0x181203020d08014a070905040b03030328020301180f09110111070915050418030e060d020c0f150601020304080a17191e0c110d11041503140d02 63
    0x1400c520261513910030486500c845800b96554000b1103418801c0e03805a03082801c01604551202440008001c1558144941081000041d84138000244140300030383c1124811010300100b00002c42c19118442000c40d80c0f941c48610030004c4002002d03205080a003004295500881c1d04d100c3e89184541100128624a0060004448000d404800e0503401e210300103021911002c144125011510302000b2101c840d841c2406020980d801d485d0000c03002d110646c00d940c00311380c02060b4180175072000c071380042d13858100b140404002d010790a0b50145a100c4c0c3c59403a50342d48400140e000281c86100003614484d5640801242e80b48258000d4551541040381c4440000c1d81028210100d65424054581031141903010a805c521450031001c00064480c2070004d50110a410100784210302480c2c05125211141c0354154410300321200b984c054840900c0842c02d00407980000d641d4084c00400a00c1503000c1d441d07101a41e04001d00040c0c07100c2c0f0700780b0020006108005444604142d950300030b00880285 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493010611 1250 493009361 493009409
    0x203100b030c16020a050315041401020a39030c06061a09090901060b030f072705010c11130225020307150c0f0825030504050d03181203020d0801 64
    0x1c001c07600202c0817480440c15940500040454181d24161100f10780b52608040703502c7c0c0103808080c0d01030b0740f04003e030038021540300e0280c11681c801c00c03080e24602001c408164489200180040d08640402d0700360350200342e4040240b49280740030f91014440c941c0c9480f092120510400300030103811404102c00c1c1c2d45800c054500c590710544c143c0000503001c0e40d4803500640c9600480d91035000307a4142c810002d465030811011600e03510303502030090700c4551101040d02e804526008580c1800355924403a000c12400200b4061807660291a525003841250315101c040d401205864410340c002005200b41050740c0808038113100d0300100185100c40c0743c407200300d030403401d014605001c10040c0584180070411401000302c45a01c074040a07a56405c0000c4140d44510164038900391201c8105641c00c0803942c00000d6609440003187d2102c0485210b1030203885000000c00b05085184034490b000071907034011a0f1b0460801d0007034081d01c201901040048895100034020141c84c581c0240a481031485 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493011861 1250 493010611 493010647
    0x15030d080f22050f030c06070f05160809031e0111070b01090c0908060c030f010803090a0e0705130305010c0311070b07050a121b11011413030e10030203100b030c 71
    0x2510b011030094400454840074100001008080d400d82e100003040c42d04004104040ba078451003e241040260000041c000c140b03100b007e501c58a681c445488100a000b13010040f40c0c1c40040c01801c6503200f8000312541c0c40303402109510401d080d442c101e891000f407840d4074110340605500000c0510180c1c00e02e030103e0014134060070740100b080351182d0081540502041064003e400803210340e0b4503840c00128402e21010140c0005c0030a0300240069551078032560104826140380440511003592075840464190040c04010250000192000824028194003040700120396503020f000051010048107118450074400408402c24034000600291090000c0c082d00511458400c12a401030304410301603499980b07110130301c869440e000c1440c1c03e80240c0c0001ca00140100280502428988005681a801072005070740c80c03803400c10801014451001c1c0c4c500c1400080c1400407003813003808000c0080d08119511480e4403000d010120340f00c03241d0340075a0f1082031104c0b42d03203150614002501d181e40d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493013111 1250 493011861 493011901
    0x40e01140412021f02090f04090b1324051602010606090b0a3e0c01020a0f02030a170d0506030c09130201031401090e16150c03090305030315030d080f 66
    0xc021100c50080c3c0613400f20011110400c203160141c1ca808039074041049a007070b84c0c48118400d0b45000702c080000b50281d0051980500c0c1014110200c2c0a50305100b03044602d0600e0306e030b10f400400d40458200d074081754801801503074450691b00995440b01e4040e402c0712414004d0201042281008020041d0041c00408620b815803402070740550500707a203010f40185401c4030403e41858080a08860009102042903075420071004122403000c060001c1d480303400044014250761003940f101e5007552000c0141c040171a43c07106c0123061102a1074112105a00406c6c100d002c01800c10b40401c4407458002603020710241c4c010300c0008183c440d00e03107000d1311365490f040880c141038644042448051076401001e000345a4440c0100f5001d001c0f403c142d0070300000402c02d803120a2008414050808899400c541d401c600f400c8c002c50030740c075500b001d442e0b05095500080c0b4612000041200720401420746000b0000250201c803200c99a500081da100c0703108982d44502210104006040c0017145007414881c0b07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493014361 1250 493013111 493013113
    0x7060506040606090b0331020103051e0115050c100902010f051314040f0603081c0614040c02030d02040306090c0504200d06030c0b25050c01030203061815040e0114041202 75
    0x903647d801350702d000e420105808900c4000050015a040d03580502a06511121180b082481c04014200f6444845010300480e05560490052820b019005e0801ca86c02858543e084030603101840c00c0c0c62014000d000b20490004409e59045c00c2c0440c0510256070ba1114460203201c0460b080150840609150f1001d03035900c42e8030768084048404030381c4246005035004410b134940d40c2c201c030100785071000c14000121210728a03118081210200141c0b080ca80d103942200c0205590442c0c0c1c004a14502403907602440c480d10008000013042841c3e40060b0084d4402c1d85c030008690354501c1084200d40c05205134504a900c40c0550780100118035008080c3c095440300005819a2203803900103134842190841418504005101128060b038884103071449203c003401040001096030310a030701d440420401d141810f40110100e091a591400c0d00c01d4880000c480c408040d160400f81585802c1116031454090391a108001d41400010b010b846403400b668103000a581c0c81c0c07541c82c1c0c0d004586c2d081c810011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493015611 1250 493014361 493014391
    0x170d050313021c022106090309030703020f24040602010506040c020d030507110307030206010503060a020f04030602130902030a050610020d0906051308030c0a0309080a0c030b0a090209010b07060506040606090b03 93
    0x5131740c0d9840c01c6580e2120f8a0704604a42602103025142490103054148640d02c1840b11400345d6074009096001c1c0d941c1915400c0f000d00d14030000c54041c3c0800140803060926000520343c0c01324100d0060021100107500030310182e1100340c11702c0100c0c1c485041030360060700310100790a220b0b802074000380c2c1c0012281c41c00d81510403c0ca00c3d4a42103030001c640c1200140c0011004001a140070031950750003059400086207441c035565034115a1744074034800144019008150003070f0104980001c04010002c140b02990b886c0380c02143c0342d0080c032080701c185108428104064242d01d01c001600105000305403522100740d030a240082c0d0360703500521b81c0e0030300191000740d000c200c0f880d062028045508000c03004103034544a0f0724000d441d96441380c0000080798801c128100c00710383d402c0713154801c9a411100d078122903120004150081c0600300000ba40000142c0c00021300140348000400d4518040c0720200f241d40c0b151410001034621900c02c050009042c650103000d41d820a0004540004007260f048074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493016861 1250 493015611 493015613
    0x41e0305060c040f0806270a0206071113051b0d15090606020d0203030c030a0e0309090906150402040e0a020c0717060703051f031103010e01020301170d050313021c 72
    0x4039100d82102c141c0c40c600c030b000c10f040022101030a9001c0143c01503a001d046240360920500c024507044c11780070111100c081c0c50522090710144016452103802500080d07507004241081011403141c801503034040d1101840e1004a03004c41d118040c080c0c0c800c486d10156800350341d2100c400c560040d452240e1003640d070f40a02d030301400034401048000c001c1680089500c0745010000380c01c0c03006116820055400030000c020600c509241100d40c001000080002d42c4000600c242d4a580034011480d90045604402e2000c640000a0214030400f02c0b0943d01c3c04a52540080c80280d01807403040200861511000c21000090b5801400c0b01c502c503d0b08a03038619030b585041d003000ea825454a1240b03500701d00c050101141d458014139600c69109204480d080041d80c0e603500d0340005074031000d0a00d502c104204542a81c00390050107946016074000d40d12540c46a614940b4825100c1c4c4a075413501c943c4403201c05440c02442038030311550750304200d40c24807140c2d5020b20514030038050f41d107251a00070681e410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493018111 1250 493016861 493016863
    0x70903030e181503060c0f12040c15120b04060f0320030709020406080708150d081e090a06090308030106140d050c031e090a060f0f05041a100b041e0305 67
    0x303440b032043c44100c0001055002d080c903082c0b040c06450303022510802c01150040320b4509040b1220b4804039180d001e0107a445040840808616800c44174901c49031131a079803000f40e40002ca5280007100c94204010412250041004680e268420602101034142c0104041a4011302c00300c0b10400119080070500c0004c0700190a00505420070b1340c003540d003c1014041585e0210103103900a000e82082040342c241900310300307400c116800d101442803420b5003501041180404c1a5048000c011510550b400103c0400207100e0708181d10309402915a004000b806a00c116401d9040301d0b0410002071071a400e0150848204621414044e103043c020005460b1180d018819203110780032080740346440f410700400080e95003100c404c080300340076001001d022051390003040c1c0300f9041c0d510090016003540c01c0740d01d48010301003524440c2441440c010800090101c038140e0b8244901c3d00c22001c280356a203006201241c128280a030384402c00003030005110180324842d1856001585c040c0000c003007640e9965403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493019361 1250 493018111 493018159
    0xf030d03200a05070c0b090a0e0411030303101403070308030610020313032f0105040b0a2007030b011e05040207030309050a0c05030705011e0c031107030605071403070903030e 77
    0x10b200089000418405208a510411019095032030945103019070000010707001c840c0500818268001c0000818101306c91800d0202148001805036501da00d0020007600e0300044910800002e007041a613010a00d1501107606070503a0307400340c40103095031142c1003032080716804224203000303501c0304002042c0d410003408081030046216901c0350a040349401802d010703000400c05418000c0c41c203094010120381c0c2100540d401d5840380c9100c503468000c0c40e08111000c1d0f880c03003030620304131654101e010500700c0007080003800d40f030243c681c00c1207a0740d0714003d2240342907034040b452101c2c890346503043c03101c0e244c01d80003403030060301034600803510340240d072142424041d0210048410000d414020030050500f44003290080c17500b402c1c00e180f1401c144961401e04040da03c40d000822070106008010940100e8202d070501c0d5a450031515016217070718010700185012f55011010135807544244000c1c207990300450f80308503000d42e9a10062461564241c9000b0720640b0f00300da00180146040d2143d10400c401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493020611 1250 493019361 493019377
    0x31b0307030b2a070201140a0c0803010806071e0207030f0f0614060102010606030212010b0304060905030a260105030c010c08040b1c060f0501080f0c0904290f030d0320 74
    0x4545920500301e60403415258030f80e030603041000340a120040160b80c10105041c400d411100e000c40d0b13035082d59141240d0411503040020520f07079001c0004104000700003201c501c14011503d815138060110905200d10458a205d01401a480702a05000082e01004c4407011a0b200c0e41c1144459102c035680c85013600c1c5400c04607000305001e0f4042110b40c0d039090017108018152400c0c118a8000b0300700541d140c8070f4050258682c03098000001c5070030012168000200903402806a0b030701c40d402c109000341011410081718042619861500161b002d0910a0701d040f02d40040c000c240e03412883c40151281aa80c260603603106006002c001001d014280080042d4058a0342e400360074820006440f0482c3c0300c503000708462400c00e07001072145036080503480e40c0028218104504640c1d80160101c010300c58000d0b2150018103100606003180f110001c1c1120704400c0e20030a41c0125211010712421941072180e15525501040c460321003640a81e02c01c200218810b000501c0da11500341410b1441d51090340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493021861 1250 493020611 493020631
    0xb070f1a0103110a060f230c01020703090f1a09190807060e040e01050108070302060f0403120c02090a0902030d030b040b061201062309090702150108011a0d02031b0307030b 76
    0x80d83c168685400240c90000c0e12a0703041c078002103886030340c0c0100444584103200d5241108186843d071500c25050586500e090040000d564078082c1c0e03d80180174030803d2240b4450300058280104046036042500d00b0360524034446181803c0710f400400c005e00151108030901458000310200b8005000d00402d006801c5503100d0400c00c00075441407004980b43d0a10550ec285d140c90014004880045205000c8070740489003551030744070b280c12402c130074415a440113105990001c20502100c1c7c000742c02c2c1c50300b02c0c02180c0c0b800d116a43c1d0940d074410f941c3c042c00000d42c150000c0d0700114403107000b6480116807403400340000030115403c81c0400c450340d0101c0080c43d03203111340d42c004000702680004210600d801c0c007124072403020114520401d07240140c0c58058440c0720b9200014882b28420040603a03980b400821085555a458541500a22928000c10354170302c41074200b910b15086c214410301c191903010b80248403060b00390010340d07078002401d0f081035410300500900201007030035050a9801450021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493023111 1250 493021861 493021883
    0x901050d020a0c0c2907051c110105070f11030c070614070204050a0b04050907030507151b0620121b09030a060b010305070e010f0e03010204120f0b060a0b070f1a0103 73
    0xe050384170704a0b12003126503c403540c00c2201070005900802d400d5101910162480780000c110301c81581c901074504440c80c529841d210030040f141e44c0c00303c2c0c80000c2e03540d00c2e216805004d80c5c00701521f071a44111008424180d1015004101807841880340100402d003520016003000c4481d400501510403c0e1008020b468503444495400d00c2d082c4100c07504a6040002000614a103541c0c1c1074a40b00700f4803e50710002a03110703018501d00c0c0520811094000c42890007442c50007107280060013006001d4054281070b107441c601c12424022001281c84206007412001440e0b40c0e0000d003c46910b051b1030a180b200039042c030075004151820429018018410380d8046204107615000504a4400030318a600304a00070750a50742a07608040180b60011030b038a40640d0001c00440400d029106551000c841b9010750850340080c44a004d030001c9902c0d120f5140d00402e61140000c000e298101801107604017041000000002800010964506440340000070443c000340d00700f40407815001d1f801510340328000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493024361 1250 493023111 493023149
    0x90b1804060b040f030c141e041506020f10270c0302192310260c0a09090203010803160f0219060f08150d0804050a03140f030901050d020a0c0c 63
    0x1c00c110113011b03c1f83c8000701d190f03035180028424480340c9505842900b0903910070310254031290404242c0f81403002110807141e81d105030007076441c9154060388660b40503160720009640d01c03034002ca42140280c4040400507040000401041162040088801112200d070000041c2ca50031040030300032102d00440300e04a480d01c80c44040e034140d4920458114807a40b801d4030142d03901c4040c02d071100c1c441481d044001b10101058a5117650203038800031100da4001c000c00c441c110580005100d4a4460fa0340c0c0d0140e540d903036401805900003030091510701d410900c281c05845803640c8050760f100703000c1d101c0c0070340348074540c0c000c80ca40b0750099928a030b501140381c0082c00349503002080c0b020054024541000d061a082171100d403402c403c0e1074104c2c85040b200500106010b85102501c0c05420300134004500c8a40d24034280d0a0414480c1d6035540302c2c080d01140c030000e100d004c002cae5409920306845452500020380c1100c0b009601c05a120018001800150030203e680036541401501c68850380741440400707 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493025611 1250 493024361 493024373
    0x20d0c180801020406021207082b0b090f070807140f18240d060b12040c06050313170d0c020606150412060b03190f02010807090b1804060b040f03 64
    0xa16000680700e42c2c0100000c210442e40000d050901003442a0100e40b69036480c54400482d104010019902030200c21220390101c14002e880e421841c040d4204008441c110400d101540c01c5c100c40c1c0f183d1000c00704000500e20360003001299401030040c5001703203800004014000f1160004807400f1040c04c004101d40010100991240315a0a0200d46100c2c1034294031185080c40c808140501c001040b02280c2c003009204d4581241000c0e14085040300c1d02c072407021080184c0e000c0221000d9030001122800019100d01440c11240141170304040c480c14488a500d59003401000c5440352a140e010801c50040401d503a84a4840305514175405003032541851010442484502c0c02151101082004108082801e03400e1700481c50341c1c811008618400180006402c01120340e504124240c001f0848204002c2141e9191010314400d0322180aa0344400300101c232100603070700400507080d03803c12070203c603803c091400d20700d103c20052001c50b4030f40d00da0075031410641181d4090700c010a088801072040241c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493026861 1250 493025611 493025657
    0x204120c030b1e0a09140304030f06110304080a0509030703020a081f0c090513020d0509030a020706020a0c0e15061b100b0603010612060b041203020606041a010f03020d0c 75
    0x10751440941804244100380706806540070303000aaa00e569945e0940801c5030b1071b6039444808000d82c050b070351610781ea810090b05049440340d08840091a20360b1200840494100380c130700403038000300c0c0d403802c00e80d10003001e581e0f60344580c0d509541803249080003c0144d41e011214005407001002511441040310f1005801040059500511a0400719840c00c65a40810950202d0b4001c5440d483c02880e42ca00340f45c024030682a000c444141424100440c001001000740130310301c550ba089130703001680c404040b070b00d0344105000208005d868800800c41c41140500058124104103c00200305030408001541584200840d06500c51405842280c9000600000f1260b0315204000e024070b00305940090000c1c40b05001b0b103018407544c07480c02001e8480036400b00c80a00f58001409503030f69110b004010b02180b030408100c0041c411500040c0d00c50030940501000304208100d1007044004500041d0307034144688920030f040507401c2c0324032802105d00340030380803190f8000d8440460046005003c062100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493028111 1250 493026861 493026871
    0x41a15010f090b0910140c0109151806110d05150406050a050603011a1b0309040c03150e060d08030412020f03041805060a090c0e010908010603080f070302010204120c030b 75
    0x460003000400200f2240c404039440c8940846541540e0341a01e03005448001800c44054441100810681d90303800055000e01c0702c00c1e0142a4640044007540308040a85154408005804580c8043c950000b403442d000f0704078a1000d092154144594202c03100d040321021142c010b1200188840c0c1707001d6080600c941f03005403400b40c6101c1401820500824580d200611070308948000050842000f5240301c0d040d50380514411080040b0309062940c250707a2900004403c80c4501e2410320b49080d014001d1050981440f28500c10b803144515168100040c030038000d02c03540d04201c140e02d0800028a4900065225521540702d100d25001010802031605c095000f00b5a03041d40b0820050000380e900981c00c401860091001040595440021076849884d0f507101400c024203082038091055000f0811203441e0790f080e178400c0d48655031805141c0c2a14840d00c1b01400c00101001940c0c0c0b143d0007500140304040c002c0c000586490350700c0c003030401c145100c2e82c02074481c500096014402c01c00942003050b006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493029361 1250 493028111 493028117
    0x180a0620120604051b030411010903020907030204141002190303200301031406135d0e0105090a05180108010e0105010f060c050715031d03070f030503041a15010f 71
    0x1741e1201c000c0038483c4000361002d001c0180b510350309820350384180150307005107074080c000c20903d041c4908090040d41241c0a80900554941e0343c0c0121418a61035240203844241e000304007181040c014100d821000000030707000c154540302401c5001c43c80540300d01412000c002019034a41c51401c15807003d50071080f004645e03402075024051040c44502e030114800760060660300b20b24034805221103c1d00c100880140404000c0e07c2c01c1c3c4180300d80c0e003200f0915130300b04003025143d00701c1541046031008994000e1002040134028907803442c0d40300e0006080c2e101e401405050010391190006120301c0d402d0050075480380c0100005101007a030070302030891103100e5540244100d5060040c410201c0c40300c0c1c01004100680d260100c41406000c021180040c0314403d6140044020194018041c0c001044241c2c282652400e180c1d0248400200301c1d249140c001c2c48070140031907607540c1103500b03900103007040d50348800b4039420004950005010b03a01a002280c0a665640344000016041c1c00a203801a814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493030611 1250 493029361 493029391
    0x30f070501110303040c0506131e050108060d02060f16021302130905040b0403030908070606090e150c0a030504050f16170f0a0605130c1409180a062012060405 70
    0x2140000c080c0b09442048a00d180c885000c00e020382c9e590303103581c0d10941c070101400740c8101914004100d0300003601c10aa031980100e0340d417a402c0c860403980300c0350000d400c00020402403452030040c40160960b0300080070031040100141d0001440c03000b440566103c2d03240c2c001030b05a8542c0e1800291001000b111a09100d14a4113403181586003900402c060245600e4508620420407072008544101c4e030b009608120749a20b54501d00c0c001d0026105d240014441c0040e462103003000420160f2050352401d5000d03240c00703100310080b0007a050280c0b044407035101d202d40200079000140036081d00700d05040c204604041c6008038403138038a01c002004a046800042c40c003242d000c80495201c0c0c026402440100302602c540d12212a03c41303900c0390141440a0f800c030007107070241c0460049a07014070201d034501c406d611403c0c1c2600980c105401085000c1d804689000e000503015000034080300e8040041403c2e0161001891200b540408503505400d5804810860030b4541441200d404c14904c84080d18 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493031861 1250 493030611 493030613
    0xf09040507090b100203040e06062203030207051507260d14070c020102210d0f051b0a08130503040902031815090703020d060b0325050102012315030f07050111030304 73
    0x1d06c0b440399000781e051100341d440000390a9141c0004842e0b041ca1610400300c0c214641c04d0104000714001d0004a0040c0524240000d507454140401c0b040400a000c20030b02c0e0400540c0c07800d01010311034000c107418284004d115003130382c007080f400b8145c00301469170701080024010620500c4020020841c01c140b080c02600c1001503640001c2e041c425840c00b04e03420088164000b400d19a03030003400c0d0308204141c10b110410250b07081640003d400b03401c1007400500450700328000d0381200d005190690340050486000118051409880d080713105006100340c91401d616140808186e910440d0004d10030090380c003141c1c0c40654104480d0029403042c2800c903007d03061082e040d40d1a00c58500c4083c2c0720b8842e0250440c1408059408180d004600070201e4100440d40c1c440503144c00105130101004840300c078000145035006004030b400d0300303801100500c4d044208149201102c1e402402164030b904450081400a0710b04120845c0144540001484180d1810b0001468684020231035a01d91300f003842848 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493033111 1250 493031861 493031863
    0xd14030a0507020a02060406030603060b0612060121092904051c020102090303040906062010180b090717150105060705030c030a1806031404110f09040507090b1002 72
    0xc0e042680e00c003010500e51650b440491402800c81800303984404001800101c903a01030744904210f0348222428802240040b04002d294000c540c41c603000b02613880d0000b00590b02c18002c00000e0607442a0b02240c14003645000003c441c0241812100c024060b0480400300b040040c041982e10140b41031701e0103d1805a030313070644521019041a4a004180001d0f07403115000b034042e25200d14026044135250741e83d6062400103032010b031040802003540344407000003000310000040711000000c00107064162075141e040000f454a41c2c0420b05048440a00e000000c1d07200e040d45016002c03072001050503500307100c00c09149404448003071405601c00515100003c01050034241111022210749840720403605000c0d0171441188607001850000150406905030884502403498014203541c905542c1c0340d00c001c0c1c0803540811070f1741d4003400b180c0001900203946079441d1206820301802c3d0300b0320000604040754055805440c2151503420110081c04040440d10819411341d004685034240b81c00403641c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493034361 1250 493033111 493033117
    0x50307021f09140609030604050d03200412080c010203091b060a020a08031b041806050609010806042c010f27060906060b071208070504142419020d14 66
    0x4510800381402c445010b60344d0700b2050b5405540701070161540b601e42803402c140c546d6050020100441d14101407000e1116000001640003103c094510380340c11b06110017041403000e06041190000000c01ca0060000428000f85000300c1c07203480203048405405101d034200c2001c22004030700076081440751070b56660307000443d50122900104429501c0d1500f907030f1401583d2810000c050b04a00016002800394038041c1e1414180b4200441000780a40f10010800340d071080b143d01a00185400000c1426441c0a41c068240003c45070301007442080003090b1485001c0300d122807400241d5440380c441401800300d00031700d4070200307524070400c07540c0030402c9142500c0c820b40c040150a0907511012001003106950244002e8141310b0b00c00794070f40000d071524512105c3c0da410000d001842d48004200454000c10580e003d8490402482582c1d1252006009440f00f02c6080014192100300c40c106100b001c18005017010601c4d20841c6907045040f02003c0e20b00495481c254081145946522440b008201c0039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493035611 1250 493034361 493034369
    0x7030e0411182106071202031006120f050c0d050c04031205030c0c06040b0612010b0604050112110a0c020a0b090303160f0c080106090e07120209041e050307021f09 72
    0xb0440a440c204008240000c0c5200807080065038030504a801c1614009030340742c413460056607842d10410b0307001500c030160300040c1c1d106000c8075168681880ba00e40101005481103604500000c0d841e142c0007030b001d080d40c80c10390750b40c0070003103000600610b840030501405900198600c80d091401c0e203075647d1081d1281070800020100000840800d20600016084031095144441110742504003800e20b03401141055800d140b04040c01402001100010300402501030f500800c1107041918003030056851001021003104010380e0b50540380041d1070082e0280018400c1540c0300540341c480c41c030501c82c0040d49a04a07000001007400304000f15a00007040740c050040d014004820b124561500d80c20500c9080340061040860320400b060240c0150301800845110b14014421091811b00580d1111590b000d078803400100103c0301005414441710281e005407081c18082002e240340e00d6001d440703245602c8211001d4200040d0300c3d044d0701d46408240240c01c46650250200c401260024040340f0035031007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493036861 1250 493035611 493035637
    0x1e020a0503090910030c060207150206240a030812090c090c0301030213020f0d0f0b2b1a09030a181404050403030e030705070819080a0e0604030f0807030e0411 70
    0x182008040c3c135800d40c0290f81c031003520b41c0046d85540c8082c3d2143c101e0b005000c0b620b04188102d4641510019959001e40c00c1d04070001800045603040301e80007518001101d0b0002c105080000c0010207040080c0745182801072845454100440c100e03040071503c7e030b070452040c07054005200000201e0821641100d504581c0d41d4030070040b14451344041d01544001c4c0400c0d54011809100350415500480800c2d404102c0c200003416004040100d58100c250b10203000b20144008801d000490704050386910303000b9201c4400311340e600314100b02d079001c0859100e2031681001c02c3d034510240e00910306404890300c40c0820042c8506180300402d08055445a0511698031342012a0605020391700030001212803600382d03550740c0017500300b0590f04d00e010700c5a405503200e40140303c0f4940040c140c00000282d4000e900070b240011003001115122000f114581d4011800c00002000400d20008061014840c03622075803100c08a050141c1880c50680303082e405142800510154500100c04840b52600024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493038111 1250 493036861 493036879
    0x30c04140103060b0a0c0b060303210c040905040c1502010203012709120e0a0f05010e010807171311010234090e011b030c0e0405090309101e020a050309 67
    0x10300100c0203040c43e03a0180b0405030b8000b80c80704805610000c2d02c0899406104411115140c00003030581e60b11441c0651800408500c054441404050340300e26044400d82a5507400d141d11918000c0840c3e0080d50104c0c4d008507116410460703000407140310410882940003c5056600d0700396140145c440480c1024044d2a50b420038100341c91103a0b0080340982d401554900c41200c40c4a006420301510002d418030a60800000040d0b85400064640683e00103a40f00034110540c42c0040d241001c0c083c1c40901845000600c4c02d40380e01020480c10710400b02512517500c4808603040c03080c8440d031001c8004d811500300e8900040f40d4501916102d0b403400b201d240d03c0364011800740c2c80f008044003d4000000141c240750607055001d90540040182c4610f449450700807c44680c000d808a8013250703210303400b107280014180b2072403030564800782d4401a8401505c2c41c0481500002e28407038201400240400c0b100c543c41900b011035115200ca040903540000c3c495201a0380340d00ba9280141c1010604c100510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493039361 1250 493038111 493038149
    0x190501090e07021c030218041104030f0c0e040b0414011a13060509040809011e12020901170403020f0706020a02010519030e0708072c0a0c0302160b09060705030c04 72
    0x200840c03a80440080c4c0c02c3c1070740d860400002406035104005109800e1000701c103a40c641e02e8a40f1580d0400462540064079240c82c5503126008502002001d1795046400d40e030000d2440d0100300b0341807141c2d1050f000506a40740a25029401c1c4003c8000390100768940905040001841c88001182001c204c9090601c2011450228041c100740e070049a04200040c043c0020000c440002c0d100c01d4000b42c13a1710001c081c0315074551030b0300c00405007003100241a01d048040b040089a0040500c24011f2401c140d04411201c10303c1320030a42a18110016400140f48101d00c860a1040801400851010704209905500024100c0c0126100c0d01d44d00780300d2034a080c0e0202d0081d406603043c811014151254a0790780ea0003a40c580031a48100c64911403116207112243c4010191850034085860050b04a0b840c2c00d45840020030340c4ca1032034018140d08015203007100802c5681c0c4510644203203007480e00380c40c1000c41941042805052041030160500520108202c0841624207440c800c0c2c80c07541242d445 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493040611 1250 493039361 493039363
    0x703080c09030a05060a0c05130603020903010902151218100209040b030601080a060e2d250303030f051005220204060906020c0a0503060a0b04020c10020405190501090e0702 76
    0x191140c01e941072064442510412001089452041c0d412400410801c640e01e0010b1354035100720712800344410015032041c460a40a41c2c09004201805000010905215800b040d0480c2c20304686150240010491011780c21a24010f281c0c010b01403042c003107031a812101d1f410754907511581521062034010130144403d407980c0c0c1c410041c0301d8004040783d40c41d5035150b1150f40c642c98940c0041d95854100f2010005142e800140600c0c02d2007039070003c7c240c4d03090707540402d41e140d0404642c85501d40a20004840c1d00150a07a030f0444c000403208a070b0300c8552452034007500701d56101107100c54040c205001c008040003c11119412900107031004065504900340c0d4104c05100e4550400b44948040390204283d070b4400307a00c200796040342d002c94400f00080c400300701c080710203485001c0d0306900420000740765840c83c3d00321301000c0d00c0141025061410303550340d180c18400701000030500c480e40424100154548244100c0c810a194114401e003d41003400081010015006103100750354400003040c0e803144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493041861 1250 493040611 493040617
    0x50d020f0a14030706090303020d0c060b0306041203140c120414030a030c030b060c0601060f0921060c090e07050f07060f05040b010504291801120b0a0504080703080c 73
    0x30000381a001140d848501c21182d01c4030948000d40244903106002c45c0e190b000b01c100c4010f51340c1640062001c1c0611120440304440890780071545251144501d03030154408010300c500652103003244500d100b103d444001d0403680d64016800c2a00201414040044400d40c111400c0e4440390b8001101584c4505001c40200e0354200700d103041d440001240d04080b0350541c8044c90320b0b545d0740d90901002c0009010000b40d4011003401c80c00c84d0b00040010840e0074000c810706000381601c0d082120702d8a0703483d903070314a4415401140c11000300c050604403003040800c0c82050045103d84c00c04961540c18110500c1c480750340148510140000021035009241d005001d8400c61075120800340040f003001d21100780644400c4e00c00725549040e5200104452030280900703081c8001004190340242906000e603100d0150480c002c40d0002800750030320080009112000d1b020f0b0515041205060182e4548440b0300c0130f009000c81d500c035140805120008003000c040350710f444e416181c03401d200d465000010038144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493043111 1250 493041861 493041889
    0x9090b04140c241908060a09060b1b0705120a140604080a031503141507020c03030d090c0e010e1506070c050f040f0f1a040c090303050d02120a09050d0315050d02 71
    0x18951200d442a80c1742d00894480c030401c401d83d8480415a41c881400342509d01d24080d10036030103400d00c2140411003140220144903083c0e04111147c07160b0742e0f4003290b00504603266418050300310005420a000309141040310412840c4003e0440e850179490341141030007640e06100030562210100d0700032102d400185009150405204045626901c0640c0d42d1544a1003100d800c2e100c00030300045819001180034455660043d01440c07510750800201d80061542c6001180c61440e02007020811038000d00c000390103001070100030b80e0f89080186041014090601d0054410041040b4040000d08100d6400c01110015141e080c540c0c40b02c040010040e0507030303010301000286011503840c3c0042d5541c121483c0c60b03211444040d4a40f00746010300c07040d10440d02103440400d40800e02000042d126900401107120010b4005007800008c0c0c00743ca86040042d203140c000d841c0c45000701028418140240018902c0b82c1c2410821011001120340d444101481001d03c583c1d50350b0012070554640890440d548 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493044361 1250 493043111 493043137
    0x2090901060c0506060a06231b010e0f03041802091f030c090911120c190c020909010c09140a12121e0903060f020409090b04140c24 58
    0x2540e119039000b072840100c1c0c1c1c07054a20348590004030355141849054082600c4103681d0340301e440c0442503100110703920354a403c0540c0e03003402c211025686a040315082490410f2500108070200a0504c25180400d0908110816041000108010400c0c0c40000d0f111030703e0307408056119458000014000040520f400010001640c04640740e01e030b040e404651601030a40b181c0c00c100352902800d000f11100c00300714103500d81c42082800c409002401111b940025010170740c0b03251212030302c400c02002c1c04030208440820400c146842c2189840c40500fa8042d42c287c000700944200c82c2001854001c25224020550041031419107840c2c070b0301a01c450240c0030303894003100102c0c418505a080c084050802e18002a000c5082d00c40d265120107038109800b075550760382249141192640b80c01010700b45000c0061907400c0000144840d107a00655605600414170400103181c0307030520006950140c10030b040107800c81c5c100943c0703683d1006550008e44080001c0c20140c064800c0400385030307106854464400b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493045611 1250 493044361 493044379
    0x6082208070f1b060e310509010f0e0a121806021f0623041b0c020f0301022b0608030f0c1b0d060b0301060339080703020d060209 57
    0x3032050128204980780c0c4240c00168641c110701c11044242a070b0b80c01110700269031180003003902d19003121b5080005044500c08200741419007a0010303480d2040240070041074445c4100030143d5020b10810411860216043c00448401c00318a510351440c040010820f42084640105151081d400c40c0405891610b005040c561205c2c00a569000401d10100c8000c00c075a9441c3c20b0101a401500200e40314000c0050326146c484003441c0051800324406504581d4500d160400409050118075840c1d61503203e8000340c41301f500502a240000c5191180240c0c01003200040084080403201076503c002007650481d4241144051b01900740e5070b215043c14800070070803c80344140341004141c1e050510003102c5021b1842095010512500b14400c1c1c0d214910483c3d0201268403a080401000350017000010300f261255030303080b443c9017008050102420300c82440303160880011290541e18060085145200d40381400090b07540c40e280c00004e000e5101f1488240400c03107103030180c0d03411210041904903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493046861 1250 493045611 493045613
    0xd2006030c04080f0a050a08030c0d1404050114190218031c0f030c090b0a050702040501090b0f0303040b0702010c052416032f0c01060f1e0608220807 66
    0x14141c0c205000f05025800b90300c00002440a0004140840d507a000001d0075010800d03440f0b400103500700402c031050420041245041c0081c03a8412091611817401c550341981c146801d00c00d003190860060244811400c0061100321000d2200405142800620260350b500b2114106a613542c00211714035003511500340f0390511070004a10720340b001c01e0140e551075982a001031b0708070282d4411406034404100d100c40300740318034181c10000b4004650241051442c124282d40803c013110000d030310145100da62404070005516120050303080d000e10450040d41000d051120b001c1483c42446002810301c000c003121001040002d201242943c050014003040c05e082a80c08030413251000c4801344060040c6040e041180c90080c0300c0d0040b460030303030f035400345004c5100203040c218a0703081e000c441c599805c14802e90101c0602401100003401c4020040c1c2011407414200c1c0f907041c0240007101c1b161101c1c9000a00a45a110074102e0388044240030221200c1e5507040c80222103460980058041003001030140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493048111 1250 493046861 493046881
    0x1b1a0a0b060c010f1112040f0f0b0a0c02010f0e2808120406050c03130b100801020a1808070503060c030a29180702030703030e0f06130605060901050d200603 69
    0x40c4030216081418080c68141c1c5d20398840f02d1180170034030151509540040707000b04905c0c11103500c0e080d2003a42c40380c000100d2500c900821680c1190013540190300c1e4401020301315130a000728007002d4001d4600f07001079004140d10540301d007551070402c060964554014200c481c100c8503040c4045802284040e0b46501400070129503807412103003500e026091402082c0c90181c002c1c106c030303c07940d91200500e410310283e079560b40c046440a88045030342864002c000c550401d0030310003008030547c241c403060010403405151402ea103031030f0342c4840090703000141b003048681c40111706a40d0102c03000301c1c0781d6a02e54801390303640300074030300324080508602a1303a214030401301c095407040e0f2040804a505558a01041103d400680380c21220314005030405c0c00580d00087c00b076000300e603040b0008415684003009041d2172610300702048907410954408800c01000380f0210b485070b1900300074152015074142d03060034049404000200d00c000c0c40c02602d0382c00a08803c42400d40140d0301000101070590342d041c070001032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493049361 1250 493048111 493048121
    0x7140a0c030f03020601120803010501030504020316080f060a05040b0718030c090203071205150607020307081504020901080d090510050c0d030515041418120a020304061b1a0a0b060c01 81
    0x103c001d445070f4030001c10300003241d144c0407602a602460070b51560717013007100460142201900481e003504c100907207501100040d003d03142c0901410360040050f250511030107460402c000c0c0824070384524100a0002282d01d01c890107a00074514107004c12405596044003407682c105a001414181d08a140404d0068141d00254014401030303584c2c5645144032800c000c1159815580895400c05441520b51113050071009022a03600003002d403806195a41400780c05c020101c5124850481c102041000b10714040c404075001d031085400400c101d045524004d0f01c00b400350301400c1d1207080384108840041d48103504548030342e02c400d804e4481d01d004452003d80030704810341c0c4020090505220079561400c05118038643c010300c0030446411038a0782c12442c1d40c1414001c107000c1181c040d112800d0094450b150042521310025801181d680c1c0c90040002c000c1c02201c2c4026516075094121680899401003504900a0043c1041401503d03001c0103100200603a000e070315040f540108038444411419400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493050611 1250 493049361 493049363
    0x31b1709040c0f020c0f010e06160201031104030b0705072922030c14070b0406020a0209160c02041d0f07090b030c13090602090409111005090607140a0c030f 69
    0x8140500c00c010201907a551030015603400c0103170701800c0c0e80d8030710380713000043d02c11032481c1030406405600300c1c0008281c46900a41c003031405034401802c8401196070600c51110003014034841a401c042c19030740d54105540c0051310303000810402061390300c00d10052500c1c10307041c075201c06c4282689100d0800c04a80803a82150700d40d50151001c40440009081c03c600116041c2e416991103441015642d1208400310040500b80c0041c03081ca48045101c88a180c001e00190400e90002d2001e24840e10401501010081484400c1d142080c40940629009071000b410701e507045502261040c4c06444840a180100d072000b0401c0c803405040114070000898a075040c0c542481302404481509010b0560b903c119960f090382100050109038203d07203144c0d100c48181071042402500c0c1041c01000a810f8424032078058035040c0b00014103503c0d82c0703003500725030b40995490b04049050129680000301c8030300404202406c3c0e1041070500308241c940c2480110b06072903201410400490712030500d9407e085010344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493051861 1250 493050611 493050619
    0xc01110a08160801181806140a1b050403060c020f1e06100f050d030306030807031e020f030a03020702190f030b010e25020115080606030c0904050a031b1709 69
    0x70300ba500443c031a40d44181691640040010026030151204004100c501501d101301500e034001c4100107641e5000751480c10b200e41120500504004d2198000c0b148060341a104400382d03262152900c81e0040296012207402c2440050602c41121059080c4040c10300303a140c2c9800f170b440341c0140516040e40064050051081150956510201d8244040899016188070b820710103038200800d14002c007951100510034a070104005a49a07618001130b0050803080700418240318030004d4080c41c4d076480400003100d602c01001d206400c003500c50740300d20542086100b0503800003200415074848826440c5901c20b03a4074201000c0d1b55548108080e4400f5000440361400140d0000840101a141aa00440102a0900c2e00030f04800b41c1441c540006902042907548900f4003094282100503044001d2401102a01d10340ca440f004150529007030314101c501c00d061660a100c00300303000180c4406003e505040c040d500050005603400d1300700c0e8448000b44010005185102200c074110058401d0074001e50b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493053111 1250 493051861 493051891
    0x40e07090f0b0904023c0111060f0f100314010f06170d03050a0e0f0f120f19020c0d03022a0d0627080c0c040e060c0c01110a08 56
    0x880142980c080d0590507a20110303c40100e00035141034100f80e0342d48440c10314800071645030315500990150128107030364000d01480340c02030480e58004020b0841da603010b1001d00800e1400300c450351100c00b00906200d058524844c005805008044104006581c0000300f2610015125402a000c0d050780160382c1c40881c02c240300052212088103141401d1440b01003e003482c1d4403881303411001004020481c1003015225160000114001d014000d90101d603032b8003a04c0c440700030011581c0741000004490122001c01c00c85801c0e2038900b04d095070111600c0402015030805070790380403071505111466041d44070213841d003120308054000415a004000500031210070400310700d007074106859130958164204100c4960100014035561084403442000c8003001c440c0c001e003603490250300070b69520490b0744810010f4070307000c00c030010044a201480c2c00c44040c0302e08a03001b4134050321018003422503204560080380301503034101d080d0071072940100e217200001e40300d00304004000c00609080d1000c091641e181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493054361 1250 493053111 493053131
    0xf060803070b01091e05040812010605090d24050129040522090b0c0c0f0105040305070f0510140114191a0c0607110f0c0901030602090609040e0709 65
    0x21054038030842c1c224849442076031a05043e680500424400e070b01c482ca00d009850021403909200b254016402481807a0f01c4d110000480c8404410607000602032000902048403e0380d00c400c42d440903158011001c01da440c0001c200c0d2a122101049011045400c1a002041802005081c410a14488039400040c20a82c3c01400003620a0340203d90f08a081e1600107940c4842405030309403607002c10403000480b5030803621400c86441e020744500400c030000240610701590f04100c03001c000304600c0c0080095041a80e0080c00314802d030031008001c3d11083c00c80741709011080c403038080c0418517801c00f40100c05281800401c003c0c8240211036000d07025107504e04d0740382000350008902c0b80e82250f44045050a110443d1600484c0042c0f80c250444100044c80b040d1005010711409a002c41c3c4030176020200385807406041c00004400d50b221540010303551003065031100341c0541141c0d040400182c0c2d0305806000f040b00340c401e007019280c100341080b000c0ca81400c0300284ca40b040302d4001038200f00400384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493055611 1250 493054361 493054363
    0x3010b031e0f06040203090a020a030503130603060e18150c040f06170a0b062217030703120b04110c0c0405061203030103110103020c060a060312140319020f0c010f0608 74
    0x815140840b054500300001007180c2402c1e4000c58220180d50119000d600f241d17400035074400c4a0340c20468654002150400780b180e1010681e0001d041c6500702440303280d0500502d0b20350a0001482c450000b030007603060f40401d1100b80315200150110408880302c82c6445180a1140d0340a480b0380c817040d2120180008210307105981441908540e400301c1c0e00300d03854041428000d0502e50020701d034008410080c04290100c2c0c4807101d035980c02004250031405181100c0300c901c0c441801c51062054000f0488070000aa000000141c0a400f2030000141040382c600400c00034001203c00642035a0000340300100b01a00081060550070300b254240060350302c075014041c6130300395907403962181d0344240018000518081c929a061380410300d00142810011800d1324507044041e01c1039800302e50f98407000c2c410b0045204400241c00680d051811a100340c4101c01840b40c03100800b00307031107551180f26226146502d40c0444441d042205000da0301c500e030700c1c44601c1c001c01a40e000394020f907190440000d03402070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493056861 1250 493055611 493055671
    0x7020a0f06210e19210903060c031814120301170610080304050d0213050408130501050f03070806180a0e1018020d031103070602090108060a030c1e0b03010b03 70
    0xf02d4201a0025403007825031000301c1007450404459820580030400c0c0798030420300c0c80103039292a50784d421100b1803031400d1040495415160348020141070012010320b0503582e8042d01c0507d50b01c10300030012100c554400320b00300600325451001c010380001c00081c030041043c5a0b441d030076041005545035903da02c9807200c0c85005621858500c1c0d0000c0c441000b00d480d000d460106141d00280c80203080f03880c02c90a200c21030b68211800c854115020070b031220112009a52100544030030700342941303010820451007866000047c41202080300f02e200003540341d180d000d9031100f86a8042c0401d691400d06411500107440c0301316a01e8000d101d140c01e805503c40550050001d4011591500d011042c1c0d01d4090240080c41c5072400d8083c41040044032401c0c840070001420058020f10005031102e1524000414924002e000d00b40b00301c40082061002c150b88032811004c454900001c196001d01c030740c50201541d0031a030700181034207401000000c1d0740706420b8000c620880d0603034100080f56284000c0450001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493058111 1250 493056861 493056881
    0xc020606040b2101020f030a0e0f03180f030f010c110114060607060c052803060501210222030b0717010e010e06040f1b0e0d08030c07020a0f0621 64
    0x521500e100100d084403401d0301c9808880f900700151400a0304441c0c40455481901d01503001e41e41d880030f40c42403403001c6c0f1104607290001400f5600d0139a80c502c2c1a003610021007002489550721200b1100140ea01b0000c030040040303104001e014a860301c45002d02810409041d480184d403c21400d005078141070151241b00b11002040c2d1418103042d40c80303840050411024400c1803000c02c200313401d0220100098110920fa02c0681d903140105440d000030207a031260b42c403a50600100754103003046a05c8013045081042d0070400c0058503440c1c0c0d00c0c6007140c6010300c6c00c20070052461503200401880908044ca9101390f4094031100c3c502d1034030000c620b02d020424841c0507400d200d00e03c0103200c0c0d02c42480040303030003640081004c82c81c4988000c54400700c5400c02c0200c41815401c151000000740c102e201065941e2046401039403403030315501c49010910006224142d5214009404421980c454031840c0203010381440e4a581a44c66200150440002021400202c14401c0030030a0800050041c5a851 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493059361 1250 493058111 493058119
    0xa050904110d02060d06061205090d0807180b0c0105180a060c051e030601030c0f0903061e050f04060e0c100c0c030506090d030b030102091c11030d030c020606040b 72
    0x15540c40e1111100101c201002590000c9101c881801580c0d6030f50103460400403a10340052424070b0864007401440d600022000c0483c1040100300b0f501d82c0100341c00b00801c8131800c00801030707510603004a4022085242d00c0a60709814100440d40c0c24807000500001800c4030020011900c1d21301100c944090b045080100d030344c0c000c00c098000601d01c0d030040d1180d0091401c0003401d04040451710b2264641c0e5000083e5004c001204202d825a172500410b0f800e06c003c2d0501c61114094440300510350005400040c1410352101d41d1100000c00c1e24a04507000045541c0c00c0140307041400e84000d401c002903600383e914074100071201302c1c0b03800302062138410410020710b801c030100300c568000d80d410188a6002d4510440000c0c0020110744140200c074410a0b104001c0c1c02d04c48124507014080705c2c8001442030090f0301c140030321285501e42481202588800a0100c482c00c3c0e502c3c50800342e01c5104056107030b050701980d001280600d170035400101450700f981d026521035a4414040c082107501c203003030442d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493060611 1250 493059361 493059379
    0x1060f1e1a071202150a1a0108010303230702061b12040e06040c020118030306050102070611070501030207021507080405040b040903080412090e09030915030c04050f0a1d0a0b0a05 79
    0x560b424a00c0c40c3d41c0100b80c0180d81e844560164004101c4500303c5032944015241d110030245113800e1401c904964009080000d015411078900800415603403055200c200c090040702074200100001342d4011650091450b0b40da5404002c010b10012400030b400d81140c45111040c020340c0c40389909036002d6408003007258a00d59140030400c405004c500100100355542c5290603034030141c0051001407150b00030349022404916001c0028942074031a4020710030001d40a030484000140403683c0c1044030006d190142c0c48030000e000144a5002c40040b4081c00540040c44c4000c00601d10058002c54908807400c1109000c01014841070300c1c42000d0050000b442c11001400003415908420050041450444521510740c07101c140910030035a405070b125400841c0700d034158a484401f225410b4210481c00d81541081e03c440e2401e4026401154440ca0000a40e5021502c51040700340090440d201c0400c0c5050203c1d0f4003411901041d10106401da040012480036414003038112400c4510141640381 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493061861 1250 493060611 493060613
    0x1703040b0a0e13050a090302120f0d05040201140c1f0c080f04060b030304090605090c07020a0e062b0c050102060105010f1d09010303020f01060e07050403080a0201060f1e1a07 77
    0x80c40d071400c280d84943c400400d402003c1c802ca028840d492040006000009610815050203450400d0217115108a00e0301001098252103548082c2c2d000c04410380404259a00c4610061342d0300d2528408038213032200040350340d080000000590804034421a1040350f1034940391040d48042e80c4010151070b010400b020003203011104690001ca034400c0c00384e100040c1d035450b60703000a419581715034803040c5070b9038803000309000310f1402d81c020310f0300013038a070800034a828015400302d41c00705001e1044140761222040080d40540b5443e04032103000d050340780d03032100c074441400813244880710114041d18440d03003403c1c0109455000161890503500305845104c9040300c000b004813201d81c4120f00e580007694082e1031403082500c0d020082e5000c1c40c07281d000341c644607004410285c01c561080d4841040c43d41e80e030043c40700c0d05030490101c405980e00900940ea4400103000d069003d401194403440c0e02243c0c5c4000001c1c20540ca6907141803041c0a100d41c40141c81d0b070b41082c01200c0010b0401c0340e031000700c1040180c3c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493063111 1250 493061861 493061867
    0x2150307031b09140a17010f0f0b030703080706110a0906021e0619020906030702071a040506071502070b0f0106110312070f02071508040b06040513060b030f060408041703040b0a 78
    0x5569000b00074002c0c0341003619210586c3c0b1400f00700c3e4401d081607460b6010b000510318940200401c101003c0c404004801038000001e0b50f41c0c80501c006031001000181d4141400140d401c88030b2048120316a0540c2c5940042000f0b09002d0588503101c01030080840d403010440e0303030742110711542800c00300038038103a181c20910030f522090303940794001030b6a820003d619123600d8542c0039610802282c3c000e00541850310941d85441100070102810143d03040005120980d44d80061340c1081d0b40200d2001c03002c80c01000000003c0c800c04c1006002410000e0400196440c0808980c0c142c55039540e90121440b40c1602d0296240520015440c144a4003000120a10311556100181322500d2045810080d5240c0082003004859005c0e00c1c0050342040401050200c0d440200d030f04180e0580d000c10084c40c0c8801d020f02e50b0300041c0310090426403103100c14070041c1d07802c02082a880500d00e0a0b01d0160074a2301e4011599803092140030340500203407600820070140402503070211108016000e01c1d10140000031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493064361 1250 493063111 493063139
    0xb0607030e04050c04271107150504150f0c0e030c1804022209021504080307140709180c06020f070306020f1c020d14012102040902150307031b09 64
    0x245803001c0c043c440080c620010311280c03501113503640c5400c00381b2000b400345501a6413000f4518005030000300311001c0003801c41c26a0b8030030b61540d070000107041d40700c5140c4103090408009812b1030807401c001c00c11440310060380c400350003000c03a9251011105601014940c4440600008981c0f0000b8408a6050022800405640a440240800c0f58040022040311881c00780c980d40c8822295100d006004500340441e0f20040f01d41210f4032181840d01d407881243c3d6a100b4000010b040d105060703180c030394400c02044404040c0c54500010321002c103101c422500c0520f0000010b0310314041c2007030009003243c0040f0700728100c01c80e0007000d40103080c21a04c03018007951103415032495054040100c1401e541950b01d044c18a0350703442c03d015a4880c0e1158041c070030368418403c5410200c030300034010018115031640c0d101c03107040c00c08442e840442d118000240200b0300390001a4000fa04100485a4000560000c0d403194072152010002e500e0171203d5204840380202da900e000c15901c20003400001000092 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493065611 1250 493064361 493064371
    0x3060b030a06020c0d0e010306140103020a090f06030f0b06040f030b0705040509100602010c1d120a0b0c0418021905030a0b120313051903020f011803050d030b0607030e0405 76
    0x884020420320b9071254201c2e84034440394030b515004982c1c4000d8180c0d00101114580340309190600c2040c0c1040485446445508910350615600141010a69010f21351a000a1945540c040d24940c0d80303002c0680600f00720f2400c52a8a8a882c0300100e082c5014401d4070240c0c3c0d4140d030054401070555641544410300548040b0600400b4080002d0503134a40080314401c65981e1000350540b407826001a0035200d40c80e495106010340407032007a151001034164100c406104680000c00c00310080aa82d04085603414060400b200190811000c0d05614000303000b201c0c001c2c108640d000308100802e40490040145010851164200580142e44030720003460b08607903061400100d24061100141610260303507217a1607142c0011420051a1005c411402c00030039054403603001d940c1c0c810b440c0c9030208000740802442800701c0c80b540030481e4820101c2d80314110741c801080201980300d0906540e070b1440b000c0000006420044698854200300c0700362040f465240c0c070350310741c07411401003000045c3c1b000901d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493066861 1250 493065611 493065613
    0x807030f021801140909060403081504060801050c03180f2a060c1617030409020a02010b0306150a0b040b09090402040e0118020a080a0210053f0109050c0403060b03 72
    0x76044051484080c1128004c0100324490034881416105000d803803400202010b0741d80c1c0102c000c010200350000c0100743c1c4500c800c1d4114032000c0e000b4001070010071290300541d88542c6808208000031584400450045841a03085401051a5540d11b640e595080704010550780000d40c0420715206000901d020440141801c20501d1100328046001500321841c0d40044d0740c4010b1407c000121000700441c060220408030f14411080070020580e07030700c124480d00748425800126185042e20079800074800c4280201039800506115800781d000d01c040c01c0c6090310500d0040c000240103007030b01084800b01c800c449021030520318100c04205881800900680c1c22944608049400314401e00c01c0030072090f42d401c51880880300c40d0041c03004030020b82c0c11000b0154445428070001d030b0f54442c41c0140001445c902255034440d0003411000c4000c1b0481209103400c406086449541d611070712840d60b43c11072286861503aa80d40700300001383d03402030ba40d00072807120400082c0013086440d0040d025203c4094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493068111 1250 493066861 493066879
    0x106210302100209040b150d060b0a0c020d05070312170a061203050702010c1e1407030302060c0c1c09080105090c01140901020313030c17010c08070e13090302070f0f0807030f02 78
    0xc000b040b0405581f0303c2e0b803010140c0002d510b211a100c03611808016104507809281403000500001d00030300c4030b40d04068421381c00b5440300802c02c0410408100915400301e128018005500006801e0000303011075040c841505500044180442d445804d08894414800201c00911500c082e42c2640c4500707000d80c10000c4a10941c3c0c0800c01c018422000002755240003c0c144c0d20758100110a0304185441403501d0300104406c10202e0b1b8001100781d003001c2c20711803640d0340ba02c1e0811120710b0b02c044140c060b03615003e2640300d054032a400911200c11260461b00038440399039015010f030303180c9140106550100c2d03c080e0511001d40380e20000b80803500c1060040342d18003a82c452202c09032100c03d900485410171a2102400214104240300302004080e1000740701d4042200f2014191a0000b4501c0c000c11542c2654092140e0f01c0c51a24425202503035000c002038019400c0080d115451340c000c41c003a000c01401300003170681c50007003010112401c080150104500355507551003020f20300c42060368005404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493069361 1250 493068111 493068131
    0x708090d14070b270a050d0809030c1911030105160f05160c0305010b030d1b0c0b07030c2310050603070f06030501080607030b0d0201032a02010621030210020904 71
    0x541c20350300030b0134106050003540896a22419041c15103201025540e00022858030001d030b80040d03401c0b0641620304040341640d8030111854518004c4010740546480307201300c0c0c0f405824907607140c7c20610b8050003d41e20b49411202c141402c0e00c40c1076507940e00103403000c2c1001854030700c501250b40e40d8068903d8418600041c0305601c2480000c040c00503a515071800a00700700700071092040c020060020f6010b0700b0000751400010f00248210602c0c48666400d0028541c101f10002148102405802200644540d1a4100100f105280c02c1007100c501882c143c00c01040003801c7e01340003100e000240209a410f00510a2202801c00a2304481c0c040c4105036021440340000c1e102e90010b020140e400040030361500d0b1000c1d14142004d0190006d062421000c03480036141c03140174090b4260282804a1241081011742c074080152180030f8a020078009100403210b03a043d00f00500b114a203a1540100040c0c00c050381143e480035800040140c0c1c4001031051095165801a05001b54020300028804d00e070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493070611 1250 493069361 493069373
    0x80a110304032a14160f0311010507062c010605062a060f0403020c010f1e0c0c0b0702030c04020a020723030a0c0510020a02100c1e05060106080708090d1407 69
    0x41c9800c225240c844410414440b000100040745d48400c886004910407444c10004901c4030310311380005440d101101c80c1e605001e9014604a6104580c008420040d80707445000c440e5403014401c90340844440d00710f0b041800c0b040140038543c191746005000514090003825694850701c2c0103590480c05a80e10740009048103c10310a0a110361403140000341540b6003840d009082c0580d030030846060140303a40e6120202c6501005140101c11407100000e45010801d02c00d961004142c90300800c4131050800100b210a00780c406424194400d03000c43d4030352503041003080103900840c4403080040e0700c084410405041d0019480f6042607807909501146071200000c01e040c0640000181c0b90119614000c00103030410b480000030018440c0b0190038050201da0000d14202c481020030010000c642280c00c091040600081203600c1c004a10001c0c020038619081d6100d2000344507400108004100080510b401800c0440c81000340360003070103148081030f9050782c01056210580d07030420410700603040000e003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493071861 1250 493070611 493070687
    0x140601020d05130806090c0328020d03030f0e07080705220203180a1a0606070302070644060109030c061b080a03060e06030d121d060a0903080a11030403 67
    0x3246801f50920051803418549801550940c0c1c42c0c3c0603180c1d400b0b0034806d031810004d01d00c1c0132b641140c4a05001800303050032009441007a82c1e0201d4145800351001c0005000504c070805c0311104d4064502596440081000051b001003000d038600d22800c00f40888406d0541c01543d0100130071032020581d805c0d41c0c031000e162402c1c2c66002c481c40b501307200501030501849003100f94005001c4401c50721b0703c040d6540003921043c0310b01c14841403082c4000c40c01d102c0180c2d142e01e00c0300d02e094040030044d640c4111140c03041007444100006080354059020031440c1d4801c940316070559070003040c9d084c00545006421035070340e0080a244100b10120400c0313100060024030040020030180e540c0811620305000c030440d46007001030328182c881e5001d00e078802c68140c0c110b800846550710b940d80000749104050540d16074192200302c80403050160008003c203299140d8413000390280296614400303580c501503070400f203880f035441e005d29000c024000a00020b20a00a4022540e5030040360500c03c020780e25a004855 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493073111 1250 493071861 493071871
    0x7080709020d0501050a0605070311011b02070e0f04200f0402030c030604050c1305040e0a05030a09060e030c060d0b0f100f0e10081b0c030d0f140601020d05130806 72
    0x15000503000c142d00c8600c1c0602d9002d8282261000c21607454500040e002d0b110301000242071085044512100d044203502442a000e200d0301191542a105403000b500e840060280528036000100820701080c101000240700c1c9600690208050049a107101070014a150005a02c030084c103c07506c0460300d41c0d0003e0344c003c0102c4800540c4030b0809101304030a40700c0043c0455aa641c060145200100383d0240480494906490000d03060f81005119803c0809140d0013034054400000c0e40c1c400d440e07004050b8412584240d0300c0e406218102c4c01010380300c06044001c282d004200344000040344031a41c1c00b001a81320001e0207110105032800120f52043e40702008103000c10b84040d0810850b5800100e034148840c000c640745550384c1c901250103400c3c028098454201c06840b0084521107103c007004540610f00ba44d0304480d20f0b807001c1c0b0401d4000e852507042410403942005a168018810540014007609058001d42030585455004030f900c0c0d041507042004200c2860000980c2c10710520215000d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493074361 1250 493073111 493073129
    0x18060f030c050f04270218070c1b0506180607050d05040602120310030b0618010801090212030a02061911030a0203040c0806011d250806090702070810090302070807 72
    0x414074000400c0b82d48026080003a02480c1003079040d4114203c0d40020540210300e80f1000400050035002151070701f04840c1d810081090004188010250400080e003841445011341d81508444508003007001046403044a80000c82402501071108a404071400c44e400c1c003621050820086441e51071926413150510340108400090a10010740c2c184450b11500307030080780316455820400c814002006140c480644000200008141d5582d1032000148000003400950600c5503100e04000303009200806080703100b5244c41903406403125002c419109502d80c1394020340358980e5586c210b00803034420f482e00e1842090b070350150f4825140c4080d000d180074440c04800144c50346400c1c030749000200382580211081d940910010082a000d00c42c84505901810112100c50749030700001d10300c800d203012003100c643c08604c0c8410407155030100c4014070404040703401d40c0e0613031201a001da803202103601610030160002c0941c0900c2081907042420424400d00c116003d0301d55801c840350170044690070481032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493075611 1250 493074361 493074383
    0x9030314040c06031518050a0b0d0501020306090f07080a0c0210020a030203010509340e0d03080a0b040615051c05090f0d03020307171504020301090c0201050901090c18060f03 77
    0x301e5070316126030390400c1170900344003554900745008540001100c241211503075450700300240403d04140c020001c6908054a0310340700a400c3d1030030501030b420071204035000340d003e80006000d65101c500494000c04032900c404459407128103010f005030204600c0b040079880b0782540c82ca80c4624030300c014881091141d80060b00c82d4101010080f40000103094000300300803086c003d03560f803016030306030b50307132820326040328110658080006135540c0c4040303070446500c94030380751454041c1604840d0007481850754540420251500e0401c20080702c00c0c2d40a401c5a0f1a00c4841d40c104142c02280249a070402c541c90301c6a1895200b12203405440c003c40c0d40320000d8029082c0c58280c0c1c0310070055620035600741c0c2419811441d19070002400c5040c4c0024200f9500407c00124100f140c034025a2500d250000d4403d65903036071154107180240600381040c500541c030b080c00003503c2102c103104917142503034403030349100d80720b0300d41080303007030a104250600c8042558a11000484030041c010400080d0300c54001d2001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493076861 1250 493075611 493075619
    0x7030806030708060c0d06031502070213150b0f0c01020301091d0d0512040f050604050102031008071202010f1106090a150c0f20060a09051c0c0609030314040c 70
    0x162100602038900a42c007551080c002000f0104040794020041c20010b0744968191034428080c01c041d07400901002c11032a44041d00380c00742e40050122500030303108a010240001042d0044810741c03021342c008418044400e000410311840200180a00103481500f01594003034501c1c220703031081c3e0024038101e07070701c50b88940c1440203e03507455a0007110401a200808030124060b0407480383ca00100c000810140c0050104034003401100401030300001218140d10b441e1030858003e60003690601c040030074210f800a03580780d0006018007600c0000200400034030380790b170054480c200c0220942040c07011620483c204111304216151107094100014001540c890902e00c1041802c0c194940c1e94905003941484542c1e040044c1128640d42480c180c1c01d000c041c84810202580b499603180c0c100c3c080e00b8140484014580c100c03003540f5020303d003a581c9022503958546a42c2d1120800d03000841e074101300780c0c4e0100c0d12a91200c00654000c4c00c010807201c1c1102c001d490284800c56084840a1200c1c03c180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493078111 1250 493076861 493076867
    0x90b091005010b16030e0105070f060606080127020f040308070302072102030d0c03110706080604060603090507230d050616030501050307031b050405160e0306150d03090314030703 79
    0x18010440b55651900d0106420205080c0c01d1308250b020b001c5c054030f0641d038106a480b490484a029070032103001e003ca030349030780760880c0502000e00c10348002610041c000318240c648500b962460780c101c00c0c20001081c0c0200300c0c420107500f01c82409110018244000008105040001c210f001e01c240e01505550b41080c0c4483c2105007182070315000310950300310130401a01d000600d500002c0b0300d0b0a142901d06441e16084500c5003814803104401d0049060005401781c000344c109008401c100c9052204646400c4224101d910402020b03141d03038040c4808200800304141c1814480c0d030f90400200c582c881c80350103d0a800c446842c12030380355100400700105008040d0b072a042030800c515040c4055407400340025910882400043d2161204c0c0c000b80c1107414450400c0350007400060001d000702d02c2c10004447d9060300042145d0007182041c541c8040518011070450722910301c2e059400382510103001440007001201e1421010700a2014000c00451074031007a0702e1070307030711005c000310b550b8403842ca001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493079361 1250 493078111 493078121
    0x315020712090e151828060602121e0f040b210612070501051c0c022a0d0809010302090d080c0f010608060f1f0905070806060913020d090b0910 63
    0xb6046004104001050707683d03038000c80900700103140241da10b0311345651030000070742071359140e079611800d100303150f095108091a00140300301c5450b5029038600d0907000601e43d07220b20400c41e1413040880c04045962f07800010340058274080208000040c10301d0744a03202e2010f90303400115903111a400800c140c0c2c070812000f50005921500588100340300080e01c2c02c0e400d40d1104580100c0341400030100fa0840003001402002d034500000076410f20a51100003400786d02c1d8400780c0784910080307003d019811180e05917030a00c4401084082c004070680303a44c070342700c0780c0403a00711482c10707410981c08220f2078805030744040e011803409000b2401240d075030300c01842240c0f42c5192107440844136410710004000d00080032400079442040d61500c808550340e40365100f400700d4090080b02d034407941880301c0855003500c141d01c00780c030428454491501c036444403001c119a5004903074009074000c100c1c140d580610203080e0090900f400c19070401041c10b07611541c80d100c0141c0c1c220380380c07602c9503c100c3e403401c0080c02c58041c2e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493080611 1250 493079361 493079371
    0x90b2703031021050d080a0b0a171c020c0f040204032a12080318010603050706180617070c06110c0a06050c09061801200d0e0102030309070315020712090e 68
    0x43c1004a56030309622400001da958080c800c41e840004c0c2e030200b080d00024212000288660321641d19400c48840c4000105508020780c840d940e0320069840c800354440f0070100b1640c00500b41c2c1c00c1d09070b003000851070f2031509494007d6001e010000c0042c0e4102100b15800b00c25170501d424085030070b0008484414685d10100e40303132003030304045404104401e0172607400c04100c4089041002d00300d44410701500071a400180584070340c0000141082d4083d4030002c042d100034a610045660f03561003100c1c6000b0b502200100e000c05031011807032942c01364690000c01445410080340c60340b4051442d440c00d821581810005400410028041100610559520507070b1482c2d02e9003042502c4001c039401e4003801c4d00080003d92004000c0e601a8021094407103000440484006103000c941c95840c0c64240c034000000109030150b843d100c942d800481580c1c842c10b410001000d0143c5146c4821131803400300b50180c20a103500b0400b000100e010300305007548901640d211345114030300c8d103003010b9030290b40102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493081861 1250 493080611 493080659
    0x1b0306010617041115040e0a020a09060318060c050a1e0905010c03020c03030a11060a09020f040c11060c0a02070807080a02120c0a03200103090b27030310 68
    0x6102068001800c1c0304100322081c6000b00c50f90b01c91074900c07541e106401d00d40e580480280c2c3d00f035241c8968000204160b600d841840c0b681c41d00c680015405901800d4080c50100700b11141c1486110705c643d1103601855080d203a080c0c10041c1984030002214048408500010000112550402e8118031f03148042c0c049648451081d0882e11401002c09182d801228100304011800c1000e05100b000b0010140c034008050325038604800c0d00181c2014840c400744a03081c0185400200da0f91400c0c401c00540070303000f07041e100900d40c1a04c208002040b2085a040c10f01c440030203525084502003103030901c41c504c40701c149603542c404100061301e171401d140c0c40f4840340d60256030180500754000c0787e14020181d040d100310400c0100700074850b0904c5040070080350400c031040b03000403e0203443c60402005070300205900c0010000d8400440540b000d070311001c1c089854600206011420801d00159800d20401c0e402d031021510b07042642c2158800c0d5880c00740c1450888050140304c0555401c1c804c2030382c03588 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493083111 1250 493081861 493081873
    0x10207120f022b2306060907051e0c0109020f060a081b0c01050109020a0206010806040c09090809060a090906060f0e091b12060a052d030304050d03031a090c0403060e0307020405091b03 81
    0x6c00083c0b0390180100f0103001c201c03020070780310040400b8070000031004c000f41822688980c0f403281070600808190307205030301c1086001d0b048141c5007001b10490741401031565614004e81d42d010010b507501e402600c0c101440010800191250282c05e00c00d00d4044e0407800b001580d280c2107000b0007440e112040e000808a80c0000b070034003001074201400071f02103408540340410351b00b0007428154235900a103803659800c0800084c504000343d6000c100c45003600c1d8020400c0004c1038686a0032a091034154619030f0104440918030b40551810302c82d0341c0da0080c0032006000c0200302c25030088050303810420720400180400b40c140301e120b2800703103041c038040e000940301d03010707a90113081d00301400f902404c150f41540140000c0c0040e0ba510b041c803c4901600c800340c00d00d22050070900d002001003c010019096001580e2504039242c0380c0902400e00990050b100d15041078150b071140c0008050b407a5a840e07251100300300000058941d4042c25100302c1c03102c00508440003030309071513410075003d51030407e00c40c0d00301c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493084361 1250 493083111 493083121
    0x20f0f0d06053706080304060f0c050307080f040f090c080f04020f090c0703030605060910050a090306050f0702010e1203160903150b010207120f022b2306 68
    0x40585680c040e0061008545610b0308030f8207100401d2004404402198245010702480e459280c0d00f00d0000f00100341001655581ea04542e164004d900400300000d001c2100c03009158800c4021007009030192058074a01002c0340e560090503440041c0c02151944046000c005c0c00f400c11214000074003a940b000e010718241c50300c2c010902000141580701c80300c41500810b0564580050a4140d40806080380030181494801d00307120380c101f900c0c11800a42042804259414030100b80c5400c40406040d0030f4010f60300d07d00513902a0804203402c0d007084850b40e80040070801a000d41c40c0a50210090ae09140c02c00e208001c0c2034461200034104580d0200c0904102e1001d5036040325800803e0b0510b02c9807416544204584a180b90f034005440b4a0400b07610401048e103d51150103000700903002c03205225030364079281c0000040c04201406980440302c034000942031450007849540002c403d00c03840310407ca400c8c820503004201c815121818003980050000118480386143c0c0010b880007400b040c0741c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493085611 1250 493084361 493084369
    0x9091a040302060604240b032d010506071e0c0f2c1810020309150c030403030506012708160f0b1605030c150a02180108091903020109020f0f 62
    0x40504500e000380c0c2e95860725100400300e0142d000180301c2680301502000d5039240510349a41041d01c580d441f1940714000007c50003030342070b040b0709d10b003a89500c6100513a2030502048104e4020a2050303600c1c40c034044032410f8503150303615041582c07481100f02123900c1e0304003c100106e080c00b50300800c492920100c1107112200381d0f030f04814403000d0110b103146029600d0250800310340c40c000240000328460403075901034035803e9030065845061200d01306c50f2070700100303e0740c001700c00b0040e43d4074a00c14200f000814003091098020700e0348864181000c52070300090500625445131048018026810794490038040800c060007440c1076225860b202d002c00b45e040400060104841d44515005801c000074584125200c81c0d640610160300442902e880301301503e8a40d40302d0320040000d50a000f85040000c9075008a0310a8035480c5069040804510741060b0054400303001c00f40641c0143e100b11003903000c1c070b80040c0d4000c5903074500c13a03400401c041300c09205202d0110305840d001c91203101070302a080c0c42c6441e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493086861 1250 493085611 493085623
    0x11d03031906090c030f0509030f030a05130803010303020f010c08090c0108100b040b03161805040c0917030a09050a0317031b0304080403050f0c0108060609060d0609091a040302 78
    0x3000482035045000118074400140303041d034048605542043d40d120b0000340c16500c0351031a2240400280581c0c0d551703d00031504e87c4600160001c10b03400c10310201e01345501c56440150b02600501040c1c082c04615242c15000341c1007640200c0041c0d110040704444c500c02030041c8050550107081c8500c203070400403401500e840100d02868108041c00c000544000c0690164200030142040c4851396035072195448081a80202e9460a1054050702a2030055202e003040c200500c030060000c045242c02e20041201070003170350083d00200400c0c044042010320b5006190324100030300c00001d541c1c3d0341c0080400f404a00150703200a100e10703030764601007002c01c100e050f00301000031012040315507a946410f000c1604540c1401c02c0e440c40400072040101300321000d00204142c0b801041100c201000042e5070559a8010f940501d0010f03031480c2c0410794030705180024080341000145814140603620030144112020741e44803610464603070046600707001d40002c03502440d59041d495004030f0321701501c3c040d540303035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493088111 1250 493086861 493086871
    0x207060633051903060b0a18060e0d02060d0b12060a180209010e0903160c09050609090c0f0409021806101e0f0908032b060608040605040c05031e011d0303 68
    0xb01d441450111094401d03801100a41050b0005645400c7c034178800400401e90701120850142c1c4109000ca80c590150000a8030141c0081c442c40301d400b55070742132091300e130045580d590f100394864250400550b541c035024503060034440001c00e4186060407031042540e60740006030030710042a5a0103000740c0c0381e00c8801c5064030440c2c8903241013a11049503803032661013200240481c0490f500400020040400c1218048502070042032040d0b071102c00810441103826911190b0540c040000714000d401c000211084003003008100180000860300031034030401c61f99807d40c0c031240100b000c001d254a8820301d01c01d0315182900e0503404103042c0c0344c0410f80c11051701c0e89000c140005980c0c0301e01310034860b070003040142c000d0405a98444030341c8071541420700b0a04a04105910564458044c41001031048004907203c0b9680c64840341c03190340301c0d40000c02d009032040d2603103003441401182c0c6032000c011900007038101100c0e8400d20b4046200030741c02c582200070420303141c60701107540791050100001661f42003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493089361 1250 493088111 493088137
    0xf06091c030e120d02010501090203190504150e01020702090a09120c081306020102030a06051c0b1f030f050c0306270a0606090b040b06090a031401020706063305 71
    0x1a80e030a003429502e100303900c2060b583c07000003c03140c10710326000880e071849100c042c2d400900203030362511300b52416400200e440a140703000910002c290855181c010301e2300580100a00000089560082025500b440034601c241da0340001c2d101d81103081945c2901da00c44007540003005841c11596882e80640d02ca2401002000144404441841381f41e004880b51412400404070f03045688007000381c042d4204685003130149152a90024507801c080d403542070408481200c0003c8001d09a0b91265510006418400d07800015080322461482040025000c0c601800c070480c0851410702c1c0403468010200c0c1d04a010340c1049050006000310211250b0b00f15401858a0004460701c0c0030b003a103003600c00000a08420304007080000d42e050680d001b030f0303403212090b54144440c140c3c0c4c40901130b861050680d84c0e5003007403071410100041039040d0394850000c0002c0001520f1b0619940741d0f10140c55043c0c10103400420803d0706000c0c2c20306548000000e14410036504024039541d12400361850240071220800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493090611 1250 493089361 493089409
    0x90606110d051911010f090b0f0c04091806240f0f170313060315080a080a0c030203161b050306070e090603010e07120302010507080906072118020f0609 67
    0x3c40b5000f07245921080154000800c040303054924100c1c040c0000b100c06a411844407004110f90742c2c401e800070b0b41b168043c044080c0c0303000e1a0240010040a4074440564002d02400c00c402c00034044c1d00528180144500290451031820780000409207500d0780440211495200301300100070100003400101d540500300c11130f49644c0c40b446a810f42c815035000f9580c0c3c021110000c9641500765100000c2a503001d41815511600c0d48c421903914082d0000141c6056010711514042c20301c03032501d0031142d9100b407040d83d09056103a0b00070347c00100314407012220314007210641c0e04030030a10709280c0d0040200320000c0809060644014007200307410f40303184d800340200c0c038000707030003500d00750465030107441d080040b11000d075590380030000c00b100a035904800550a05000c034090034880e040e454020070030200076007040d4654400603150a9188900714102c8400200c1c000c000c140a4462041e040b54403600d02d01c40c0c040603104000d20103d1007980c89200d8001404003a4103501c0f1102081700103d66112031082e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493091861 1250 493090611 493090657
    0x70b07020103060506030405010c08070309020f090702071a030f06010516200303040e01080d08090718230610050a0c030c08041a0a1205010e062206090606110d05 71
    0x240281d604605d800c071308004244020018154800c080c2c102c4241e65601903034880841c00c0f0156151200e003e54041c012002c1c24005141a0b4011030b0400c0c010700403168016170302e0041036603000e0a44044d00003040003104124843c048014426480602441c00b00d1422f08100041d0340303100103c0d003010b000500300380a0307103c40504000140984400040071a41c80d03540e210f0224100d013000340070741e140f54002d50307040c2950030b4010590381d4020f84e501d07009000181e08016503000107210079005076042940701d445290704a9400311720300b11003010740002240146070a000b8014551020241d000411501f000b115070b500384e1144616007a01e0303152901043c102001e043c611094006c0c3d0304034120703100b04451b902e403091505a00500d034218041e1201003512016000117004c441d82403007031015190490700010928500222030222001020240030346010075114000e080750b446800041b03410340d07580000d01c5095000020030020b400050000d20346e1406115000f0820700410751511101200004403403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493093111 1250 493091861 493091867
    0x304050d0321020c28020f090c07021c0506100b03070e06120c070b0f0c0904020c01090c060f030f020c0c01030b0303040b0d05043806010c0c08060a1d070b070201 71
    0x11850000c929025512004010104d0361200e0380350490000700d841e0458142d018600c00c16003004803540040200402040c00414441e100d40c0061020402c08420050b680042ea180b40005031940b00d0750b0110100310115182c51417403d540a080100ca2800350342e010050004403104890b8441d0b410305d8644d100074030b007001041650143c02152081040c000040000300000f44003d0100d803401145002c4040e01c0c0c040b40120ba141d800e03205401482c0301002100c00c07a0401c4c3e0020071754007003010b00000c1c240a9071b440b60007142619802090000300749124440e503c540c94014081ca10005103821458100c200c0707201a9152403aa40c81d505140c0c8030202c14103030381da060041c0d50042c4056807005a6440214507100e0050000f00c40031a500e260701c60780d240d000700041108460101d00c425001c0900c1d040003280c09140b400c020002410400030302c1800b000203c090105900504109000300110f0500300e100b030701a90740c0407c080211140610b80e0803030000c00000c043c021262540d08050f940c1940380012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493094361 1250 493093111 493093157
    0x11503150501300507080c0c0c0d0c0801050403020c030c1819021c0204050a09020f0315040e031605070909051c03020906041401170c0706020c03160b070906020304050d03 75
    0x250500000f41c5040c00c4481c030343c0ea08428417422081d80d40303446e40d503608072613583c0a010300e4034680b1480d1300c40301d076500d981d08280314074050b5a40185200600035035141c2d8030702e0a40f00c00722000c0300180c00c100d404402c141030410001e001c3c158101d42c044008201c207401e007803040700002c2807024a404900130743c2c84803040c0d5a04480f0030b443c00c0d41903000d00d04214400c00000c1d42c814403c01d40101c0e5446000201440c00e442601c1150b400c42607000c2c40e40e00d4001e1024204803511010a070321035034522485890000c2000141100385a01c901820800e40d90f0500d181800e000d5448040964105622100080c0020808881a009030140103a2000f1401c01c01c4000f80103042039a07400500005001c6030304090030529600d0818241c0c0d4006545404123100d0304d6009060307460a514078002c0c82140c0000ea04c1c1d4001c0c040400d6100101c90400640c00300116036400e00c0390381500c00505480510400c9035005001001404aa000461420740f80c08080760102c404040c1c06410041c5802080800b03100c49610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493095611 1250 493094361 493094417
    0x16050702150301060804260d09060608010f060612050f060907030603060903050919060203190509030d0504030c090b0906012a0b010807171b0a0b040806011503150501 73
    0xc020703141d42e11204064803c1c01c007a2821349041101000181441041010383e80302c10110107d410704200f00410810050204039004a91040c4c81c6d4a0200b4500ca0034480c1c480c0300a035840021540500d000409001c48001d2610600207908100c00c00080303c0c8071191094100304140c4108500d540e8500c41100100032540008080d03a052815980038581d11001405003c80300300c0760854000c04100c14040005e003148141400b68209001e209e03812092000c40c001000c0d0941403aa00c0c01070081b00007404c000c5070200040100300301107070034030a01c08030004c5a40a0445c412040001411030000113140c0180281031030b04011451210300304000345207134005055019041040300003c0d96113031944060f034090044601500c5000300006104000f0304a000c80b0700b5505001d829404262480c020310300f088013410b90381141000c00001503252a0600520007400c8440262049504140b12a002c510b03040d80170104240c00c08654801006035424508110b176000d003041c60340d2404841c24103e0a901c2c0c416 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493096861 1250 493095611 493095649
    0x406090905030901051c2f071106031f0e0a06081b0402030a0b040f0b0102190f0807050309030f0d03110301260723030f15010e070903060c020d0e040516050702 70
    0x603c84d54116194902035900140418111614407c005002d007a0258480c01381114a910f1042c10080c01d19000940e000980c5101156070700b844c20943c006407400651007071100c041103404008141c0b4241c81070740041e1200380c2c00f51200c1e8501c2d500c00a4106092a103061045a0010101d03450b005240c1c0300c50080c10b005041030104241500c40b07080201111507101e030140c01101d001207002c6d03100e559040302d529440082500c5550054840d41443c0c1c01c0500215070a01c010032503040381f40c0d004c00480640c5d507135110041180c02c220000003029100c540c1005080320340300748018040500e0310480c014080c1c0c0d4800030411102410148549460f940d6030080c8056059003218040301e11217000c0c20b10690009404898003251503507811a9280f81452500701d500081d4401800003442c2489500d070441500c4c6008510f8580f42d884802c220788880d5683c00243e030051023940e074001d800242c16003100008407010009440d0000540c40c6034200803ca80b0b08000002072818115030790844100300915240c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493098111 1250 493096861 493096871
    0x1218010f09080703140301050a0311040b0a080f0f03040f06120b06160c0b0403020d0b0403020f060106050409053105011d0705030f03070c050d030e041103060406090905030901051c 79
    0x1080282d019488040241c0015400e280c1c4448410803a01c116412114007610f0f01c000707149107450b01e0303400c000600c2ca0182c7c0300346c0302c4000e4415562a1484040034046d10400760404001071a910b07494412107540c070412540003440100b0642d00d996210b50121949801d019281015690456006085940d03944c0d074030000119101c1c003c01d807254100289603124001e485085904c030541e0242c02c2c0141d100096001350b03050201d20008000422031a08a03200b0700441da003040c0d23240442c5082c040c0903000341d03000481c0428104040600d80c0103003504511030f40d00700030003141d42d501e4103041d0320a0003042c5004020f02c040c0010030040c1c25071060705030343d000b440d44800c4101132012658640c400351240c0d612901c00c0c2440ca00103264040201c5040d541c0c480480d140f0b8614200c140203451906180070740c00c1c8a155440424107131594014801754000b802059603403840e00400300400c541494203c1420503182500701d100054000040342c44041d000d0074129240d41400c0f20240c1e444180b076400c0c6440600302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493099361 1250 493098111 493098113
    0x40506220c141201110a0f030504021c0215030c07021c03200c030f01021201080601060507022b061415130209040b0604060206070f032703022401031101051218010f09 73
    0x105d0003408510711103640d203042c90a03000c50202c05541d0195170181d03001c05414071258040c1c801d0f0980851680c4050400440321480040840c0d0030b410071200e440800030002208011460200e0703580700643d616100542c0d5030a5540c800418180740e144000d45044000c1550400142c1d04110150407032000808846141c00d0390307401a4043e4100314498114201d4000012941240c08185203040e200c50b9034a042c10180142c0800c0009000503c6602c15010b5620302503121400b9044100c40c154068030010600400b100101c01c104540180078038408103292107104490303641d07000003004840d141d842c05a182c4030700100140060004002841d80440c0000300081c06540105000c0e02c5101c171515611800c11520f01d09400307440500c2c1d80e002c06034400c141886401010445102c40d1140648102d40c0483e02400c070300c0020342c42d14404000b5101006004100304569130320101e100d20400e10301941040d2079414aa080880c0c05410242c01c480748100706e00c100d540035071211560301030100041c4414581 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493100611 1250 493099361 493099391
    0x51510081906121a0109020406140d1b031410050d030c11060705070816060e01270902070c08011107021c0501092a0f06120f05040506220c141201 64
    0xf488402c1e0f07990024800c0000b441c3c1046d4800c2d50110740241d281c2d0040c0c025516031001c60740d80b21103a614009075139003031503501d9180c0300c1d50311031707010501c54030001694000b0100c0c0035040c20004100c10b0b140f0103500010b02c1141c582c055203500546e490704260a10035914074201c9a1900000359080c3c00c8034010518800740400002c0b10011a02c0d004296119900c00340302c6941c0114035401844040b40c00100b00311800d5114074070072202c40135881e00d0045030b2000d10030f607000310300c1c50b0741d000d807200703580104144051003044049040201030500080000f21101c400c140c41c0c0c1d00404201a00c20310141251040d06403019944a640f41c1d030000082000d1003581c94441c1d0780500b070908540565000340891311000f130f4085d0351035081d0740c9004080304105151101c215000340c1c5842054040e684c4560f031a06070701816000c0d40d4040c500c076601800092600c074941d028001c0c410b01004110380400c410a1001c03601403009001514401c04c22040b2111541c400301b4050400c01c000c0a04541c42d18200a442c00e40e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 493101861 1250 493100611 493100633
    0x10e071a0c070b12061813030c0515090102091003020319230f01060801081603060e0c0d1a07091d04060e100e0618030d09030903021305151008190612 66
    0x14103c8046049588203c92841418007c80380104198030111044001c80d000e074420285403445401200c40b0705206143c0801c80e035005944200a80c6e401003010746851529031075000c480c1d611460b0440c10741ca040040340d412200c044000000381641c814401144009641c4000081c8401400600480c24051661060700c4000d00c0307070200040810001080c0c14002148410039080d21602c8140c2d03450868980e03800404039401d89042e41e1282c1c00030ba03192512101410700103940212130510403894210207140003420700802600070402c0004080c41013025501c41080501030103003900700c184d1745900d007000091008820091a500c0b07802010300c1525069048a0192803960060321226150100750000c045160540000280c10521114206d0300650707008100040c0a460284c60031640ca801081440100008104a040c0c81300100701c2e00710400f03030b10304003807042c01e661010386100b10820040c43d05c0c0c006080c0c403d007035030308120002c141c01650b08518094191200650550383c01407030280d90b801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 493103111 1250 493101861 493101871
    0x60e0c0310150203030a05060111120705060f04020a0308090102070e13020a05040507020c040506060706151a040b0301060507020d0b0c0c010b04021e1623010e071a0c070b12 76
    0x400c980400d90404200e0b0540c80c220880d0011801c0d501d03080203070400341500425050421540a00307607682c0b00400c01c82505103110040380d04c0c0d0758442604000e406d01d680200080d09808070142801300684452030040c2c02c0342c0d08409041c1d10f80f00384200403030502e407581d400a9107921814060004014065500b0007020341700310341c580d5005a4440601043d20310868801d405600141d8542c6500c0c00e1540055a0010008010b94642010ba41e11707442107800ca40f14081c403100e00803000740710f82c0319502c164120f145030580d419400c0c180b03011080c2d4003501c814001c003410800041030300d0b011900c0350511a540309078000a01752003803502441c91806901307d82e03266400d075820402d5400303441c101442251000c2d021511150690310a061101610354007191501d12550001e0900d200440c1c8000b02c5070000d45c11038180c0c030740111140d84241e400d480c4034102c0020aa040041c04001307d842036030241c011100d504800c4e58956004107070043c20002a0f070322510742c0c9600081d1448080403040041881a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 493104361 1250 493103111 493103131
    0x20f03180102061303120f020405090f0403020615130b0103020913050601020c1207050105091c030306031515051c211403040c091508010c0809120c0a0f0501060e0c03 73
    0x1a40c0e80b60030901186444c00005004604d04000100310700d62140c100044c0d40500c103102524065880000c1a0001001c4030b20142c00581300b0148000c0660512041c0e0300080700404491440b0040d00000d000400c001d421211950f54070500d07141c01e03034060740580d43c1248005114003426216a2401806810119512401405621504019481c09804192000c80200d00801c040340c01c0030010350f1144c0c49a0411940480d10800030117207480681c540051f00c501c2594049500e80c0f85252055102c07100f0702c03010740c0072818886039502c0300c144a144082210b108885102c205000400c1c2224680707610a40948028100017084034039040300c00c140342c2e100e00e00d5a641205110b200d00283d031103001c01d550003000506954410004012030b900044440d075094540001c07119520424107007100c10700300304400440d10400801440c510b0a110001070301108068107071134840c1c0f5036561900e54405010040044455a00050500c0401d43c8100c01410031041065040c0c07c169001181542003200d1001030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 493105611 1250 493104361 493104373
    0x110907020d02011b2109020a03110906010c020904030f0509060429091c0201261e07020a02090c1b1b030318090a09230609120a0f020f03180102 63
    0x306800c40746550358800115079074281c17101c1c40a41c0c00c0e00030100c1d2100c448581d5880d100e100c07026944101500c402184241ca00382e48542e411001d02c00d500d0002091a4140281508098096103032100d10f04c0d4003560502d07140120186c845411f130f0741409034a02c6960400303408240451141080b13614100c0b010000304081c400c101082054002da4850700c1903c1b40c21041f41c0307031303220414480c0010361250648141040805070714104400583c220210b9820800c80000c4002e102d8441004005403180c4c00e6070483c030000c0703841c180d0300283d50350310042002070044884500141405418a00340e900d4a10000d180c1d81d030881a10400c00d66440d042840340040c3c0d5403e014811807407038004100ca051a00a02280b0403d4410000300020020000c01508400d6206d0403c00009181452a030041c402c546140040050070643e0107485d0910041c807404881e8410f000301041c207000f46080d40c1c104a03152038101c7c031005c0350b440200d040001105803110355105c00f2540446c2c01481a649100d00207080e421124 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 493106861 1250 493105611 493105631
    0x90504140108120d18060207022e050d18050705132a02030714030d0b0d05030904050402030312011404051e010b1b070e0f01051005090d110907020d0201 67
    0x3004920a00ca03888071940007031110814025100050421086041c0c0006100160101c01c940481020302c1e04840799a0300089040071441c00c0c06c0c001901c0f001081c01070a50640b078031500c0300c038264901d420000303206e00414102c403440201c2c0c00c000404c0400449400040100c0d2900c01d03500d8040b8000d5600c10421150010124180c500c1142c08081210318181000400b03880303181d041404c401c1c24902140820000d150100740070403940c407009091900196501c000c0071620307100300c0d0911200c00788500000303050313200418400801e951154508580c0094241c03241d200003880e601c503416a40344581c11400000594810310040882d404500b0355051001c1d0740c40c00e104100e014020390540e00f480028000501c50505440040c3c416804000a11010f00030083c0460303103131060b2984980400c2c4603200030072148590100301540100403c1d203202503008608103010746180504e503a854060000301103490180054258040c91122014110300b440317043c001402501d660401003114017540c20880401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 493108111 1250 493106861 493106891
    0xf050c030f1506010c02030318040f0b060415032304030206150315041403121017100e011e0506010206060a0f17341208181807090504 59
    0x10001030035200103020aa030642e41d102d460248060b0029040040a000c400010b8400304020038281c6060041c081c51203e1000800064484903152003426504051042c0a152910815901991030419180c5c400c46d00b051012001012280b41d10039043c0c407aa0030396074800d0201c0c44c1c4180154025400d4407d40e41d14000304090040d400e21103203400d0342c019001c164000480322a45500a44511a4080410b00d451f4115107190008030410303050044038414020300440c0201c60200410100e02100c0e08440040541034075150000248540c0540f80c1207100a000b00a61108290100441d04c038000031006250400c0144011900c0394003503c160b5002c10018500b448401c81100c29040b400700c0d16505050410410b1202c074407000e402445940310040300640d201900c04803030f849454416a00710b42081104100c407000354040755001c0300340310401c40850135150448040b90b0280b00405800d0441c14003144039580c0e0016420000c000d5002030144c1c2950094917001218000c403014460101810030301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 493109361 1250 493108111 493108123
    0x5030a05072a0f051b01021608060c16060513020414060913060f06120201091e0506070f02130501080c040e0307120207030503030f070f02010504020f0f0d08070f050c03 74
    0x320000031036507416025200c00d0b0890041c030082c07045100700c50300c43d410313911249040c1c692440c60680821050b070107a001e5070304200d5010700b55854032241404500c0c0c10030715501e420000e4002001c82000060095070401c0c05840c0340d186aa11000030030a520f40746c40010b111400a00b000c9204509042c181500c0750214400340340038240080440070315840c0c80000424191000b01c0441c0e00c940c0710399031086008068481c28004001310840407041c8021880010008082a0060128021114103400030f8911040664041c0c4105581a540e981d203182045005183c8003103000391f010301c0c02001100003403155001a4101c4440348200c4e14040304000820080d920003001030700305030303000380302080201e07000c0550031001c01858016030799506d13140d49501d130a583c02210b40303a00d0103210300280304a89a22065896801c0c07400d00c0200030703034105507000400003039450019900c20002e004d40004107580d042242041264401005580c0e9526881c084000c2c02c1441c0e8142c41c0c03030080c00d010042c103060200706 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 493110611 1250 493109361 493109387
    0x191d1b090c0a0914120f0304050922020603041716030212071104150f03060209030705180a0c030e0a0f051002030f0406050919060f0510080d200d05030a0507 69
    0x14403040c0d1404e200b20205500d480d900701070360114095401c1c59000300c0901c240e4a4121215016550b514100024440d400d10098095070203007404021401010f24480800e0504c640e04583c02640e075156810029000b600c40d89150750481c43c0022580d42c11480d0095038010180711f83c080c0c071a03662480300408a280100c94000e030041400c01c0801d141480c00b076100741c0c2c0401200c17406036903503600c42914407140113442e0000c45819900143d100038528003000781200501081715070350520400c0003007082a44074003a1407001003688502070b41c11024001e070000308000d00002c0448400074000c1c02c14245124080300161030310302514070380418410343c1d4000c692203a00e1034112500552030b2a07880100501d001018101a0b00402240300305514400c00f145058501940c00071038010701640c00c040860350043c2c1082d89030707481c005080000007004180700c00030804504045082c1c0c1c1c1d02620301a40c8a40300070110f8042c1c0a51501a00359540081c0518098032000d0b800300025540c0000c240c5180340f1070a5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 493111861 1250 493110611 493110617
    0xb03010b0f2512080c03190b0a1e090f05070804020d03022a1806130207050c03070909050d09060207090e0a020409060204140306191d1b090c0a 63
    0x40403151000000080c80e00e4582110340711040e1400b191580480114400c080b00e000300c00e0204105066407080d403403508a0030880d00c41c1d2450070f0462030460104186411003203034a4403100300a0041c0d07030f00100e00004001001c2c031941d0000909044552940701402070b0407070945480b01c0a14082e02c41d2040e07510549090b00c9007800b540f5103800b00310190110500840440c4501c60300120700d4103403681804c2c42c40b41d42c0a50390100034200000c025905c00d08001a0040d41c51200801c030240d41c9041c001154544103100050381d60000b0f046c20760400c069494141d80511809000299000180d4072402d080d5003c2c4094404d031b407150f400125134640d5070b071088030010381c841d1005102d10b01c0c0c2a070004040100100031980803168a5000c1b0f0180e407502c41d03098880701d901003010003121690070071055203902d04501400080c5080c0030103035105910041140324066035400c0512103000384100c80d00f1700013042000c4420140144511160300b01241192074007603102c50010418240c0b00c0c409444240c2c1d0291 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 493113111 1250 493111861 493111867
    0x2030307020d03061511100c030b12060601140906040b04030809190602150a0e190b090316080306010302090d110f1203030712061502160e09150901020d0509060603070b03010b 77
    0x5e5002c43c0d038925411001980350240140c00d5a000340ea40c070440600350b000351030200f9803a489100f040081e1030404207030560754008804101140c0e0b40482400500720600140c4c0d07488a042d070340402e103940520341016011000014021050082081c0a41423019048900300140880840c0154542003035100e14005a030004492045415880343e942d40e000c29980300c0015041b024507181460111480c06603c4003006041605050050b550000c65001040000035803401c011803020310040f850000000c0c0140d000440400c3c000c2c4c0c402c1c0c04940b2100070061171458025400d0601e81105a0008616845031015500320300b43c03030815111340f180c140c4803140070350f0540d40c0b042d5040d00c01d501e40e01c460f401c00d07a5840001141b003807100f0111120303200300d40d40100201c00307040c001a0f205407443c0e008480309541c0c0700c0400c81043c000003840f0040e0b80e401d400201080c1c071005a031030b001e400f581d070902c008182840100700129000082c07482c404e0740100c0845102581d02c040303c0c1c030240b100f8001c1c81500c510030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 493114361 1250 493113111 493113149
    0x80d1a01050a03020307030207021513150f1b0b010315050901050610260a140a0908091210051311010807050d0902060705030301141e0102031903020c0d02030307020d0306 75
    0x4d9010b543d10004a041c00741ca410b05030f41c0042e40c3c4481c01d0003032110369400411308401c3c0e2a82040d914000e45193314200e20056518130015001c5460000031100300f242c10b00c810703004010110700c1c4801160b405060103d20356164035100781499580019070700484d14082c0014449031050113000d00840014102101c0c08001c8002151850382c000d2410760320b8541401030258039060350241030b01c60507160400040349010102010788110000e0300b00c900e958108040800410541c3c07003202c00c0c2501c1115007801c00c80c0d08640d003a0401c0c8036490404821880d220404c05d00f0324982181c9140d85121b03a0700100200b42a80055540038025100000042c50512034000b107803009600003520140002c2c1581d09103000c5941e03003451603000b604042280046020069420b00300313112a1440c3c150000640a000c3e602540000d40d64051550105d00c000f140112440a0728020350480d0103900880707064071940303406054040d640c1da0040d106000144a014081840c0c507210b440342c1010344100000c800882958 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 493115611 1250 493114361 493114367
    0x203030915060f040906200c010c090b0f0a02120d0c1713140307080d0e0606150304060c0c2a050a05150d1b030917030f0a05070e030703080d1a01050a 66
    0x490355048409075600c484e40747d00d40d0041510503903081c6000302c19950341d40428000c5400d44103143c4041c800c2c0940741074140b05210106040e1041c00c0e048209181d1502048403040740b0303100c10094490358640000680d4007003020315410004042d1000d0301c84020810b4403400310360390031004441000c20303407000c00c414000080340080510151580034045a080c03440c42d44030100151300541000e0782282c1d403203032000b050742d60500c1a40d0b03115070b04480c40e4040c1b81c00c0c100311401d24440180b008040c16565210b20300454060740700f001020390040e404000e0740203801203a070402c0c10023141d003c040440066002a071494644140b8080e40c0000d03048a0041903010514401c0d5045022039001e11a201c081c6400440341c0c03003034280000079860b680820010058104846902d4510300302004002c000c00c1001620030045883c10b4008480300390014172950743c1141140c0c503a444400d065410f00070550004140920f0038085e005480701504d08101804006240d05007245070205014040b6806003c00a15180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 493116861 1250 493115611 493115621
    0xa06080609041b0513140a0204060507030c0c15080f09071a03100902031023090115020705150a0810030f020d030e13062606060f0a09020a0203030915060f04 69
    0xc0c01e404040f400d80300d41c0080c508003000b0715031a42c950390350040389008159405030a03400c0415848118503149c01d1641c020020302c18150f014040c03040c0340740e00170204a01d03980050010100b40345c0c0b082e15607200c0b01000300b40c0c001c16030300700d495a500180407a41c80d03100801c0c03134401c403903107071803200165102010040c0c0160001004580b0342c102c036601c009041c440314001540315a00010000300140d06000c3c01303401022801c0040030000d040301010940607120320f0342c100d0558000d4503041e01110615801245004020741025030890008ca20000082d04564054601d04190b03468042040e03aa440408018102c1d511018110070443d444200140c00c18020004c0d4290081c81c144110000e82c102107801040014088090942d80f45030810002070040d070840c00209080c0b101c24554040c020b006030f030351a005044c0070f00c600c00303041200c1c11a03603400c0401001000c00341400d5440340022240170b0f480c0d4004880070a440c3c0104041c40c8040780c100b00e1281d01c501c1000f00f100c20411111021f0100500d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 493118111 1250 493116861 493116893
    0x8030628090e0c2701090207020105040b0705030d0f2f03151f020d0f0e0d020108060315150f0105280302040e0a0c09050301090c0b160b070c020a0608060904 69
    0x101843d55103210f5900d1385074041d0341c840c90394040712080c5120383c459003054010590284211741c0c030511500005070380c0a0211400c42e4103680b0156160300260420780d0071031044020541c403691034032140b541400790503004030f100c5154031121085a035001daa54039842d48a8445420303a048420400200078803241150311408620140009010696144c0243c000300401d207864005a030010039540801d40e80200182e41a00359841c0c9a8140340c003040200c0c030000c0d150417001303041c8541c030b9000034020f8500f005070507600b9525006611090411017010700d04103e1110710307240102072034540e40340c941d401681101c42080441c0901c91a47c4014004d0801d002c000314410b404258081100203400c071080104036004a15a4a00140b80c1014901c003a2001855512244c0031780d0425803c0c20210703500c49414400c451481d0b10345961500c1051000d144080d540400a0080000a09000c0180d5005050381d103032a1007036540344551511190309540c0500101c9002c0c0c0e0114800001400040350100250701d59 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493119361 1250 493118111 493118113
    0x1b050d05060613061e090c030b1f021002070804030501050c031918060903020f0f2e0b0306010e091b0a06050a03090c0603020d06090c05070b090c030a08030628090e 72
    0x103605d440c905c0541c0c180c00c0f00407039125040302505001c0045c0c030f0700c5621b0300e0300e41d03034181041209240c01c08210342c20903c61000503070000451035000540c3c002c0c400e01e005600e2800b411075a9150f1854403481c00d400500080e289586000d000800b421400030031030740a020421010503d204940c100d8038003900c910019400c0b51800200e40c200055031600861544502ca034028240b040402c50403980780c028600c030b0908540d80030b000e01c1207a08078049802c0d039600e240c0000800e460109651580041d10b46d64403025007620940c000081d001c0b40c4051004d014005290944034080c0704680002504119420b000e031380b101011200b000b0450181c03005001010090402040c00c1d41141c9403c0d02c20701c1550712801c0401d0f000900d1081e941013921800001d0005088104141440705900800d00d000d4002c00070311072401140071501005c2c0800402c2d559501c004c0888000a00503d0807640d2038005031507440c003615140a0000e082c0c031410110b542881218000c04800d58600721016000c0c0201c3c40a130841 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 493120611 1250 493119361 493119371
    0x319140a17030a0b1f05090406050303120603120f030c0702010e0d21080408040506070c030605070201060329073903092103031e091b050d05060613 65
    0x281540d25400c120a1078001401e407079181c400034031000e441c40300c82c2503441030302c0000c1802e4411096074245140b0551518140e61548000c0011400400a603000070b0b90522011510700034154a03880c0b4907201b0713507095080e41c515031071010060700030740203a200700c520340c960038400110305095103000b0f00360f454014540750b1800303003200d0041421403a202ea000e40c1c000c0e81c401703030300d0355a0802c09229401519040c0340a003103a28154a030000346000b28050280305000018002c018000c43c01421000740d03030095802c105a003040c0034043d000308010701c030481c0da41301c07204c9007243c10540d2841d00a40895403600700ea19a40d513020000c82e18500704040300701d5072016250548816085925190800380740340050060840d01b1400d01500d07201e22940300649140c0714812030300c0b122101c828a40c0445506050104260407d108100392070039158200106481c0b604840e00280034042c00c4140c40e01480290a141a0b81c42c0c600380808100c503544081c1156001d04040380860030050401c00f42d034128140b000079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 493121861 1250 493120611 493120613
    0xa030b0603090a1e030801140d0b013321020c0706020a02150a0f0f05120c090f01110703080c0c040e0a05011a36010902070506060319140a 61
    0x1500d070000c0c2c0b00c407082584240b04520801040114a80800070a44000300714030303106950090071214140202d140c0c500a04202900644440703400000e0240e124840410302c3d0f0711200f84413044405101c002c41c01300c071007106100c060006050380002d10100e40e501d11452003c181e4014590a030340c0501d44c070019600700700c9950315020603c80d2902a08056018200140d610300400550458001108200b03440c10081021100d410107486031500001342010498080c500f0415902ca000340303541c0d039000503040000c11142d466500000c108001040f01c1007401c0d0324110004640c1e04800724604401640b0500052000c1307075010020b4051100c8541c12a01c100000d0404035054507a64440000682e2100c800320082200a004003202c440c3c1d6070b2142c5072150310304000110703a282106803a00c085890903000c503020003c826000308002031070300c8200d001541c1d1034a40300000d5020714030039100c6000d00d40101d85a40b60101d001c02400074005048041f164458503081d5909030240140303c0180301d000c0000b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 493123111 1250 493121861 493121869
    0x10b1c020a0207051306090b09060916050d05010620161202060904241a1206040b031b010906050906041403030c0601030b0a1d252105070f030305040603020a030b 71
    0x45c132900c42e202c1c3c08a19141b61588070010b82d02016a40c5100304200410010f040d16941003456224a555100903020040340c00e05a0b514070032411038620043c18080046032040d00305e40a80020441815003402044d003000406480f100002c101e9161550400810056202c110070725281c854001071440780703040080c100080440b03288100e90202d644c46204483c90701d80400c0c40d42c000a100003c001410700410850061040c803038009440140e42d044004103c807a1200e9121841d00c083c00344c200c0d081041c1c1d22000c1d0a19140e2120007900180b00e004c000300324680f05505468129501411103410b150a10ba030070280d1915184007185c1511040c041510004410030006009501590300481d240c00e00700145420384800f10101c41440c0941d0340d517100c7c220400207003050590301154415901d60070260a403503001045034441c0f1081388030f2803542c1c201070700116600c0030068440c0040301d034229a12800b698243e44540700103008184248070030050301e03020390002c0145032010b1400143d106031203c001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 493124361 1250 493123111 493123129
    0xc120309050909120d050114010f020d030207150e2a030c0904030c1a01060207210f050c06070501240302150d021e07030311090f060c1009031106010b1c020a020705 72
    0x20117001d81c0392401041240000c26030407e01810030b00e400001c1000c107400281d6603200a058203003c040c0d00251200611251256071540e80e00500002c0c42411001c40210303541d150301d01c0000484500c070409540400003031764000b401c80ca40207805000300006050811503600e000410a6060160241c40e40340007451092118030343e048010780b040c5055050110084c5040d0158012140c0d4121081d0303000003150311408200c16441d0301c81c40b4401c11080500d840341c1011071070a0115080500842c0b440104081904100741c945101d500e080350010601e0f40c403040380c110a22019410691494281d00e120b45544010020761300348101c058030342a0f515100b4000810110138000701400007040c2c140070036506004000070482007511007410550b00741c4c0064180d540c846a91b620541c00081c4c60200340105024080241c0743c40001003081035418100600410b25429001c540350144000100c0e6164203501075689400300b841c01402000002035003e0000d40c02206045c0035845820350019a6907210120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 493125611 1250 493124361 493124377
    0x301090602041d01120c050d03030e120a030b030604021f021908040611070b04092d0203060a150e010e01020a02090421090b090f0d0605130c12030905090912 69
    0x4034603030460f070403811454600701c1a0080c01e0600030030741c2e45001180c4159035607415a2011559000c8000c000d24095000780000780c00c102c010700601030ba40c6102045080a054001241d0301d00303100f1440c8440426032a080120380007544080b002081841c4500043c040f842c100d1101e00445500c0e25020300028102050004120386864000505220b003d42c4401500301c4842d501c002441401d09012100c1d0443c041ca015040c455035690500c20000c8030750421000c902c194100203044203480e07aa6503000a5031044030004e010368052500000c0300e50101e01031281c2c1514980d102d1462030496401140d0070040244000d04500c200280c0310302603500c40c0000c602032442180240180d40001c00607059030300716611900207000300c45200b003021034002701c116111004112101078226a4078000283d24400c0520081c0c58245800700b00f100b01c086044070106618000c081c030a07440ca44c1c800c070103c00c000300345d80c0050005000c00c0c410482420122007aa402c01c1419003a100d40c110030030b502003026009100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 493126861 1250 493125611 493125629
    0x52517070513020702151c0219030e0303040b04170f03070807030f11120c0408030705010b15091c060f09031806140406050d09020a14010f2606030109060204 69
    0x300421862030060102055403900820035070070400c40f40c0004100e601c128a0741b00c4d80100c001550014464440030301d02400b87c48a6085444036200041c548016188006210129140840100c00c000001054034030450744045109170130fa0791980c41c82c1240d032020300c1c0d004007481d0a02040d040e00f05d8450143d481014190703940205460120750084c113441e0b960204d03211345403802c040a40c60006130030031500d00c0000035034a8409030301c40c6103108005105641c00070b00103020110703844040107019003259000341d000b1501591800381d4900211001d104100007590b000244499141018071041e40c0c040c1d0807401388800240300c003181c0881034240e80300000110000f0314001740b2603d4189500d401000940030500d00f49142c03948a1031b0028092040c1d01640060020100340030b800110983c104e0a81036070701418500c40d05035a0b002c10380b50381c0045002640030440310018035030882c1c450600f00318251084e00883c6240c4426080302c1c02a11000380a098041d501c6000340000b0400a0000300b004140325a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 493128111 1250 493126861 493126873
    0x90b0a09090515061005041418070216080d08150121020903070f0b070803040c031217090d09051e12030a021b010207210506040605150d052517 63
    0x2030299110b0040c001d0100b8800c0e045076017402d00d000e40c00420340e02a600710910350340d80111b1540014408604540402001280c40da0800a085a02042e0076070501c01d06540300c032103d520340341074984654562080300002002600028480c2d031110b041690301a2043c1007081700e903c81c400b01007440b0280349603c2d0011a4000402c101141010000c40005007424550400a58103024401071184181e99019182003808000700b010703c11105034000045a00803802001d000030080c000d06200c91008103842e5281a03000003424669020a031034102624903516403500034140020406481c0c07000c088080c4420b296415020305445a43e160803510745010020750300e884908000900e01055449002e0140c80040500402640c0001d00384056134218412500d4880e441d1410110030541c580d4050a14402c01d418802801038650126015501c03003840315580300c4502042c4000f441c41e400c0010007503404515115407031078803c60b508410b8028440180011551a00c0920003651a84c02518846d00a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 493129361 1250 493128111 493128133
    0x206070c0f12031b17040303020309030c0604030c031704050a12020304080105100f0f03031211070602030f04020f191503060314060109050a2307020f0d0903021002011104090b0a090905 81
    0x14040038030344c00300c081c0741181c000381d03100d0640c90203400050b000074203240e004404215900d0003482620410201141202d40c81c0c6804d08004018482018003513012404c0c50102402e1401e044894174440e54001c0001e08085500342d50701d000d0440007070094001c60000b840046260f6500b80201c501401d159040302c05c500d4105100f00704401c0300c2d9841141008111442000000d8100710740080c82d500d155000950840c00019102840c1325000340207004a00c000708001070034501d01540c5004038001d480300003a5417003045c00d00140e503032803841e2540400e016503c100302841a806841412510720b280202c1c042d070756940d4605003410311490056042e040100107000d120a1449003031341c0f2440b50041841208a003040644040103880081d40c022045080020340700350003007010034280d0a07017070200c0e03100524185005094060b5030004030301c00c06843c01081d41e003078414011030090790801300e40545000d24128410009100ca031000c1508480044e000144840c82440b0341070381140502c020b84115104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 493130611 1250 493129361 493129391
    0x20d090b06030f010c0f0c1106070b1602030f16060b12030a121a190e09160b4306020a020c0409150b0609100207081002030105010206070c0f1203 64
    0x8040d2102242c0c944852000c417294498002c0503400e210341400c4502420a007091200541c01c2d10344c4a800401c00603400d410019150a060301c110111607420200c904078408c100c0e1240714071003c46840700c0060152101e074901e500d00303410380c80f40f2580300003e0f840242c60100b41ca82d980004000b44940012a01c00b804a0700007609290040c0040e400304010030200100c0580310751042507240c01014184030111003104809903840240c0b000301c1410f00185800042c03656184414202c846415901620004007000300d20155802c10081740c1c0c48101c009688003c0c80c42c01c0320025807210300005000d0502d001d0740e8204101a2449003d80405a42c0c0e40841102a1802442185103801146040155408600c0c42c10344c56002220f1000086030b4800c100001a2680c0110f0300360540c002d4425120f0084c240d0000717071007411140d0400a86402581c404d00880482c042407080c10b0250704141e00080546128000d101d01580c0700d203180580c02445910381015000c1d00110100c0407a43c0d541c0c04a0030111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 493131861 1250 493130611 493130623
    0x306031005162604060b1009050f041107060507021c020c0102100c180b0c190f0204020d090609030906080a060b270607111905030c13020d090b0603 65
    0x118028003070101d401c1480e44070031000016100c500811102403156100e410070000d0a0f51500009500214141003900344003009180740c0c00020310510344200a81201400390f0f0160080701c500602d80d0004d41e401c0c0080c8005000c02415500c0b40c01c2013040102c0c0020014850301d0302030200d980c01040107a5550000403c030030080e110420665001c02845841a03a000650643c5070707040d0307200072a00e8210414113481c50004007007a491500318601c2d02050701d0004c3c2c0c0150075105c0c1c00b94100c4807080024401554401da0950016014100640000d405030400d0380060a0340301c0003d10015440c41261580350031079100201c1100000d4011600b0401c15611000443c1c0011001e032040040d5403825244038110f2240f0314407440030361039409040603c0c0045409080a0a002030070255481310743d481d111160340301208005200709030800004641e036040401c3c1c4400c0d0f8002400800c0041c5444040110002450840350344150b005c00c1031543c20f21795400f4083c0114400c040303030412403e0040805003011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 493133111 1250 493131861 493131883
    0x715051e0c0c0a122339031b0102031309020a0305060102030315010c020a08010908191b0201120905010e0109110409030903020909071a0d0b0102070e070513030204050103030203030603 81
    0x20481003c1c444c1c80030440100308a99406003500019404801c10701c00d8942c8072a90f600341c98000e40c0c843c0d2401140031580f46c40b110242c1212440411021144070780c10140c0c107280c0c0798141d4021031841c007181d80350084000d002401401101c0c00c0c4903200c0f80c000800c0700c8a82004009940101d8042c5016805020700754005009002840c1107286c18074506541c806807140042c1000707081e00b07100c0103648814a944020700780260017071100704100c0c01c21980c0381d88540e03103201e081c901103515000380300c3c841c43c40d2000c01905403090407000340f07040d001150703c4204805070b044540d03512001200090303000d20401c202540041e0001c80c05083c0d50401e2140b80b020450214019814a0841c0303000070f5000caa41c0703040c3c035130407111541d03940c441c1145285400c0c0103170015440da00f8901d04080307021190b10040e1224881298060041842410049844641d288520640038440e9400305594501401c0540116000300111a0410b42d503500001d040d50070030b904c1540942c00c00400d011440c102032016080304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 493134361 1250 493133111 493133119
    0x10f0605060f09040b18010f0605040b190e0301060305060915130b19060e270c1c02130606030e070e04060b061204050709050a06080715051e0c0c 64
    0x1840c0801154092240345181144600000350602d001c0e91240e21201115001802d1252a50032000c0313020581507080c0034859070300c045500d000401d50702c80c07030848081d5101c500d0641e0405541c4001900c05041040c002000c4c04548004040940c4003441004021401040104828105002c8042c1481c201342250100d9858040030026804a110b081c1742e01280d0206d40401d45603940104070507a050900995502ca07810503900155050f0805510390042c00e07004080c2030000152419a082203105c00070080320350f00080016405450800445128001c80103100c074a1040ba503400544040b001190741e600041d69204284012030789407059100460290005002d1581845a44004d03030700b008100822131501d50600004c21b480759400d61303000700030040204030b084c140b610b4070544500540c041d6110280c40d100015042d05014060042228102000740000d242800c00d00340e0020707000d0740a4001d20008005010610350413150358180c1e000c0200d001d40d2075400c01400c1070f0070308400805451003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 493135611 1250 493134361 493134371
    0x30a0c1e050318030a0c12030807050a0806040b1c06050906060607020102060a0c0909020301090c0e0136030b0c0717070b0c090f0a080d020105090114070f090801051305010f 76
    0x30400000c03200703000c9500d05420407100a4034000f9240202c0700c0d03030081c80b5040c810400100c9040c07c00904031f810384a500e500d080d0f50b80307500007100d00d4050107240800103111078010a810382003561103040a0b4401804040c0c1602141c2c0d0b9250081c0f1420404440041d507034410080d00d59002e1001c2d50700010202c0301c07245007c5441d00000d51740e003409426100035a03510003042c4901401115104000d0500001c250b442e50703560620b0b0801800901000750100380c0740700c40401650310402d1496080c1c480000c41c51390f6112028079007000c074034100c3ca0b01d1961840281d0080080f489403035100b4425240000b015580f44c656140c15122808600103642100d0401c0c4000c10000e0300c10852564403c19090702c5540742d010000c0007405421610094a400601d6144003080c00c0202003120014550325030002d100310780300c1304455400c036500e0121007412103000b980464a0b0b41d00c1750004500c006441c0c036001181a4403142040e08403a41a24890341d0300300390003101c0013001000c0c0200305a003101c400701004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 493136861 1250 493135611 493135613
    0xe0f010b0a0524070f120206060a08031b01240f06021b1e041a011d15030408040915090c11060a11070605010b0705070803030118020304060e030a0c1e 66
    0x22808450f02240b1403e030307210041d5440c0226404060701c190b036030408410200e01d003aa003400035020f144940c1e410300502079017000a660707082c0383c100d001c110b5140ca402140341120200086914001c4030024161a5403100d565a036541e01c1c18103110301814410141e20342c41407034031070924541c2c009540305200b9500060365240c428110003244107000e420644455600401200030103095040c200d003003913403280c0b82080c3d82c81110084101d49040c201d0a0300c407048020094400000c1040c0610820360744032007503a040e00c220744c107400007440d0030911441d54182042d0302c42c07081c10251000310203240c0c08604440d80c10400c101c818011101c3d0048039003000d0300b42c810b10b40c142c95140c280042104004546403040c1d00301221200303040350708407034000c6000c02507940c45401c064807e50102e04192000d00ca4001c002c01c80344008004c80e8100c6d40c100d07400030300100c0130300c0b40400a5000104103440032560790f5222920000300344000d01c02c441c1d044c1c0d28404211004d1519620310b13400f0542e04202c00c50310424002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 493138111 1250 493136861 493136869
    0x415030e12340302010506030c0105070c09020a03060b0a0206040312022a0708030a120c0e010f0806130207120801081603300c0b0a05100e0405010e010e0f010b0a05 72
    0x52080621104168403100c4140c0708680b01c00d404a40c0300c01802c2c0b60b0b07194142895419400f050190748110103030ba103886001d1004580c3c074010000041c0044610480801900c05d4580c000c1c9001c03600e42c1004669940c0d116141c10658001e03c0900c0b016030845000c0004240e0701c0750203400c819590200440c05c044500000b1000302124266042e02d4184248045908a00c200b1225008006000c12203560303d1070a00014911003131000d10425550508541808041c05000700354250a41a900c2c540448040b000c00c0300c4403c0d0281ca4280c0225404002c4401c5006038002400480c0c092100349d014004004801440c491050b03000b040d01707030000180010503044500e44c94045a8000c001450303604803580701c4d0b940c01c40f080c08980c1d412031051041c21500c0c030741041c3c0c80134605024004001072070384c0d045810b03c141d40044076070443c028201401408441498861590000c0c000d9000103500c0b850115187e08403920442c2c50000d1350302404401009810900555010b904269000c3e01034074503290103e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 493139361 1250 493138111 493138117
    0x4060b030609130606080d0e0315060105070c05040911012003160516030507060915020c131b0e0a08010e2805151905070f0f020705060415030e12 64
    0x10312880300b2a02140d07540702c0541c8100340d50340e0403010412001c0c1e81c6809042e500c2c0340c1c01203800041420b018191210f4640440d070120f910303d1403001514140d44080044581e58020b02080f550048a10008100798440c1e1192410f0240b0440c4050201000c1c1c00014021f00c2490302103000000042141100d00d00b03012007039452180c40c0c01e8180003074060900d0010704110302c0003504086c000c0800b41c0001030260000b086411142c03240c0300da111003a182e1100c0c404200c10301c0c03000805607201d04d03010805800c1008841c08801a240000a540031082d070f07403284003218070300c0f6242c00a03e03404280803151502005102c02841c1c404000c00c060f0300380302c0b0031544400440441440889011082020005000002c48051640301080d01c0707800842e0b04090503804419901031800a04a1806224003031a52084d0750003103680c0d0315101d1907082140f0080307901c04c0946048904601500350b00003000c3d08c8490140018042c20030a0009030650490020211404c50844240079400b8080c1650b0b140740e09012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 493140611 1250 493139361 493139371
    0xa020c07060e041d21070c060503060a091811010509030a060e01060f080a0b060909030702100e0d150c0f09030605041a07020d1707021e1009050a030e04060b03 70
    0x80c820b00300c000e60018008003000f40c04101803c0d4004100d406888000c00c032101c02c510b0300c1a92002103040819002c0544c002d61703c001308850485136061003094054405142c0c0058014000d618803500c031450f0340140c9270b40ca80e0107a03603036024034010005c02000e1508004020000c3c40d18074100f4032420000b80d03558881100103440680d5800c101900d8540a41000e4054807940e51808140e981d5604480c0c1d440c02d0740c1000f5248080d8481c08518a031030440b440502494405005509002c000e4080202c0c0c003a034410100144000c1d0041e401c80d90710f0b50b22121511358022203000d60700600c13080446040ea0609a07050341000034400350100070320780004902c4203598001c3d00010b6159110f21748171441b040a086000c0840b0800004c100710301d580012034070301d100d5090751902100300c11a4294a02101d0640e590f1000d07800801c10320280c45c030032a100c8030801340d01c80100c801c04807031400c1e01021100c00200944d041e421412500301810340000d0b41c604d01000542d0208000d91902040c1c0700c003404040c107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 493141861 1250 493140611 493140617
    0x5180d0317062209020312030115080a0203100e10080607020f211e07060f0609150b032e0314060f090d0e01031508010c1704020f010c080f03010e010e0a020c0706 71
    0x81e041d829500d04025001c44903400c0881e466607035855005000c2501d8ac00300400e4000750101000504000b8132b0b0013a24041c2d2440d1000c006c910382404569650000018180c402c00401010001200700341085058007500458014081c0610000d80d224141500803d0a441d054a000380d0b5030054419242240c40082a05060b103100080036191178080d4030500d203000c0c19050519407611110340b4194840c40c215090f00404110f400140074100410307031068860062031000510012700200103480c1003031903102a40318880d40602d10180b1210080350990001c1c0e070640114404541c00c2502008590b8000040d201d02189034500507000c150740394071410804040150542418166900a8001e0a02c12041d211101d40071a00c0c1d6040500034151155280c00180c0003d40c3d400302da15003403410a000d15000340c002103d8007050f000540350003905a00c129000101080019000c0050401460280642030903244203549008101080441e01601e5500700c03030702c100702c480840e0100140742800c48405007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 493143111 1250 493141861 493141871
    0x10c0302030c061006030b270c0417060709051206070c080421150b1e0f0909250b2b11070b011703030705180d03170622 53
    0x8641281503000d0020000c0852141c50103100c5640c1500300304106031000c0703981c100484004041040604202451b9401b06030f1165004218070000303240f1420f0380008000b420701e140c40c0e524081c142c0c10030300040d09891680c00c0001406444c5510560b00001020104d40142c0c5c01d1200000e05a00c0c2c91000d80400b0034056001e02c000c0402000340c05680081828507131100c4151074403058140881c1001c601207c040b9614205c000728104039208154600002514006400c0100c2d002d02100568100026070b2100b10001c0710300b10799a0f0030140c14440d041c0b442c0a85032204404038144000b522006000b00c41c1c0520701400d11291540328260b417410000305200604c0480000d480c29407200302020f8010030507040203081c40c240f6241c40700600995204200748003288c0c0c0d0302c0b00e01c41c0d000030005070384d02280d4008002064450744142c0c090721109001b812100903c8503502b0000e40382ea00c00150442c0801e80b401070644c5000400700306258004400c8d6a0341200a40e1a0910b040c0d0b00b0148030550503a503600c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 493144361 1250 493143111 493143113
    0x14011b0e190e0a29131b09030c0503030f0a03090c0b03011e14010c03180b0720040509071203140a0816110c130f1a1002070f05010c 58
    0x122009810300c0c11418401c6004903151204941000011208001682e05021101002611a410001c2d00c40c01c01d0f0410b01c5000380400411660701c8124002c0c1090300d407102d0548004c2c1620710541c403502d07011070720b50100c0c00c1c0c07444c584030b030351000c1544c840d920940081c06192851000082140c9a09400e40b42c002000301c00703484c01210300b00b0a60000d19000c90040700120303003048410303000c0d000d03054000034945a1030740d00c1100c10915035050070480d0004107541070301e20009020b41c0207101c0046a10039030805264035260300d41d9150704160f0082c0c0e0102c040c9620b51031044071900104101040c280e905100350300c2e040400a1359205148071303042170108003001e40000c2c588a04046821810051806a40d1f03103510500149120820340718041510580c0c1010401240501c0c84002c00c891000c0181001c4901c400c10070121036520008819001e80302d122010014165100f100d541741c0d6808071108909020109001030b1540d61010301e0299400250140301c2c0f10000340282c1704440702460002d02400712 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 493145611 1250 493144361 493144369
    0x3030a0203131205130e2a16081207020a0201091509120503070605180a061104030204240501031406040c05091e010e0402030403050a0e01031805060414011b0e 70
    0x3070303200c003e030101902c100a94843c03980f14006090405022103103c008a4403003619401004081d41d540051800c2042d0301c0b0400d8007244007d440c0c0d4a030303103040c10f070800420400d00a102001010200c030f41d0640018905441c1a505000070741040740c3c1c0c030040c6410a440e0740042c0503403a075806440301a46000a00018162260f94990050400c603000c4c0780c8801c0640c40c00036078a4000d1070040752040e06040028030750094100750307540000b0142d00200342801142d2142001070241c15001d58004c1802c01010000da180da001c1c190103500c0c1c0d0311a8580711041c0c0c2450107210754a541046042508141d2507444680301071042c0c0307070415021517000030440301c861400d694038815082c030345800000c3d00c0e44481c03200b111760100207140c0400ba2983c0d030014040c0c1007000124442202c0c0140800c0c03003400b604641511502510010b41010304001514900107800d00d6043c4070004000c4901d54859002c0008200c5a1041c000b000c8113010000c0c00300300301901101840f41d100c682501d042203140d1a4003000350b41c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 493146861 1250 493145611 493145641
    0x3060a020a0c031409272a0c0c0d050f06010801020316211401080d1e0e010908011506021204030302060c071104050a0b040534020a17040302130b0303030a0203 70
    0x401090b0700c1204c450800c034410f0404411004e081003540c480e0015400d40c42005841c7d203068000b54800100034400025120a0703002440803081a00c2070381024012520b031150382d1400d05000b500104461350440510614003174050300407171180d0b40140244400100311985600c2c41d0921802d064200b81c0090700303024600306600c070035000c2403810070340045860b0403a01c000030f0680c1c05440640b2103d0203a0300c0103566071070b02c01800d0000c00e5585a00d111705d05202c0d01d03600b4403100b0705140c2190055609d01c0c1c41425200d490403590758130303840404108a601d4041060083e4442c100c0301081c200303403541c1c60203515140300500c40c13044000000782e0701c0c0802003910074600c05000018001c02845c01c00d5440302c1e0040c4900502c0c1d901a9191a0101d5003c099086240e0040030141d04014286c3c104c9089848103070103001d040e44107520542422000081d00c80c4010440100c2040401c3d84803861401085003a41c03441940389245841c1030071a8080f504e011045a40c000e40f42c4102607a0307a20707900c00f0105284 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 493148111 1250 493146861 493146877
    0xa030e0f060a092108011211091006030c080f0103030f0c080703020105010612140a0c030e1e1501060516030e120c090a140609060102070509010609030203060a020a0c0314 75
    0x4040c910070041014a20b81c8400c0c0050f011300062030003000c2c40510b643c14070211580e5007010852520040180c0202046130052031403084512503038103241400403559038201aa03043e448030840110522a03640d0600c500100d03500ca07407a000c0e9013414503100724030741d00906001c080c040282d0102e081c002c05000c2c010300311009a1040749a03990b00d0780383c20028001c0000307020710400034031f10180050380492207010380d08101c2d48034541d803100e5850384140c0100034600f103240c1d4810b01d51a00240c0d81448014400c00904c80c0350b030b804c00144001601003142c24241c040d844515142c01100050000580c07240c1660507014100c40d08484215090030192903003002c540d01a64400486500c01594a5021801c0e507101e12081c0d50702c030540e4651810b00c1060b81c0c0d00c003100e451607412450010304189803141074181c216006005940216071150302041ca0000300360800c4010030348081040045013130421205610803a500403c60606044a400400d04551aa00a002c101d0810110b4400710f0010007107407004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 493149361 1250 493148111 493148113
    0x1e030b040b18070b120a0c172805061c080a0c080405060d1b091208030a0902060a050a0e0904030c08130e010f0302040605030105040c06080c12070c0203010c020f030a030e0f 76
    0x4a5940903884c20540c8200940541008240d01003501d0030300c203000b2207011281039261242181400001c0286a0100078441400d2403582c50010000703c0c0000a941611241900089450728013402401400300c1403900e204152880000c4110110b05850250707040080d2514004041540300d003000140c0b405036802950f8000e800007803d41030710009510440c0c0b0909008080701c0a00c02402065079059001e200b60311403426030b040e40340d000880c444005d40d031040711705500041406480d00440da00b078001c0c0300c10001140780016811487c40c1c1040c882030f200102250220342ca45081e5074020091440010001c16154000c5100074608030002e402101400c5460340d481071940e526503440780d50114511007a4000ca01d00080400d007810306002d40d512681e000a1411017183c5403002c00c480c213100007083c4050400d000d2060040c0c502c24188210b01a5aa89d40c402068081c507004140c21600001c07415829503100c2d0900400d9507801009580740c0c00d01c581000203004d15001402820803410b85094030036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 493150611 1250 493149361 493149373
    0x10b0703020c031501061d15090a090903030e15040c03171b1e01060e010b0c0703050d210c080a0e070503010501030c06020d050301061409060913061e030b040b18 71
    0x24480f440004a041b1049a80c8010000804801c1e00041c50700c51880d064000154110750000065014001c08000d03201500000815903210200000c803600084c007280004e485080d850400a4104000b511843c0881d52031001814240d644510f0704c005440300a01d201c0003c1104804c81c0300c084140c680c5030380c41c0c101c0c219119004240a03a122454810030b45c9043c0c174600741010b11001c0511915055400e50140e0b41030507424052016816000000b4a8295104002c404800540306101c1124000c000d0344980c0102c43c18241c64103018001c004444e002240b912000c40303401584540340c01d410107407291001521000c003085007410010a13420403509503080000000c2049440099007088440079401d94018030743c0840b0442d0684400c1c0300e40c2c0c0000d4207102c043d5500301f000d41d005001e95013008004514001d80d100c04104501c2583c000c20040b1990fa41042080c00016030041044074080c01c8489185400c564403070150000240001d040002004000394242015503100081e8102c61800c582c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 493151861 1250 493150611 493150633
    0xf1b08120f0403090603021602120a0f050c10210b01090807080619020720040f1a0f03010b030706050d0e1c090608010e04141510030309140603010b0703020c03 70
    0x1400781d03410380e03003100028108180024403038428801c2e200c03000080d90b494000303504113408100143d2206c110745141400f98490102c00203841c5100d025110b4481e1000d00a001404410050009802d00a103004d206074198601c00548009402c141041e03540b0340002008184030004950703110f0241c00c0031815210305100030a1846001504500c18a28200c00c1070f95051008035500c103034000e000000340b440200c109600710700c14420080c208104000341c00051f28009543c0500d0549003110b81480c181ca42c1101484183e00784082d00070f901480540092000c085544042039a5681d20b204200c10040042200c82024036507400201e0403450b000c084486030021103000c80d00310b01c0d510700904c2c0405d2031224006403460003010302c54102c030003001b0300d00c0050760390751240d0032081c2c001d204030715880c028814012040e0000c0003400780a166200d60701c8146504601d8050b1000f09103400500f209183d40545482540c1c50308101ca0669031140902500e40b055480d09900e06060b0300c40f00c1d039240c0111420704c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 493153111 1250 493151861 493151881
    0x607110c01052514070e060f0604180905010f0b180405030d2003040302010510150c030503091e07150302090d0201050a020a0501020a03091707020904110a0803070501020c010c0f1b0812 81
    0x400b61100da00e40c994460301c03458100030302c0540f40302d03234250442801d100400c021850b04c2102c0100310000d42011135407130501c0d0344844c2110071591071744c15400c0d03940c042d1020504003021901070b5403030803d58040d01410030340c8405540e0b0040d4540c4400c003079241c11000e000100e850034401e59141c0503900f2161282003621740a070103000100c5c1d6010410044640c0001d202c800e51440108400385500c810900000c5a01d0440b59540024154030340380c440e0030b043c00220a560340d60440c02c200000302034036015051001904070721402c1c004482c101401401540c0b040d0b0307550f81c014030119a090130440d590340c0c0415000e90604070803240150007544086001490150035070049030505204815095035a4a82c42d0190605d00904001a42040d8001c0000e4005071100f5400444034800801290b405030350b0b40217191455020707070012503031039401040300d500000e001d019942d03c25145041203201000103650050002010507030f40c1c14524107d59100040c00306c0310040b60b00665880e40c01c0040d900e4528150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 493154361 1250 493153111 493153123
    0xa0e0402030f0a05131b05010206160e0d0f1505060910060e12010e0d0f020114070f03110c03160c1409040308150a140f1e09061f020607110c01052514 66
    0x51fa015009010000e413404005440b07040b1010703001c0d150400d510785850b051001441c04620200c0da040c5001c04010007190555403081d4499405180119451410005000ca41d120103031a1402c0c200010308103000c4180c00030040f03c0703040c000340c07210850844269a02c6015205080042c10307540105c10b141e80145601008440480c02030781c0003440018500001110f100f003003152840f000030701a9204100d00c0b8881d0300590701c100c41d00c1b0380280c101a61040030741c1c10b69002585030000e008040400c07e040140c5103d002d8000c12500d42c5030320019404c1d034017045480c20024001000c106004002a162039907100044403058806011282c0c81c0d80c03129288061060b043c4807041c842c2a04807010106840c20070800049150742030807072815802e585c0d0034481042009845c803503000e0141d5460800c0411200f0348001c82e40e9081c2e00400d4913081144001e82580310002d400603c640044a0024240e40c0120031165074409258941c0c0c00e90002d131701c1300c41c204032496000820b0300d890282460703c254400928 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 493155611 1250 493154361 493154369
    0xe030d02180424050a0b09040509010e010c0c2d080a0c060614040e16060e03010603120c23150402010e10020105070e0607170723030a0e0402030f0a05131b 68
    0x30030f0900c5450f1001c0020301d090520844170741500820546040d41010780000e5003000c1d1200c0041002e41c1b00c1c99040e82501e2141d00c560001894811040061140001c0300c0000c0d4110f41610a982440f035620801c41a07614260190162500140511001e4855031030b4410454000c04108116a01d0796044203100108080241c0304904280345055449004502800d40c0196040400102450040243c6001860701c10041c1d040d543c3d40e100001240d008072080d03010826694440c01079002514003080010000310360304414001052650304500c01c0040c1c1c0102429406e14040c0d030070f640b288012522002c14507070454026184080c3c2c00d14a94054101310f005101584401c5600074265081c0710301801000b1002d0510704082203640c1503403c40380000c1071454080c0c006001509841103405800100461200c80150720000740b11310443d034010381e10706807004211825890b5041045481c1c451810240440218558800110b080300400060070320b4100d6101022500d09001652840305081c11842 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 493156861 1250 493155611 493155671
    0xc090303031b0807210e012a0504060503060d0812060906030a02030a0b09010204210506060d0201080a110c0f0114011d0708100302041b020706030e030d021804 70
    0x1030040791030302d440b0807404050a030f5a0300e020f650f6500e804482640203005850a020141c101101c81a4600d018111502004030f0020407002060a01d10542e0482e0002c1c810400c8030010243c260341317500c02c1c112800c6030320500d03100d5105d44400380020841142e9400c0180080c0c4001040103481c1c04008000b845810201c59668181e503500c000d00d5150484180003d61540041d8000c1d80002c0700080ca0325000100d001c0014100342d1070b101404060102d1a070400c844419000c0a4000c0180c2000310940c4890305869001d4014415030002e4800c910243c191056182c8454401240c8004039042e14000428802214840c0c820003103224000d0000860484002c6c0445002041d1003c01c02d0012092412012412000d5662100704403403641020709000d4241001c011b0000140c2e541d805100f40a18864403801c203481003808011746008456071106085c142000001075a03a2004010740781c4112140f00050b80c0d950310701e01004055507900d4100c0d40d01620b040305111004c05089007059003107072054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 493158111 1250 493156861 493156871
    0x91b13061805180d03050a06080d021501060e0607020f01030e0105010f1404020702150c0c0a0609061d031c0513090207030801120c03120221090406061701050f060408010c09030303 79
    0x981503d0381641480a066568801e555400e442840b9900803540401c990400003502504da0b840c0c0c50070003098804010040c0e0001d600c64005511410348075004003140d0405981c000002000300d9890701600c18043d00c80c69a86101c50f809074083c0d0400040e060042000304095a154034600c92801d245000c0c54260342c88903880e001e81802c1c203100312100550000c041590300903803e00a5003596101c89112000c03402454030700d040544401d18114007074407298075882d400504100000300715450606070050814500c40b011041518041030420030f14080e1103c807924282619000d03926071080701085000210080d200144d5140c40ea8060007516201e42d0390103140e030741c1e5940880e2080700c2e601006044200300036410070000e001003045405410580c01503481c0c05016042c4c0742c0c44031112500c80c1070341980016500585241034440c5001605030360520403126504c0d0905001003507070500940c0e00503600c00c05444201e07505c5405840003020004002d0210304e070052001051041c492204501007030900c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 493159361 1250 493158111 493158121
    0x33801030905030d050402060d2d09030f030515030a0804030512070314031009090606050901050a0b030412021e03041d04020607061a0607030e1008091b13061805 71
    0x9010745000140c00000a40c10b010350004244c004090141c8120b074400410010005959440d0090900640008a0311600701d034561444a00010340a4072454046180110b0100040d030810401040c428807407400082507a900e10311082c2c0d0140e43c0070007641c544500d0304601e081018901c0180182c2e481001071f20711161146480300000e00407181c1c0140410b0401c0300c5003004100c10b038080c55021100c00d02441c0c03166510a142402c440c8943e0043d9100c517280c6609000d00e0802d0b400d00f900600c4251801c0e03a807540303003101890b050f0001410040514021111140c60b1038420021500068801180c0e1140000d44d1141c0c156654018842d124680a130641d0422491124046a900c1540c000c0d02103460038980341d40c2c0b140140300328118800c50040c02552072000f034031a0000790040e184203031901030380028560b040081c071001c1c444640c400c0000c42000c1121070b41010600e103841d124a10444240f440744940043d0b8001140100b01701740c14900480041c02444e0341c4030541c82d244190f48108615212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 493160611 1250 493159361 493159367
    0x6090708010c0f0507110409060902030129060c28060b011b0b060109030c080304030308160203160c03080d0218010e060301050f040f02030c031609050f0d03033801 72
    0x840c1e0070021a10f494542034141d0b000e8002130502e0b0703102d04003500070f01501c0c500240072a04415025030325107035910031074021801d092107410301580080c50041e0b00013892110014940005910f1980220710100320100800b808015104403100c401503c0030090030242c0e0811059102c1c540107540c03a90030104410340a50040c0031405e05610400c0030b80220071000c0c1c03249010064050304c0f4504012a00b13200001003a1200d900c400545a817202a6075039510b182001841c0d038034046d150086100940c185203914540010807200c21160400166000c0b002d43e00744030f170b0500980d81c0041c0151400240c241c903550b20760741c020036035145540c545407001c3c0310b00d400444403081004901900414100010300651410b401e1242d1042401440440c41c0720f140b900e020242c0c3c0098480900c03041011080c494080c020300040d00e0400d105140c400c00d62498400056014240c00b04114015107a0104403420300d0b100c3d8100c0c4500030781506c1818100311004850002c0085268165948a280600750030001d600c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 493161861 1250 493160611 493160621
    0x12070f02160e0a1a030601140f221512050c09150d060b0310020f07031403090c041a0315010602060106091a030702030702031c030b09010b0307180909050609070801 72
    0x600080410495071012050390082004e110307002c555806400c41d060040d602041818040c00ca40c00f155458008411f09000d9141c01d404c050501c2a13120080326000682904a1131611540003080464480005070300c1a190080c40d030000c0052110942e42c1400780311000904c010211401c1d01d8450310747d5505c41c49d42c1030060114071700c19030258402d90f40e000422400e81109201340b0b0000d041d64610910880c02d0801c076808001c200649000c0130454000341034120408604071001f503201d5500c0d600d044a10262514001d1284a100c4d582d10b203800d001c4110b17003034030a12a1407406030480c0c035030004007020311036000400d00c503200c014070076400042411803080c40b500003283c0e42444070945051500d20702211a4000800f02d07001c5210a014041c01b42c0c3d01040041500380550741d000031880407081004058911042007d4000c0304003000421100c0c0321002202c1d480252482d02e0402858104071151007c00740764080740e00030307042040751403c0c00400320700d507801400505c0454001542e00ca2149090364 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 493163111 1250 493161861 493161869
    0xc070804080307032d0c150b030a0321020306031504080708040909050705031c0c080f040b04140102150601050d1e020901030509010902330d020a030b010905131112070f0216 76
    0xb0b146ca41040c2c0000c0103070740740d01c0e081c520125001c2001b8052202180c038200b2602c5082c0c0019850707110846034212a40794002c80403040c4034055103586001d00103c0d40d076a003000c0020703455049c00c80010301845900804d84141c2d5501c1114142e44a80d03800007074015000700c1000352903034000e07407034009400d140000348011404a0900c148035240b408030420790b80526030031000d643c0184100040c9200c007195100074400b07450300c05100307030302c440c00c0c46613851003e200a400036040d0f5000305140c40c0b84003480e140c80380e031040f400d2034181d5450b08180c01600142c8503030303c1d1400c156010301512140c1c041d950340103085211002c0e81d0030420ba60b145080142070b2154403001070b4112610280900110140c54500d218580780c600032140d210b144405200814ce100f03138440b1500c82e601044907400268035014a8840b50070920740151800d05200c0020079041030400e004a05d980c0d2107240700701004508099904251103c030b00000c40c0e19003141d029242c0b85079410704000601600000c2d14881000c0b2131444199 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 493164361 1250 493163111 493163117
    0x5030c0d11040b0607020301092109030302120307051b0f01111801050c12040f03030f02012c01060305010e070f1e03151d0a050709020c060c070804080307032d 70
    0x1d4541800300034040d424000e038009000b0426000540c82c00d010315041c440c0315180074981b010400b00c81e000340c44481c1c210b1074200310300000c1c2040869400940c08921800f9082d40c0b9a882d103908c08240c44a100c0c0204040060400108003800c1c808042442d110080141c4000c2c014508600e0003d1071a210b2004000060044840701240a52250303018040b11390103481107450081c000c08a49030540c01c10761005491802042090041548c0042520420302190000f840f0714204840f4100c2411102c2d042d50107030085a803180031038482c094004200840e0880000c02200f07800704091922020a0700440c100541d00000000c1d4105005041c40070009060b0301c3d0803140da04507654464200f46800e102c1410307a40302c43c4071b03009240103a07410400c062038500080c090345400b4540541040c02030f6010100710380c411300803000c1268012410766413080291083c40da85d4040344c5040d09480c080d60700440564403020a010003055001600f0440c4e104011080302e01c1c2d20206e040d0510f00e205003031814400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 493165467 1106 493164361 493164383
    0x9070e10081e0304270c080906040b0613020c01150f0b0406030c0525020312130e060a0e010e1e0601050706020705010f020a030209120a0f0818041505030c0d 69
    0x8a10040c7c2003a603002d00d403c40e6490303240e0900810180c558421000041c0705562401074120210515000441d140c2024002d014000d0617541070301100c900d6004408244c401c25480e086c81203401510101d442c250600700308901030105500198140403050007603168503080741c03002c107960070481544411510fa8500415291562414882c2d990303c4040000e0328241003160b404c5019030343c0c4494a1503498803100701040540702c1c00c0d48138207c0e4040090010460441511016000d01300c41d1010b029070000007a44046000000d850351400304404008800000d441600038184090150b4000584001e2810112080ea8030558006000a0340020801c060785801072100103101e16500003802900d00b2980c03256805100c804004d08410000b1910301c010381c08a800c56041c03800090002e002c0091050444595140c03540541c900c00e0192480c0342013035080205408841c10313040001e12038 = true := by decide +kernel

theorem cover : BRFrame.Cov 492985611 493165467 := by
  have h0 := BRFrame.cov_init 492985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492985611 ≤ n) (h2 : n < 493165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
