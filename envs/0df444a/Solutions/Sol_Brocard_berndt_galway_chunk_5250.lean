-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:14:50.414868+00:00
-- url     : https://prove2.me/submissions/65c3a6c8-58aa-4bba-8c5c-b641996a9007

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944064748 ≤ n < 944244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944065998 1250 944064748 944064833
    0x15110717130515070b070c0503031503030c0109030203090f060f03070e0f09090a05060c04121e05030f03011806030c031401060b1b060f07020c01050f1315030c0903 72
    0x140d00003a460303d2140d030351002c20080c14020380600300b40042907a031900e003511041d81510005140b60410000921024003410b240581d40d40b0240490341424643d401c000d0842c0e050000940250b4004102c003805440e011105100101058079514200040c220b10002e0703501000d05003409000c1c900d004001c0359180d0805086003824001c0007102d6500740f012190762100350b201816601d6018443c00640c01da00034038116412105d0b6840c0c030502020f8162900100d0f000c4648000d0783e03810007070444001250301000078041200305031007101d940303515080c0a4040080d030307030083c14036860420348104046a88000301000301c0b500b10301d28181102c60020414014a00c9e81c02030849940301080500c940904081441001010a0122921038031500c0c04008050021034410340140d000089070b1a495110b90094091044c201c003046040001d20f000d0203155040e1174100105400041c20f51035003169140c054206d0146a6042c44154a421a00c4015802d031001c00000b03134244011080104400b00012080c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944067248 1250 944065998 944066009
    0xb0301150e101d090606030a020d090506010305071d010e010902030403210617010e0303040f020d1e0210050c07060e030304090501180509071203080a181511071713 72
    0x800c0502e0540d00207081c4400e44150149030008128449400e828031040042c05605d0003011a8110b070f58560324140a540300e00b0204848503142c100c5100000d070108681070185100c0ca02414000341042c180c0b506000204100030221a000f00c0100100040c1102c09030540d51440c1e070169403959141410b54000901d0301c01c109900324484802c2c02034028036800744058070345054181441e00f803010402403d886181340c1494040d001013022a000400c480c00b41d9404a102a102400c40c2c00076864400d9130900001050707141c1440030940c0c030114035040d560740c506108641045810203504606445c0d650460b40102c00901003041800b1a855031b04105440080c024001c0501c920740e1501550410503008400b0100c075035040c000800c45034040410702c4005c2d110a201c94024081c80c035282140c0c10b80000e40075002c40c1d50750343c40b02e80090251012142c011030103002e40c0040c841d80b11450008948070012440120801440780d074001a000d00500c00d02c080000c00c20075222544084000035400569220 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944068498 1250 944067248 944067259
    0xf011221032c280203070909030f03020a0c0213110c030408010c0c050607030f0b0d0b0402091b07020409050102040506300609061309060e0f06100b0301150e 69
    0x380a03801e40c10b412241c6000d2071442e60303025a0a00101c01240604601d450580d0b64104108074009030991012401000c080d940f8003100e81c0146070042400d00321982c0040b000152210f0301c420a1540001d6685282c1195103000c52805429250040c5070302071180002b03100e5500360801c840b03104001c1e048603008005d0b080d42e590b5a40001d050309a0703254010301c2800829401c0400512819001d40366282034181c000014180301c1d920100118014142011202c10050b600c00300c00a05032100010801201c1c850403c0130114100382c0104040000000c0c0040e5480c6811000c00f03c07526501c100307482000b036041d40c002ca404c0d6403514190b0f019004580049800001c0880c800c8000e00400c0c410b142e10086c0032034180400041c5140400e21140c089900c140c00164410205070241481081c0300082c00703009000280010307040d0394040540301d0320131a108440e4400c180342c0c0d408000c14004113801a503450041d00100b480c0002c082781c2d6010500c10420003148000302090001e010305a15080f1200003400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944069748 1250 944068498 944068553
    0x6030a140a020102100c0818010e030d02030f0a0614060f0705010e030304021008010806130f020a0605030118020702090403030b030a0c0e070801050102060601171b04030602120c030f0112 82
    0x80c2039550402100140c2c014031501400b040407086922542c1003d074255a0b4648240d914109201d080e42a50402c4910f01d643e117952081c4034840c10310240c0b04030314451402581e02d0610038400b030322012000d4420500103141038800c200384032480c1c04910000006440090b2070303240e01e5128052902820501900650070980101440304010000310300c42e500c211003844100401c4001290f03050024028503505030700c0080450340d850f00000c88060741c68841e04009110030300d19404100b94044a074080404150b020006000c008000c490050300c801e0036900450401034950002414800c01402c054241656046c0d01c12940c0c405025038810365820046502c545950342603c08d40b6110111014000500746400108036588040b550b00d0080c9016591813035601540004280701d01c0c005800040703a140c1d4115540e05032080900a00f0045005800058a4100060f140006407000401c064044002002009400c0c401107101c241510101000174061600920300064800d41b840c040281008010301c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944070998 1250 944069748 944069783
    0xb12011407032d05043c0804081504020a081b04050603011d0a0b0f011d1015030b1005031e070e090a0f0e030a050a030e010209040e06040512040e040b06030a 69
    0x42040c0c5c0694495502203c00c004102003068a2820700040485d030130035402118900c0500c03948116005078012100607207426030b240c03038581c944030004081e21407100203c2d042000f586030400e03002004106c40d60181085824a62130100301103080720007507120f00c1c3d81c0d1000c607090b5102540f000c101c6902c072000c5400c00400f54a0711540d2003904003c01c50381da079400e80000718070f68440c01c15581290400d90980b800340c80d803100c12401503603000309500b9694001c40e00004803d81003003074403000141c044d10700080184c014002c0c00340380c44c042c04c2640c044c01010002d11440c1c20039401c174140440d20100c0c0e00e90703031a01c4418003100d1000d081003c00341d0085030b00c03040c0003009078903600040544c030b445501080b0000ca1010046e4072800f9640d11a000300d0810310400700c0f003a001e0307001001c1c5600e010b00014034098104c80054221803c0c80c0c240303603559000108100401c08204905207202c0d481c403080604207032422841b020160f8004200034044c01210000c1821600e0800c200c0090703550013080d0054600d03000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944072248 1250 944070998 944071001
    0x5040e0304180b2d041a03160b04060c05190b090d0903020f060d060305070b1903050c0a030e1911010f111504170301090b12011407032d 60
    0xb409486000c04581d140341078075016501c0389011000001e009008a800e10b4500038002d00700d0b1120050a2414021025220340e90340d1040c0560140e048801c80d552000030b078145407501e440c581c1118003a0100180c148010780420f01544d040701c510f450854072041c00d6290035418a50507542c480c0d02424204080010400b10040052140c8810000c841013081030039402c866040c400d11000e908030503c22809212428000006d200009481001040e2256071703079180c2d41790412a0344095415500450b80c40064000524001c07202241d615080c0a00d04152842041d644104511b00c424941d03180740001e481c1d001031180c0e6900925041c04101801e805084c003514001049080c00c1c005442c414104c02403d000e03009099035481450014074040160000790304190101900c02e1f11202c0c01c2100a0440301e143c80f000350f0117083d1130400800c2c102020742c1800244140812210074990500300495401c0082c84070381540130140d480c01081c58000d4004440780402801400580204034600380070041005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944073498 1250 944072248 944072257
    0x90f060a0204090c1805040b03160e040212120d05150d050c03061f030615030b04030f030b0a080d032d27050607030c14030702010e0f06070203040e040c05040e03 71
    0xc03182131084500d18001107444900e44009481101400001400981841d501c00e202400c2e001d81100d00030034221b190040c01940320f138003003125650701c50100011030078411141c9603443c80c600014080001c0c1044211520f0051426a10380a82d070382d00020310a194040c56a62951005411300c06000d100d03003441d079200c2c0c0d40c80000600a100748808918903d44046240701c40c954049038071407500d801d6680c0c4102800f01e944141046440e000380110105113144c1041d40124420b031240c82e40c801c03400c80040c0c2580d19402e001d5103c3d2880e0701c4100b2008038041040d4008891a26001642c91104100002010900300d08140012045488004070006590200500007880c0324003a820450300d1440c820f490150503030003003868000d8404640303601d0094020402c00842070030070030541c20a555042941e50000c494501c0140e454980c504490300d01400007082e68820440502524540302e030b4003a41e00c0c45a4411141004d50b1000020240180342d908007000d820018424014540340301c0065960b0b030132 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944074748 1250 944073498 944073509
    0xc03100906080d1713060e010f020a11070801090f110307080316050f0102070503041811030a140f060901121103070305010621030e040504060b03010f0c0332090f060a0204 75
    0x1020801e004e2180e40030350b281c3d1003403480c80704486001c811130b5110000b0f0b00d20044070b103c0c03035900c0f946070803403001c00750010f070040318100c3e03070382d25002901d03000024030305120f950107880c4a9141401c280b000c030365000b902180d100e40040c540200c0020440103e880c00070b0b00c0c0c0c80800756000c00b14842c00d08803a0045a8202076014004983d24010001c4141d8201d1180501c020520380c8100710401c03030304035151541d40000f400c55000250350141e07002800342c1d5034811a001030b1040c0e0b8920321807000d21004514150031030a903d031700034102e2405502041890300103006410420b0704484001c130800c14400310415001c4e10141c02e0703d6403560341c4d01d0101e0180c00640962038032400b03420300500c104109070283c081c400d82c16650b00c4c0c0808501e101071000030080908140c1e440c40d10f0f0261010b0301e407030074002c50b4682c02c0d000600044141c40d048005003150554070101c600c131003c10741c2e001540803842004598800d0000720501d220303115a9141850036036400e04001040c042c2c4010004000c1c8a030380900304950 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944075998 1250 944074748 944074757
    0x120e1609020307090f050901060804140703080904051509150406080307210503040305070b060a0b160b010f05061e13081b0a2603130803031506120c03100906080d 71
    0x2925107100350303203509540c05034a410000c1307d0010400c643c03184004580090080c06842c50b042c2489101a003480529001968660300000701e88405091034800c8640c0418079807114120340301c2000024074440030160070140c1c800380076202c0510a07035459110100800541c03041f80c2d514041c51070615039034820042000040241030040da0601b40c003030310459110726410ba03100e6141c00c42903900c3c20641d0a010b01506d800c00300768080820701e80c4001e001400341a8240c0c50024055a0702e00d40010f800300140c000b000100f0380c00204000c161643d40980c0c0200449592850080b0304d00e0030040a00d005200c40e001d0308400d46940064414004908503903040c1f01d910354850b0f0040440c040c031408031250310032010340c5080d04400015034103010103007010300d4880c0d209492608c40001c4184903001d0068000e00815003000040c040d501c070003811140070b43c07101520810b007441480c1c05014294a00184004408200000001c0b41d91300e605c58928054580c500040040c42d40380c982c0107542d504100103030f00c04103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944077248 1250 944075998 944076017
    0x10f0614040f06081e070515030f090319080628091404020d0320100b0109150207050d0809040f1b0c0b070c020a151e050a120e1609020307 61
    0xb0400e600551081e60f4200b0300410700c10609020060b83c02e14082c0400d905800381c4030002c0b400d65603001d0135004528107160034580b28104100483c00c1c8010291a65841d46d0082000f0310b24480103108042c048006030801c07a00e0761341c4d510041082090004d82030700480c0d2141c981d030308540300762081c61826030754480702c100240200d0300c52244807448103440c042e42c0040709140303080c002840352200070500715100300184440ea104119191514407692023280138182c4481607003415503444a800f5005012600240740b0304080034201a441c4c0516014450003800c20310005414040580200c0d0b1084001810401288051514400007004010080d041c0c070308c142500b040030188200c01400290350004149406903c455000383e50b40c3c2011081240c116041c00310014802c0c1e0403001400c1804c1c843d0302d07038400b0101c010400201905015a143c0c007400f17021b1200040159004500042d5011301c4200081d541e02011b004500c3c1c0310742485036880000070824041b5a52010380c024601038030305c1c1d0f01c490010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944078498 1250 944077248 944077271
    0x9030314040308120c070f0501060518010b220f1d0c07051c0e0402031e0c0c19020109030212010c09050a05030604060c170f040203060a020c0c1002010f061404 70
    0x14070451002a14020b002e011421962040081107034000c3c00301d020071460310216540d21800c205450205890b240d43d2050100100d003444184031520002c803a07021140e40d07040410041c40740c0500c2c010b84414106680d80141c00d4070f10405090044c000d40070100500316520b0107060460141900a140f01c0c04541c404107210385001b41c16145400c0d4004003500c20402e200142810429072900c19008009656103c0b841d80d0700c0c0d600c000c4ac040e503c100d01d00c3e40340b00134081c040030b21584042d1511443e45c404020120a103000030a42e1909520b0320030941040340c1c22030004132003480c1540c001039800600c8814007901c482c1d0540c001c0075400300b1a2101c0d8151503480040150b180c0052250700c1e010b40250b4002000182290701c0301100c1c80280c20028059041d0780e404600020782110000007100c264802c0c0401d5207020040c50f075000c440c1e820103501d400910b410f00c40d19a0803c91403d0702801038402e00211242c000e400c51011501015410442150b0720f402c010007124501d02d05900562924500052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944079748 1250 944078498 944078537
    0x150f08011b0e22020d1a03070509070c11030a02040f14010510090612020d09081c0516110a0819110102032802091f17060306160201060e0106090303 65
    0x1001000c0f83c805118815840b0b60442041c00700c4661640c1c2040ba2262208171032080e200104c1510f4000c81803482c01c442031614044c066007103203100e4464a020400350b26801041692080e03480000903d800700d4580200385400a0400025070140c04d04412082c00d00c0076500681d5800c801124100d0281d07038502c01d0040d00d03c19400c40400040b0700035424071000b07010703600488000e10034441c018134100045030901d040b40c0311090100d60716840010b20000c10008244c41c00c2005203000410481c0d42000c0190250800022180c3d40c14003147c0ca100340e0500e102030200c4ea070400d4002100682d00d47c160741c8a80021f01b03450040324041031009450004244051003520f12039060356000824149145611002c40d00d410b4021010903602040f0f0008542c0718108000c040b2100840e5050110300600300c013600f603010307001c1050088030607201003224a41d00020107030f4000e06501e5407002e000c0907111049014014a40011b16881141000025496032103580c000c1101d000f80d13241d54400b1032600e003c24 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944080998 1250 944079748 944079767
    0xf0f13080c1005061e131509021207120e0a060504051009050106051504290c0a0803010e011e030303020d0e0f0a0201090e0c09010311070b0f040203010c050a12150f08011b 75
    0x2500000304e02d52126200000e50712400b501c1c05428108111136a4401c130323035020f82e4040c0800c00041c210030418040800d0b0800c3c494901c22909007401c0c09000a032804031035480d03214201c06001540c648010030180305040c00181c03040d0f48145c3c800d000e81038941c10301601a01071482120f000310422400451201d0a160035034040d0703a01b103411085000c1100c02c0c000d0480384000f0200103c1c1c0f504100c00007600e1020095045100e00c65610981c6a40c9031007441c1441c00030580c001c0c0300340e580c8180b40304d90304202c10b81036805480c2d041c200142ca40d194000f0306d8006000d940c140340914807a000c1001c840702c0c0006141703058a8800d0f6507407603102e40c03184004030001400369944011a001804540250740c02a00100c0c08440058001800d04c40240c81d25500d800f02618914030340c0c50400140310642c00c0030f020b80c02902c0f0007401c00e9840c10445c90401840c03a50089054022140d40c1d5603c40e10a1000400120060640c00d007180107643e00c40502e10f00030084485003d6800e56407040001c040b50180a402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944082248 1250 944080998 944081059
    0x10c020102070915050a240507050d03090303060b120f060a1505090112020406050c01060803040501051803190812060108060603070f121509050f0f13080c100506 71
    0x500305035140005201c00b81849000d40c800c021310b81d50011869448240720300000303007800e22480d1000c3c810101e0074104c4540c82c60003041004410820300001c10700000d00b00350002030b24035000607007500da810102c004118542201400510001e04e41f0b1043d1300840d0f0f694040c400c4041003022980700c200401051000d0303841201c511080e40d2562121890242c0c0150131200d9040c1030083c0d100004070446000c90340241c02c0840461404601c1400099013446200d0180603064000d600c0d103800c0c0f00028049000b5010010704100c908404450603880600034101ca4860003284201489050f00d000036054201d043c01c00ca001c03008500146980d841907100f180030380030150016107191258042114500200c09000061218008845d04602c1d264800c02c40b5a034243c845100c6244d040018074000d6030805070519880044039424031070303414006280503810003205200c002e503d1a4614260080d8050280d0140d480e0090425030200000300c2c1e044103100e00c100f140d0903258240c841c00c88030303960035000899 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944083498 1250 944082248 944082253
    0x17071b051212220b19092a06091715010803030105090a05060d061d070303050904140906010b0702031c2109170904060b1614210708040506070f11010c020102 69
    0x4000109464541954000c0303601703801422603032803010100c4192000e5a404980b2074400d503960b112002c44145da071400360b803100100c910200d07180ca100205903101d1405024500909040d1660361824104003a0884005032100707803c6030341c1d46021281e100d40003403082e64010034549001a51020f880c0c8211486000c00401b411100c3c07001d0f858602c004e044c241207681342341140181d0080c1d846400c000c018001e51003a9110750303440d04c1c8401400103440c0001d08910710044001c041c040040000b2540174152511904990f88400c02d81c00020710341043c0c4030414034484006031690004a60020744100d0585141103001c150440318400303041105c8003140094018050094004200d50890b00100b8010000a001144003506ea51082100d940b20725400c8156511190280080040d540545284106100003514400204502c0d0b0300080e051004d20216003000050750700100042d043c00d88003d00400780140340c840041e49080d950142d01d0201c01d1b2210481e20f021414150721a000d81c0b40440e506901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944084748 1250 944083498 944083561
    0x31e1221060a0302030a050607020111120606070515010e070f0804021c0615060c061a090414120403120305100b04050d02061b0a1217071b051212 64
    0x414010300300d0182205501460203000000941d80402c910062280104064402414108006405c4074a5000e842807100002c0c000311301d254203c0903000354000020380302d640c0e031111140340003404c01d2040318440c003003a0481c000100c1ca515130b140c043d0344540d1064803052640404035030240c0311118101c90003507100d11201e2800480b5280c400001c56442d220b482d000c00d800a617000f104094210a402c01c1002851056104c0280306640c0103000c0781c02115001c1506802c0704501140c65030301c0c002d00161864416a02e045a90740007008100c503840e0030000421340342d5449240510b128181d41461600180c140070124000d640100401c008a400c51100c5501d098509003d100e80215410000da900500070b004000000c1042c12a100211301c0c071801809040303e01d46003a0009030101144c0c01c0c104042d0a2180c0e034a11310880c1080d8000c50281002c910701c2c0041022455105416a40100180913462a40821440b040050f0034a140c1030120b03c2659901e00040910120160440607030802c3c6118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944085998 1250 944084748 944084797
    0x1815061e020114060d032a1b0501020312040525090c02010b130f09051912050406050319091403030a0608031303060915021c0507020a0b070e0d02031e12 67
    0x7a11030170340354807d0401102c420405070071001c002d008079640d01c1074080500500000c2240080c0150300032290403003003071031031801c00340001e43e240a155070079100000c0711000708080c018200154a68040540a1141c0700216904520590300c542d1050305100742c10305011002c803500600482c0610304c4040c00d151200c020146402000d008007582c9698419500c03840003011542c24480d47c1480c08240003100e003001c0052409401c03407036000c01da40042020a20044c01041d9110080304c1e00300c6103049440048800ca990460002e0070700e2600180b424175210340754051004040003035403181b0b0345000100040703542d8990281e140c1c4620b1500ca200241c1c1e20105000140e180e0303114800c1076000d041000826402440048200da101207400e1b40c0103100e85c03840c41c50000c00d40c05a2540249148040c001400030f603a1042c14004000e00b04c08c0500c0865080050305031658801507003c5500282203924400802c0d4022503e865500e02103007060207070035170200f44030348500101e42c1001c650b41039041c40a407456 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944087248 1250 944085998 944086009
    0x3060b010c052d01050a1a090c07080d1103090a02130605030303010302090a060e070201020c06060f010c0f03051e09030105130b01060f02070f090f1a0a1815061e02011406 75
    0x788070f07001e60076201a007254040d40e013441410f02c10b01c43c0712000902c0d107074145145250049891a0a0b08c618290406c006400f0f6690f01640e01e4640d04ca402a511401d1428400002d041c4000502c1d841100c04000c010305602e0000d40c0c1110303503000703603050880c940e61840b080e02916454000c80c1c0e01680700700010030042c10526611b66104442500015005031074156600701e00405441000061f900418440314821050140980000040b41e4801d400314101e00087c1c5940369840016080e50340103403018062502650884161844040304100100a00f019024094100f81c000501030341c0303004005510607a502c0e9114442030342000ca0007003207030f182180888000d001141c8000c01c60045140001d0703100c02160030840a028460300121741200c0b2090074004407208403070f030040440b4022504640581325010b8a00503651511050031402c8803039140400602007a890040702607251b06000580c3c294080b002e501d06010400103101410740b040004c07800d843d81c810480c07101d608041c012500b146440e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944088498 1250 944087248 944087293
    0xe0c01110c120d030f022b0b060d0f0e0609060606160b011d06010306030804091a0d080a09141f0c0f050303100902120604021e04060903060b010c05 65
    0x1000116600c950151002c650300010094084410390b000d032500000d030039018003032a030030500050b03811802d0442400c1800340302c0d09480066004040080c2007084441c040e07401c4104a02800350016070b031075007580d000070700800b48180707860078032441c000c4030040304180854801c1c0245030f00b5004080701e403192420441d4503031203030801c86203440361120640c000172540c0005038020220403089040c0c040e4000307002e04020b03000a0a481c1058075054081c000030b00c1e5030094400307442d00d141c000100300c0901038044500003580302002f540f0000c1000c0e08001c004c0444024622080103a03902d001c030903076903d030200d50328441c1452140c0c004404020224460241c030a90420003220f481c0c00c060f42101501da004548819102c10ba0711500300100704010009403005410040008400440c41d1044024002c2110080904035611440e00052008107520100001501d00c1d00b80030701040d46c884c0c1c1c07030700043c10000040c44111481410035401c0101076020721011500300340c104000d0507100042c40301c107510b001715 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944089748 1250 944088498 944088527
    0x2030d1b06050103060507091d0c0a031e090210050a052512020c0f0d0203120d0b06120f01060c021c170a090f1a04140a0302130207030306090e0c01 65
    0x101440c014010648a0140b40c0c02503008070000103050502c3c0d1001001c0745016001808070800503003900345007000d604000e5501c004000c81280d1204000c1900f01c4c0507003a51900750243e05840d910140f40e803c4a80d108840d8244200e60010f258001d000045c0d8042c040d000e02c1001142080c84072a50001543d1401407240326100c200409800781d680d038104d80d90482007200030045c0d02c59190f00c0b0341d509081c4030241d20500d080b140d01d0381c0c520250b0300017075650000866a440000002c144840c1d19203240d00418070701d41004003031130348400056025040304007049031885462030707100c00001503a0f40940400e50a054028001004803440b60920004020420301c6c111905144010910386071001f16001c0c000000440e914103410390314040094185030b502da08014110001440c00660107041e00c001c903400c0701d1030030071102d002d1060381c0e00281a000c0e560340081e400540e8882203440d541119130040c11168440d4404116050715525008101c5408181e044031030340c4149040d80300d640c020100b0140104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944090998 1250 944089748 944089787
    0x1080a0e030412060e0706031e090c0e18010b040c0e011d040608070501080a11040302010f1704060608060907141513030b0910021303020d1b18060b040302030d 70
    0x1e54503851009850003100c0d082c0d8046030f648407517110409003171040d00024203840c0340c14040d10a08500540c1300a00c14030185605607642c03141e01c82002590310f0f00100401d06801400224509038402400180710709040c180954644034804e112482d01c1e01c51504100300710381c3c50b00d020074031074030064545200d003e10701e06104030041d084141ea1780e03ca0007135a000d04004405861403078070f014005442004040c14680a450821084d940c1300070246013542d0850f90246007040014114000a40b4440c4511061140401c0c080d0100014460550030031000c0780c054400302e4915946044420f034031040c140c02000c50416a640070000d041c41c0040030a1800071250460300e143c00c0501039110555429507204507107685550040005c2c0400a100c0440c040d030700384100b54500340104004440004450100920825044013100244250250f501130400340f00e8440f042556114241d12001c1c0e40352504d9500c00d18109030000c074071110364006403801c80758040c0c010524031110980503507014003010800714980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944092248 1250 944090998 944091007
    0x903092412140a0b0a0905130602090d080f040f060f020616020c1e010905060f030106080703090506070903020f0d030203040e0406022502040b0f100f030b0414100806010501080a0e03 80
    0x9180d007102c4580180e80e0308200051120351401170140313243c001c2e030010850364505010007500d0483d02c486510200da10050040e511158100090041c03d08540c000d442c82c4004200601101d5085001340140d840640440100380d81e40d030801c0b10303118003010340c5000503044400454040704445855030003ca023940150790044005001083d80d14420a01000350034004000304001960400c4080001e0607050b0b61152070300c03041c03400c40112444107101d10410480c49030000b804251003548102a05540700040d1903041c10511002407441c800d9000691091485105180003440c0201e030903160300c1d905401440c1042c1c60014404c0302064003c10031388a05400300218402c001290f1551010f84c4d000038a42c0b8441c200c0307401031004603617202d103036a03001d0443c0010016045e52460b820304403e42c0149403051050500c03000440282c440192a103030450f00b0500d20041010025216600c0341d20702495046420f42d8824013155a40800e1007a40d0200d22001c020403408821038100303501c03411440c4200d80c0360 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944093498 1250 944092248 944092271
    0x70210140a090e0a020901021902040603060e0a0201020f0c0d1b03050a052505090a23010b090909060f04081605120304060b1207120c0e0106030903092412 68
    0xc81e80040e0180c800190341d000306018049043c0341c2c00303402070700c002c1d070441c2421565000030350743d01c1b880c0c2243c2a20f01400ba0100d011540c60b0307040280a0f690250b010700c200000d41d0070903651004810012809070042d01040110280000781503070b650350004003039100480717480d11251003902015400c000940741859010011503801c00419929070310a0008000416400c0380c8038124140680c00782c10704411200c42041240d9810030703201c0e003000c800306000421b9001c0d10910301c00e41c002106011480115440002900c110f1400508080c440503220021159598008030342c603050100d502c007000800040102c0c008ca007040c40500300558407952408114105c6450344c0380341c22b0080c1c1200741040000000c1100304200e40c02000c0410000fa40d0160342d81d4440406140c0f01d5125002e0800020031604014003405102d180309002005200444a91942c503a0f100a02608400000ba0003082e41514009604e054003130150503070250010f442d111030402c8050843d81e416062640014803502e0380e050450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944094748 1250 944093498 944093537
    0x51e03030a0807080f040b0c37020c0402030f270a0b01031a04200a05041a01080c1201090f020c0f070303110d020307110a08061f05040b06070210 64
    0x25205565111800145040e040003844c00500a01721941c184100301804005511010340315000540d0840181d1101480041a1841c0084021402845141c485020407811640b01072070195000c40d420784503000b07606018841a80f000785c2c0c1c5000580010b4002034154014401c02c030300300020461036070081c101251402440c000030001c0507035091480c0c600410800140801c008501301a00c0440308040c5071a840388083c602c0e00702c018089510310303400c03d1103041c0d6035810f1800c040c0000600422660650044a080c4c0303001211045000c0b4100301c0c045024044040c098800d06100d00100d1040350b8244030740c40005d0800195500d03035640c0c00340020003820509010340a103011074040103119003442c5050040101694140c1e02c038161b009019039040703140d03020084485254201c2c1c4881860105034011481c00d1030301d540928140d00800042c841e100d80305002c0c0c0101103449605d100785d22501e030020481191b080c2c07900e072903022104002c0701d00181096081030118610701d08000c0301c400c2d40b196051a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944095998 1250 944094748 944094757
    0x703171c02030a0609091101030903230c010e07030c03120c120e150310290313050c040b0f040e0a060615120606171807060306060f1701051e0303 64
    0x410381500801005680c1000e841500300400d1004010702070300207992101007165140300a001d0404d80c0350002c4409243c0180e40384041044403400840a490104407502400c6d0000361316a504d650030800d4082010000044140c1901d400035480d010a61455803588084001d207403c81c402d000aa4402c4030225405035032003224281075490b0382c00070072140c400300200c06001800310582d0303810a2042c0085012820003240a40d100e000500105a256210a01200002c0d9038034030703508070703002081200410400500840d9544100211601e4800c120200003d40d070b00698801d81041c4413039400d0240c0c0c46c00b600181344a030010019181e081410341c49900541c1c00e02e8000e01314009440380c51030b44041e03104080040f48142d11a040003181c1c2084802070088010803c42c61614607600c002c520100001c0440882a680740011035040c5641d402c0080c0107084c051090b200455000c0e4242402035019111003040000189110403843e820300c001c01c481c5a2900c440849507411180942105450810060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944097248 1250 944095998 944096047
    0x30309062706080603060604050f16020316030f021002210402271f08060c130e10181a060d02040b040b18030d020303070f2a030807050c070317 63
    0x843ca49400750602d40781800180034039004602d0042000090302034090b1260700004109445901040d0b03006040b8074500508011015501c0002c181d8000c141d00820700f500b910010b40c09039410907000b1400c000403070080302840e040c469085240317500c1480406040e581e003c0e00c003c2150749401030001107901401c117080050034038080f144041c80044044030808201d19140401d404580600300118541c8520028007117160104d80880c05a2a1014034188e580161030b582c01c5041c41407508142c14116100181708028204080c45000640100c0a00a40041180030003045142c0c1162500b1711806034003440240d18403543c03e01003c00d800721402c006100030801d1a6880d5180c2d0b80043c9009419134031a560540300c0d50182c101303414015000300642e60701c801181010540042c20f8035055910f40c02e41e015000e44442c0d0040110300180c03035038610b008814002d40d680e80d1035603144c58003034625201f4109003419076403141e4000c1001030b41140081d1701a44100130180d040c44001a54003202c40e6060059 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944098498 1250 944097248 944097257
    0x3052d0109060f031110030b0306040506041b060c380402120a0515060f15191809020310050d050304140604050f30011410030309062706 60
    0x10000c28a07140034800151500b103103043c80840c61591811007844040700168000e01d2401c10041125000b40d100c040e10040140507581207141030300d81242c48038001c0700c040b42c002020240100e8144400c075819002d90b00540c8a010f620340a0740c4030400070000c070034101840410720b5a00411000b909000111244114640101d440e007032900c10491030008900d5502d0090f4030440e00c410104e84c0028070042040c0305528a22200d07151180030440441c0d9140d00ca0f50400c4000200441c0309403120020120083c000182c1c4002c02c10b2103404460a01c03100701c6070078030034075954014801c40450358000c6410403c2446080001d958440c085005080603050a840741e80000c281080906109400704403070900c11201c0c185450f040c540059007400002030b041c0c0c062091200e06001d0320038445001c400c070071100075540115010004c0103d0107000740000310101e80740220040b40c00400e02c00d01e01400d595054544203500c0b410200102c0344d1a150640344ca8043c9000b00008007030030603511100c40605004d45e00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944099748 1250 944098498 944098501
    0x1c0507120b0a1103130c08030f0304111008010515070506150a0b03132301090809040f110a0f1806030c0905010206100603020d0207081308010c080403020307020103052d 74
    0x18a9034075810300030507401d1030074101501030b04250010400c503540302d0031810042d8161465814000c4e0b102c80079030420011440f00150020705081c2c1140518429407103203000500f04c1e5403a00c24012012045180c0710080350325000148140d2500c01100f00440400814841c104036180c1c03105403400a0a07070703c0060078110000040002e00340480b2806c00303480300350180d600d181001c0c4203440e04181540f00c0601140c004151854407121840038860801c451400240039106241c2800f00f001e500c0075012910030307481c0089540380d21390140143c1c0bc0e902c011420035814030180c00d40556500102d6070344c040821007103560189521885108100150600d590001407882d004100500340341ea49410141c150340c0400304102401c8084070562055a115140144c3c54404140b03542d000380c000d488008100d00380204460800c0360344650220111403111000707005c0c6c0d456108080c1d500321070960340600140c01c2040002e001d94080d40056420901c9800300d030000c031089150038141d030004a46c40b420038058a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 944100998 1250 944099748 944099753
    0x11120105010e0a0806010509060406090507030506100e0112150308071103010614060a0f030b040e0a0203151311060d0e03030a1505220905011d070902181c050712 71
    0xc206690902518020042404d02860955800c8144552803262a0f444c3c00111580c0712500300a0007000324480a100500b045030014003e010122400e81c00754000300000b48400f440340014510425044e124001c15920b10194200a0000600003580401c04080f00000040a140003802c005005078900f00c1c030f0302480c0d8101420340d01c459201c8a00d40c0700e248a0311195680d01001c4450789103450030712401c904030526059002d042c0c0b0710021070384246040c15a10300c4081c04150031641c140300f241901c45140703410304a52078584051b06c90007242c030600e8010b000018003a01d0310041d542070003803025003004450b071000750a541444084520ba504044203014500c046801000f4040c040e403119801d040b8181008a100c401e01c80310407104040b8841c084584c1500140c3c81500352640000c0248112040301d288200f80340058041c01e11588652540016580e1580c403e07034140d03180452604501c100440c0420020760040405000440003698030400004e10800076200280780b4100c03650384070340860 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 944102248 1250 944100998 944101007
    0x6030b010b12062715100e031c3204180e0c090c0d0e0f06010609060503010810020306011704060c020d030b2413270b010206040809041112010501 64
    0x1911450140030810300b0907440d10203148408104c0002218040041c0c2d984501e0100070303144490712550404001400e910b1030075885070701c629030380750250115221041551640c2d50034031060740410300054104000d13041c16004071503000742402c1c5050b464100540d50640071300040c0d405a4403030303010320404030101d216080d210f00070307500d190120740044c20659518001103500d40400501c03501d08030b44000f80d428108040ea60000c030380c031402041210341c900d81e0100030300e0f511343e0207000d0900441e0b08001b001a08601c105c0441781603608c624080c0190107030400c0c422029420150a0724180822582015044180c03801805c2c810303402420007003a070080e14a0042d041c210020304410030103050407514001d54640351140343c41d038070359104280c2d0b40c22810000004a8021601c180741e41c0408440c000030303000d502d620b50356529125141010905450750000800701d5540c044906d0158100e0710020b004280024060918100040c0010940e800d455544d150340b0b0340315500200701615940018443c1d560300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 944103498 1250 944102248 944102251
    0x8060402120a0308220f050c010912080405041a0628030b0f0904030311071101020105010506040e040308191104090b0a0b0f030714030a050906070206071d030106030b010b12 76
    0x20700c0608002c2945480040121000a101d4902d0303000b031380031558a0010520b000031025400046883c0ca95066107451925070000d103034010f00140c040e0101050b4104820b14144210f030707225503020710b0940303403009100141500340c0902604a020581d0b00c02c1945410380209141100d540010010b0301c010001c140c030300c140d800c84000400d45096141c540076242e10801d00301c903c504aa0114280d92035140440c054440540c500c070300c529020a03508104601b00c0045a0900313030907002841203031389071020b01c0312601603486404180d00911001c100424050404c0700d40004030203c0501e000410501c41c202580c45051040b40024000201001030b1038039441002d446010840380400340300d00d4003400f07146d1800f42030401c0300c2d02d8500201044050380251480741a07800da00c1c403019202d180011003003008050480f040c1c450743c0a01c10019a0292012403280d100c0c01c40c507100d009186003900e48441240440101301038141d0342c0d805001c404501231882241c005c00e8154417149e44d0b58062108010048030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 944104748 1250 944103498 944103529
    0x7020411030a05070320090a0924120f080a0201061703070b0a0218090a0204050a0b09030118210c080d0c020708010c02100f150b0306030c0d1205070f0c08060402 71
    0x1360940d5003501c4405091b2082c05a01c0c8451074a4651803000d002911090140e409404c102e07142001207003c603014016501e5a442840d0007103450f207a0385041c1c00f01604402540140051160714821001610440140444a0152000044040c0c41d1882100e504031030501956050f400440c254041000300444035a12040001042d8286910002d001412501078154140700d10300b1840000c1c00782c5901c3c3e06a400604000b08085411560740c003054045502c6049118082d5007043e4465000081c4103000f460910381c0306000d403070400e040441c070070140121162644200244c10003800c021880f030b40c02401d05401d1608001a0b844600e0030064600001c5a2050400d41d05010880c40410307004107501522070160b0201040e081e0039848100020b00d800c00c544212411100d4020402c11041d6020f180310765030541c01c840c8003071030840800c190f1011203003004001e0642514014600b621480c040c0428030321605800c4100b0009994040700780f111a00103c3c8180d202c80c1c100004c0d4a4880f012810b40da1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 944105998 1250 944104748 944104751
    0xe010b01110a02040c020313060c060b06071a0606090303030f060f1c1203180302250515090319050f070e01081e030c0f0c090c09091302040207020411030a050703 71
    0x20000c900305469040b40c000180c0b003140c1d9005041d07080c6000380122a01700130418660701d11151100c00142154815402c1690424a0541d55012a040000071200401c0c0c0003840e25040c210741d43d00712240904002d010a40100c401e00c80200d40780c50070030142d8001c0400c2007103052646004001d00c0b900394604c1c030a0a20401c0364140c42005030f490840342c02074180d0003034003140017002031620940281840c100203d41c3c2c0102001c016003415070204094900d8a80814680407206403c0d41c1c049030302141d0701403103501800d4600103401c01d10750303480205103418014040c1c07400d01c07840c0d8100d4a0312030020141a81c95410004486885140c2030000390080c000101180d003495040c01d5202d03545005c0d211420019840c80310a01c040c428040080e03404144256040752004030118075401c0d114110b488a0740d015411500218071260341c554140c03031900c14007606031032807580d48403c900703841400700c041070703030030513400c0084802503200ca003d416085000c800c02280d0b00c1c00e00141c45401c64900519010800d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 944107248 1250 944105998 944106017
    0x50d020705131a060a0c14070602330f0106030b01021c230a351b0403080a0804150501030b0c091813170a051c0902030d030e010b01 58
    0x10742e01c604040007880c0c5500400a082d16404100758020104203a8040e40a440428107131000c50b44040301b00845e6100b0304241703134443e441003507640e9180420701902000d60032604e482e429090606150b04040c5070001a4072110b000300c141c00d502c4410b400d6643c06403182c10840103000c401d8250040840c0031500784028900d44400b01c0203603000301e11203424182000007e19114000340c0540f40010302802400076966075402c400d940180c07146190018882003204070303c940d0342080c0d44601c000601c200d40c10845240982e94140b522040b6111103241c01b08a50060001002141a400150071000b060743c9640960b4201410200c1d110107002105000e19800c02005000064041401940059085c01a1511400010006509000d401210f120300078078100805c03104200c2e040b03e805069018182c0d54964003600501c42c030452040d04041d4001c5002000054209c0010500464170001c03a18000542c500880d80046e0505e00d40300d00050020380c4584403110380d4030302071203402c012030000d0030495240d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 944108498 1250 944107248 944107259
    0x403051c05160203210901091a070305030c04091104051e0d02060f12240a1d0a0f09030f12180803060a0e090a03021c120b1504060c050d0207 62
    0x22481441e282d0b415048440e1406021524100001c840c086482003650483d8607080c49207601c40d8201c2c1d10040e00049031010001680268420420340b10b107648001d803440c058460b2401c2d2203030f0f48003600c090000b1a0030803000540b9601381c82600030f60564246101d43d9140352a08010321059442003d65070045842d1541e144c2e96101e1503078205d01581940c0f06a00d9080e41c000d400c42d2030140407603103241c0802d101d041041500301c5103803900d020000c1c0442501410161028040344c4042c1d030044640c0c0e03000b46100d81e044a2140550f865000103540404140c05000c0c0343d0050649034400780843c0414030b40040e0303102030781d042102980d1b90340141c0400c0203004040040c0d0fa03400e110130600500f41c0c031300000100d012911210340b5900074062031000d1003030a041004100baa07800346903030190014003c8403140521016200b000036629840e41e40c5545da4005e400d403602009101b002440e40d0b0040320441403a8110341218064001070066458140d1400c409050080c200a103528000c011500002d81c18801c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944109748 1250 944108498 944108507
    0x20310060f0f05060a0f050906040e010f0b09101b06020a08070206010b0a120207140109080d0c08040b01030210030906240506030412051c02040e04140a05070b0a020c1002030403051c 80
    0x30410b46ca03142100300314000064505100b0108056000000000c01146406011600c18121405405058000c0341e80d8034500f1882c0c018500309a50040300460310350030281c8101c60081004c100072020b0f40000c0c1c920747e50344040b07030311803072000003c035030060204108260180a0700b401400c4c215446490204806001002c59040e00d80040c41c89601144e14800e110591207201420310380480204007514140c10320300003a0f04a40101d002503400d240218429600c68180c4600961b4804031030492030342507608014005c000184803a00301541c0e8140180490650700400061403521200328000d09452182c5500c0300e05c02c0d42145000308002c00c2488006400c08000c200d50040747d24006848000c000350b06641d803005a03803403062582c00410080350f016400ca0301140142d101d00808094107402c000d06c11b8481c1e06c21407000d00a42c1004030100321840181c802050514281d02c155104c2c1195040064101400404450300580c4046020f0007040b5042060514100c01403104401c40228440001e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 944110998 1250 944109748 944109757
    0x60a09031d150f1b03070213020711010c14010c080915310c0f0e01090c0206270f15180a060b010302090405040f05010f09080d0b030a020310060f0f0506 67
    0xc4801c0400116401001c0f44075050301c2011201a4402d09464a40d0319603075076907004440264403480211000ca60420035038401c4400b2107500400d070314100c055980041d56580c40040c0140d44800940403900c592803028800d01ea82c1d05450b440c0c1544c1800c002a9051030304860210354403140d1a02e8050000003c0c1413020030358419984d91061495024021060701800454800100314002c1420081050140200d60b00291451008002042d030781e1200f0640907034042180c400096002100805c0300003c1e00340101d81075250340e010305e0030411011034217a07280c6800001307503070465001071048002d484c001a0403280c0281c0ba025800c155604030755900381c0c45e120145d0001748496580e081e4864107034000d8040e5666410020001c07c05450641000c130b80c80e01840100725555440e0014aa11103121031284600e165000043c0360f041008a0040300010669808100e40c1841441441da0044e60304001070b09000009001c04258240340c0b0b0300c0103924900681003d860010351003020300035619000107a6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 944112248 1250 944110998 944111029
    0x120b1b0c100908070b010602030309010c0314060f150705070302100c1a060409060501080607020f0105010609062304080f1504021507060b09090313121109090f060a09031d 75
    0x10302c20300c5403a003a4214801c901008145450305d40c000601d80d5004405184296034440c028840710600100840c225541d0314001c070f545409060200e003083c00d007205000c04410300074009a421100481d916102508581e6080b0fa069001c2c660130302c2181001c080040084041d4109400540160340c1c9003107980e000c9442d1090781038044400a20969103681204103455000441001996100d043c0c01e51100000c45450015105486074901611414400d42c1d04940c400d43d00ca0300c0b06820941e0803141c01800c00595070018540ca0700b60641c03000e01c1d400401c003e1202c040107215030400010340da07040c69294000d100740040e500c030030003002d0b0311015418281c0500030b000d030070750307491841c81e103400240119002303141c1040c1c8003000c00c074a00c480040100b940840d94440305854541d101607030b21445000406c014505801c90040001c54101400303180d40160042c026140e0601c041c0c48603d2402400300c40113020030b6200c031140410701d03812140c0c0c40c000320a02c42520900814900c041400654140b021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 944113498 1250 944112248 944112251
    0x15090a080711060a260f1906030803011d0a0e0c06030604150b1e182106040c140306040201200c03031201062c0d0c120b1b0c10 56
    0x10703004110001c0881c4850200040805880300301000e4014900b241822010040c2485400302800040200c0402c0d481141258076003c07844d5101d40f954010031109201ea04056901e401c0040001105000554040c0c542c600c80511403040c9a540003e00340000350428844034a04501145441c07000300312801c0100c4183d58ac02e98036159400842d00401094002c041d80c640358031004242c4007000c50045c8092140d080c02410011074032035000d40d29119501014070250794013100d07240c0ca4200701020b540e000035801c8540c0d40610820304198105941110125540e9103074030002c1c0020350302c4940c0b01c1e0a0034402d8006100300d2820313500207000300b68000c1804210703c0d00958980e10051081110340d000950140c29030ba1200180140b03111a20400e0107101e001c1004000c10000058007426420000700300090910144244003080c880200240c0e43c055507908101c1101250700d2100d0511041031a03c03560580c00d051600c16140754815480504903511900704000034032084100240c2020380c0550207030f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 944114748 1250 944113498 944113507
    0x1051b0a0f090305010c08061908210715050403030c0908252c090105070c0b0709090219184704030b0106080c0307030b010c05010f0603020315090a08 66
    0x1802d4500c03801c00d41c0014042d608081202862541c00342025015042c02c6e0b41003003889074600d043c1540038504d8011640c459005203084a5200e1024414200083e0621940c51400d5060348aa4541c404009a0031340c0207038031202030104041c0d144c42101510015850714421203030602c0065902c845107925440592040511802c03458440c210070300008060f12038020714150b541021040004a030b8420080008a80c42c5c00546401d606003d04c40c42020f2542d00d564096681d95540902002d010307001608000b00396101096815040c40100f040040f01d0041a40b102c200c002c005080046030741c0d091110014405007004000c44141c811600d005035010001141100711903908211507028400002407000c404500041040003402442035030b0190307180a4450b078032580151524642642c50b0440200200001520303e4420b40c80038010000524109084441c2a110300e420344442c1c1c0310700c070042c0b9641c1707a0030421464100720409544541d490b0490840c64440e0b0565112186048081d100440005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 944115998 1250 944114748 944114777
    0x609083f070809250509160e09040c030b070c060f1b05090d060203010605030906010f0602031206210f0d030902030307030309020112020301120b060105030f011707030b010e070201051b0a 82
    0x4050408503180200810f440f11035002000703130802a1188038080d2000704040b550400c1e030b0741d85500f4104031a4540c0c400360817168043c0460740d44000c00556800400410103c0002ca014140d140a2562551410203180c11801d2513402c8583c80000d01204500d00754000290340350114004a80000c1803c000751503815003c04105c0b00da80a50700204964400400820700d1504807019500079400c000c11540300b0b03a00c910304520030032102d002c0d1002603801889000c844400c104241c5502c4600601181240d4060501c002c0c411480300820891030380080160b001c10a60800c5650104116450709101204260700480d80744e1044540280c1050344804408080d640510070201010380d007482c0071940d0f503030740e0104400034240d0703110111454a6054041540b940c483c9082c1c9000e98400d000504442c0d207008152110300c42c884a0045060080c290004003103500074421900038005d600c0b1103041c0d03180c1804000c0c21281c005110000807400c1c0c107540d01c00001806e003900d2140b5a0750410f0181d031504076 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 944117248 1250 944115998 944116003
    0x50604030f050d05191d0723030a060c08061c0807030e03030310050a0e2401020c1005030901060f061e0e0a060c051506030c0d0609083f070809 63
    0x25450f0710200b4100028084803035900000c1240c070319220300342001131420110780421000c10144202c1c4e0760b0f90140c2c0081c03115a8440101a010741101500c1740e40690002c400709007031103015842540c03c2135031503c071360004030b810100e40780e0700200072110161744146030340307000c0c400c085c41c55000352000002260348070425000d4003616660500041c100c07030301e81c0b034a18021141010203016050040a18070000503011652000c0603000d08014a211286103481d01c005d6003007807801e074030100d04520541c061080d241d00e400024030807205e4140d43c0c2d02d5591404183d035501b50f03940d82d8040c45441c1c0c400c08041200d5940a80c1d10740c0b080062524054108000007412a00d0441300720500b540a602c501d400613425410018503500940f055094031014000440c4000340c41d10700b15a00e40c0c00d80c020001c0e1201501c0d04102050800e032007404002944042e80e200c5803c6a048099840007a22011071081188070b42c00e64030002e860005c82ca003420705140c103418a41e185001030440d005022101c03010580b0070100b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 944118498 1250 944117248 944117257
    0x120f01052103040911030a1103070903022806170105270709030203030d0c1e0210090302160f0e130201050702040902130f05012c010605090d080d050a05070c050604030f05 75
    0x482414000d0690005d00c03000d0300c1d0f10a8400d82e985601d005030721100b40150a0581b0300c24507850300c4860200d8591303020f100c0003018241ca10f0340c0c4000104001c0340d80c0d141c80440d1a014198903942c00c26102c00c0000c1c0843d180e001a0400d510944d0b01a410811204060b042c49008040105080392251100e10b015100e10704c4030f42009606000c0842d80003103d000380d9000c3d42000c00d0b1540c50000d0710310588220700c40c00c81d203100000300680055803402ca2480c1c2036000122141d22900c129040300900200481c4103842580080c0403030900d03003008100066507407285a800c40340540c2250900c4215500103000c522541c07500a0045449944480a65540c504014420b14000f08140905002031102d8002014240640c520b07400f00e1070130365409070742c1c0c1402c01040c200003560040350700d90030304c0c200b95440d40101d41601d62010285a00500140001e4094402d050261002043d01c1c1010410002a02c1009004000704507141c0c00103130101310005036850b00b00f82c01d8106803185001403881102c49105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 944119748 1250 944118498 944118509
    0x60b1c0b061e07151b08190e011b021902040911101707020f0a0b1f03050105040c061707030507051b0a0b130b01090f02130b120f0105210304 62
    0x141030311400d88080c003000c01021020300c50f0326132000d0030400c45a042c0c01c5131303541c5031901d5801c0100007016a80d02e009070382064100516200d01c03078810124003610000d85900704146070003030b5103595080103040a4841d0201c0b0400c4d050000c3e0807400101002c074510041080c03406441152129056028000204a0707092401ea025002c51581030314050f014203a8501704c280c02c8050074182c0d0020b02010310100e501c8840100b00405407110f4201512041a0040040c2c01c4400060440c009045d00300d0ed6010817000541c031990020400380703420b061103551000103501c1802400700ca41c003a03140390301040c404a0350104850a001615032920802111540140d289800f40c2050301c201c4080c51041c0090a006018810081c030449640c8100208503e081c2c9603000a003a41c5000b070040c400709816410020810000d003c006041c4521040d05804681c0d10b80c1c000030581000281c0f040d03940c600030352003c0d40070041c1020301d06075500d0103010885500d46803114250b65240c5141c41c91070907c081c003c171001080e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 944120998 1250 944119748 944119777
    0xa2f01020307120507060c23041202040e0c03150109140402060421080313020a0915060c30030c0c0305190509060d05091005091506062a01060b1c0b06 66
    0x403400c1c0207080d4051044070305c101d403da14008c1840e0422060110b40a45840e186a594005041c2d802d20010f060711440102c414098003104104644041120001b41000c0040300c1071b072035140c002c880c0c085521541082c9801000a07082002689482c400c860499202c550580d0808d480c43c20b01c044c01c51200c08004051107400030504c21001e000051b0591034500844e80804d0b080d82d10b0340440c0480d1601a40048503a114050400140f802188000c2941d40141c512241a0368840be503040700302104040c0c20407140744000f68054042d85446100340c0d0002d01e040a02595009880c00b5100c0d018211010b02800409546501c68500c82c0003034a0003004040c042d1511389039030015034005894100ca642d070344c41c440e035440e5000b1045140141401001c2c1d980c00b070208403401003183e41c03600d0302c02002603800c42c0c41004034200c035907505003c12100d5a01018440b51580c02c1101c0309003500c81540c4248e070741e04418800c003101881c05c1804c110340070801a20004244441001049031406020910078010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 944122248 1250 944120998 944121011
    0x60209040c21020304020d060b03031935040b0a0906110a0305060612240d050615010201020a050301090e07082a0909150601020304080a2f0102030712050706 69
    0x41c0c0e00410030607100028000c02c0990704070310089000481c00120b501952001e1544036000100d501784d8050814124003030280c0b4540034041d00b036508072040f10140300000850051a928800c0e50b00c00c0c0d00000205078415250b214003d10780c0b41031246e0409040586006081400300c0c40d400713456071106041c04d51101007400f403e9015004c13009039810994004010a040000280c40c61070041c084803c1e21031004001d0519890341c0c6c4600b07800c4265503404401c1c0f4480d61000340d42a594020a07540310a11940050600c0e203005a0340a40070850144014103580c0180301e1105900c1d001400c0c0d90560f4401c3d60002201d94024415600e441d9a951044000740548a4104481400381e5481e40200505800320045011200280421544101c5400d403480e0002c60014421540155881d600108140b040301d04040c1c440d403850703044c1a140c2c0d800700c80140b0202c400201403540300401c10b00550002541003030f51484440080e44a00c15208000d00f2102c0038880e4500d580d0041090399146d0350418400c0001c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 944123498 1250 944122248 944122271
    0x120c0e0310090516060c0f08090604080c0f1c0b090c1503010603050c07080a050315030d0207030203060c030105031e01020d06061d0d05030d0e4201060801050d06020904 74
    0x108614003040d200750040c07003804c03c0c02c0c030719815a9008450059490501d1100c007600c0c0d2000a20000004540c029010058040749075201809000078021500203440101803030f02c1000313458002a0001c500420301c10300b00d106d581a10f01c2208680c560000d490485569032610a581404200d50b950b42c1d00070506148a5500f986500165058650740c4c0c0b002c00c0640c0341da1001d0b07001d80c02a40c88c000c107400802c0104090141c86003010356040540d00e00300f00c0d244101d8000090401044203400b130016800b2910800039072508108070383e0000c0d0b85010192130355061502203500d40c88a91071641c40d20520482911005000754112a110341c1180c0d4100940c50700d0b000000c2030400d07585040c10140365401034085061401403040116564020b00842c9815400000744000d001d0700406181d0900075481d083d401c0200c03400103258a58a055120045246080440b04220345402c04504100040c81c0061014a4000c0c0703025065882c1180e00c4150f4559500e4840c01a1040c150388541003070602000d003d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 944124748 1250 944123498 944123501
    0x2040b04020d091707020a0308090102030705070b130b03040f020f061c050709090510090c03150306061712030714071a0609090f1f021917011401120c0e0310 69
    0x2e210340fa2203083d01310b42c6039401c0010300850720060f601030f480401c10000124110024170100406005680c10881281c075103606200680c0e01507610b00d400010380703440b0b1a114404610217441012030b40ca00750300f4207848000003210709510090080000e5004000150f4421054403190741443d00c18555503c0c0c20b92041014080596228001c103002e400702003000200c0e80a545d100742d5000d0b001000d014940305241c0050310a882e4802e007407640d91703040070080307590103041c500c0a540030385400302c1d10a10700f440005841c1403c481d04015500034243c0461800c1c1f0071011250008400e2400ca4020600d00307039503008902c41d000c0003c0c0000c2c0c0e1000c0312145840040c8005100f010200c54004055881d0080f05848500d43c0040e851503400c40078402c02e243c1d59007003500c40340201d20500182080c600c481c121100d9214100001c000c50065403e00c1c002c0701d610b045140c0580241c0809a0740580440e0000e801405004032000200362105560000503105124041c400e400040442e114144000503000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 944125998 1250 944124748 944124761
    0x15070912141b060a08041509050f0625121407080612061509040f050d020a0606050a180f14070e040e0703020a0e041103010204060e0906031b0d02040b04020d 69
    0x90a0003044110001c2c000c90010442074400042c0c00d2a2400004140c21204200700420840d9180340c01444520402154415140c03038030300c654010320f11803214600a80c903044000b0035030302c0c4100841c07000c803911039019100c0e88100307841d908000032804408042c0d4000343c04030390b14580600d0b550b2401c21145c1c6501c892914042c481c00c1d00c551002c0c100220115840f000704840c40c0c0c40c0c0050800b600452400d203a502142d00900410015205081da42c0e00c407418040405000c0005910000f0010301380076692061400a00040307504150a070b240c00f00369031500b00c001e154520070303c0d50380c841c0300c0a90b100340d0081c103c510160810035040f85800400942800400983c01d402585090080f60f504400015024142ea17001012025a07500d04103900a401400a0045410808454a25002d07407002d00160010309403d0712154204a07070402030282e21a0f0040031540310790300803027180075040c0c1502c2e1404a80d400076680949404460f0012070058103602d000150054400509854010125030082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 944127248 1250 944125998 944126033
    0x12060f0b0a0302100f140d090c0b07050606131e0501061211070236040b071b021e0d0f02090612190f080a0c051002040815070912 57
    0x1048841400d0003403207040701440c04000d400052070b034607428959006000c43c0380b46901c0f41c58103020403034172200d03400c0e91600900c00c4250245e8540c450141001301c1000342c2405004450422401c1003a10b40741c07075a0382c0c02c1c05001c4500501c0c411001c540002966084403a01101c01015150301c01e0084a0100050909114002c0001c0f8002d001d43d541404500800c000d40f0001007a46040103416001c02040c200c0600b2601100d05009080085d00e070340c0c01c40d4020b00385040010f543c1c000c1c070700707420121450758004000c1d808000c01d0200e40c003600031450259200c9203030140e0f2080600030544000c0700100506c401900c1e4080250b81483c01002403040b540c2c03400920036500102d550b2900414044074180c410404e4a1640100e980c3c441048540e64010050074000c9820603491001a00c07840300d0307540681d0909000031200407008091100800c180f11140311401400c500e000c3c1381ca501692104622621000d50442800205506604c15a02c030400342442e00103010030040c052802000388904075001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 944128498 1250 944127248 944127251
    0x31f05121e0102070510020f09130204051003050f16051308010221040804030308040c0b1c0b15040905090f0601150201060515070b04061e15080609070e090712060f 72
    0x503102800d040c002d54544c6a8844020201110f40c92209006034208240a00d00c0e01820304c42000c2c030b50703a56500301000615a60f001650b030340c1000700f413250b46854094500141404c110a10109452280c2c4480d0720412090328611403140c2e000c01121648602c0040e001100403e401c0869500c4041d4003d014070844c180031180300355124610444098004c0340c0161141c0c40c1132004002290054019a622a103e084507940c5c09440d10784442d840d81005441c940303040701500d1000c2100d4020700c200c4103640d00440741d07540c1704404000b070b000c2240f0903400f40903083c980300c4011170103081080002c0212104002c0039558030b580c440310360b1480f241160060100541c00e060340042c01d42401400c00c0d00c2c00d0198203029182990360388030b42266000180c02143e0855652004074165902c0000c00c80512541010100d400280c8240c099044c902642000825401407010b0040c50f1000050b000c080b60340d075400440390341d6114042d640c20204030b82d01c000e07440a41901e80b28100802d81d03100c280101c126590 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 944129748 1250 944128498 944128543
    0x61804321c140c07120b040219080304050d0201170c0702030d03020306060d0207020d06060b0d110c1b120706080a1404020321040315020c0f03030903031f0512 70
    0x40c81c08484034070412440c04181e1244805030842203801c010b02c04040c00100320b07402240c0c1c4403002041c881e90180c00361740180c0702c442800110301d081401c482c5c40044400042180a0900319644d0301c0b4421031040e240310700a003500030400c6902440303055845048943d04419146407640074a001503001501c201e100c0e010704245203000034003a06c01c0c4c9029000140007203060002c290141c50003940301c0c0c90241ea00040300c1b2001c1001400600654018103500000c841d2125440c0d00000181e07030302030382e034464801002c5c0003041d8909400039090302c2c880041528100410718500106c2c1110144805000704c43c010224007064086e080040c0601584c1c00702000c03c00001c0c1c040c4018488941640c00951603044600300d50b900701460040160040b04580b041e47c60b05940e03030b03140348840001598082e00d4640200c0d00300941c03903080c0a01aa20781440700594034601e8000b06041d140e04c0700500d40310a440d100000c034281c0915918004010300340c09048116046503800c3ca00d55948802c00c0c41c81c20300c00940c0b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 944130998 1250 944129748 944129773
    0x30611070c361d0a021804082a070f03020904020904111009031505010303140d0b040905031315050a1b0203190b0601050306180432 58
    0x1821500c1540d0042005200c0c2400c00c030b400e000081c0c50746803080940d24620580040c890020b190740b0162680d90300c00098190300400b01400840036414450b8203500030325400005a1120040966030026904120059035035500c2c00c1a81801800c1c1c964107000301741110008115900700c030b406a41a5408102c9200954130b1b40c910103c0d00c01400001d4000d15400045030040c189011840c3c0c010f442042d1018040390324070f02103004202c68114200000d030b10010200240a48050301031400c02e0342c0b074401c0c0160342c10354030081e2452800c0c1c40e810704045e40003d0940e184500325444140946070090080c00b100210382000c5640b45c00c000c0e0407180220841d407001031003c4c164502c0b1040d0351010340302c05041928070304040c1ea03420b10130b0100180c0039210003e0940107035418040f00d0200d184a03000711440503441e040c0110600d2000303044a05215007001881483e503a202c0903816003025844044056541d0380c98806000c030801c055a00c90800345003400a052841210801c50464251003103590100090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 944132248 1250 944130998 944131031
    0x71b05030307031e230a110c06030402061b0111030a0513050d0302070f0b18060708190c0c0209090d0e010c110108091204030501020a0e030102090108010e1b04030605010306 76
    0x500010f011031500c0240f040d90b501098032807480004141480340c440702000181c9000d0480301d800001514000043c604007040d04001075a001c1440913008000541c0c0c614040740c2c961001400292182c030006c541300302211860081044010135060092142c0100e102003512290030544030b02c141d4508000005811820655450070341d0b6800c900103026040358942c00b58001d40c4004002d0350407041c0e0007050004250f04400c0c10b40100e02c0b10340000050000030540c1818904054180d008000f5070b2018402e041160f15010415004c5041000806101141c0140c40010200b04020b4200b0444410801d44400200d80c012842e1040d84500340d040a829004440d21b0450800040c05600c40390b080c201254454189690b100f0421411154144103600801d0070a80141c3c4c812641030b9000a005201030343d100ac151580c81000b50025814103803c4070010b801c5100500481603052040d100180b500700300000c100309455a288081340d40c9940700e0910001070902400141c90701401c00301d1f520b440c2d04c0755 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 944133498 1250 944132248 944132257
    0xa150203190509060f1506161115092223060312040306020f041208040801060e090a14010f0c080f01060905090f07021e0d1e0504090b15071b050303 65
    0xa034003511300e59489110148242001605454150061100d201c9181d1150001000410348604030f001d0915090b240c82c2c40c03c5101c617071441303009030f00d04412106092640c3e8155032039158120740801d6540240d40400c010078081c4003074001c0176030401501740f01001ca1480c02d55852201d10401405942e5010140342d03490103d900e0717585400038104400c0001c90241e50280c2a20241d61501078034141c0c3d43c42456001000d40c210a444280000804001002d0240710300300041c0b4007144661068546200059150703078100d035014100260313a5070020080301d400c0d0300c245540810790108005100d02c40c1401404000c0c01c50b0130111500c0e480002152942c0986030000442e5001011b0110f565502d01264590800180507401544180301d002c0b00103041545110152980341d1700203040d152143c031401001150b9000d0300d02a0002c0c0340380e0185100d9072203c21503041c0d404210740450300301d4414022411303a00c2c60a101c8c140c05c890100f100c03801c01104480c00316110181544c052191500c03141056100e108 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 944134748 1250 944133498 944133511
    0x5070611030a050d0e06010e0f01150c02060a020a0b070f030b0306010b160c050a090f0b010f120c0c0b090105181513021201090b07110a050d110a1502031905 69
    0x80c4202c0d012244603038002d0030400420030002c9070340001d002005283c04000c0e08103034640380310242003003035260b41d0200440c0103207200c12100c40c19410105001c4d040c40141ca001900540b0300040c40084a4000c11040842e580d20416451a41c60001e000038000c60700044d400c00041d04050184030305250000e00d2a040c0c0e10380c19081840c1050368210000c05001e50113044070782142c000c0e00010b10740d580e81c03c10801024415008588564040311400484d540055001d051000444c2e50102e0301c1e40c1700c8102102201b01410003e00c00395011030503242d1109080d8020100c0d0b0015040200d500019040346000d0400410354180c1d44489090302e80d00c0b03140001c000205a480f2800084040184541a40001380094101030144030001226820350b052040184c5000141c2024405104c7d805440080451080b6020f0115070225a85240e1105080e160742c1d81009403c98103030080d0002840503400680c1d1010520f0099070b904941c40010f5041190360b4030a140d45a0105503a60a1501a0512905 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 944135998 1250 944134748 944134753
    0x30609060311090403120e010204060915140315040513030314040b040303050712151415090f0609030f0f2b03050703180506150604050d120509091305070611 69
    0x1142c00501101c03050081c03090741000341100c0070a40ca04050312502c444490b43e1000960f595085c2180500801c10307a0344a101401c2507a03002d416401c0d0f00c02e1001d101c3c5107508915594076194851081c80581d00c00136140c1d480752400041c00061b1a010541101c1d251213614140246c901012a540020004403009404140800005000a88683d03c800e91001641c10501d07076442e0f580c402c1c5d5040b94a400c0d9010f84000d000b59081c40720081c1c4218a01e00c400741290102c46509000c5410384090261709512800f420703108075500050758034902540c801c90b2000d000c0790b5044000e43c240c0b5580b80d440003088110781c000d0111340d01605460140f1a030100c0d050007003517201d032454008210000c2100404810425941c0c0fa808400f46240341c00818405005400030b00007030038011014074201000c501c02c10300c2800d04000c200200e4442c12590420182c11003200301c0c0c0b007001071600f60303135a125010303203d40c0c494603c40800181e4808041001c400038040c00407a407044c1d0300c40b20291920340401c4c0e0070240c00d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 944137248 1250 944135998 944136023
    0x10f0603020a1403041e0302060a0f1a061e070b01090c050a09051c170405012d050f04080118150e1b0303041503020a110303070e0616021f0306090603 66
    0x80d00c0d1400116040381c855550311820308401c011b14003200c01d0340a4114010f82102040c003100d048140103210000416280070042d60b0344110481d032135003610043c0f0034060308020810810481200d4000c0c0d03107003500355850b517070b4800301450481d00081e03090164202c074528041c0c8c4d03e480e0341d02c03410035103080c0311180d01d0f0000c802c1e06100c104002401581500c00109007034500d658002004c08540c0c00e40d00207029140f41c4c4540c00c2c20b001422101040003100c54200c0c45800d208150707075100444e19444c044504007160398484a100104042c407503134110b80410340c01e002c40303a090203982d644012415401500101400301011402806950400806d440c0c2d540c010000030441c1082000034031303c801c030028222403134260780320f9030003c031484442408008641e0115185c41880c0e00842c0310101150010007644c50751800340005000700c602508890f001c0d10300440c8420890000c06034248005800400300c1030052032071a0240120a03000b8844800242042800103070b4600e1405108180c3e03070310081d0030641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 944138498 1250 944137248 944137277
    0x715030612240f0e010605060c03030f0709270501090218041a03160602060f0405030a0c03030b0d050105070e10020709020a0201090b010e040219050603130203010608030d05010f0603020a 82
    0x38501e90202d0700c408900098402d5201c1003980c0f2070f80ca14841c0f10000800c09110820405007100c0055101c01d01542080007031200300500842201d512015840003110340f81c8802d80215404402e5401a00428810845140002100341115581c1102c08501030109a1301c03580404240e00402003281c1c00c14503d075040301003518254000c0a05400700e80c1000d1416a000f50010349000e80c585000c6003010081c05c41448440c3e07050240035840784031552a100c1c1400c1071f50b0f8056a81c0b140380d8000d810007400c032049008051194010b00c0d400d00c0700804c60000c4400b64280180241000d4407001d0109400030404855400d040b90100c001c0e0806170054604949822002400703503014200e031f00210355860180a0003e000040198081c08009203404414a4184103028989040a50401e1244000c01040019940300710450342d00042c8000340080200082c4007180c0941266006120f090001207484010001582d2002d0304072a550414603007059070f1000c05604174800c00700391500258020203030600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 944139748 1250 944138498 944138513
    0xd0c091104140f2202030603070e04020603040b06190e10050a06021f02070b04030207030605070903121b05010f0b0a0b030402091803191d01031104290c0715030612 72
    0x10440400f500000c4d800c52041225200070202e80c800e49241540801030201505007008982c010701030000000b070450400d030300000c4c1c45010050005104001d8800000c00a4485011901656280241402038151203003143c56800c0070440d40c9075843c4014800c005928640442458121500d580245c04c05010380342c00050f0301d17940c0044418149400b00003402c0024031070603c2d103215500075400351058906510346041541c502514800c1048a040341c180045081803040c44000081400c1401100c850180c02c00606130220b0800b0b02030313503e0040340e42c0e0030303686a41064480407001c0f948031012617100d00001308c5500059031b02a40000d0118001012400e6004400a001c11000c0440341001c2102c12010004512040940c0018001110040445840212116000000b4202485142c4411441a00c80e000d144a0755030580a0a400c8901170b8100e881d1000103001c6c01c08146a694034043c4902eaa078202e00d12a02c51503c0650400642c0035100380304d07040c103036100304459110340106900c03205c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 944140998 1250 944139748 944139769
    0x130b0a020a090f0303090503060a05220201020a1506060f05120708040f0605010303021605032a190e061807081504023c0702031504050106050d0c09110414 68
    0x2080c84120203001c524900310045503c0114071a075600e40c00b00d0700f420309040c02d00c40090b0900083c10f007014203200c0a0000f207016050008140b0f00c5402101c151400100e00d0070403448006851000043c20712201407050360000000c0d22899210b040c090fa00f10801214244142800c90301d24420110200c2c80b031a115488854000d4044c0440c01d10400154446504490080c3d1040700907a02c50030342c0c2a10b1800c1400d41100415044014240c0c0c0541000c000000c011640c80d0a8404001d030310350724141d642c0c1d020721220710114030b40e041054644c5a030384192840c1e00a4941350311500c0e00900c0081d00b03907507090740e0600c00c8809075586242c640740c400550001c5949a200c1e0f40c1c0c172540902081015103d045a510301100d42c45c01c0c0c0000d901002220000803200342c24100907070400c1000500c0140e100041e8100940d032640d04591120340d50344c140b00303004000603001280e000b00700d81703054003e1000c0c188114050f0380582e0400c000c00300903016045901d00c500c0c4916994041e407028052140d103030204802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 944142248 1250 944140998 944141017
    0x61e051b031c0f150b19050409230c091503040c03351911120406050c010f06050d03031a040219090518010e0703090605150405130b0a02 60
    0x5a041c1440c2c022000c450a045020145000e035480b0020228000c0602a41e00003000700c181c4c3c000031508040c1c4ca40b0440c41070f40107103e07507858103550040f0002e01c01c01c1240c00600424a0400690001807913a42c070382080c02d103244070020000ea02040303101c0c50303d808403400403c0003480403082d04100b455100e05500010801c1c2c070700041001c000008200089a00008401080c11480c040201460400008041041a48030500051016080d0003400380050310182c89542040350868000442c000c0c5030000e404144802e0080100b400120325822001a00324111150300a00c00481c4805041c4101d52151152a900400000e82140864020b0340300d43c03002d840785809042d480b005100441c00760b0348070920314001c1401142c06142e4403507000c4d410b0000740c6402c6a141d1811012003141d0048400f046c054170b085a00d0180218030a113019a120b1540c455000708180700780c0c60540c818803142c20303008820f54080ca0501c4005800900a070001c0c0580c2c2da4000700d200b1080d110202034000940004454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 944143498 1250 944142248 944142253
    0x1503021c0203010204090c0807080c040b070c050a06210e0309150c07030819110705010f110a0804030c0b09030d080702010608030f031f121101051b0601061e051b 71
    0xe220150301c00f80002c1c00a0040c0500104a900b00e000d0300074010400201244104140c40052088001d4010200e40882d406180c2d000e4a403011400c114000846130f501c120b40c000c881800001d030586e0070000403080340032016080041d0100c0e1083d05030585c2c2c0560b001d4195a0020410180940b03041441c180302d9190000f8810704040b1b5024003a80703001a650030603030350b0310300100e10743e42d02c040d83c00624181e910341e030724150541541503918160b0300c0700076005eaa0306000c04621007651840c0300d2510a01600c1d40c0100f01c035a100200d0800c07800a80c49400700362080c1c0f2034000080307880e80c10a002c4500c070b440e01400034003090307100b11400c13070300c0c80c03c0030300a6001c554903424001005242080500860f05100090715601d0030009441509080360046410580c43c004604000200501000c0e442071a00151410111418400102c0f2903100b80c0e482c7c154404038641c4405484440002d000e41a64002c0e16504040300c507401c24058044d0300ba07903030400041c0080002c2c00207100c20701440c0004c0703001d4204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 944144748 1250 944143498 944143549
    0xa050903040e0a050c091903060e07030b2a0d0b040605060a0c0609080c070b18010305091002030a110c0d02010c030b151e030906040308011428080706020c0a09150302 73
    0x9001e8241048003142c7d05d03040c0710040c003d11a0f030b4811040c07040d410100400100e071960355070140d41e00d4005c040d11014050245034201103100540c4180c42d40000d81ca03450f50311f400f1a03840e14010860038546501880c03802e400480c4505104088414851864a03268029040340d23139600050091060f0481d1019402c4c0103142110004001001c098120000c086031507454001c40714a2001030300099138109801c0100380311b19000041141c0e0041400e0500c00f603500d071341e2900450007420070a4058425070000280c0c9441d16603000c80d110001100c070b82d00a10074a900480214165801c4c8240698002074440340c51070110504030003418104101c041c50350700480e0311500d00780706410446d00140180c21010412040603480404c15000d001d42d004010b050320100740c0880c204a20b00ba03d030409503e1f40c030003d5002e00308524103410041ca00d420442d80b8541c2c481c18003e46031282c3e1300c25503004180742440814041e06500606900750514070544105500d55002c200058629070b00094115041d142c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 944145998 1250 944144748 944144767
    0x24030e070914060a1203080a020403051207031d0f011d060301060c021206090312060d0210030e010b090415020304080409051317030601121e0f050a050903040e0a050c 73
    0x100d2100142612640021600d200380c1c68005400c0b40104040d01c1064407140a100301c94840c050004031581601d004401540da0080102c0244510f800103071491042a034400040d001c0c002c0203001140c40b0341d8401030021600c8004e000d070400f1280600d94400ca03501d540348903d5100d14511001151180201c5038040019804290f542c0e00a8010000040003001103109500307000040080c6602e81e00c009201034640450100d40302d00680d1030325070350b4108090229080b69541991484500e400900c1c2d000c1030345041001800030100349401804c20350034101c00c4485031814840c001c0c8900c0c0c000c4699044074808802007402940004c000b12200c0f4418131022130803042030300c0794601c107042034034001100000d075040c03840c2ca50078001c1d403a0520400c02c100304076550b640310030960781c80705010308041200c2031904001c402003d2100c0a20003146c1c6011722201c502d5046030441c601a500d4124200101d4899029558407880b85024810306041030030f0100d0358404c8580d000702d034080c081c43c425505055502c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 944147248 1250 944145998 944146003
    0x1205040c050f2404090c0c0f060b0d050f1e19020613080d020c090a1a0d030e120a260a050a020703020a0305060417250f020405090a0c050301020424030e 67
    0xf10340c400c040010200f8103218035641c42c4034078503103006281007818000d5a180e0781c44d10201d812020040c8015291402c0c02c0858907600c0405100a9100050321101001d4528265855845403415103400c2040f2068861040d13010030b54010349600d10320080300e070880da6001e00090b81d02a62400003a0048204002007804080c000c00c6c1000710164060312a01030000308100d050740024017100680c078609903100b0101032400350f5038283c02c1c40a0340c0315007511040382001c0d10701a200640c115042280e0842c901d0b420706d070206120f56254450300515425080b648540203500400301d03054501c0b2041005500c1d080382c0260040e240e0030320284115000c0302e40320340c00b00380d404003e0340c070850701c0f507202c11705000070000700c0c881c001c40520074402c8031030078035490070315055001e0400c0d04520840100c0302c1c1140b0501150400f403072149a0003510034009400c051050700e94540030020240c03201c00d1403070804511840c040c001ca804480c1407101d125080b075031140c1e8a20030146c41007104801d1503a80c0c00d40c40304000e0b05 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 944148498 1250 944147248 944147299
    0xe060d050705030a27060e011e0608011a101b08040b031602060c04090903180f0303080702010b030d0827060702010c020703080f030c071e031205040c050f 68
    0x220742c0c9003a140e0410b1505402610042056120303c0301e1081a441c003081050249850302c0c60308082d0100c0d80071800d071039a81c014142441540320001c410110101890b0458008070100d80c00341008110b40c00e40542c0d05c100c204044080f0ba5840308211041c442e40394480d080d4801410b90f1800d10300440e0b05180d4602c80c560b40258025546148003008101d01910351921500203d0890300240c02185040d890f00700c20b61045001e4901001c0d95800c0340340c1414400c982d2004a030304818000e04959440d500c2c9440070480d00c2c84124001050340c800186080d04c10300a150113400054000c000c806da40c600165040803005000445549d0b0a206420710780040580444566803114080c0c1101d06004130004e09403605034401e0015940520002c10000d0b11050454030000c022894254036500d611800355014850242d02400188a003011003004a0092410003400d40c40f1b619803006880300c44120100f61001280c010341402ca400004220904041100d80390340e03000244070300c500e200811450702d1050074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 944149748 1250 944148498 944148511
    0x103090c2c01142808010608010608010e030a09090f09200109050d050619110705031228050c090d0302060108060a1401150311220b090307060e060d05 66
    0xe2009903a074180716107180050140560003000e4502a2815020400441105204904856088654800c0e61843c0705160016100d101c00a0100c01da4905005010b07003d14002c544240d443c0464500c1c0c203100000072101281c070035407a10380d106440e081c45640142450308d504000944c40341c1407070002414052110740040f10101d115a00c9500b500001031440489030450303801000c00001240c042000003030304a900c855224215040c86080a60600140c04420002c11031500c021400400b0008044080c0c0384100405440c0c00c00c550b9016004007046242c08004a030f01c0d00c06800d002c5202c0740e240c1200364800e2110140d14580300b1501c0c003061174003040c0401500103821110040c065541c0c1441201e81007141a9024050801e42e1611407100354018410003100181070500640d02d2402a00700030220b00700c110100e034550b115000500f1b260514940e030700040130042a408128510030100b5901809005002021140c1c140502030354400701c690302459000c042448444460003136030046034458807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 944150998 1250 944149748 944149799
    0x1360303030515030d050f0304140304080a0611070f06020a021609270302062d0408030f072a060204050303030112140d02150a0e15061002010e03090103090c 69
    0x391843c0c0300d060740c09081910903c681c114542140001d54481e0a0394001d000d510181c40c2e40c1d849600d8032485415407812484054040400d0004940c0c0d40401c00c0107495005602c10700c010066042c0b900e441d4072880340024041c900d05512040450180d60141c000c085850044890005914051903210001c0f540040642034039140c141d13119141a00040711090744030242c1d0228071444e5078019441d10302c001d1507c01b80301218110005c02120b201d0090403499100c10500d022420241001241980211502d840d03807002c0b0004140c0c901e2054213a00301028080303205440041c2c90a4944891821003041622540c2d0207010215096500b070000f58001d000b4481c000c14801420b24114210384a10306201c9072540010440340d60f125008241518900c05407a40d0201c40e6582d007240070010249840500b800e031281040348904000b01c281010b015410888030702c00d403811001400c0b030036a05600094800d680081c42103000d0355000c3d401c0002d1041c441d078030306200b0945035820703403084400f41400d0441c00b6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 944152248 1250 944150998 944151001
    0x7031d120c10091e0c09020d0b01030e0604050709050601140f07030320030c030402010c2003060105150f0a0215040506150a050904031812050f1b013603030305 70
    0x1c4004000020710000014002d2200600b01e458450203a200704621004007000548180c00f0031501d21803113000f5003035131901151a10b40d059080001442d1155185010900e403070310400303419800240040c4519817110050410a043c44000c401602001e080700341405203404d1190321003031041c4050060180651405500d40c3c4540c10001c059a450074070345540e24100448407212021030904a907404121454403d580c0d4442e4801240d03110380071440640b40b514054051080300e9003c00701580140c50440031541d0990329441007191002c01740c0e00300100075900300891020001828058015404e160043d81c401c0c020208010f0a645012102102c2c20b400c10020801a48071102c8039128102c1c041d107030a0629030030180400c0160101a1000e020b01003160442c1d5a101640b4001d4405482007494607035980035149000f5548812030010361140380a00800c184031010440c00d441e1400105a42d0030010000c144050b10180080c0300e441c42002e0044203120002c074080605002c0214425900003609 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 944153498 1250 944152248 944152267
    0x6191d0a0b0d050d1101111b120c0d05090109090911090606090105250c080f0712030806042a0201020d050903030906010302060a0c0b07090503010f060b0f1308100b0a081507031d12 79
    0x203208084111401c00500ad00030084041c50010311100111b40c14105641d88294840060314004200d503c1000035a06080311003080059007240881020701c10350700c4551545076001040784601400c00d201d1700242e014010480326024207416805044100801c1a40120050b2a4200ca60f40d8540040312280e02451203180514810131680c2c0040a010108580e909019680140100c102500c5c052103542c4540550504103814908014442c1e400402d541594542c0c02010380030790400042c10410302d2501d40040e040140100c101c0348603094074070240009a081d60b00300300d03443d00600011030800101c405400700041c00050514003c625540721101080e01e800201070944142d600081c50783d600707000707082044030030060998012108590380c040d12900c0c0c05600541000081c0e100341e84a100c1c0b82c40301c824155890740704520229096178080002512409560741d11401c00c41c1c1c1c004000d9070b40380019010b51003640400808041c0e203281b02800f035207600c5040d1401404080d48043d4410025200b0807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 944154748 1250 944153498 944153503
    0x40c0e01080304030c06031d0d020c0a0f0308070204020c03070b25050a1d040b09100e0f0403050a05092e020610050906191d0a0b0d050d1101111b 64
    0x5101c9140103600d854110307a940403190030103219940905803240d140d103403450407412102c41e1940800c03088551090b503590b8001d41d65180002068002c800324040443c0b95070380400c03144196900b1403042c42c0b800310940e003884025800400780101c0d50006108120006e080862140d006114034440c6103d0032800c5244050074040d00c150f40824008200078844540f5003000040300b030f424840d40340340141c0c8031100c0407401510600041e40c1d8071031803410810200307500c1c82003c0000e5070212980d01e46a0b40d01c1685c05072907191f06030341c00340101e0000d001000009206200400103403102504546c06414249003440712100300765011408000ca8506152100b03138100859640903000ca505400c910f0b107807801189555a0161045006125402035205104150110782000307044400c01d20300301691003080c050320110300382e8982941c0e90501c11381a0b9149441c2c03083c0080950004007821a8044118040d1580711984560318680e540354001c0765016022800908480c403400020301d410a10425039007030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 944155998 1250 944154748 944154751
    0x3140a0605070809100e2e0b0a030533011d06030706230f0301060c050f060c04050609040b060a110f01050907050904031704080403020913150221040c0e 67
    0x2c08000702c160403c111594001000c070125000c60b0000195100c2d918910750611941140350101c1e034800500d1102180d0101c03102e003070742e5030000508000c1e41341e01b0800c020080781c4a101c017400715844581c03043c021041429404818203100c1c0081c088010034241c44100d0351800344c0c8142c42a1200d040c902200404650505a205c2c108801070a034070303814500e0281c5081c6d02003610300d0280e40e5080c2516070741d843ca002200c0b03a041d070160489407250395410006010840b1290121010b00a40415001450000502d2401121a155814105400e06050006a4000101c0258441d0302c1d1060a405522100300a080560780c7d5501c1841022188901920748a18407561400307a030302d89010046c4840c00880c0707074415514101c0703020503540c07160305080b9200490801030341d00040e0243c1c2070004000c40500200222482035410000300e03039649040c0c07281021507c4010301a0504042c1140d21054035038004c081580302e1000b9415624204610800940c0c0b040741c0441d403080848109006040b00b450005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 944157248 1250 944155998 944156011
    0x1603060c030624030e1b0310020a02060f070509190609050a05030606040b010c0b07081603050910180807150b1e131d01140601050f0f0f0403140a0605 66
    0x240001c500d00007400542521590031140103c0f060300b1a501d406102c1c1d0007140121034400b013202c000801000d4040150709001c50310a20902ca8400003c0711090b480c0207840d107030001c45d000b800480da14840b0100885800078042c40400c541001100002e0391601202e0017402050104241c0704c03400c5c0100a09600c50f00c3e04860712841a40340c00f0040790f6400030f41d296101e001500c002c96a10075400068505040540005000f094800100b014840c0e000480500c60042d2500400c110f490a501c25812a0415100314140c0d0f00142c00c015160b4940f5044840210390f4001800341400313032030301c950080d9000104216501d070200078800134075410600640d40900021a040b40c2e18a01d4450316204952603001ca140c080d412806502001d010139038019039070745208440050702088440c2e1814020514424522070400003500407070040c2d41700708151313041240e0707411885103080c103600815010380c0c01c11600804000b004000110010b1a44645255614950401040041c1e01c514020781a5000240003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 944158498 1250 944157248 944157251
    0x105070314060402280c06050a0e061614040e1608010602100f140a0e1506010e0904061d070801180c030f0501060e190b0f06040e15031603060c03 64
    0x108141c50300205409400031400c0710016070f50729540e20b000f6100707181181c41411001600702c40e025034940000e00036004502c40e400801840e514955071000700c81c0040c000400690120f0000340d8180d042c40e4180280300c10754105000b0704074005260410a6015401c880c0e042c049100a2041000801550704c40803561170a00d100a50f040c503000075510140c21004050080d2200009520400903602070418814120803a10043c602a521305d00500515455076036180b040c038807120151950411780034000c5da0140c0d50107640141d0002041040f41000c3d0007078034003d0f81c804240620400725040d00c601c1c000805c0107040a07030710341140d05084405445018000711a0791140c94001442c1c04654000d47e48d0000c0300c02c1d04001141003190040a59407c400321040322242405144404075039000c100c821140002d00160f0f04040a00101504900605800520611090081c442d218030b50b0391340140d5004091540e0469400020310b401e0f00b04d101039442d180074140a10501c2070314054100320348440d080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 944159748 1250 944158498 944158511
    0xb01140c0a1b2405130626060a12020a05040501030c0509010803090604090905010e01111b03040e040209090f1c08060405150618150909011a030103240f060801050703 73
    0x85040102200f0b11007401d400c050002c0301d18505005205590008540501014280b40c90f10000340031071803020b11800c50381e121446500700407030118a00d60712501000d0102064503280c07580d44403940714450350499000b0040040420305403200d1240038000c6000e203005000140c41e140c02d1004409041c1c02611103170f0010408160a030700c802c0104d4043351148034002481b0005800d042c0d0041140c83c080100550034600c20291001c0c032400a858651800700e00028421070f43e12099a480c031481c030921481c4519500001c6c0035240074031100741e1045440703041e0f446555074260f400d4288529200181000d210303904401d03041c580e00c040010380c0040165800c00190801090910310000ca80502c180300308400900110700e640e0061301d14070f001b90090010345480c80b05102196040d000302d02094040e41c65400002040c202c0c10624000400041118500c0d603401c6499102003295001d00680e519028a00102490209880b800c41d00c40b409440004010341401c001c01e00f036a00240c0b00c6402c040c10b141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 944160998 1250 944159748 944159759
    0x41407021903051c060f0807080601170a05060f040303140c0d0c0504050d050307110d08160611030a020a0e0105090121091b0e1e010302040b01140c0a1b 67
    0x180381c446034402042041251112840c0403240c1d445410041c1c000183d5400441e04000400c2d044841601c0210601032500c9440d0266280d4464051066040d00c0d400f61004006075a00c00f80307503103001e10004040d603156034059220075241000650b00406040d107014204024958035100d045805056010b0780d0105003000400404107014001400c0010b40c0d40702d0807102c501e802071044800408002e800b600c9505110b0401540341d402c01c2d0810b0707940380300030410707080d0510380130b0112412668403040490501400c0f9400180c82085134204445065803500000034030806100030354403070760440710090b175600d03e542001002080520134080c103208090040c561942c0e0040c1400c220b90904640d00821071180c01200c41c050140b13420041e1101d07240442c0400c1428060382e554054840700500303080700340c644c11003400600002c0234031000c5280c400001800140340540041805000c145003088960301041c40c1316040d0b510100308081c0a501c4026118208104841031012200310351111003e264a0310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 944162248 1250 944160998 944161003
    0x61202040f030308090f0601421b02090f16020109170c1c080906010e0123010c06060902031605030603030306040b1309050601260a110423040204140702 67
    0x74040107003889a07420014645d00c1e0200b01050240c4003c8045420550b035803503201c110441050300d218418922036110a5801d00314409920a41e00f02004c80c603044161080d080700e1001440a071000c00f00103a500c0240035941c2c50036054010407107138070100070f14145443d0301c4600c1841a410b20080d0b90500c2d5086004c60980703c15005101074035103281da40e86420201090400c0035002d2409400783c24500708213251335100c14000e01c00c01c101c0b0112101070b40c179a0b646050546003407017149100c003000a843e40c10200310340b002c041458018101086404259500c0c1c00c2a117005401c403103001039000c400c209002c441c650000001c01ca4505190b403070b5084c0300011940328800104054011a12121920340c1d40d16441036004e6030f625401c1e8100031074619860b211741c82310420301c10035a0070540c801d10800d6549001c24076a00000f400001800503400c0b41d55410b039a07420a001055210b944c402060381461809640c81002c0b8120541e4418245080c0c81004111400b4507400040503000d58100001d45400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 944163498 1250 944162248 944162279
    0x20901030b090a020901081507080f0a0218030307050109030201060603230405210403030f11210c2b09030b0a0f1104080c010809010c050d050c190906120204 69
    0x8415002050b65070081d54501d08884a08000d4200003a00000580c6202c0801c20f11030341900103000607807980b14150304a6580d070f07041c0e41a5061148034800300341301030ba032907008200d00c40011911000826106000a040d6042528140c5d80d0340d44071068082051f5080c42014094202c1d0308080002d005540a880c66046180701d440440313807440e10216080c01010089180b1013a0050742c1841c0310703200c0c0d444030125504188411000310b03100c94852504140a244525100d030a507074014421001140c03042c16070301c18000c9451107601070401020500c20804d0000f4084a4400400702002c3c0d0544000f500a248010821000308146a4420310000314000c222503009500408045101012110134200904a1252003160100000b0700081e0003007010600a000381400d0726401b10541d17440300c03c01d00340e40c1d0202c104030000b44100b02506c0760741050351203543c0048401c10020b00f0310f501000c8601c0041c80400002c000b0034510f03141041000c0c0d00400214494544100540c10071b41303071460b0181000e40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 944164748 1250 944163498 944163503
    0x1707050c0c0d1b06171b120709031506180c050f0d061211010e090624090301111b0d0c0221150106030b03030903060106080606120f2202090103 63
    0x149249040c00344010043c00c0b8020108070008010340359501c280103001e0814600841806200c4c0d17400040d00c82002540050844441c001240d1600c0c265070300030000c5040003001c0100f0b000312200c01002060702c00c13108030319026001c40000384490400c00680d158108507504c0450380341c01c0c1000040f4190b800340680313500943c0c105608e03840d07840f00c5407544042c0c00c484c3c00055a101e21542180140603a100d603003510004280c840500d600d80381c07010700442c000203c0e00a07801202c41406074003180d4981400504500c40f292410381071180c032100003400c0d42c0e2004069280303001c01250028204201603480d200b00394402c0014004070551500140011003900e5001e4800c800f11042d1680403441c0d040c8112054512000303446040c0f420b004081a03d00b000c1c080c150021340340c00659407440c2000002c0314101c01c002001420144e280076011144200000c6c4015080380d0140b01204464190702d91050280800008146641c81c110901c0107244c1303100b8800c6c0f900000c50302e032480701684843c201300d810340c0e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 944165998 1250 944164748 944164759
    0x5041b0905061018080102070c05040f1401140307080a050f0f0a030c0b060406120f03030b01181403011e0b1003050705031314030a1205010e09070e070309020d031707050c0c 76
    0x2030740f051541c142c0c0c0d48130307501c600c405500026011080110380003000080e920125410095240190903201c2203900008188041c44c1e0440c0040c401155410410a8614801011500c15948446c801400c0c05181602114581c4c0204031210301c06d0030602c18001c4481d15000104042e134400c0e01d00400e05c04100c1805003090f0800c0d00400e280da256a0000310140c0020b40d0701d0459410a07103405418118030780300c260300082c5007244410301584900d0728801880b106001380c1c07080074144a4450b03035284100260340c1d410340d61101c1c040b821420090310f00145222941c0b00050b0481c030b600502100c3c1e8200c04806003014504801c11040c0b40d0010b080c2c94206d5420104000100311500c1d21813030484502a200665200c046826500143d005084660f10180c03c0001c0c0450b9a030b810001004440aa40c01800c41e00700a0050180042020810382e0004841c60041010141c9801042e040140301e00b00f0341c006001980e050050b0603400c002c0a40005042ca0990715084903420300e1926040b01d03900325032007072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 944167248 1250 944165998 944166017
    0xb01120506030a0803070c05070603060b0d05090a0b1603060614041509030c080c1e0607030c0f0b15040b030c1c06060e0106030b01090803130b0d020d05041b09050610 73
    0x54808001094220f1342c4400502d0380c03400d00d010003130091615140c04a40f54415043c01284080c40b03030140c0400c80d12854a02810320496812100c0078143c01040c1440601c07581c800d00380031981c0030207045c0c020924690b00301e545401c0048000c096030040c0e0007600500c80d900a500f000440640b0440d011694030041550b10881500c078110f03016040d561010b08008030008022407400804114070761114000c17608030f85a50318030055404640b0104452980c010300c140035a00201e4054144105440d01c10741c1a03549010655607505c2e5501002e403145204528071700c0c000c00306805d103403103900300500742200181403c0c000c03040002d8030842884004003030040d40b40c440004010450b0024409030007810a4800650307100c4000800030000d50355181e001501d6502c00046148011003205c2601c00c0340e8040341ca01030704254104500b50b120b000105503c503801c01855162103842c0c40303100d014a1040751800034002c182020400b400b622900b00702445e030700c1e10080c0005651403240010480115040181c0c0f0f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 944168498 1250 944167248 944167261
    0x70f0c060903050d051815040c15090f080d030c1b060f0905030403060902150408030306011409030a0b0414010e060f06010903170d06061409040b0a050a170c040b011205 74
    0x98099113005003001400d00c0140441c842e00c00030121410892a000c946001862503a40c405500c02503034040c18542c8007550601901c00102c1c0302820b001081c1c14580c0c12036550380e2020000300050b500c0f45015030000c03a40510450b915009000240505143c140c2814400300c00e90a640d2507406401401b16030b686204010341c480507007003c4501500081030b02d88840c1d42e03007042406008a844102c1c4035140c91380c0525000e01181c81940d094030520002941550b84180040d10000c4040380c00300800842440141d480755000c01401c40e005100d10459011400c1c18900550340c000c1080f40b825a69041484000d418080003420603072004403110006c600341c07200401a00c1c025115040605642e0f101100b504140c0400c90081c5400002c0300400c02040f9503e0b9030440b000e1075500c4403070101c0141084a50050710b0309800070300188100a004205165860000501c5600ba940c856011200380b0011074000d81c50a208519180034203540a1200c00b00344c9000903c88900703000044641d0b41d030b50010500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 944169748 1250 944168498 944168507
    0x131a031e091f0e0c0607120c05071a0c0c01090b18180c0a020613110108091203010f06020f0705091f0b0a080f06101e050c0303010902040509070f0c060903 68
    0x4108041d99030310708035110602c601c800b4240c0101c1c41034152040055214090400ba821540c0b101d80110340c00d02c0300c90100b0f0003201c0d5164418401d07030b420b00c11132802040452440d80f44418210358204403659650003495060304284c08034016038148149107504009550f0070800b02c4080e203075100c140050540c02c6200041d01c03490441c091481380e44180c02000640040c000c014651200d02c3e0302251007640d10301e50007040031060b075a001040c9500c0c241103126994010741c0384a800007040342c152841803a4030381c0c006186800036485440c0800c600903040041a8040c0000c0701c621011001038841c49080101060b5104000b901c00c21212000440760700c030f07005030700c600305003c0c09001746011f036260745000c8000c10b481c07004d03560320041401040104c0d03407d1030310501c03d01c181c41880d06c0c2d050b143e4182c00c40070400307001c0445590060003400c10004100000c10700045011f01503403000140c1f02c41c1000c007440f0051200400210502c9000b1400001003a0482c1c0521403540d44400c0101b1145503500e01201c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 944170998 1250 944169748 944169763
    0x7030b060f0a020102071a04080405130e0d0e010f08010f060e0607060509070914060321070c180c0219170c010c120c0201090f021212131a031e09 64
    0x265610000304100c8182c5a042d0010480c25000b00b1903001000307000c6901d4141c401060313600400c901010002000b503030614140718007c0d0b05403604009071002c040103480b420990038042000018030045c0000c0403540c0c22100e5140f01e15090700e002c090780e41c1070014481c4c0c5c1c0d00e03880c0918020302c964410400d80c1542c0381c8084640c09940302c502800070b4101303015407a40d02d00700c1e030145880031800c20340d411410307101d45864903208040050081010040403a012401c030707003405c41415020301c01000f0000115003000c4200005114014144030004010720104084495403011003086400141943e0000c1d04803c00700203816800c58044005020729950340303801e9120f8000801c21075428000c40162b04c5030002c0000c008001140c10910101c08440b108070b00300e540d075000003018042c0d41c540c5000542811245062000300306401c8034110712a00ca4110000d4124112840c289000c0c42014403a87c4280c44602403000000e000e540d0550070040f1a000389a10460300401420b245030700004c441c07510400005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 944172248 1250 944170998 944171017
    0x10602071a22050d080301090f1a1003060902070809041805070e270307020406151403040c0f12120f0801090c180f0833100522140402010807030b06 65
    0x441c884803443d21517100e4009125182c0c0036840e2440d000062480c9000340c8a59680410f48028880300302c00c01c20031b12044140000007050707a911000304908009100800f9031070700a01c8a03685401006040105031004900030b00010500e1021000004000080c0801903031111188170110342c2d2a010a1407103042c3c03003ca00601e41d2402817100e622010044001d00c070042c02030b182804079035114002010711040f100070050000d140c000c0010000c464040103140c20034401c4807800440360b80c4140c940e450700c601d50030281d60140c68414141c100154840080e400d900941001c10700c00403c41000780c0342802c14400c42e5a0151220800c3c000e0034891000d03c3d2203400c041c15240901521403954200b4240e036401038450a20aa0404180904241031051080c0141101d5808004800002507440e10800b400c00400700d440040d000c6150380e55400c44000f001150031012140c000c48680c900c0681c3c005100c420002501c031014440580d90140e8241d40c05015420003141c00c10301580807880b10704c0348920b074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 944173498 1250 944172248 944172259
    0x60f0f0a030e0d021507030b0102010b040509030301050109150c02010f050d06080f0706050f0702040e031c0221060f0f030c0a031b060519181d010602071a2205 70
    0x14103801d030594000703030070312006800301e40c4258111034003a6514810103c03c2000c4a4079080000d03841c030b01c00e0f0006804804184000300703508040c1d174046001c0d00e80030382e84c1c200550000b0005000959100d003140000f044409280d850a940d045000313031403503080c94006070400642402841c280e6000d0411036201c821104810801295902c445980f00c000a0704103100034010b4a4001544511600c19981e1004090030650324180035a801c120062100c1903040318680414010280076001b9076400750102c00310341001591b1110406524241000c0803822030100484490522070a42c8580c0217655581c81c0507101d801e042420100000d113080ea441b50390b640c1c014101d1002100300003c04200301d410b840a00008801b6545813041680e45019828803803141c040c80e591003040e058800c004400c40b40c081c5000030a006038840c403042c003c400c0d40b00701000040244078010030500c1e504016660050940400e6400c4036905554404000e01c135034110203a04402038401c05440800d00340c208001032000506 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 944174748 1250 944173498 944173507
    0x4090606031e12091428060c03020d1b030c0816030309110d12081b0c03070b010501030213030803180d0206010303080903030402011715100504030521040302060f0f 72
    0x2001500b140350702d8040f14103505642c43c0e036401c140100d84640a9a507000c50f02c0118074504800d00c09442c12414070403810800300f0001d940070f00900064880500785070368030f100d001c0e0000e0401138503041038100581c08000588003007281c2c1900300855180480d901d450704449603450f41c10490300c640a000a007070b41801917000d28504054259100c603100c14440c900554028110b00100300800300301c4080502200342d40d00031811b4151080d0001544441d040c0e0b0304450605d01c01c003210a26803c4040106616440000c1040500014007a901d005182c05d107401c1d4509140e00301c240400108a21000300603250110100c1d83d94014042c0b11182480e00008442c070f40c8101d217400a541381400e01c001d5010039090307000300d0721280010044034071960b01a125410109641401281540c0c001060058001041104090950750780341c80b00e4502d0900ba942c2a40710ba0071070510034100402d502d40400c0d441250600480c441805105a80c200e03074044590303540720f00041c4d000c2c2515210b03003006072915210006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 944175998 1250 944174748 944174783
    0x32c13240e0907030201080c0d180c26030a03110717030f011505270a06110708010905070e0c1201090207060e0a020102060a0c020c1905091e060409060603 68
    0x1404601241c201031031031400c5496800e10181c41e080207000182c00290704500181d1035a030314030028912130000600c0000ca00b18040c100051215103210100c41c52040e070401000741d65001001e0a5540b414501800d42c850b45401d0059560b2144480345424540c6442c0b0740700d00c6100c01c2040d40c0782c40d5004002e0f082c2c07a05041d108044c0c0c541c402c43c1c0c920030700c904a000101e0f900c51021f0661140382e0454840910308000e003010054949012903110503004164859417440d07481d0030211400401507030311340001008e5035103040d42c14902141c0060242c0da15002d05100800ca00040d03180840381008840c4c180342d1901c1201c040b0702e12403250f8040035000700800000d4003440e583c0c000c06841c0e000303c0040048072a1030f03911130b4640b505c1020190040c3c3c08007010032448185076100881510042c0121038019045070302182c440700c0b2a900b034004420804004028606101440d658003032102c580e508a222803451011840c1880600031a0040ea0f0b03404038082048681ea00580c05950440841c88501e030042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 944177248 1250 944175998 944176061
    0x114040906020f031b0f0702010c170a120605010c020d020904060b0307031b090204050d02040c0e13051f030807060c0509040603050c19120303020706020f0304030c032c13 75
    0x58078051316003004001d0030175208080c0c505807040c0c04607500342240f038011240c00440d035498603003a0944101c40d0100a100207090f003440141207040c02c0c2e41f140a849803c0301100401c07101c0541c00a0706024074440c18000681d58401544d003041e9040780c20403010b07107035418080020304000140c2505442803007404410f0042d2410b01c0c00d41c4942c1529403043c920344860428060780502c1c4111600000c00702402d10040c40e054001105400c80fa18007020940580d000155445041400c21100b80f961103060001028911070399220410107a0488460186903581d400e40c1072007031a1015140c0c3e031b40c5a9208030030610a008640040200800502620b926401c00b82d440d44c60501076248601b8240c502850f40141c5c140218040b900390382420565104141c90580180d8042041200c400d5400c10001610440001c048d50190b8042c0e1742d2019242142e01c0d0203444080300d0300d1104240c500366014400602240613280c0e1002c0010b0341c03882c4542003d007901d0000303071481646a07441b840000e8044a10103244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 944178498 1250 944177248 944177251
    0x3301a030d02070f0906060509280b071a04030f050c07050a09021804060503100c090506070501141308032202030709020a18050d031b050a060902270114040906020f03 73
    0x2400c2104000550b03905e680030845105109410110b101030000d002e40346000214840d0340e400308241010344040f9500c03246894111500440e04c10350000c21303200e00740005580f0b140c802e0740e240e10046181e4101507c001e09040e808040c000d0801500007841c0468100c244101001040050858054581c8801400c0042c0d0400100e003440340481c1c4031000210310b428080c6404440006c0d028082009000c1006806010481000400d00c17010400004107600c44200800495001c0c2e0000a03503401d904d03c0c0000001000313812403250345c0b2903040c0540481d00c51001c907500103a58105140c41098035262000a6164220020b5410f000d010000180e807c0030360018041c4102560b25102504140312503400191403500859400c40c0c1480e41006c0000e0180c000000c503280e01101000203110a9502e50703182c8100090200c45882e2100403480442c2808079106400501d80c036141d003461041d01d21082440f00f030510540c80c0c0020701c020700c110240c440d60b10101324160051001d43d5030700c400da41d110f81070350700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 944179748 1250 944178498 944178509
    0xe1009051e01091104022208010231050f010c0602271206040605060f0a0902040602070603090b04150e0723040507050316050f0a03050403301a030d0207 67
    0x2081c18550780202818070441858607802000c07151404440380600c0000d400445c04600400c41d2515841d9154032048021001840e0070b500169803020404842d54a82a50a01c01c01c40c40c0d40051044281c404003805110a46900b80c82c1d01064000c4040122407100c11094050728161002404020322840d400407000301d00110455101300f42c500d802844603e030a003007044220764010f440401c2c00200103800c046e0b0855002050600c0001090000400034280e50b4413010300d65900003020000e0079018070611004001c136040800648030181c44503181d40030014030041103132000c0b40b611080c034072403507004c0b1081c09003010450729013035124180102d5005600222181301c16a5801411492501d80102e500c22480c5980b0f0038250303100c0843c844603c00c0c506004409102e4188906012500080d01410101a842e50049180d0a0170300f406810701d01c07984100d03e40340525540d00c00c2c544036044417625030901c031740b0800507421844000d050111803400c01c1156245c042d0072840c0203125030000300d0324180c0d03c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944180998 1250 944179748 944179783
    0xe07030b0328060c02030a0e120f120406030b010f0e040203100b030c0d050609061f0c240f091709120d080601080c12152205010602010e0109150e100905 67
    0x196212000d07a030b039008104a8000223881c1100c045007a0902e000c40024004038039045410000e0404002d0342050100300c0001c04420011604200320b07507050003160710340d400c00e003070000403440141d40c028104c0040d01b40f0240625000000300d81e11205070000f42c030041020120880e100c1c00c001c0b40402c0554450385198a40c3c80c10600440d885161000790107002d030a0080c0440080080380940403120724150b04c1d18818403412110398404607141d0940904a02d071aa50200035040040c2d4034641194072a0380440c2641e860465600300288040c00b421213110b00c60b00c40c81c0d4403401a580000c17455181c08080128030b011b03103200006002d410030324142c050803003621100e44560311100305d11102c0c024040840642141440800d0384c40200b2100c80500000150205664031552102480401035a06525190b545c0d034800411071140d081c401c18800d8002d0b0b000910650f6103c0d2120f20b5001c60900011501690780d0250388045501041070402c0016940ba05014031801818400d03200c3c4040c00845501c0b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944182248 1250 944180998 944181011
    0x7032003040504060605250804080f060f091c08060a12050d0f1d1005070b1f050109060e041109030d020102070c0506040e070e010905120a05070f0e07030b032806 71
    0x1203001d00252000500361f505d5401c150780440250800104092005071100c00f405c0101084402c414090010303000d009800401060804002c00e0740070000052412000d60040c24110300c0203901c405c06040c1c1402945446140340d1100302c0040c0d0352801d590301130071030403065118520400c40c000c1022484824907031a40511720b802d03400305945405000c0d0b13150324504081445810301e0300e00050005c0250075285030850900040e56100304142c2001d541070445010a9504040500c003080f0b1854040c08007868001e00c400e20f40080034146103401200750f0303c91900c50803050031300945101601c0900704018104c6860301c1a500002e8000c3d400f1010944200141043c0403ca509003201158211965268030032416594038104035000850040001d040007560382c4e000a8a40c0c0d13a0702585100320019000e800c514501d440c0052a0100a500001803050007000400c8118594142154444207900b0041100ca9044c4000783c00c294003800c1d0940c0100c0f03211048806032401030b64074020140315441c01c0012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944183498 1250 944182248 944182259
    0x1207093201020a0c0603110d060905040c0611030912030d09030f0809070e040f020111100204260a02012303010e010611010b090711010b03010e1518030304080703200304050406 77
    0xc50011000141c01c03c0c130110003c1040502c25401201e0540702080d0711800c11415401c03503000c0c0c0d11664011214141c542c410b1000344805400d1000061010f8101000e00d0540c0510700c2e0345900800b09030358411102c40c07089507101c030340610455400070f00111007006441b08925025044441d1030545100040d145000030b486100d0020b14001a08c005c2c3c100e4404d10f56a690340c1303070000c1412503002c03070421040364a64860403604120700d4421500524025032a41d0802e60a00c000d0481803c02641d01c4a40c0303603040032544c00104440c0180c075020720384040e203841c082c407511094a20005107a452100000000180000c150340e086060b10710560300c4240300d00c8903038090790030781e50011103d640c8020398101065500b40a480c1030005c49030310000100d160910240040d003104c203610b00c074401c140c100a680407044c01e0301010860b848003207072110074800541d0000d0950749000040c80208059000120340e0103160180506451103543c02c1c0014080c10181010b1a13100e40042c49442d000300c2c01d02401080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944184748 1250 944183498 944183503
    0xc111507021e010b03151b07211809140c03072c0a09090b01080307050a06090609061e1112040f02042304020910060203120709320102 59
    0xe000d194024000e201c10034414108182108609818035980d5241d40740c0d16490500403034208044180b0030506600e04a5001c8050207400c056200021000700030207000030340c0561500d9240041c4104000310820704402c140c4040805035002e070882e5010000004900015402c41d24011030200e4111541e5291540d000c0d00c2d07030005881080110b0705c0e0b15a458001c800e0395070b28800103850740315042038104001010814602c66500601410b0303407103080101c24804101e07103c0d070040020320002d40c644107036a1036043d100c4132108030043c1401c1e1103141d444140012500600c5c038070f0b5003000c0c00b00010765030111040a4007a40c3c81e880900e5034142000c84890403090030640c0d03008040c0c803a0410b00e903501e560b1488a142000082240d10503550883d07289e16403101e4142030314421001d0fa5003007003230034540100244c103240100040c4418940220600c10281d02005079052140c440c1002d03400ba859a010903140c644454026882900e8412115950040700030422114080007040d219441c0404500498 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944185998 1250 944184748 944184751
    0xb0301181407020c0f1c06052202030d03020a090b21060109120803040f0507081014010f050409020a0503060c0703090509060102030a140c0115140315130c03060c1115 73
    0x1000b44c1c002142c8040d003801c1411020469200c0103040e80100300340840d44419181803028141d5110342c2d12000c00410b668040c5085144d40882c03410401c80a42903400281c1d540000c405c440304241d00070403100003244c022078840001e00604040503032221514101c507801036030840c42002064880c0404030b11070b94014840034080d41d00d0045080a00300c05619100003da002a00840340c4444a6400c040440d0052108201814580c00601000158188408140e850b5090a05041c10a050040042403103103107682040300c009580104044515000182d03007005a584866094014907007001411010080100000d0340f2030344442c03910f1b5448400703004103c1c0d01160b0850160f1b004000150080307000700b00034994001d03425401c6140c8060940040d00790340598684001ca480054030a00c1254444a030b58900a00181c0003408034600060700035110382070262040c00c8145190a01500341b04240b66000040e640010b4140200384072030100501d066401c804c1508540103009020080d098045040d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944187248 1250 944185998 944186011
    0xb0316030501030506060f061204030e090a06061d06070b2814040602131d0103021008060d03050c030c0102030f0603070f0e040b0a0635030a02030f0c070b03011814 72
    0x100aa070390b8046c1844081122410b8030b1b90322080c2400910081041050003911480c800d5846908120368141402800312014000d0040c640c2000402d0240941c814103950288290580880000082501058a610038400080c1440c0110405c124841812200302001207010644004007180304440200480c0c1c0d42c0380325002e00300c0c2c846001c1000f2550b16006090492041c014000074103544000800240001030081c1440c0d84d0840010419847e0852101d4589542401d04403c0307440d0002c0000d0b00c03030008600040c28007101080030209410100190f401c45900903000715600d051056141031510700c1125810f120b80300d540001703c0c00e41104800d010482d00c0224101132143c43d40d0759160361111004001066040d964034002500784522041e10b074010b01401104048044c400c90007800d5007904440c5980780b0f0380708010b90800260300004076044401c46581c1350341ca8808030380d8440d00f080350a51001c00c2d41d075400b000204030400c103001d08498141380786208116844513000e54105510301110348 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944188498 1250 944187248 944187253
    0xa0602213603120a08070c05070b040f080d0e061606020d060e040c09050c04050d050c04020301080d0206060d0b06040207050f1905060903121605040503070b03160305010305 76
    0x501a145655015110031807403064610703044161900c0c1a40e0107108100c0092100c803040d291010a07003000c0c001200310603034a540c25468140c200002406441c8040c101e0000c1107505807891080c030000b4045003002d4003468540c15680c0f0340d65080381900c40081e01540c42e01d8003868643c0808a400350050103201e41001d026a4280310003000220804040b0074400e0718007075001c00c895040d281e8244110f46c05440c1c510203400c21402d0500b0004140300e070a402c596000f5207880c043c8900a40c221094800b00c0d00300710b8401c0305215a616005d41440c0240c42030701d41082c004000071410a40101d14000800041d83c21624035503103550401c01380241e0701401401c1111654003082c100d080c16002008020b000c3c10464080442c1144003900d80f4401103469040050501d411a0400c0001c0c0041904100d2180c02107080070b141c0482040440744c0039001400044000103001000c5005205850080800400341c5804541e500400c0c20250700c1202c10441100711000315410440c024411103040e690030600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944189748 1250 944188498 944188543
    0x906020610030c180605180f0f0103080313020a03020a0e06011403070906051b0d18060521070221281d0f04020c010e1c0f18050d110a0602 61
    0xa14041c441130102e0f5414030961922008035031a12000c128180c5074040c00700580d0103261420007021074040c040c04450582c0607120040020031580e009483d00086406142441c0c0125840050900d00c12640000c1d0010007400002640311b481c551418442e1200381c030307000c079114807410829409100444107400031400785c50083c04a14803e502034041c0300000c606140d954003210241c5e91602003801d444000180c3c03d01c42d11400c40d5400c048140080c20f983c18054102600000011400d8800b060100e074076010010004145510070042d01c500c186c114546609000342000c039030500c0da03001420f5051042c407151004440c03100880c10040406005640301402c1300c030300c201d070400008607201c01c0d01c1d4000300c20b01c11204103640c2e51000780900b080b04000001d580140d0314030300f400d181d04401c600005041d242514201150030803034060b5030700b0307051070030111040100d2540c0000320440d81103276410061f034880712000c1007021848011038510880d0401029035980000f240c1d00e803404051040060711440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944190998 1250 944189748 944189759
    0x10b04080c0603131e0816020109090231180507020c010804021c061d10051b1801032a11070b04060806030102040302040e070e060105182e0906020610030c 68
    0x2140c5032070001c2d0203442841e0905c5030b0749850406802482041e119a00c084641c2411580c00c1003900c0300421071030350258208815a103090410f00c0440e00a140c031748180c610481e01141e0b4098449020b40210022564040300c0003d4041c001d020440b0076102510800c072030030043c0d6000d420701038441c03075005000011082c03d010042c811444005002c6540a454502c06510400a400ca40110f075162000070000925a900440191030340038207800c8031003401e4000d241080d03900004580d40d92101203224000b1100346001200140620421203801703641c017010180001e0000040e010380000240d0350b03022074620001340c05440301018490700c105012304000400442d8014036080d540508002c000504003580d03500440c0075907810010180e6180c00c01d0b5024003a09441e80c200303507084031080c80d0039410202003001c80801441c12481341407164469034103200c81c0f1031000382000c102d1403103013003103400e41c007451000074003250000d00030f107000360107a000010f502500649401d0216034000c103000c252280b400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944192248 1250 944190998 944191013
    0x1106090d060f0605280e060a050d030c0206070f0b070e100c0302011e0501150c0201020c040e030904091410051005010e03070f0e100b130b090f09010b04080c060313 72
    0x203900810403940f80c01000a45a8070b101c0c00d100c40ba400b8451026000256456200c00e610302070304000100c0003076a060003120380b108070412003030b284140c0f05903042c042c1c281000d0f2480010150020350141001904c0001c004407100d4a0170800e10507050125581c48000040e145001c0210285030011022445038414034422421803294a000b400000744900d1000b4003022148040c0010551158071480100b000160a203000f0400c81c2c03031482e00c0c0d0804500f55000139107aa07002400c60348102e48820703880900f10307401d108441010400070400c00220a0f13038a070510345803444002d018001e0154482102c04060203005c0c56100c0d1200e40305900c900b5041c4001542c055801c800b421303415110b14100450340d5840750b00c92070081e1188084000e440d151550310100e1014468208800d140c3c2c090000e06080d003002908181600d521450160311105c3e040c2c04070300f03031421840b030840d403009081000040180390800100140d800341c1d000d48042c68101802e0086602c0156014001c0d80c240340c1c1143c0102e00700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944193498 1250 944192248 944192261
    0x61706040b21030c07150503040803150306180d14070b0705820504080d051c090f06051509060102070609120c08030307020303041106090d06 62
    0xe1207411403003060700300300e01c1c1c040310410102043c0e880000c0b1401d407100100103080050030310319104207110340312410081c083c0c04003410003801e0300e802102085000c00e040c00303d175500b0403001d0100c880d03074a025602c0280c030280140b0b0744601401020324044400e07200e000d0ba50000c40380410014034007003d80da2400c8075508014190403c00030240500e0185e49400c51040710030348142c040300d000141045010010004100f2140005240c10720034414a56100340383c1c810004560418880e81d648170303c0743c41120801400715070801741c1c84180200002c1134005000d88103440e041812141c2c140d544010984007807050340340d10341e00044400780d0005006080e4110481d46071054200111108250740d950003038505c1074a0a4552501500c10504541400303100d86500c0b01003480100b20251400b98082c01507200341c000c0320701c1e4000c40c00110080c480c03101060401032511104495683c0303030044000b9260f410541e82207503801000c0000340114641750041d510032040003000d445100a0341c0d07858ae0010084c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944194748 1250 944193498 944193521
    0xc0204140105032119091406120601031a0303161e111c150603030e0427052515140a03020a110a05010501062a020f010207030b01060c060606170604 65
    0x810003020042d41a0500c010b5001700381622000700046c10300c0f129918143c2c541054900901081c031000d08800345440d480b64003c0c800782000a850002d480200d0995814030003440d80510001030440d8a0311402040000018015101c1072000e018100f10003040741841e16001d4000b10703201149092030314155141c100305603069004c4403519161071340c03000032004611040300b10f925950392080041c140c001448a09142044804010010428040d1200340310340010700c0e079008804100001c10040d041004900400c0c00c41142d5408400500c07000780d0a400f1400384580b098440703401c4691046c081c44141e42d02143c0040050308110340803404070000d400400364941000350a51408900c5a02804200b01c0303180540c001050035030414101a1080740081d0b04822308501203910030320913003000300140d01c440c0d5040701c2c45c0905a0364040102c0c40d040c020703040039107084090400025010b40000030203505621a1600340310580c1e0724441941d542c03402c004e8400c500382c0c5040000790341d49001c0e40603a2241d01e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944195998 1250 944194748 944194813
    0x1a0a0e0709080105090304153612031d0103090b0a0b19030c0e060d230615090a020306030a0804060207060210050708062101180c050402030103050712031b030c020414010503 76
    0x602c5429270007445141e518142012848164242c40d0364100140e10280524840000041caa295002015030811000900480c10b481c981c60480d40c0c42900081481a00071070426600e080009403140103000780800280f0a280402c050704501c03140c0c10721b83c1c040340c0e0402d0b1810440383c83c0810500180c40028440c0b948039004a071a000003401c2c11807645481002c000c0214000c0c20f5082c061440d1010140074030b00e80300c0e500302000c1c2455461800c0140c1c02202a00b0142e1651101c101081c9060342804005022840105003c22901c0d80013031000e00325916a0f00303d0341d0050f0846000022500c06444c200d00242ca8840003610500b04050341e50303c80b1600f605404081140580540d0841c0d6001c40c80090b0402050b420b0f0b003e2084150000000c3c0801711002c600d036500d995070b11651040039101b641503002e004485074041c140221500308903110315502801c4040700500c0c0050062181c8070b0f040b8401c03442e1000915041160882650698202a0080555a00402c2a10240805081c03d2103814 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944197248 1250 944195998 944196017
    0x1806020c0a12080a050114030a0f023d0c020a0509060a05121509010c1b060f02030412030e0c03191401020c0a0201021b01121a0a0e070908010509030415 67
    0x140c10140031214110b903980d906180b40c200f540c5000c1c141c84046e8865a000720840c1b4203010103a5003c245400607a9000c000c0707503c00c0c101c2c0c2c4045281c8412000914941c0102922030000707855008100141320a00d000b40083d100540d0141901c01416a49000e50041d0245074144480c0c2040103500da04280c00503c8400d50303a030358000194840300d00c040ba4149a8000e072080302100c1d4002c182060308445010000d00c08103203480750017881d00302c41450002d51102c2c0c0c807090b070043c070034558082c0300e03000448042550340740344c907081c03040340709044a134100002884d0014496083d0000708035801d50f880000c0242c8008003040300c80704003800703003d18280c0d20082d07100307114900c0d000244000c2c4901c4c5d0102018001668040c00060708103410813401800440e0b0603044000c1e50782e4441d541d91180300d51201c00003404c5c04110700030ba00f0300340c100ba0010b8001140700300102e81c1c0080b540400d44600c0c81f566558049689072044076003a01e0065501107401d50080c4014044c5120401c2c81c80101b08051a00540e00b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944198498 1250 944197248 944197253
    0x6040804140f10050a1b12050f07080705060429070e01020102130906050306010608151908061302040b0604050a140607020a0f1511030901140c010c09140102011806020c0a 75
    0x82c100ba10040e40131030070000310448060f81014040c022118225a01c0f8000d000d592202020300b1040100c03281000700008418440c490454260b58407036800000d03081e00c414007850100d40c6c0c0c51040d04c0959088043d142403a0003c210803c040703004104142039848070b501c55510a4860000b0b1110791410365400744000b2280e203848031080002000e8200001c14003d2414081c54100380041c0c00140030001020300300500003410101038002c0b802d007910501030881740c29a402c10204225084182180501d0042c40140d1040c8840c059403240202c60030081212100100b002a10543c0300c0c2e0342c2c000c20748200401a4416007410651540c0000c1c1a080c58280141d00003141c050207900700402d041c80406041c0407003094a40782c0e50600350107040c0311070511030030428a0342d2030140020013030401c483c3c9604203114469110070303103107410b29101c02400b500307031040d40c05821441d42d0300808001d0308242d1a20b01540d0b20502440b50140703002140798403194425100e8030080c0d80140c122070040c0c0b00b400c152000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944199748 1250 944198498 944198509
    0x905010209060d14010b070b15030703060f020c06162a0605040804080d0c02091f17071e15140f030a0c03200405010507030e0603040f02090906040804140f 68
    0x1c0f018440200059442d44031403c0c01c04246040c0c01c459001c032401d001d240001880301e0800ca80240c02300203100114a00000000e01d0704203a80c000078440750500a218101d100aa00944102040f2609441d069038941080e40000c40a22800700001004815104505074030f1921507082c041c000d100605031003042d1b8a03600c05840c000e8500700c420040005080285000a000d5000c000d21946080440045250009200014080e005200807600140d0b0040304000c0d4181c4100104070080c1d8400004a404401036115010ba20415000c0b001e400310000d4480c07c0005040d040c3d60400000c085c12625013001211b00394040f03140031a00110402440e14407210040103103100e0003002d0004181c09201c60703801003d0710100404071402c0607240c0d001601005c06117042c1d07400d6407000c0c64241c0d2500300505040b10740130000044035070007120000a020a02c003d00030001801c6000b990b03051780607140e0940c46a940c03242103070094440302e02030109101075000c90310b805100c4c0038004c0006910810310b600045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944200998 1250 944199748 944199757
    0x30b0d1e0302070e011a0a1e1e03050910020304080f030a02040501110312070e0a030c082b08040807020f04051302040e0102250c080f1f0c0f03090501020906 69
    0x114204030103182000701a8100015409401c0b881100203942d450f1105000544461000302a17503040e0103d83d000445102d1480c0d00941065400000120080c4000c05402880259100c4605203561107c00810b90701a0089501682c0c00e8002000880c460080c10002904050070032070312250208070340304103502180080c40c022850114010f9175a440c050015108007084418041d01c0d070018400361000d0300d8800681c540c000000d040958800091a000070814041038000900c2a414a600400d0740600003407030b00310b132101485c00c5500d0232101301c0c8502c2c1041c420218060009810a00040019103010041c080151010f004100a944820005010b4407070803103c030026005210702c0d4000f50301e003500605221a03000c030021803805520f0004000100b11101002c001060130135408410040b509018100500015043c2c0e15078034001e10340b1986070b4034601c40054224981d0003003a807404c4114896150240d82e10349445c030300303400042030540240901d0324040d69195801c1c000c03400c4a440f1b140050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944202248 1250 944200998 944201033
    0x60319060c0e0406080a0308060a12030804050f0604020a032405011710051501050c030c0319030506180403030c170a020403150b0117090a06090308090c010e010807030b0d 75
    0x100301d84a07001c0d002440c0d4000d001d0058450b41c10721800b048a032501149048001c5d400d481d01580650300e07040810040240c3d83c0c4003482070501413412809040d070215440740030b10301c207000f070f1608071300094440c9980700c0041d90041e6010080c09400c00000718014209003001c1840380030540300c5c1510040d01412181c09a01000f1552002070040031120428000b10381000202c0c4010002400c02c0801000c44443d0300100c41d041c03000c0091950700c400020820ba4007802200821603682c2ca08030200440701c80001f0100d0000b00703040a020400c0e40ca018030501d0b050b0000dd03200b06881d917459403811006010040f444c8405e112481d24002708034881c00240c00d109149590000da942e034554640034480c1c25040f00c04a04061a0003000711843c1c2e4070915007003000c80c10f50404070450700d03541c0d0781c2424100c1c00000103007141c3ca40300c172038402c26800003807403407091000300156054005088019500078480441c2d81e8000b0b441d0000040c00d00d4020350000c1101c800161007000990281d640301048254540c882 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944203498 1250 944202248 944202251
    0x106240c05010f090b160801031115040b1305210a02011407050f300a0e13020a08060f1e1315030614010614070f1109161101090b0f06031906 62
    0x30010348458003a440d02d01d04001b460a9134480d8034503141c41ca00c8003804022b0034481e10400445044c81044881130b10081c6c040445041d640b42e2060042d0040700440b48102401041d05070803900c01d0b00703920822000e051a111000c1c1c02c0010721031707004464061105003110519603003440290049041080365400e0048050000c081215081c490358001c01004000c4d4006004840350840305650b1103001d03903400b04480d08000050300090f00c0001e0aa02040c00641381c10761010407147c00d80355204900b940200e0f0145c81000c006e00304c4409100400401022641040100394412a42400c1c00e502d06611000070241c00154422a040d4030750458500342e00a0f03a54540700c6051603a940c03501400140140441c0c00d041300d14000d2905016058000c0f0740001d804c40052420150910804420000e10b2200040100e10289410900a60680250200327400003507181084007040010510484c200c0f40d0300414000d642d9502c022000b001170900130000c94050080b02e004c0085403c8010032818250300c6210b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944204748 1250 944203498 944203501
    0x13020703090e09010c0e09071707090f050904032c10050702031501050a06050d0605040e3f180405041208070e090c1308120c0106240c05010f090b 64
    0x8034200000c041c0201c0d4160b45000d040704c0c001074101c400d40401c010141c0e402c1d103850795a20000d035803180000c10170203105e65591082200d2b2580c05940c0c101504c074001e001586541c0c44005200d07014504403001004203006002c0c1c88810819081b1102100c200b4180905850303c0346008108040e40c184110780c0480c00201c0c5280c00c40c641032005d0328071020800d800030040c0d8582000280480c010f4032076803051090004040c00c3c0d0700d540da00410098100604140b04000d10040701c0369950082a6060803081a0110750f03603036034003800a6030706050130f840ba23104480c0c0c544130862940d2075126181d20070301006048180d42e20b80e2640d00805206034000c902c4ca40d10703101e15840140060320000c0140040250304441e640c00340d9a07030342e402c0d0f422850403911030740c0364002c41c010442300c110b15820807010f6114030710451100841c944014040304a18400178002e181e030751030400c100b23a545110300c2c1901d140c100b01c81d0802c041c0b049800c090014003800000c110b021084500c0000c5070b81e684c50030b40d00152a00e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944205998 1250 944204748 944204759
    0xb0c0f0d0c0b010509040c06050c0102070507150f030c050a050f040503070f0e011401140a0c0209100911040f050904150e0c010e060307090311120105010e0a0e0307030c0206091302070309 82
    0x1c2c00b41c01814180c40418003450300c1d03500c007044005a40500d0b800d0260214000100344025416203080c540d00004842c042d5494246101c0e000d01c800f00b4030000140c0342c0d45a100c009201e030283c91203030345042c2c5580e8207014150f1002d8030746802503802812283c009000001e00c0d036404010310402003001c159250320403814408086030301340058104041d09074407001d0a54040c0d03400303840c041040c1c005100c0c2c01e84480c519082102c0c20403c03110081c0d4003c42c44001d100d180e144d03003a2018200d40200008010351100e80f130860500d80941d201d00c07400210001d008100714200118580c0d8081d00c41e411002483c03c0e200041c2d8111000300819800c260700041501e440340d40c0001000513101400c072046825031800400041c01c000ca030b07000003442a592320308240800c0d242d4142c14140210054020320a035138544a01740c00340b8108a400010180c00c03c101d04c40046400300868110b250181c1e075003500569183c0a008507035101700c00d00758001e42c106032030b040d840c501c610240094910076580c4540c0d83e407814 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944207248 1250 944205998 944206013
    0x10090c060206040b060105071406041101021608060a0f0e07080c010f050403020d06090c0513051b0702030a0b15040c1e03050105031f09080c0d14130b0c0f0d0c 70
    0x582000c410340d0710103814000860b0310f07a014240c1c02002440d1550b41c0c0d000c1440c00c070801d40d80403058141c4078840c0809000030820241d0b4010586542a4202c40003e40e0200b81c1e032007224031034450141d00e42c0050303012035000511600318010007500d80038040385411101030442e18106050707010920035041071000903404d40e40110142010981e42c6130080c10300d030454000800681611400501c0c2641d501400010451140880c00081c100104172212000c1089180809004204e451089140d107072082c80c030907100c982090340e41158002e0700034045400326a0383c01400020241c8609420303070418091901650740e5004080400b101503842803540018201181001491125400e0030b050601c0c006000035100040d0070b00218440c00345007603510329203440c80703001018207800180c05a03c000440e82c0d241e890004214101071416584c20301da400340389400000e20b010b15540b96a10b002c0040c801c0002e035826a02901080e0a00300c19a04007482d0810071514042c009000030340880c6031940f400091200d10f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944208498 1250 944207248 944207273
    0xa121103041503150b040b1806040303021e070f0b0415020a080a030b0a030b040f0b0f15010815040509010c0f09031244060409030914121009 62
    0x42000450826040ca800095890300038030b80307103007095074941a8551402015550320001d0440c241c02e2569680ca41100f1001d950000d101d00d00003201c5024148894202070707046a0480350140d01910b460308905a6600b8008580c0b0602101481030010104d002c00300441c41d00c0c01070402c6d200440c0d0310b614150303002c1030706100c8174003010079508090350305d001151402044a940c0140d41c6800559036510070005071026800e500090100403400e41007002300010440e80a54070703030203909000c01c1a40c42d4030300769901c80021205554100356040d408121940100044ea8001504034440d5900e540003102190880700c040ba4050090781d1120b80012110350464046c401c2c40c0c016182402d0650b045480b42d44030101d1521441040000040f0640d8560b050241340e104258516035141d00d42e5911585000100764502c003611404442d1080482c2d242d16080c8500d8817400e03819220400d002d0720b003800942c0c03039031000034040b5040002c2815403164002c0602042d030171480440d81c00107001129050242c5282c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944209748 1250 944208498 944208527
    0x5010513210c060e010213030f06050c031015050d090b061e150c011e0c020d090e0a050414011815050118020a0e0d060c111f1104080a12 60
    0x31507003080e890358000c082c80c0c4190b400c02e002281c071510040d01d50340203106206458080c400b90030303408010401c2154800f250070b40150014070039611042030108542c44241c4049981c20b0920f41c003000528a02c0503030f1502040e1500b0301e60300f407203540740e0380501f55088040111a40c400345010090280f4080300ca03901f4203258484208403c01600c80821203000c82100825a20b000108a14048130400d40000e0822010554010701c030152034504030000c2d054101c4010054002d25907070007240f034802d45030f5400b1500c0c038250000c03007622103004407030003000081c0c01038825820117842c481a0800c00d005d00e40300c00c408042c10307000180003424442650070110600200b52402d01004001d407a80c48000a68440b00207400180e2b41d4031016015a115040e14010a40041c03040c1c2140040c856180d000d42c20780e941c0740c2c03108a40c9100d0a10050b4460b003074904540000d8600050141418040354403494074640e801505e140f806403101d151914000130980d04039601c01000754540c681c1a40003c1c801c60756030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944210998 1250 944209748 944209793
    0x110307050a260102031905041e030503010311090411012303010f03060605151b03040806160e010f02032b020d020307021c0c0f0302011b050d0608030910051605010513 73
    0x4002031b90542001c041c041360100692541c01180034003942109049a00e91400d0301900030000d10300e8080c115030800d01c000d41e05a6244604046503081c041c80341c1e44215800458140798034101401515006410b00030b0b11300701b00d988828031960303045e808011400381403000858041103155103000d5003a2042c0b9000580075008000b00300d0081031845003990000c0c81310070009004d8100c65000107156018541c04030b121b610520082c4040c0380412a021900404035940d00c0407000c0c80a401540c498141400a900580c000c0014500090552069180d4041c3c010542d00d0300b8500102c500050b80c1002583c00f01444e8000305100b22141c0400001812540c810852000002003440140c1002129800034004c0510b002d0038504162003944440080d9003512006131a5061903a001000350308640c41025078641341c0100451040c3f8000242c0d900b0441c01440e500303001000100c100d80503008640d0944448036903182c65070000c0d10038000e461240900100c0c0d0303080c5007a00d0a12440044d48140c01c5030451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944212248 1250 944210998 944211001
    0xf050301022a030c01050a02030a050603030a020d050d090f052d100c050f0c010501050f0103061a07020a03051f06090b0f0d050f010c050418050112110307050a26010203 74
    0x1a080c0d00100c10b0300031031038a80342d80050008032a5086206015450710306501e08000c10414080c02ea0140d400740300500002c211643e104418503940e0300c140c8008002680c0142c10601400344100c00900344016841e8020031005180d0340c510509006815003114640c1062041c0d01c1e100c014610030020704d0803112000c4d1740d42c02d142c41c912038861810030a0009807644400e03482003081e002c0e0301260f054200003004d465492010070f083c14000d050a0040038404c40b00010302001540c400d000b0082075984034100040080b42c2d20358a50101d900c20707901280c02844001c0c001003c91000c0c00425a01400307002c10250600c1c13080420700881d4400e41000e03a0003441c040480c80141c860340e45c40b01c5005415100744035401aa8281030345403030100c0d6485c0203150b080030400c074072301e60780007015001300c522041505414501018888041d83c0c800d010303815450484901c850007042d12a030200d140040c02034182d4600d2a00c40f000310310b4801440c0c0001105074407440440b0142404080c00340c803c1c1070711100842c1076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944213498 1250 944212248 944212267
    0x3060506181314191407050d08030a02041809020307140a060c140f0d23030f10090203100608061c0b0a02040b0a110f060435030a0507080f040c0b220f0f05030102 71
    0x90280596009d0103a50340840003a00e01040d55048402424029080c1a0454005035608005d003c060308220f000f8098100001440314940c0322446440d038000300300c504c400381070400c2102c80d01c0100c0003d44036100382c071300c001c0a213580a01031085880828005051016903048000e4203080c515500c0b9184601450019024607414070183c0c1c0d080f4150150b1140d9a80315044030402407805500000c0c03d0b584008140080615003980c0ba0044545648840c142035882d00c04000007031032030326001a0f17010042c10f40c1c00d002800160030183d000d41c0a400050500351510454142131308204075900101e2041c00089000e408200040325541800d270004101516060f41e6102075000070841f800083c030301101d0310300003541055042c0c500c0e54007514920b507100e1a280500e40003402c41a5051408103828401007580c2e071601100381d611a60b041400000c0c25071031309001c9101640710601c00b54003440c2581a40010784020044040208192500d89100710308068001c45211201d6005070300c66031040098120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944214748 1250 944213498 944213509
    0x51c0506010b18031e07050604030c030807030c15150920030907050402160606120b0606030601120e070e0a020406021b03010908040f0306050618131419140705 70
    0x55640e440d900549483d00d100038001024040010a50300d4052945030150100307010380f0000d00030421200b1651400c0c0d445091084d079104901015000c0381d000c681c00d001061101c3d0040c20414400d1600000031076583d25495210303001e0a81401089032603204071600d035016140810068140c42d88104550030300200749016a041000c84080c3d24080803000803800001400703e24014400500f0955850400680c4000c29281d0f40c2401c851441c648900883c0203118030041e5203c15070302407c2d0b20529202d0000700142900000c01c0c0074104840f0200189000417540200740940340c83d0030081c070b081810400004031411300102000f41c428418041013103160b40c00207075086c901803c0c02d2402c07102c180000c00310b0301400141c1c10152802c2c1000900150302c0b0300508011045034000e000030800398586208010b010f014103081c2c4112800000b010801c411501c00f5003083d01442284a5a10003195410041c00c000c52580a5809000080010000c2c00010b0701e43c4031503c41c414014114403818040041c0e03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944215998 1250 944214748 944214751
    0x212090112050601120e030c06070309120311070c03050d082409100e0f1803070f0b0603010915150e0c0318101107021801030305030114042301051c0506 67
    0x10350582c8880120780940d020700218001107003601d0b0300b40030b81c400000f40c080e40caa004030540707803951050b030000a00c82d501c01e104580c02c50381e114074020410038084004a006c1d1081e072002c4505d11004204000028441500341e90085100d44007418000c0005140a020540c0080081c0c0c00d24800c1c08c0a0a270241010942683c040000c4601074441d842d0300005040e00115034200045000c0c0000a0083c1b03e091080f5a601c1041844540e98802d0146d010050f260702545100800d00c5c4414003a200000c2ca0211081e40d014401800000d00040c8035140c03010940d0340b200201401075130f105000401c40080381c5020b0040c0c40c500d4807c5003542013140fa0821244001440e03403180d101113142d07160b10340388244480703022203070040300522001a00d440b1620f400d520005080344110400100c14031007107243c01d13240d41220780640b20075085030f20b00540000c0f40d89500a1855003e0340c0c17600751084181704104130540c0001520b0312489150b04000906c40c030400c60b01310428608182c40b400d40c001450000e40385 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944217248 1250 944215998 944216027
    0x20114090715021905151305030d0b0612041112010b0a0317042304050a0b0108041509050a0605010521030f070201171e060d0f111c050c0102120901 65
    0x90002e5402007203041105446032242401c0010244200740000001c411103001801d4681402c2500d80300900c88151100300f80040041c0c00902146400050079804428000350152406152108400085081c060101c0c0c04543c0c0c1d17651780c1404e08035414459149590041040020800d0740100000501000c86a00c00104000b00c1480300526064601e008c0d100207001d10f140700c01d81e81c0e070407160b680c0390000340000030781c026441c140004503030130118001c0c84411507040c1c42d010a141c94544901e43d600145030080175003181ca500020b400540b0801683e14494007030407000801d17504007000c018580e0f1074040700c00030342030310325000c490f901c0f1010044400c44030038007401d00e40e02c8113644016500541d040d24400c00318070300c0c04200100f020002c00e030a0b9440180d00c2d1800c12981d103c100300009051249000703040c011841c80e0b08000180c5107c620065204000c110407036241460a590000001c0d840c0e040f11a9001080c403a05156010800651029200d0703003c141001100d8000a05048020006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944218498 1250 944217248 944217269
    0x807030213060e0f09100504120804061104060c020f0603071b0c0b07031206091509150b160b0c0711041e0f0c0e0604030c171f0501060201140907 64
    0x1c070106410a034080801058552200903e0786010240c00820720780484444049000d1820005041a201d10486200c1d9600800780400d00e07400748401c94036440010011118150f4450100c03400508107400342c001070040380d54a40714590207205010b40380c21001c0d03031907000b107005200703006605030070504950320fa124803440c083da201850b040c100d443d02c000e60b2058403d9180082d0300814164482c0c146040300d26114024440e090341d5445000032125180c6034200c00000d40c2400b4001c020b940e8000d0804041182407508a40e078076224a56900d600c00545c95030044a403440c40000c0002002820b41d0280f100209107080c40495110a108500140e0249215036640d000210307801855181518201045070f1080140790501c0d1103a0004101202c59200031448844c550012494a5011641034962120f003100a007864824aa107011003280141380143c0100d5400c0780c41040070426001003418066800310b101c0d450058040d00311443c0c60010912180850100b29012600040c00c2003141c000580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944219748 1250 944218498 944218519
    0x15170313120809041a0f0f01050a12020d06060c030807090b0a20070608010513020301150e180a0218030f0a03080a090602270d03080a0c0905030d09180608070302 71
    0x180b824041c4114103005030b1141c50096101a9090103201098056201307130784844c0c0c0f500071141009500428000f1180c00280c04110303942c01507129005091019840342c9001d0f06111135011220252010303504180c00107200d070000c010516034009481030b000301c070504088144078202964040c451244505040900c100300300c5400a0b036555500004050103401c1c2900e03001c6443d02c4008100660078130403d4403030b0380c0d0101103010000c0188201da0495000400ca4000c903440c03642d0507281c1310319200b5003580c80b0144110340c2c16040380100c1c3c8144135079140c520059648607003401056103950015031b5240654895010b01b15a090005416950749406041900c407582d03400c001c500141c00000c0d030042c403807400843c009070000004000c0284502056465002c0017400364240a03004c11100340180002e005500402c0740303007560398002c3e1044c01c000c0c0380c00b800440d16240403074a4034160b40340580004050342410800c1100306245801c0780c148403101071152031f140050039644c42407a800040c1c03081c0030018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944220998 1250 944219748 944219753
    0x8031519140d05030c0604061d06060f03030f0a0f08010617040f240209131e0504030e0603160e22111603110601050d08040e18011517031312 62
    0x2c1d552868503801000c680d500c50400d440c40da16504240c508441140c1443c04460994094140d01c1c01507011040c024029603588008000a00c0c1d0304402d035680500003000a120702032a084003e004440d60380e01d940f0107944070058014074091050b4081002c01c505600c03a0081030300c11924072034105400144200703140c50700e400d0003110310605a1101c1507140c005841c001c00c0c041c4540240c05028812600401c82d01c000c114a00181c0d0080181d19400000003081d812824109604c140d401a0203031800348802c01e10080031138200d03401510021340d0007052074071501010f80d2080780c40d800c8120503500b00b050200003031117103200200c0c01000207d485484200d001d1100300c040d002d039003030f60402c41da500715001035605003e030421100b89800300c0c8501466002048a00340b4685400c102903000e038241c0c0c0b40c545804001c1803e05401f80164010868008082042541c03d020701d0308410302c0030740085070a07894201e05000320341d0001680c010540017030000014014003189541d084070620340d500c4840c2c6410f032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944222248 1250 944220998 944221009
    0x1060903350c010b1c02041410170708070315051b18030a08040e04030f11120f0702180a1d0d140415050d0606020c0d0318050603040803151914 63
    0x203080d180e0040c5244103403170380c400c41040c1500300b40d900030744c2c0c20003485491011203403041c442141c0704c0429030006c810070011a49402c070500c0e0701240b1001a2142e150325405014105002c56000340c503000c890741040490540140314041c0c01407500201d403e40e500760205c011382e050046450f25120080c4a030490402a2024490f0181c3c417680000c2003544e903078950707141c0404c001c01600c1c15000110502d21105002d80078100300014043c40c00000d00b050900d012400150741d00c225074110203588180140d8006071140b0020201d0304981d04071072205803800240903801ca07024052255907000418804248104020030041d016400c1131030300e1240032429200e006803502c619807291400e00302844424801541c024007a000b01c0200e0a07050040c107507192000c070b0303980c4619066241d01200f015980300000c4c0c0075181c0080c443d4242d41340c542c9581d941d41d0015045402c125030030f84014000200b004030180b0000e65618841408966a0800c001c000c83d580b03220003541e0084041009000c42d41c070301f1982c0c40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944223498 1250 944222248 944222261
    0xf0302183003070b0717040818090405010902010809010204030c050922110301050106170a05061908060a05070c0803010e04230a0b06062b021201060903350c01 70
    0x1401a9400d61074038110155901c0e402140182d50041901d000700390f406200c0d1201d40d02c40d0b00d03031100401d03040e151501d4041a543c043c070803024128034a60741c0d1903541d803284c200705481503010304000100340000d8000035000d148001c0403007509901c10407041c00002c041440da601929010356840c9a160344d0741100000011414034122641c0e00024200800c008002d20f950410000c190000d2021340d82c0d03110705807020240b0f03481c40030003903030500c0005011580d1a40881da102c54003d2400c261002c40e4a401011429260400d68054014000300040d04415000341034106c03510b8985a4003ea400e42c44031411404107001c1c1c042120749280100f001e002e001076209081d000f030300c4030307200031041003080150759000c0560003191300368507031300002e4200d10700380741501d940080600d08040c080e003408074427044d00b514030403e00903650381c00d10580b0780c0040d03102d04942c00380545440f21a44a03042d81050a030044150440f03e1040303111500079485490140703450744c0f0707024407000403c0d11041d4408845024008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944224748 1250 944223498 944223559
    0x8010e1f020d02042706051c030e090c0705060603030f0a0c08090402030c0a120e0309100215010306020a09240c11030d0201050115030513020f0102070812030103030f030218 76
    0x2c20080b0326403a000c91030480c06170600d07035441503108200e01030303005403951449a140c0c40840c00ba03459160b07103564001420741910a1038070b8840684104005140c0320816905c0c400004000b02d035640800c081044219017022040300194185555980341902903c00c0d81d0031b84042021208003201008410000c5e5012690020025516494400764421070f542111a5100c00104079070800350100d0400d215461071a401d5002452034203030036070300b40312004411842c03400452044039114002070021014a9020f10b20843d00940d031002c0e02100208483c0340307508141c0039240c2101480c030250007040318a2030b4641c0c41f030800003070294190604540801c18604819018001c81c01d602c8103065040d8171403810b8a0100c0b5006001c1c503500242207049800490780414410b6000501d50094174140c0002040018148100c5041d16143c404007814200a01001c032800d09001c40103004058022281600f00c0070741e80382c110b007481c4100c014000c1001605985032701440d511202240c2e130240c10081c3c01080320303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944225998 1250 944224748 944224751
    0x70f0b07141606180603200a02030c031303060b011412270105012c13110d0302010b011205190504060e030a08010920030f09010204031a04030908010e1f020d 69
    0x2a50340c50f0203030084035a2205501c10070550480400e005000380f00d001901100e030360204080c103080f034044448651200c80400e0551005101c4404004801c00c018440288140d41c0032514900d1880c014040d00d28094000c1d040c00304c0580001d0007640901e05981e60002d908260f5030040c0c44422034040010211600407000100c8618580418201500f0850485191517102041c60000d450165100c00003401d6000602c0507030400324540b0040031100131a6a4099620206e004001030b00003600d506000c035003100540d4488150030610b41c0c11944040581000d480188032924080410208007100800070b181800c0d550300c0402c042c018994000c5400c84078130301c2102e6803600d0540300544408400d03c1000344007410107030700c0800300b0301a00d1840080b0080c0300c401419a113420308000710101c0000c1503031511f5075003800004045601303441d004000c1c01b18003102c2052810a401c0003002d2007002d82008215a050190701240741d5800a0b046500103030840e40c0040c81a0b5120522019120f86009802c070103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944227248 1250 944225998 944226043
    0x1203150905040b06031b040218091009110a0806010305070e06360a050904030c0f0804050108090a110f010c060f061e0b0306060d020702040c080603070f0b0714 70
    0x200c00d038400341c020340c05051040f8440ea500341c00c040d6a4081d14001d641c0c41e034281134104103075060907005001098450324a11840c0b404a50204840c001c1c2150207080c24005000108402c804a10501c481407115910701403929181d00009058800c0240025040683d03600c00540d00900c515810402154020f1500e5901d41002a50a8540d00311a043c00f0368000c100150216035a46040950003007180a00000d48841c603050801c04a240020700a034240940d03c540c92000032a2120175140d91441b03016469269070a0400041507010010060030b032035801514910302280c0a004070490400f0111a03030340a14820800480303030312101c01c0700182450308004000381004150381200080d1030001e10b98013036074007180d180026000000d11407030110a00400106c0c0a03400c0074002480401050312026140c101142d01040c00c46140314460320000f1126000c0c07001502c0c042c012500180040110164640d0615a004a1511503003000906005448204400d2902d0520074081d6010010440e081003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944228498 1250 944227248 944227259
    0xe0a020d1b030c110a06021c02040e0106200a02150d0e070608280507031d012f09060a0c170409051e130303021c0b030c01020307020d120315 62
    0xc0c0c240c01445000300f410115071491451255699070f81c2c140c0110f004011822503600d80400960103001c000a82c41c1c00c061000501040500040c0014140007103025120362401c0001000069a000c2240c44403650228191052000103100c2103a1501265500103143c19200955928400c5c542d08041712410984d10021014010030004115502902c510480d6030300d0200b5a050042260a09003181205148103602c164803a80442c0d404115030400103400c400b507100c184000b8041c40c01c04040e6070345444000d03442020403103c2014200c08030102c00380c0706844084050301409900e0040e40100c0c00403c1c10103481c2d2080608244ca03330342140e081880b4114003000301901c4c5c0c3c0300e405051a610f0805000c100010600342c520416002c50a80750309280c3c441d0100c5d41584201ca100581c2019020f02130020340009440c0c1028444540746000a80c0640c40302c241401c0c0f520404040d41990014460840580c41b000845e500643e801010031590700b100c2d2001390020100b900a03503600003404140881c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944229748 1250 944228498 944228531
    0xd0b10050d061b020307020303040324091b081c1b060203010605180108060a0e090a06020c10061401090302060717070305070201030b0a050609040f1b020d11070303090e0a020d 77
    0x280001580460402010f61441c141c0e80c80c03281305002505540304010070404181c42d04030b101c52020301d00e4402c0018030b2103501c2180a40b41800c5090310305042d0b00c09158900400145003d0040200d480600402540c1c01e0b9002075120f042d18110003440b0942c0c85143c109503611070fa40800340e0380007608544a584030070000b003843c0c100074001290300c1d884001d0042d2035802642c0da5403044200a100030b00e0799003010b401c2c0c0040340016207010720a21804c800da10018240c1e0010700003022900b0010403004442c1315451003603c1884d4401059160403a190690f0790364443c000c02d0236a6010b443c0c095a030041c900d80003d41084113180c0d001ca05001151440030142d2041c02081440d0003682c0c184024540041040508a02441a59130001007000008814105904041441c02883c40e0004800070450300540b015410709108400580141d0902a0a00d400c00440f1441040c03107801000f1450856501412011490040c400c8842e441c5d00000c816220381d4040759203414042e00180849500c400c04040b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944230998 1250 944229748 944229761
    0x60105060d360c060305060d061d0124060302040803040e070212030a050406060b181512010f0815070c150603150f2f07020a15170f060d0b10050d06 65
    0x407091101108001004c1d84a030060501481c2c0c01880300b241c818040e80c0e404c001704400602e02940e41070036142c0303140c205020b01c03a2114003a0b101c00da04c0074030101800c080f007010601c1c3e0001c100303041c418001403244071070020984099420042c5e84090907180e15409034905007980304002c0849100008000304120340f504070360b010b9441002c1c1808419100c400f5420f140c004d6024a000b10800012098120710b07183d42000341944c104000c2c1031811020b46180e6203400000d030441c682409680c00c0c01c02c42c01004201108034855281d00140325420080e0005000312240700700504800e86001d07011704060b4095002c100215402441920580e85102d185006414960146108146060714a0710340391540b80041e49500e112940d0500401480f8850070b07801d030801082170b40c019201d0407000c076070040b0400ca0b440f172401540d114100510b210a26058204500412907010320107072405001e100c3d1034a04030603854543c0a030601c9076650721000c0542e418516944035640c848501c3c00c098080c02040d52191 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944232248 1250 944230998 944231003
    0x403170109381005130f050f01080603190812090a03030e0d0203071b05090108060414070b1207121a0109140603040f05010207080f04080609060105060d36 68
    0x1034036900b0454070b10758001495800e998900e07580040e071010151819010b540c0c080b58042c1000e03410801852100003130f90100b90060843c8204807a001d03c503a142071440c004400400f440c000c0c49500d018004680c0340d0792207222071a500f035010080c56040004c02c1c0d0aa48410b10700c01c0c0b44080a10b8501c801555442c00d822003079000c00d14000e81c0414010002c550340d060400a90015460030b405903a40480f900c600e894820b12840045101141c56030741d44410f80d00034400701000380468141428205c007a07102614003110b417036001c41800c010300071200c41035868100790314102025030b075680032003690b10503204112841400e240c801070400710608565231140040080c0c0c0c2ea80303406905e0f088103008800c803049600d540023a0a10002c0d001030010280913001c50300c01d40000d4108055070340c40308030035088803802105c25540444e05010507841005969407046582d80280716551500020603490303c6280b0400b10b22580741c41910b64070440003020300c0f0312404c1515503458100d448040245e454012207908 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944233498 1250 944232248 944232281
    0xc030b06030715120207020604081608210a111c02071d010b090303160b0402131806050601030618050703060806070906180b16020306010503240403170109 68
    0x328000e030800050050030340e4410341c44010200500f40c815a07509455000c0001c1c00c5400b08001001038a43d4000b5100070300c0b04000404044401c02001000d1030900e80002d402603004030200ca01040460450312039407001d030104a9501c0c0309020f000c50351544040c420b841c0398401d200c24240011060f120b0000c40e014160700f0f56942948400940b0708441c4e405540103500703e450030050100c3c00c00c800040c685410021f00f16407610441070302c60103da0201190684590b5240c401300815400c198140264001d0142c1c400c10103202c84039403da420512106014100300d07a12000a80164001e510601c09081520b0020b0007c000c1e02180701d018000031280040000d082190010f410140010282d001d801700b41c6448007498140310003120030b904480c8030740c900c0f103545d40800298a079150004105150140314840b11240250044c07614103603060344032501a5000301040e110410140318151058500e9040280ea66240c60608032600444001c6561410140030700001e040d074000d074416484c100c003c800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944234748 1250 944233498 944233501
    0xa12030b03010204051f03061e0315020708070609050304090f0b030d11150c04092f040f0b0c010e0f0708060f0105010c0803060a0906090603150216120c0b040c030b 72
    0x501d07082c1d0060344595a000300b043da8605020405076101c0349000c0c42907260010706251354074118007012012402c807944c001c2c42c1c3c010a10500146000700c2440f0f40d4101c1056140c000c0607522000e032403181500c00751982d582c0358110810403a06008603402881a501d0520805110543c00c9006001c000000c0d40320f48224a82200c003035006042100e0702005040c050314541e11224034010034440300411030000e89604010100b0454418440c00390320315018580708400720070341d40e112116008589191002030a091004229041040404070280c0301900c0050f51910f801c41443d41c00741c4824070440f2854041c04c6841c506842c0300050344030460340785030111390309915043c4960381510300078003840c1c1c0044c100e001180c0220b84444025600580007921400c11390345d8403c0c6c40340403641e040d04120040b86d141d1100f00240904555000d58030155944218501501100c00a100540d07051009050150000340c200c01a03004203103e00e58070750454803584491405180038001c42c0d00500003150400300980 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944235998 1250 944234748 944234771
    0x130515040f14040f080408060c0703030e070e131b0b030f1008030d09051e030316082a04030b091501090b01020a0209090304120c050a051e011b02030a1203 68
    0xb034400501071601c000300282c03034640707a100d4010303107007141503c0c040030412000a20010401240d88505440c40003243c1b02e0360185001010340d000b01c155080701d1b901104080c012900300e40a03140d0000110004c030301c0b41c0031061034000461030f51104050701600c108140001c03014005402144101d040050f10380096490740d59050b80d05400d4090110a40d00a00c40c2d032a102c030890340100324184c0644120b41c1c00d5914030140303000c42c00d10a44484819080403090025081081070007540000301070a14000a00d40201501d50000401f80ca00c1740e800c0801d03480302c001c24040002c440185d908403184007101d01d000c04ca02507841030400100480c450b0305c500001401485842456403191050b406415044c15036020800c48010280000c0c5441c08100000188040102c0300d15060f184550101c0002c1c80c5484200910321006c4c0d489a4008d400241c1040402c810f40700c3c44450a1909003032082c0c040c42812410f0f0190f24150200035018400c20481d802403120001c044400b11085580901034a00d240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944237248 1250 944235998 944236001
    0x3b07081525020303010302010302090a0e15030d09031502071a01030c030b01090b0d020909030f0a02070e060a12060f27020f0f0a2705040b0f090304061d130515040f 72
    0x7501e4210040c0c1051006000540c4650028002c8450042041074159220281e002101c1400d032900741010364150040002401d09010801070f0303c605003045104903165403200c0300c1d140740424142c0300d031660000f2100204820b0400300101d1841c2080419060740c0c481c035002d040300d40103000589403d5096000003075450840e01403a000c42701c000d00407400461b100c3d4280a0101400380ca81c2245010600c8125a4035002c5006025600ea01d603004000d05442d01e030050080d0f680140019000e86c110b0002404481c1c0ca0f01200d818459200d0300014464000c2c8020100a20301010403540054040320700c840c00130616045e140f18035008841e405802c000c090b0407c20002000c2c1e42c0c03580c020000d0002040305020041c1e81c0f1402000086c01101c0c105168240070301100ca0440e0201d0301a001d400502042c03950303541c040d070f41c820200802145014140140588441c4121060300e00100601910020340d464040111f65a807900450510140c104003210700070a110316214a03010300e142414803560b22400c3e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944238498 1250 944237248 944237311
    0x5300a0f2d03050915030c04090e01110712090302100c050d0305101403031c090b0912180f10030606020c06091005070311060a09063b070815 62
    0x2103800706078040ea034103849a401035080981e000b4001200c0180a41100f4003c3d40301b294000d04455030303039040800305406c82c1c803804480a0640e144c00d4560054803100e8013144d1116401ca409001d000390300ea50112241d501a800082d0080c440e21f8038200d45035001441c80c4034481c411015550390400c0c0b04030840495400b10390951422000c0303071041151680a100f1801b010324040c044d64507040c52103002d00d00c4180c2003030030b10204d19900c05088083c45810300102d078202c4060800340c42c0681c001086032102d406030528031520301400d13504031800c96641c245d995030840400b81218924005401b0003400601185c0305610150181c0e1220540034901007085421121008288609102064004807816040544102c060209204040902d003400f0131010344106a40c910120703179200c3d240780143c01c0e54024250300c442e4101c1c10500640302d601810340710665030584030014014801c0e5482081c42d04904d68080007160103070325080300c1d000c49440000c40c45864141003550340350945407001c100f0100c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944239748 1250 944238498 944238563
    0x4110d0e1e1903080a0b031f06060f090905070504150e1e0a090e010b03120306100c020303070209042a03110901030c060c02010507020414100f05300a0f 67
    0x8070b4168400290181015075040745526000160848142000c40e2401501080412002c1c04413001c13100d005401d40122000703002c01c2e14080c1c0796008030020240155074035000781e46409407940001046c0ca449841078178010f00d200124404411011007010b400402603102d401e003d440c21031200c48a00da41c6070151001900c01402e415900f61901001c01c004122a209144641d501c480044006680420501340544001a401c07903990425808201144d40e00320600d00074400011001e41c0569408801d8682c245d0301901c9450343c50755035240400c3d1407031042810300300d01d0130507031b03c0001c40d0701707040c81a03005503846500c2d070302903403900c0e201004440c19092100428010040000f4480c06126440d0001e50601c10705145040080c00c0d80010140d1384070f10070210800441c0000c000c103090480032084000c181c0d11780702c10026400c010119100f1900313070340302544015502655520440b44146110f10390b1403c001070791654007403450800c0244560001c2aa40342012007403a000c2142c0d0f62119446000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944240998 1250 944239748 944239783
    0x1c05070509010c0203070f080616020a1e0c090e01270530030f0901240902130e04050625020616051909090f11040504110d0e1e 56
    0x42002004503003c6200030003c9070180580746c400695042540c0d29003000d0700841e0050411031409401c454510040f000700c02d411940280c801030040344510005102002c1e003d00c61b500401c0813030900443e4546198007242826141a0000803d0381041d48840000750051286640d858050a000720018098800250040e000000d82c0b0034400d0100300071050100c000c1c1c0341c24040c60a03404902d100c070f402c1100c440c549403c40c81b0421000750400e210710300d5851382140420003619000c4001e01c400100f00d00414911541c00105085200b501c94043e00051513030000b00034083c03800d440c086132110815512403010044e401740380700081c0c201e0390b01501c00da0b00590042400da074030082c211000c090503400060620404100d15442200f00ca00030850940540e10741d0000d643c903100680048900e00410190b000345410503190302c5011840859040303401c1141d012494000550017138046102e0070600150382840e044807072480c0e000c04a6240c442424920f628020300701d503192040d85070240081c81e1080903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944242248 1250 944240998 944241007
    0xa0e0a272a020703060c0503152707110118061d031c2301030308071416020316060c11060c030901080c0d0608060a0e0705421c050705 59
    0x55214107504091200d4412200500d5803619504102c0d00d005000740009140041000708400c4025500603400c00b080d101d50208040d0310080d05171201d6002164685040b141020400e050320810150030950440c0c40200651102d4190654284070ba41c00200da0207030404c0d002e20310303a08021a004074045030460146140849a510211403402c0000c40d1a04c1e05035a03211401044450103103550f01c2600c40b01200916505504000d4040e1100400721001c00500d07075500b040003034846c17003511250074210180520b95861880000e0604a906090030b400c0c0d00211f10020340f2030b501c2000030544901031103502d45ca0700a1403052208501c43c00480a0480e403080104502d5540b04e407480301e502920742e100c02810004103803410000c1d51001d80c0400455800326050051001e064890140c080403200e0007030105520386008140781f000c2854a0500140e000005005d08022085040200410600c0056112030b0511048007003900815540c0d0030341c107041c21800b04840c2291155900481943c0c41e4a41031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944243498 1250 944242248 944242301
    0x20409150b30040b0901140601090e04020a050402070b160201020a091806030503030114010e03030a1b0302030f0a0f1d130f11040b120f010e010b0a0e0a27 68
    0x101c0c10b00c141c9001404a0300c0e00d4841008101540c41d8001d520070b0000c2d110b94200350005c1400e4503444010f05000101c1c08007449541ea8114140e001100c01c3c0090010140d500ca00006900315080d500c81d030341203400020b1180030407010508052280b0004035008110321200c0340102d00301e0207504d8000020403404001400303642640400881203840e01c40000c91100d0b01d0b44d8400d0705541080c1d205030060010070890083e00d42e000300702d440c00e075401640158104002e800740144414085132114020302c180050b0344041c54824022983d42901241d4481e54980950038010000481c81d2100c000084210300007049405140c014200565002407070790b07040b043c20441d10340c000d24000002c400240d41d207001c1c0403201084070014000a1501354007160301c03000380d0811442c1000c4014142480414002c0040c040341c550102070741e055428952105407280e94180059480001c50958154429851a4000f030085003007444000a44104248484545003180400081d81c211145000361501102c80c203288 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944244604 1106 944243498 944243527
    0xc0f021b090408030403050706230c1309020307090315090b1e010308090f0910030309170c1531060801060206040b040606051201020409150b 62
    0x46500c03000001801014000300010400000403021505142c40b80f415505000d50001e42041071040b081645141200f0301c11201e0061010b2100286a0550500035140d100300b1800c140e10a41d42070284a41c06500000c00d2034080100c400800004521888040b01110301030145c0010404a141066aa240e100a10340b035421075003003058442c031654007086035044903003000394261620b218400144014030380a041c9a0311002103c01c0c041f949802c117010604481c42604d80900b071a6941f09200483e00001401a4898011040418960031f007900d906440c0b004a0310010b20b41606440e840300300495000140307038203d100e6545c1d9040d0945140862024041c6820807021075031402400943c0c03908020001041d50070010081410094150040d001604004014003403e41520000f00d00030341040c81940b111606000090300340b032503060300c410203481040100f507241c505442c480b1503 = true := by decide +kernel

theorem cover : BRFrame.Cov 944064748 944244604 := by
  have h0 := BRFrame.cov_init 944064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944064748 ≤ n) (h2 : n < 944244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
