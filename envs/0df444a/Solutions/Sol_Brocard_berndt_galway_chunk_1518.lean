-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:22:18.456948+00:00
-- url     : https://prove2.me/submissions/5afa2295-fa60-4ac6-87e1-b931da18b459

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 272841726 ≤ n < 273021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 272842976 1250 272841726 272841731
    0x4030b1603060503010b13020906250203210a030504060b030d0c211e051e030421021e0f12030907051c080705010f0203090d0e19210204 60
    0x4010910441840c0c144020703101070040300e0381d50702054201c511074032004d500910810701a01c44400940d004000c100002040c00f400c100030018402020441c1403044200000c80769802e009500c0c080003440c81c1582d5400500401d4240c0d0140801140a03d11490090507103030700214007080a5030700003084150014084079102d104029000b00040c02955007600c00504039110750903581340c1280900c0d0018010344841d02c4014403191840d01d503940505484003041006d10086003140e00d01c01d034410341020210baa681c0c50b420719007044c032080400c1400e5441c11042c91240110180d8000c41c1840c08642d000b00511460707100502c045e41400e0010000c54028042c0c098030018070071402000d18018919001184c2e48192204140314845081b10900084131072206141d4001a01080081030303100e100e400040341300341d60000104107a0f04161800400781e001255440c01041e4400140d030300480e0b0481c1c20010241c1400740c5005050164099010150320804c06001245000301d070701108698045c008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 272844226 1250 272842976 272842981
    0x405310c02100e0c1005090a080106031506090b0d080a0c0203061f0506030c091005070f0c050f0102010b2409060705030a08180c0d1110030f0b09090a0f0804030b 71
    0x9440c2c80500002074140c07480d002c16900750401c0050020301001000e42402c2c8034130f841d4403095070160402c1e48450b60201900070b010480b55401c3c060341e00111b125110403490070f1500c8600b00103603242500700c0105145402c2d644552a5130391701d00301c40103d03000b80105565500c0c0303800840702003080e84030194161259009200c2d0b04d0505402e80201c0300181030618000031340310402c0203ca44410380c5e9550004100313020100184c600000d2800e5000c0140c05c0241c0350000a03504c010501500b150203440102c200b41c4c04200324180300035001c480c1142440200721068103140001c0801072910781d0001030300d0b2408401069481d411086038640c420080000c3c0c4c0750810f40c5086a40c9520480003c0002005a00411114681c500400c0f52009056020300421141c5406122000f1050a4252226100c111030103130103845080030134035407511a82d00030403044c9110b00300c0000c0e00c02040781c40e03000c1c80c107134020440c654802203641320304a036015105400403043c906119082d406541c01c05000c90822900703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 272845476 1250 272844226 272844251
    0xf030d020615031606030c02030c0f2116060b03030403060e010209120a080f030a0605040212100501051206271e01060804110111030f040303080f0c040531 68
    0x41e024401c0544141282010741904140b54480740f1140301d8401100d112a01401070b58003076001514454040d10489040040c0c400e0603e24202c40d1103a4801c3d9034120800c0410382400404402e84d460b4130907101c540c90700d040401c2202c00003095000181c045681e4154220b015641071040310001d54000000340f00074115148407500039070111410912401d00050702200008011130309130401b540000800d410001e885030594501d6200800d0194002e0382d070900806c45545504c0034001644d4a0340d5000400e2400300d0003030302840c0d410b400082c1440001d1060324080f184440103a9444141550701c0180c03d5100102e0200b803011411050411003000320401640c00c01c0c0d95071204c24041d03230f411342503040c0c2d0343e48209039403000707083c1e801608460005410600b15402060414a10900001242d18221519904003a1a082504200d001403030034010301181d06501c0c21229001400945418030b001c1c90701c030005502c651b00300810030520816071400001110703c1c035a8401c0030400c003042400640660f19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 272846726 1250 272845476 272845483
    0x15060f0f14120f010e04020904030e0d0210020d0306060509030a030c020301060506030112060f020a050406033803010e0d08010303140f041502060a15050f040f0f06060908030a090509060f030d02 85
    0x1c1d00d40d00142c0c1e00000002c5c244070301191450256401614040c0141c80d15103080342d14500d49401a40c00c1850072000b40f005071241145036407142040c2d4040c00742116600001020f0b06c00310350014041020034008884a960049620b100c00d5905003401c81241044e480403c1c0985a40c1e03106ca548144d001c0300020301081001d140c112501d00c81c0e4010840c0d1041203082000b02d005003498140000c10510051200d54080d0740700000440160200c1c6000345042c4804290105001d80c0402609050f0718120340c460800f402450b03002a80800609071000e207400d40105009814400038003004001840c51011250110171078030200f007400600b6560b142c480d203542d41c1c0070a140e098200103206880000300c030402d20380f05220003a6003201800750b0041c0303030004000030904030104d0240d01c107640740789000c0b484903d4480c0356a0070075042000b0580c285402d43c0600403400c682e100c1c0520350000c04c0011082d6a220350240d0941700c0403a03004032b1989903180032a80303ca00b480c0b001351b014810071014103011034000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 272847976 1250 272846726 272846731
    0x301110705150106080109020c0c090411041d060705090d050d0e01080604090b0412030e010218030c09010f050616020613030b0a14040803090c091915060f0f1412 71
    0x140101c41e40b0142d0060381400749503007441204000340241d0018070001c841500288603403419401203c1e140d0454000041c180c0c1000d440841d03041d031401c0d036050024103060103400d40c40c3c4040c0b140e003072000200f041850740340c0304001e21b0300c000c105000840600c1d42d0307690302c8003c40740c9401c501141d20700101010064140f207043e901040c0450b02c003c001801a103018000c0c840b010b58410041d43c036545590340c81040d032800d0858083c2c140744e12980b10020b880d0003440078001e9110b51f0115001414a418241800d00d5401d8480034002c061844c014803119444502c0f40b03044a60503201180d4407080d10004240701c080741c800007035021000107050201410820989000c1ea401221100c2c02d644842c54110201c88044040d060350540c0c0780700280c0402c4540000c0c1d503000310004240c54075107007050000380c1100022a82c4511800300741441040310001c074401c0420144a986411069904103d00a4400701c0720036458800c1080c044101c5031080d01c291074403103146242c0700b282521421042130780003052504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 272849226 1250 272847976 272847983
    0x708030d0204030615121101260a2703080c0706060608061003020a090e1008070303020a050c06072d0c06020703140d090506031308070f0b07140313060b03011107 71
    0xe0051454911030440f00040407140d01b60080722192105640d2480c5542d450001030307043c0012550300800c2d10383c80c490b112200340c81d8200400828903044180b6070031a0210515240d1098640c51072200254482c12130404850305414402d5641e80c400c0502ca0341c43c816403100030106030500f1800a100c540080301140204400c03501600d9a0550b680110200c0c015516620002803069204200070411800703065000304030146840b91140d19040c00503d041501c2d4800c07030050b0312080580d0140503080c40b150313040b407034200c900174a4003805840c0d0303a8030040381c0b52030450039800040d076038000080c0360001500c00d5940300001100c266034504001c0c0d1249001d10041d50a51155048070020042c0400c0e92102ca4545484030031506081105101a5400007000e1000800c45041a240403800f080e001d401424821b14010314840c10501e0300d00030300b41c1d001e0040818407031000359148401200710300340ea0340f000440040100c005e0050406502420600d62000d405528180d0740c40e03c204036036001803142030b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 272850476 1250 272849226 272849231
    0xb070804030b0f0420040609060e090607090e0105040b01120e06160302031e090a05071e0503060f180102071b080616020703030309150f0f050901020a0507060903020708030d02040306 80
    0x460f01080ea403508012a8014258440b2481d007150315441c0d40001c10820001810001d005910f80403240c0441b00c46802203689203003c0c03001c02c445060100206603108000d454000c0c0c1462030700d2090054890103008052095482d8511802c659205d41c803a001c01604064040c04200549485a500c81c44280d421807440001d841c800c010041c040d001702c0e4066041a4200b000406200b0880e0118501c040c00c813240901075141e04c00003255081003c5800b4200084000313846072181c0071400002100c513401a030013034020302e0401144079090042594450481d0081c080c18602184504e80207100c2d59400034082c41003500488420540042d80c5015900c400e4125902a00c482c640c0c228201d000250100041c0d00c03015050000a1080c2c101700c1285100c0e40e00c160301e80d240490404140c1300481e03180c0d204240c2d0740c0009800b80b0003500803e900501107000071442d1031800240103110780310314600903216940740e038482d0041502c00c000420003040041d0030340e0744500f08103007450041d42c010301c400c1c2c44036030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 272851726 1250 272850476 272850481
    0x9060d1a0402090610080411010903050f060604050a0902090a0f020f04140910050d0305090109150804112205041103010501060f0e0301110901120b150c010e01230a02040b070804030b 80
    0x384000c00a48034541c1381c45d001c0c016900c954400c4804042350306c0050401000220020001c0c00811555030b00741c042c200a0034061070054180400c0b1070b80100001c4130740d03040c100c0107030160701d680403c20341140c83c01d507010940d2500b42207031401921845489110510001600058501c488003c3e00844503084a940d405030f03d41c400302d1a81c0401c18002d00c0d901603007186403080000c0c0100001c005410b01810181e9082d590f407400c2c11005128164980003088803141000100b140c41503025500000c101c0c2c1c41c41c0400d00d078036140b4200c1100d02050204403a581d202117014408240a03c80c16a24014001e1040b07617118003008100c039407010708400124424040d40c00d52460b060140110007071318000c00505241100b801102d8400d40c40c656a481503507135466401c219100e074148007206a181c0d100146d0380d01c0700103150908447d04081d8940703950749400502704002240b24152045120000110151a1580d42d0140001e1145501c04888501d00103107090410408401810841c2d001301c0a80031940d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 272852976 1250 272851726 272851729
    0xf0504050405030a0f030b0406030b01080d0c03140a1205070e1c08072d0b16050412020d0302030c1501030b0609040b04060e0115080a120203160209060d1a04020906 72
    0x580040d074009046400078000d44114500c40d5440d030705404180c0c13030701045500306000402c003240e459400981c2e0038031048005106503c010020001004007901d000000c002d25a02c0080c076419542d4401c166490300090403e540621030101600c02a0700b1070740c20006424200070103805211100300c20380c025503400080402c0c10300842c00440c4215000403c0e240703014555559010b50004078403c00a98081109000b51a54400c0340b894407042c0c4240e8020707609003400c074070480720502c1c0c20030399800300302c1c1c100804e00c1903000aa000728580c66040e05c030f0002a107076070314069065025114060f4aa4802d0300000210403008424040c101d0b406000700c3d1805459100510442c80411100a085441c15001081c000b4110ba407021301c10f9800100009244410146810030152056104040a9000070a8a42441410900c03540909507038001189040e0300c4a000c1d1120580c6118080d2090075960006001a152902503041175507000d5058400301e80070100c500c04195080d20260b0164144800140b800d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 272854226 1250 272852976 272852981
    0xe01080c0c2428020706020d1b1404060c081e0c0106031214120c0c0a080702042d050c090a03080711010203040b04030b040c170f0d140406030b0a0b0f040f0504 70
    0x9480a0480f4100081c10204078029500250048504641c2041450a088480d20544074150b01c0d40d214685241c0706140020000408010806d1031003404000412489030440c04020000da80b040c4210703229080a00b02d0b01b00003603403914140740d00350001040c560200e019030048040c0c0b88103907408214040c40800441e015808516143c5d8401c00c02c0200090b2449100a0260300041c0d20901034900100514150b0400140b18003c54001c6804104070045152501814942000141c0074841c1400d0740b19807101c1022003004040215076444010945003031480040780d4500101030031819a05940b441c0940c0c442e03000c00010303241c901e010a1294115840481114202c0f8440c074085410241141ca90a03100a0082c2007144d0904a060380011102520706c007488660020381c028102090032122105d007083c3e807007078280081100f41000b4a01e08480358058038265441d518000840d08000004640c00040399040146183d6000c1001c0c0c0c45a80148000d00076114035030107035503840d0380e0380090005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 272855476 1250 272854226 272854261
    0x1b0b010e04142a040f1b1d03061308040806101d16050c0304090606081b040501050f071a01080102030a0606030917070f0605040f02010306060f0e01080c0c24 69
    0x103142c0e1801c3c010090805501c899691000000340000340950810100d10300f2591402d610000f1032513004d4099001c65009220707004c005140040c0026094031a800203600e1b000b00900c0005461230f01c820f06010b006400c8150781c041d1540f90201e54940c28104541d2562080702e104641d8683e410340488042440a040c3c403074002c02030000202c04000d11040d090342c0c907810514014030144000d001c00a000300c041d00032040202429103d540c9103007000000c0c003900c40c92164003a0784a8034100802c0000d03990100441d030345145000c54840d103450f11450043d55002c14200003240c101c2a9000101d5280410350040d40aa900c0c03010800500c4d0b5218001c1d01500c41141c00500090b105140d99411580302c940188141c512810b485000094155a100300700c0d9000c1d6000c0c2ca40c8400d002440c011541c0504c0781e80007410f42801c200c02142034022004080c02c0c0403004060400c203140000c102a0480c03801645c84048800050350045040302000b0030501c02d1921484048006050114402c142d040d8940c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 272856726 1250 272855476 272855503
    0x3180315090b1807050907020114130218100b09150309010b011d0108011503140901230f0412050409020a0518010f090b03070c0f0609050c0109050a0302011b0b010e0414 74
    0x44d44034585420000e03540030050101065540703950980c5503c0d944040c049102d0101031130040307103901050051003240c0c000c0b1844640180d5103a0306000f00c980848440c07002301e5107481092a520051040461a50f02e41c0925600d1055000310500040f680c06400a025068003a0388a03034081308811074454000112040081c00710700800014020181044c0740da42c100ea925040c0400d0b0300052138001d1000700c508451030300441e5500e260700382c2ca12001c800541200ce585d440d0a0720582040d800820340c54034080c0008004100e022202240580950207650090013066411920f900044c1000b40c102d0b0301c5506d118504101d03079113910b81c0d03d40c001d500071340700308070207598043c60141065003c00c080d50000e00b2010030301a03c6102d00d800a13044a250310810340c820f02c00031613540c880d468800d282050310b4011505020618074140403645410311114100c94091030b1000c50003401d22000d03900e0389106c16001d01010142000400c0302490032481c603000700c0c8101c2c5852080a100c44000740c81d1a032001540303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 272857976 1250 272856726 272856733
    0x2306060406030203090309030f06090f03030705030604090c05061c06151b1406010b180406060e0d03050405060f04050a08030319050402010e100908070f08060403180315090b18 77
    0x6101c001e110390b0103154400000e5044030f142460b1140000d182c0b40603540400f1140d4012001c000b070184080c0150841510100021401e50500c400e019009010080401e402140d0b511411014405610b0100c801040041c03d21556440c3c0c00b41c0d00d03602c18000300c3c2008512810082c00181e03000705140c00000b20a5160b45855245462814078100401070311004d82c3c07502230119104241140c00d20040f402000d010311080e40e182c22003080041e404241e58040f900c0780345004c00805c81aa0000358054024008444c41c0300159140c1c40d0684150040d908416000b200210f070b03000c100c1402c1c0c4010410380c1c50807606c03400f002d940c520341e10740e07203220480c0d12041691007102c40c120503051035082030b1740151050409035038252041020418400d18494001c002402c444410440303c42c00303100e010054180181e445442c6410028010740e1004003030801070402074008140d10081c814940400003855011200007000d940680b4a840038100c5210140e030b18000700400309545145c0207030528a800c070054040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 272859226 1250 272857976 272857979
    0xd090503070b09031f09020108060301180b28060501090e040c05040c03061203181203170a06080706020616051602130b032d0a170702040207020409030323060604 71
    0x60382c20b4002c1c0002d90740601c50010642a910400088034000c03090942c000600003809000040c6440b002407c658042c1c1d240056022001c6503e2400c03458503034004001c0c000603200d8002c00301c0781280300c403454420b0002030b00607401c0e4014030ba0881000ca40e02680c603000b645899600000c0c1c00402642e0050485102900030485410a50080c410900e640d080008442d40d0b18040d640c1c0810b1140c00071000104083d406200c0e20009190701e01c0589540710714084808800d94028000e5150451032445854045c0d00003105002541c01a0340540515415561007540d80c2c81c0295690909440c40001078141c1000d00c19a90711504c1669001c81013040b40950030419602408003241910151580160301c0300090030840d20100484900180d00031510108000b07035210341400c1080d201404841c5030041d0050b00c02142451503a100541008440655500c3d01c40c40090028460060000e400c54144521601450703015440032810008034205c4019808580724112848a004ca414581c0010280300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 272860476 1250 272859226 272859239
    0x30105010f0f0309020d030c0203010507030e0a020105090d0f151b0f0f02070b0301080c0102071d062211030a0f1401060f09035d2304080d09050307 65
    0xb4009409001810006805001c0360045210b40300030203400c2c2e002c43e0300d032041181141824454035074841403e02e401c1003c0114584899243e802c080703c043d04000003c680e05109690300c00c4414030840e801201d20050742e40901d0801c0e2401a50074406007114506100b40340d490300c4a0440d280301150031342c1d5802c005800744209861140c5200c404800314410707101c1c08542a203603400110701030300d01c0788010942d0a0002000a1138080550842521034100000c0311200c47c3d480f82c400c03500002d0840f58000c03070034a40b0307100058107035040e5001d07124281041c590b00000c090302e034001c2d070185000ea0010310880385810150015104401e54400030030b8401001049501d12031080d094180b1a985000ca02c1c81d90380c3d840f50030048904051150380704080744504142c0c20411130f090440c51400b0b10001400c0d42040c004100000c1418104025400f100d45400d071a4501c11501c500914908004668102010302c0000f24250800d000304c894501c64280c050340ea460284803c0701c1104c40050041003ca4100034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 272861726 1250 272860476 272860487
    0x6090f0c06031f0f0801150311120a1e02010801060c0f06150b040803031006080112080d0b0303030f01080705010c1e030201020f03091b09040f200301091b0902030105010f 75
    0x42000380c540f440795840030030140b41c1c04408030052440d001c41c00380c0300b030802034000d08407500d10200040c3c80c010300c0010000200302d901440e04900c5e044490f0320261a0400c0745900300003084000400401380408a14040c0799100d1030311180500270303698014540e0b00c034181a980380d040c9203009401c641c0040719038000500c40d60018800d1000b2080c855030300d550b46003807880403901f00342c204403499000403081001301c4240300c003490010100c0e4a80491154580040000144038250018111580008070000703107150a41110140c0800581184e642e07191138100401040020b000b052054080c008002402e5842226402c103010703040f034603d805100500002803010b00100c0c108405554082c40301c04250140403000c1d500c2080c0e00780107448848101c899030b028141c0076903011071043ca01d14040c84003140b80440d510740030a074442c20003020400000c1d403500760849004000c0e68590309268208040111804840701040c02c0c90592003403584e2124491403e0f40024080c150001e8000131035100030602c03c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 272862976 1250 272861726 272861731
    0x312031b050304200307050d03030f0b060f0a0c110901090c08070302090a14180c03100f0303050901031503020a0801060509180c1c050d032406051605010615080906090f0c0603 77
    0x90451b056240c7d16008101d603c50420000e40209503130303403419060040c0c5130184000c3c0000031074515140480816240c22a4011041040d08000005003005c003008030f084201c1802e06002813415040b5a0340300c1c42032018103244900040001c43e460085070030076000b4000d030ba01e40784c401000c005c8558142101403070046403a2410300d42c407651604a07000b42c0703030314008881d0007400e940000a07542d15181c0b240c020a61210b6002200340700c030a60341000440d07401015078240340ca0910f17020580c900c1d1b8030320040121031240c00c0039610141e0001e00065040055111108540094032400341036034a00ca820310b0300c0504a007d01e0303c00d410050142d81c075481c14841d203a4014502d02000d0a0075010b035204d5034a0004d00d0344442011130303550281900c54038954000000c2c041180054001c40a0801e0341c02420760080d080e60100580040c03040504100c0c1c290820303000303048076110401560081d0700d8002d004c40300030b036980111409903102094176050003045e030004503441c0700020002a541a024080e0b0756000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 272864226 1250 272862976 272862979
    0x31503080405040c1e052208070303030b030a140714040b03060708061305040606050114070c06080603010e011b030b060c0a08070602070501092609280312031b05030420 74
    0x20f401000314950441c0c25020202c1050f40c1d0252500c01207c10303000041140158203000d101e0084040040141c00143c00050700c0d414600401d200c6003400119242410740000140418040060180d1100c0000f0b4039204980303424010340c0341c0b00101d0040c04210b405900324690540c1011b000104d00600038403249801280240102032100c81c10308070801180c200f9541112503076120f0004001039a4416940103842d080036802520340034059641c0312030300312248509028042800000f41c00c5640030361103402010814070080c05480c0310070040303184485080c000800440c0c40c09d4605485410f1203005e58038152942c2c4024020b41d8625203500000da084650100c0e141c0c0d4003000b0000028200b0300500c81d54a04c070b4000200c60740c40e2700c00e080104880c06180066000820b2000c0301d0310303075942c200f0780030030080103440565160f10b5036148442c40d070701e0b503080030b03120346c1c6503030002c028050b070503448020340c5503204406075402c12204400b100e00d44000d6401811140380b204410f005e099003610342d0f03401d0080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 272865476 1250 272864226 272864237
    0x6090b121e04050105040b010608060f040c0516030806040e011b080c0f0c0604110102060601140c0a1a011406130302011b0b07200109030c140c1f031503080405040c 72
    0x1518280c501c1c1540112821101c0c2d9444030140410400c154107018050280e905258126181c4400491118128101d40a2113070f070b02d45c8035081c04180900100c0d1820b6924070144400e8424900b800780c0651415100640030700d18110004104120610450444c222107041400d18040d100d041240e40b6000900302c0f04903501c0170030410840d507031404010700003035074108050b00c0b40d454107050186007464042c0840f4150341003201006803603a44004c00d9009489000d0140d9215141100d032146407910250000380260603803032030340e030300501f040340c007941200c0c1c50b40712a0502c1c285010a0003407500513840d001803091207111003800190302030307140d03684070502cac095880c80b048001d6103034032003090801c0d5a80c1006c03034643d00d140e850000c94030f40c100d0400e80510b00284609406640c00500d803412000e000303000c00d40c181500c950204003c1c412100c405000800b10f0038080340c01032a81040c0d80031181c1100c0440c0c03400641c000407180020407842240d400c818020b0916141c4024840075000400b0b4003401c00c071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 272866726 1250 272865476 272865511
    0x10c080c0f07030f1404140108061905040c1e0207030b0c070317060310060f090b15030a020a0504080604050c01080a05060904060f0204080a0b061801032d0203030304060c0906090b12 80
    0x84030b05c1c2c0600014000c1d202d01da4803d002420016080c06030140c07140340564180890801c000c4180e07002e10007110b078103a40028610520070812510702504405209803028580e6000c00705c00e90004034070301968042c5c5c00e60440c2d516001c01c4403040c0e202d401001400f0440300c005c03071001e004440b2591644460003070291046e600c045404182168501d81001d2450a0071100c2030101c20800e110780ca10410040d18845004500c2d840710010501005022084050300000c8201e030483c818010b80e0014010340003118010300741450840d844440160100780000e003c2e4001616840c11809154041c000183c142c3c0400c0d01c1e6512a03a01811f800d0404125251b020407000072070003400c12800d000c00b4026289075800d8100001003000c044072001088007000210b400620100b5400f0079017801500c4030031680e00308000d1440c0c468032805d14505020394540004000c100074014a50440401600c840d9180d90400744c50304019500c0901502a48010000c18480c0410304085190000e801142c2c05c0462000403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 272867976 1250 272866726 272866757
    0x140306070c1b171b031203040b070903051b01020d2c0102121303021e0102060a050a0b06070305030601090807080c060705030c01110a0206070503221403030702010c080c0f07030f 78
    0x3c40640544a00754068400f44d6080c00c84581410302e184070480242881e02400d9906c0d049900020f88003805224100d40800d0403140690010401184d00c0b8081d06c140c0074603c2c4102e0b0305108550301541c0540a4501e216a026206188400910f500000301c6600c036241c0c2d108104103420118030132419803040c2d90700a0301030301101d0050103501c0041117850340c082d400c51040c040c01802090105036503158152111149a8000c9041c0b5031010800a0000e02c56407080300c010050000c00c8aa96040140020a10181940040150301c81c0b031b0300b81c8902682aa588045a0b0380b44294803c1070081d8114540244140c50000010182a40150202d0b81440a94142c05003100c1d10401354260310640000d0b10102141c041c408544d00060b14240385086151002c5c0c0440d504481a0140c1d15605554202408002d503854042000800410840f51607240582029000b0a200340060f03002c00c4e0480300140f0500c5007841211200c03894081082d092050741c0d03400742d2384022085200c20070f21800032009510f1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 272869226 1250 272867976 272867999
    0x304260301031e0203161802070b2d010603050a0e12030a320405162601020c1f151203030b0d050a06090b090c0a06050f0f1201140306070c1b 62
    0x1b020091100f14207907868001d8100607104d070501d0300e0401c1ca00500521010961400d42c1c564002654090000c2115140113032842001881c141410420130030000400c020364183e02c0244500ca0345501001212004861550344080b11440070040c8041040014100d2310643c2140506007045517400c2e61800100c9018484443d55541000361034890404100601900b0800c03c6411614000b41212803802c0a0700107940640c000740c0ca070100f00300016401c900344403d60456078500030380d80668213180c800d031610209628402104001042c2400c0420000c820740c012220100e079a80c420341e090085299405a0140c1a202e007819408007030400200041001400b41c1808075200f0f81d40021034500e0344c13501c0c0d10401c4000e80550807580c81804140c9640d1201100c0e6016141390742016511018551026407241c4580b52124a001c0d0001c144100741220304008981610f1b10202080b0b4540c01c040c09040e95074404442900024a0440c043e401050b07115208850240503c68010001c1c0e4032128a01203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 272870476 1250 272869226 272869243
    0xf07080c060406180b070f050f160302010f020a05090d020d020307060c0b0703090b061e0a03060603020a0b12010b03100e041101020607090506071518080304260301031e0203 76
    0x1080c1c12200c20001088468030030011802848040a9050555074445c0c0404c0d950090040c41448990035100c00e0381c5018100b075031242203106100315078030380c0581860800d403189401c0071005503013044040069034040b4000d07216200d429940e207506216101c02042140c140c541c0d4145d810000c480f11200160314144580c0000e81819120210901058038003100c40c406e005058004051400c203100d00020010301000c0e8000c2c6007290300345500025101c0346258210380c000d4603980603a0048000003002180c2d00000200c078000c0f0f9921800590b0b62100b00c00e103103c2c0c500700c504041411401071010031259000742d03070052045080492000c0e00c3d02c00c0c0c0100c5000035a01503580c01c0d80d001c560102582e040107220340c840050316045410741c0c5444c001c20032a01840b0030041424101900da6400e25106a0241c00350094902d0080043c0714241041b1010381c1c0141c030103850004100c00130b45901c103420003030074203090400d03d1070a1840c2e1843e115400f012032036941e01d40103907280c4610036001d65401c004000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 272871726 1250 272870476 272870497
    0xd060e01020c150a1802040507090801150504050901111b03090d1a0a0b090705070204150e090615030d0f021006090203090c0f0d060b1f05041502031603050f0708 71
    0x80c110f4402c410004001e001000c80c84038906100c40d08040701000d105002c41980c0c1900c003c249622546415a0140225001401303590b01c0d100902c40d841d020b00b07804100b140c006840800039074a0718074400b1b090b20920503048503054010000c0d070803240000101d080c96031b0003a9095a0410a140740060409100c000c1c0640b4580c03a82150041400c11589a050304044114410044d84103040d0204440010050104003800301c08140c01c015901c0790780001103c0c84044081a0071140c90751000b42101c0420713129034801d4401e040000354090541a520b00d40030100030000c04005480d05805c49602e0819180d04085014450010b00052802d0040001900b807050015031645814241e440c500395444c40074500c1240e5100e03020203e600e5085500c100150400340c04a40c4940b40b60110b8680c0044c0301c40c0c0040202c3d1140d0102c000c5a01c00050025035030000e144c10003407082d02b642280d0301d010300414069012880c5814800003805500241202400503505d981011241d84803d140e0b80c0000c1c0d1001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 272872976 1250 272871726 272871733
    0x1608040b0d0c0c02030c010e06040b0309012a080c070c170c040f06271e050a20191806050717030c0708030a0209130903090b0f090d060e01020c 63
    0x70310960030310b4026180c03564640d01d05090072094580002e40c1d5416002400c505103c03040b0392040450315584210350103000d40380324080d40c0c0d06000c16600d009210710195144007441c074100500c60f191388844c0110b54024580e17038079825034483c0c00e526038659010a808454114020b8030001d200340180c0c00381d00e00c29021101510b8490f1140307040c04152040c0c1d0303d041c1e038101d281034824070400194450001c1c50500512000d030001540350f450700000c0600b00d0708040d0702e400a95a02c10410101e4014030f2165070205c1e01807103807000100d0440501c0781d200801420b0030000f0b1007420391a070216410708191a1091501000d0100c1200d02c452a201d00741d009400040c400007002814807a41d4040d004491a20380c1c0154507614000c1d030710800d80c0c00f51590041c250500000815211480b5070190351000e00b00501032014400200c9030b01004140d2040e00320045407030420009200314585054903203030110700d410513160254050800451644264040f581503030344131807162001c2c0e0244040c100405820303008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 272874226 1250 272872976 272872987
    0x5030603070f150818100b03010f050f090715080604090501110a030c11030406090501081f09090b07031a15070b091e01060b070201050f1204061b0c020a0b1608040b 72
    0x40480384010001545c6203030f0030b0900f9a440034000f0703180f01a80c151000024084210200007405000c2c5e5600c0e02d01d6040c207280130b0050110070745001601a911050494101035540c65110341c0641c45280308001081e00070b4009031850410707400a03032444e40302c0c400016540341c00d040300303030840c1d0000209040003941d2410469611a0005078a0620070004d500031400d0624100d0010301b000f000d070040e14104010800442d000c0c100c8100742000c03150048854504039610b410344c40b0000c244101003500e003101d6540c0401d4034a8041d1082e80c40c000c110f218003083c505902400d0111b94255a05042541c11042200e200483c007143c803e5801004c050000d440040c4909980d011643c0c404030445034540d15002e010401200c6c880d003154901942800d0454445850700700c5190940079410001105604d00c0c02003104005031130f8005081e90309505003001e0403140328071088a500c001c6010081d00f1150300301080c4200781c246c1024080413076050810300303800307682c41c0d442c1c81c903e40150340080c0106001040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 272875476 1250 272874226 272874269
    0x4020c15100608040b06040e030f0a0f0807080609060f0a051906030b061603030510050402070501060302090c2703011107050c01082d0a060b07030c0b090307080a05030603070f 77
    0x450100070102c1d4a09034105090a481ea14041440600b10a214a0742d4405c2550350550a0043da20f0000401003840d4907546407180c00f9000f9846d030b80c04000000d1604c800100005d010324a980e004040c060194481940c0e000c0501c1598050b031440c880d405100f44800041c01d9540488114086181d0081450183c0c5803010245c01e98103004030040c1300d20003d200c00b03d4400711104503511a2a00340c9400704a0f6264070a03150368062b240c0c1c20858016000240c0c04041c010b0541140040742e20a80d01c0c00d00d10364034501201030300d0281c08a000c03502d0b42103000e41d4000f21220304014010386401000040c50708070268060b501071f0301c130031000c544580080c004c0c8021503801c039030781c203a2008100c5000155a110407030910600c80c141d20310700708405417a1000c181c0483d12070b4400e00c0a0306980340780d0703550347c10503003000741000b510300c502210790080d40380c00a40d401c01c0210130386100030792107070b40c143c00d003128003005540701d4100904568142c8134046001500324440c0c10f00b40018491001100000c0308000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 272876726 1250 272875476 272875501
    0xd02180f03070e070807030908040602060f0f100b0306040b190e0f0402010503011203020c130e01051602120f07020a090203071205010510110a2315070c060b04020c15 73
    0x4821071003508241010409000c4440c280f83e840b005502d0001d10baa40e6a550503402000103060240000301d010034003084039a000561107000d00d030301d000ea008650345e62107800c1c1c0141e00210307030100d070305510110b04119002088010b5500010300510100b21500000081400041e2420800c641901114010080441707c8204a5040001c4140d01138807450650006030143c88184540d00e0b070105485081c006162003480300081041d00200f000800d100c002d07507600080c20b00c10744039003003a518040100300c081408500340f104d4860b054010b050100c0d240d03414904641c0000403020140d03002000303182c3c0145c1c4d40c48072078006480399100c01601c81c01c0450008000030200c1ca01e100a403407500b001401180d6614001560031900c03032034003049095010280c03a007000510b030750042070a480007001d000000101c50344c034007403405010110351502034948000b001d00141501d03100701150103407003100003081c400d410206545a01174009031400e8544200c403441c02c00c00402060342c1d202180d0a000c0c0d40e00070030703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 272877976 1250 272876726 272876749
    0x1a061b011b03091505071707030b1207050f0a03120818010906021c02120f0919050601140a060e0402030c0712020a0b1f050f030a0c0f030501061502060604110d0218 72
    0x850204036074501040047d22105103100843d6100c05004000b64100b032080d080550b106201401d8a007400d410458000d907200c072540111841381940c0351007210346090141d0fa890440360005200c0740092a800e1064400040c06400042c01680f44e10801e21618800d0140401141c4603610060fa1509004150a180c042c01c0d0748440d002801008810040c144080308207400c02c0d002400c8001a4640090561401590180031588004200342d140244400071800c1412184601500d006401001c410404000958012580803e8158901d00494285580616404516131010620340b08140c0c85418221030341e0545107005074003107542c060802c203980c042e10390800d403c1d02050b9250154030b45d0a4080d0b04050207428021840d01c8604006550304100807603000c1d802a042d08550b5440b801810703220740e418007044c0c40540c20440000b8001c00c0407240c7c0406250a6805804035848150030040036000742e100c903044851040c080400c14203114401425010100c014181503a0200d03024052030381081d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 272879226 1250 272877976 272878013
    0x301081603020f1504050d080702120604080304060902030a08041e0b040f03020f0f100f14070210050d0e12070303060f050607080c0a050703060c031a061b011b0309 72
    0x504030304000689480e0030100300410100d941d640c100390152080d811030700a40d07000d20751003c500c600300742c20f026642c0014050b49000365a00b001c0f0f55011881d40341e540e241030390001c01e004402c00c000740200325a03600c0152883e1000301662142540d585818030990011740011213030840802c2010050840380400c10014178003022101e0078240340041d0442c0407032103841301a01407119400c1400d803680d1019031302242c0c0b220041000440e4881c91030001d00030045800d810010508802d4251860000603082c0c0b0f011660007005a02004225881143c47d80c00039020020035a0311100700c1c0d507010b1800d10801841301d4525100d2611001d003818020103490381948030b601101402d0005200c2c5458079030880c0c0003a40c20a01466131008245404c6180c001445c0001e0164010032030302104104603500403032420b0001b03035014001080b1001d03161750600480040154044410841003042d04032140c460078100490380700014034241c0c0c2c907514607003403c090310f664000240d6941c410400c01044440407030300b6800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 272880476 1250 272879226 272879263
    0x30209040e2d0313030b091e0303040204110c06012c09060601080c0c070308030a0e010506030705010f030906110901021c0503010b09060c0d0905040c0f05120405070803040308030108 80
    0x10028080003982e030248800030006030b240d00031010940007003044840454200f5440c0c0203650380c0e0705040c80f0100702a14000010300469801d00c0d2524040303030a11803651070580181d40fa644035a402c0000400d04c003003c2000380c4000f882114000030062042d14000d0281d02889098242c10b0301c0c00095040340d46010081401a2800784210f0a50014099600036003c0c00c000d601d9485140c1512024004c04259061a1007079010100401a4400146014000c690300501107031000d81802c9007615021a030081e0036070302c02a805c000c25849801d03400946605400c0000701403c2d59186c0b202907034000c019502d007000000a40e20b080b940d0401c412503002d603035009030407200c0003400e00c028a10701c03041c85090841c2002080380740b8590741d9081110a080c2c800c2c02200c02081d42894050501d001500c503051140345040714000c4054007600d4103000410240d41c0c1c0030b140140600a2081c40000070300103a803144030340a4003040084080006001441c01070800707546a600d40321105180240e80601d043e240b04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 272881726 1250 272880476 272880493
    0x90503010903090e1503030a0e0427200301020c071403070609062f0a14070b0702040908190816030911100e040501060507022803140307060903030209040e 68
    0x80e07009001c0c4040c1c580d01303032104c1203507200d0740d40c00250380800300292079044c003000030341e08221504810324019051045d80e041c4000e2a65440710807000540d501410204400d190504001580c0300c2d61441852031031b8039090100c507501c0004030b0708a030411a101c0714141d004a00134004142004070b90308100740114000d255040c01d084000307000c0e506900c02c060500c007060035608019028508080c48502000c48415034001101040b190b80301c0115105036400f5030041c450440710200841d409040d12040303940d007407134035046a013440001c14150741c05951180c0e09000c001d003d0440383e0706003405403559543e110394900b003500a5603020711000c1302e90807e15180031003c0000443d035075000c02500004481c6880c04040040c17003590301c90302d0f1981d0307640c0c09403130f00d00003060031908034028000290003520110018050710507000b80c1400c072910155150412039100300002200280d07844c181c1d1042c1c0702501e081a45c555619001da07160741504902194021452040600305403085e40380c0d2070302d010002c00900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 272882976 1250 272881726 272881733
    0x3091704081c0c1208180d0f05070213050a1e05160c1a01080d02010606020c0a090908040e0f060f01051c18022205060a21110613060905030109 63
    0x440c000e2501040d4410140410391041d4003d00d04024410780060302c0008076604101c0051500000721100c2031024150348102000040001c0c881844040c0390310340400d40b001c0c0600646680d0450a070807a4405000c8220f243e0000550061301e025000c0340b1303800706400d01c00190201401042ca0000b1349034902c0c107400c000d00d105a061060044140c2418407660406441c00c1819407203c0d9040032842c050421030000a0f51342b00040c0444008440d58000c114650300d4000403070722600580306680d402500c90394284100803803540104910703441a5045841c1c550740341040e05d00d20000b06c41080d90f400c803000800c80281003220b07480d800b1030000d04e08203140081d111000801c124070301031040306d03c6a41e284401035000710031030540e1415400800861021607103008640a8035150020f000030070f41086c000c9595414810b81c4042501c0240032004104030001c0e00210070040690f100762002d090480300d0511a4550f200104901d1715422a10190a030404101400c3c9100941c03185010380c0c9006000c8020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 272884226 1250 272882976 272882983
    0x30a050a06020f091f08070c03090515130b030103030905010e0603070c061d100c03050108101e06060e0306090c0a0b0d09061b0906090501080c0306040609020a0309170408 75
    0x4507680840c0042e01c0b60b02144024905001c1d40b00040d4000d411a001030805c180800f5254014408595908074543e58180c2d088600305607000000340411580300085c030051a01500904451050300380c03103400c001202060450300a850390120880d5103000005000b0303da80b0103402c00141c8801c0c240307001d40e0400140841d05074030000307202074100402406c0c08000c01c155601310513084503c01c5c4070a0040035200b45c441d0b8a5910b080e10714085d1034500755520303140700d000b0f00829049030040000740514400c0401c4d448003030496581d41880b02c3c10031a0181b00150900d115444c06400180e4941c1d202d92150000e0614002c405050341c001c0b94840e125820341543c0c0c6201107400c0d5180b01c140a62038010001c0070302c02800800d60010034444c2020030084c1e202d16950405800c071840c55231230460b96582c8142c01c4d1403046044c040c050001d080b55001603018144038009503000800a000003441c56940c0784d10008a0304610700ba4000207880d00d02520a211500031003080000050004501e0140f8150003203a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 272885476 1250 272884226 272884243
    0x80c040b0a0e04110301080c04050117211306080a050703110406031a1809151510022e1103150904051204030c031203021603030e07030c0311040506030a05 68
    0xb0048040103544558440b03400000c09440000880707900d03961145c540c035031600591038025009600d008000030b01c500ba01c280905240c540100039202030100310305556030707400d0603001c10301aa11081020042004c0761059400080c11503583d0104182000c505c0442903480280000042600344942070100011250460301211a40d0400042440d0403580502030100c00708012544504170b07442c2c9403180400194014420b07440d4809a031807400242c10032080c81ca5080e2441c1c00406221000c000e144c4c14036280c4600941c907540104c0340d40300c1c5030a0303110044030a1a0721441802c01407405110403040325000b01c1500e09580c1c0581e034114a8228180002010306100540c030a05c5a40042400e20a050241c403280000800303d45940395120308183c1420f800038441241c1440034049003249041c4a40300340c42110b1040b00c410b445104494804a000e0100321004020130700880300004005070614401e1402548504050b805440808007001b0495400402c124000d402c440c00c6100010f07400700d001d48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 272886726 1250 272885476 272885497
    0x30109051b2715011107061b0816020306090a020306040f06150f061d0913060b1201140601020307030c06050703020f210604060f0605070609080415080c040b 69
    0x2426201103001038044a400c403100b0480480010140d50000052075405201c0c82544096804121000004540401c03940618854540220f0000c0c06180d00c110740350040c0385020000e814221945d51076401583d8455207a81c109404403c0d41501141130138010243d00101100c09000d0343c51094010a458601c010001092010301a50600070070610342e0107554400a4508095030b11526a48081c1c0c0d40c400e10300800011400d680080b03610b010868484203425900035042030300076110700c031410201840c20b0304115510f03501c41d106450241c641c4605280e0644803400049080b0b030214503c4440740f5405842c01c0d0464004000205c046600001210011580003100098590354898100c000780100d140a01c026000003805040703190030003200c490f111f41d60f50481c2e1300940b0b483d001c01c0111240ca01c910401114895010400540200042c00340c040c014103011812004542c0d81c12031540c0b01d60004400b6a100803078120410703901085503075001115800c500c0c5450308110aa4400380900c84245 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 272887976 1250 272886726 272886763
    0x806041110050d111b030417070f120510051005040b0d02062203080307080403020d08041709010e060724020702032e0f0509010c0e060a080601110601080a1103010905 73
    0x565414410001c44010303174801c0d50440e400e14148144981c0340c0e4020702c00c800d034002c580d0f10340400d080300c049038450469100c1c0711002850792414000c3d500014101c031090714103000320099290034882c3d034081e00c0d12a10b0361110480325181020100b100701e07940060458041c1071103040190060329810225500b080146104e074031005140c400448681000e80c0005022400c08010300001541001c04d481c00740f40700c1c3d020f0324410241820b086913004021030340584034080076840e81d412440e040005242e1000c040c500303001000c802d440407400c654400c0d00e080780ea840e0030007610102c40d00c41d28600744001c0b0a580d025441c0c48211740000759a6101a0000c6440c0c10781481403c1c00031144000307010024200c1c90b810311040201901010040000300e494a40d294207200400284510800340b00f030400400071b24050501850650849002c0401001c403030501c1381180400d9089907041249500800c1d02c0c1c0024190292a031070f0081c1c3c00104800414000d0b170600c0c588500050011a8100301d44142d40002d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 272889226 1250 272887976 272887991
    0x307080313150f0c110604080a181d07020a080708030606120a090b0105190315021c0e0d08130b150a0e060f0a0e01060f03020706060806041110050d 65
    0x14141c1c00340044000380404010030300c100721085035400c441c5603030160900800600c0410701d802d0b6031903242000c010040c2e800c0040003500003441c0e0b201422000c02c0700e141c8141d010404808081d01c502c401c0d040400038854402800501562000695a0100c00752016022403161591820941d010302c0500602050b00400054055103e0405883c0c1ca0104c2e135103aa151401c0000440c1d0050403050420f41e54007589600220b09401c0c01c1d250b0100d03042d8040c0c0307400302c15403454a5150030440c400c242c0002031502004010615403002ca03405191202c2510006544e07180c011003e45803042c0501110144180101009161030030b01c903500c4c04c01340d000200c0e0105551450070403070f40c444050035900d0344801c0d1a030b4041001850103003a9841010150341c800000051401088206440d03885010310310400d00c4014081e06105109040440410703041c050b0800c0a2035403054142c07109a009000c1651180007080140301085102102d04d80c01070b94008040d05c415280200035100b83c02d558407074552180d09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 272890476 1250 272889226 272889241
    0x304032006030a20040605070b04110303070506181b09070309020418030914061e0405042307110c040b0a0503010203070207060215090c09040302010207060c0e0114090303070803 78
    0xc01218000d008105036641d00d0001c08140041088810a40746034046100d4000803040b1803084506a80072074941e1400e200b0381d551088414030004000321810740f440041c0c880e00342c03400c00141c089248a0340103080783d440d18003811015580e407031040c080181e0080301e4050609070342400c5100c4069040c0c0f0301c40c20650300c103241030b0003420309040f000390000c0c03425025072104050701c020115151301c0303565081c10142d550400080349155204c00340b9403008040141e03205014140038810041001d00c0310441c14a03a41e00c000400b140c81d11198004608840c1c2c1c41e50407001949001c0650048042c00d1103102031050f007000a070740e21808400980595515a200780305561b030020f0340c800400c802030003075540781b0301042c000352550112f00c50310b00984210041a420400903c0100d485102084018030704880b405003084800c65000e0026401e5540c204007101c0480d1044c001e50720840416200c61030f01085107070005040344803107030840c1183c8406006556466501004030340d03030a504003074041d880b51a03251 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 272891726 1250 272890476 272890523
    0x10903030b240732030a090605120f100306180b090f060a0e0a020d06060e07051206010302160503070f03020d180b0f0906070b01030b1b09040c2f0601080c03030403 72
    0xe40395004c84503ca104d07000c0500f8000001c008907440c0c2d40d2a0000380f561070b03206583c18020304000034810a02580011112203800d0907a69111a07030b01540c854151341d80e201c4000310f4505070440c41e82109201c110000740001c120b00180c024000d0030051610f141040c03485515004050400c000d12622044681c01841c802c210401300b0680050051b25092500d280c00001015580300b031440040340710000075540c5005030141c500150003851484078560718000110001e51150b41c0c40a08440140000760201d40100081c00d041481070802d100000d10506010340b0b0700b100007111404103ca480002c95184801d019248111007202007800e40321112641d00350842d01821050540007035022403c001030089001e07032641201e01540700d0703401a0700ea410710858015440d09212050040401c951351240c18140d00009204c00240390585542c1945003030082c17180302c80d506011401d0b12282c43c0c0b140124052019600600c4190004e109030280140400d489000b10f20014081c6000751080548015020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 272892976 1250 272891726 272891783
    0xc0309090603070b0a030f06050102280203011107050a050f01020c030a1107360b0d020f01030609060f140901060f08041b0608180d0e0d02030c03010903030b2407 71
    0x21060749403985d000200040003002c001aa507008281040e90026070365002150060540351200c010100c3c40c4503501d035400e0304c4409110102d800d50f69034214800152804409401c9451051015103800042410058941070100e10745660a920411031055003040003c21203104480d6400c101c4507411459050324248000d035445009910358170302c1008412050403281e00c1d142160012506d01405220343c68504950b4070f020050342016020b504c00c0b015290004072480da902d8145004650b4503107841150068801c207138000c140341c81c080f0b0f1060040c0c00400b80c088511301b0080d0780185c01503240100c004d0819050220070400d0181c400c02281c180040d04003002102e00003000580c600c0760b0b0304d01d8000c15418003280c24503141c049800071002c00074804215040050015610705006c40101c0b01005400703c00d0450032030789803240c1c00c00010036460030301030080d0050280e2000075034407141c00144000c42c403075104901c4140b02000307081590329500e101a0b07101c413604a000f02c0b0410342502c00540c00184107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 272894226 1250 272892976 272892989
    0xf06090301090c060809030a1d041b0e030d0513050409020d0605040b010f060201021306050c0f06040c17030c06070806012c0109080304080304121b0902120c0c030909060307 76
    0x38009880284040f03200c0640444801c0d5a0340c0a40740d0b681100c0c80e440740607208002c1d000406980920603070801d1905001d5030508014800502c04250360314540900140001c003602140b01040c1040c01c603e02403141d41d81107045405c00d54a0103009001083d017040c864090544101d59414003078041d5100c03280e4054006500c52000c1000d42840c0c1405000d2900900ca07000385165103001c00314409106001751f4a0510488408015440c00c080f020786d03180e000407644030b1803841a40c0717822a0b0040204051406103000e84010742c04242030100c2880c20004032450b00c90a94400c102040c8034010000341c0300da105606d07241c078040c0c5403910340c0101c80818240060701d0f8030f0640a00c0604c02102c02041c411144c07403013621038860503540c60781480e85901581c4500002d940051008201d0220194076a90182c0d208403401c0d40c0c03021140c920545842d00b150018a03040384c1c0420360011020010104a07005440304a04c1810b0102c054686541d074494001c0042c0901040350128200b51010032540340030300380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 272895476 1250 272894226 272894231
    0x2070303111b01062102040504020f040c051201060c050a08210103080c010b03070f0b0313080a0f02010e01060302150c010f0e0a03020c100503070f050d05012c01050604050f06090301 80
    0x44400c1100c09201100c01c090315413034500005640501105940c40070580c1e203010380110702d020780130000109030007803042c2e0704140d0a01c0380269030f56582c0700300d1115002d00c2e124242c4604c030880104800c190142c012000f03010100c0310500200d04c002800440c0c4590000d0000d940304c1207061035031103507203141241c010343c00380c43d01c008410404c203c4003070503036400904002c1104d5080d0408159031150a03101d001d00c401c1d503055083c041c0348110341c000c5074041034181c03280c0400710890b42c03031640c2a4401703040b1200158000040d03109440c0e0a009400039513007400003d204050650f0001481440c0000c42002d00600000304149604003e400034280460f40e55820804551540031250311404c14290450047c012001c040344546014038941c1140403096403241c0c00c5d680c8000080c0d0700049240401000d00c8020b00c050800b1000e940503245c080c060542c800603034030029584880714401d00440c1500440240c0c030062025441c0d40c4141c03000c51380202c4042d1028000000420200e11901d01a03a41650 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 272896726 1250 272895476 272895487
    0x5031b0703080d021207090321210605030f07140105160b010303020705150309192307031a0f070f05070602070605040203150106020d0804291f180207030311 69
    0x910f02e0380a400380185140d110407039a502c0e2032089514030142d00000700720400ea50700c42040c2d0541e011090300c5070406030910a2040f011020310b03e01c19940b10300c14031141600c8800a026900b424000140c0d00d454010040102504160346a03c0000032031000740d040120100707803407001a03008241e104096401611088442d40c4038103000391244818051540280325904203078011180000440b88107140020240225030008150f9141e14603c0070025a0703190f559041300e441c4031081d040400b01c03001071000100202882c526004540c1c0751100390101c08503040000304103105a407014240c1d800060361600721141031500307200756114000c400020303020304c1c800b050f0310b400c004c202d0348114020fa000710221400e450546050303c031661400d0103400010b8000c088002415800380307210540040c840d201d5242c0b15041400c4827049052400c07040c0c54040481401e021030080f01a060300d149517021200c1c55a05420044000d401a4000c030403481020b5001428805061203540682001c8081401041c3e441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 272897976 1250 272896726 272896747
    0x30b010e0405090f071406030604110f03010602010516030507080f09120a20070b0d0b040b060d05070f03050603120d0e0a0c080708030301050d0803270a0b060d05031b070308 76
    0x206800c040114052050080210714045200c06c41c803150344c4010b007214a1540c805041c0310117011000020099901c040c0041c48280c8418400340d4040d2a4650001525140c182044041d8048981c2c0c0340c01030500e0b000c14083c00c0c40e4414001e0741d10540c0901c4c0078542d502c0e00c0490621307040007040c0b07428403404049400000190b02410318004601000c0d00d10720107221812109031642c24905c0390000c0d4401c10810710034950450303006442500001000010240200300c0815000d82c007021081c0c0f4503c1e40c810030013070381580085031013510b81110b1401b000301d880e1442c040780d600e40d03988807017824440e40440c0c00c88909034a9003002022060810a45041071100c0ca8138010181030703801420f0042c040e20102251100c400400c3d2070407101c0003011594030824a884400e0b00c0c0d03001404100c40b5004004007403461101030b8688100104015000b8030a11030641455070417220007429aa1181c0c08141c850008160000103569542052000d501500e095001d003a40c41e2445581c001005c4850204102e0040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 272899226 1250 272897976 272897983
    0x70503220302100e07060206060315010e092419090309060e131109030f010203070e0105180d150b01020a02031005130f030801060305090c0d0b0618040b011412030406030b010e040509 80
    0x840c0c0c2c0580823030710184c4481e82010745803015a40c088607102c1e10f0200400c9441d040310080c0d60010501c105441044141c90340794800500d481c80b0400903141d0607014010040c8540303050041c1a0b1a04008001c0500c243d039000302607070094800c54040082d40e81002d000703a500c2a1402c15842030500d002c020125002c08981c4aa4000748521031081c003c084803080c29100c1070003120f1055606585070850324500c4401503039980c020340000c081c1e22081e0007a00d000c0c2c1e00e41600d0030000601803809020201c0804c1c08280c183c031050b403040b50440d007002407a280182c4000800010035501484c0200e44e554561854a003001356405000e49002e50780ca645000b41500501082d041c2e403415501071000d40e07074038800035035034000011140e5082014a003980c404110f103040b00703a410040048c100d90f902c0c00303107440b00120480c0c10f0701c00b541d0084801004102c10b492680008c03801080c140d40281c150102122a036849000364400d0006043d101c0070001c00c581c2c410b08181d09010f40041c020803642c140381c510700380d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272900476 1250 272899226 272899229
    0xf08010c14090604051305040b0919330504060b0a0503100e0c0d1401060509090d0f0908100b030d170f0907051e01080f09070b0c01091e0506070503220302100e07 71
    0x406802e58004030701c802202080c0f07901a08400360310310600c01c1d1038ce034034076100e00b8000c6005851140d2840d420100840c5149120f10316002c81e410121b11414207084c540202d40043d08550301ca0203505004014030344020515455501041400050f8104456002403d007149030016603805000c4042d00010000ba62840b5891107034114001c0007104e40352418001607002c1900c090701c050b8418152451080d00c01e0480803c2d0540038540700c0e24440d55038800c149401361510074680c0407a25810300351114101080003442c0c1411500d08244001801003a5010240016100b40088002d17800044c2c00210100700d000001c010103000b040110399052440f240340d12141d480280010842e10124001307183c0c00417424003801d41e110252800342d16000b0350200a60000701806081c2d500c030807802020034040c104424403080e0030607607004510700c07510f003850403c3c0303000381103005110061050095500554040e404100d0000349400d1010030181070903071034541c00034840d54007a4204560504801e001007000310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272901726 1250 272900476 272900483
    0x10080d020312060405040b0109020309100c020a050615060a0c030c080f031f05100f020a05030d02131a07120507021201020c01140f070f050d0e03040f08010c1409060405130504 77
    0x3842d90301c0746001c02c402d4600940b800f0b40070070992001440001030f541d00640e0000820310845518a42902140c03081ea0103600a07240544c014052a90030300406205803580240900114030a44560a000910b0340c040c10034104100905041038000705030284112404094012041c103032100b600480c2c0707141c1179004071401c0d181813a0080070003000d00c040d0803000050f12001800c038800d4103001802101c065070360014150071440790603890004510180001c0c00398108220015994401d4003000200c0000198031886110080100ea28140100d5005032249640c1c0b100d500551294004800c071910f003d070050196004e03420401001000c0c2c415402443c40200300b000a10a815070f0030120814080100c070307080f2100500c2c500042e1170520070f94110300103404504185090040d044030b40740c101c1da22540328000a0740005410310110000110603801460400000e01c010a50383d88020034404414a800099031004201101a9a00d800549005c6c0c00094000304414072550030450207014190b8094 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272902976 1250 272901726 272901757
    0xf0706060605090307142b0606120b010501050f0f03131509080306191e030302190305071103030d0f0204051014040b03061305010e07141305040510080d0203 69
    0x20214001c2c000d4030f00206004018003d400d261000d000048261542d00aa1101c044403410034103400c1d41c03090000f015400c0244000714125464001d00700c8034035821000c081100007030440002000880624107640080c80d00359103c0816201c40001c2c0d0085a40c1d5107007101010040140581c1c9003690080c0003401010580f500e20241400d400c100e4101c81c402510701817003080004e1440c1000e5269200c0b031088a51159516a6500b102c8040044050b500309403910306a2402c0085c035604000e900071104c254100c0d907070307840c540c1c1e50058903501c03410300014204032004240900c951380a00030707150913030030440040c01001c40300071a43c00254400e028462060403d9503040150034400d1103001032076a032100d0050b282c82e0402d42c00659035040185100d40c801c5181050071240c0c05103010b03c070300030710004540800034201014054101d5200c0701f00081890304c18005415500000c2c0c4c6001b084a4080d940040c081e01c6050810810300c259030413400f680d01c10384040e40200350b8008001c00e2070b41038a0710303030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272904226 1250 272902976 272902979
    0x3270d03020606010f031802040b06070804261c030e251e080304120c0504020f0306040f0e070504090312050c1201090b0d11012d120b09010b16080f070606 68
    0x5030700307c0d0a00502c004241103003120f14401818594440c60040784010131241c1040d80a9032008841e50080d0010b10822000c2c45218861040071081d01007401c0c00c1c41c014103041015403159034090010340b6015405c0507100d9410742482d01d400d200158252070300d4140c240d00c6500c01d007250746d00c030140c80c032070101c0340c0e0343d410040041503c2c000580d009503401e80c07016500d010329080d4041c030103151001c01a50002031040000507680d80c2d0380300402007074243d2440301d40c591038114104011581002c15251805051000303003009210040303100801e40740e040303c0000700041107080840c0c1403403203d0081d0000301c0c60700c01031042596241015165520030600c03401016078950788140180c0b110034071140d4100d1400c02c2c0d10070004999020301100668185400415808901640680485c60040c0c0d08109000c1070f918260003039000040f02100b01d20072101f0700500c0d18070b00c08148055014440e03085070303000129131001da2180c0b11968000342a0001d0040e51a4080803100d0001903002060840307000d45054030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272905476 1250 272904226 272904257
    0x10b0f0f0603161206060e09010e04170307050708030c03060f0118150302070203031c0f0b03030702060901020c0d03110601060903111003060801021804060b0c03270d0302060601 78
    0x2031210014034064007a600319160380075080d0810800d441c2c40400c1c41009070340703a5080103840c89074400802c0350f591003a01c00d225103003d00071b0f1860f060300309100a401180402c0003044482d000040c42c01c906082c034990701e42c1c44540803100ca002d07601c0001c040210000034400044181006180a403908803800c954401c109401580c1014a03208903c0c0b40c20a8500300b0405080c410108003403d070144d0030050318001403580041d0440d80540003034080c003c28030501503502c4c03159100e81521148211f40c05c200c090040c00000f0380c0d034050b1041c0280f01d20000070b000300290f44280195110068054490002c040992801901c10001e9044144681c403400000080e1a0321806464040f650003410744480c6150480501008160a0003d40140754407490300003180c50003440144130300e840c0488810460707000c440c200020307101030394803e6031265024003807003a04030404002c0390050842d6011620200078445400722804480c500d11903484075441c80e000d024160049443c0e48240303030036a1502e0f0b11000c10359 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272906726 1250 272905476 272905489
    0x705030c010c080a02010b10030e100c020c040218090f0f0c03070827120414150405090403030f09030f020f06150616050607030b1201020f0a1b060608010b0f 69
    0x329454000350003105010041854400144101d0640b0700c0041007004d01c1101154a081600952400003a900c1801c1040000300b40804141d200600700140460f103940f00009540320095400c10340310b01d900003800364017460101400c802202010f0003d5807203250002c0300038a1070358225000700e5010100c200051160200b081200e1046549440701f0b48113880d0f4840c4202c0c5d12a61801c0000120843c3c0f100611100b020891848079010102406a42c0e0b410848581203000340e25808c203003e15201c030001600507481078191410b482c001c1da1400c0a80e561070400310003500071801032340340142c0b6007002c1c4401e2541c05400050a18440c0d0215156078010200481d074907642113800991295a107684d040c024907100c001050f02440e54907180b0503111071034541500b044070950709070011a907240c4440030982400b904210190f800200214181100940070401901c984080c201c1085409103080c0b1865240c4e01c00d8584450b00005c08210941e111600345000704060b08249200700d402c007648028515001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272907976 1250 272906726 272906743
    0xe0a05071a09130c020c0405090c01020d0206011208032d060f0105072001021e07030c06020d0504050409080c03181306030c0302060a020a1704050901090c051621090503070503 77
    0xe022150b018083c000300000400212000350210b000782c65902d406907845001e52800307841e010700500785600198001a1034540d01000000075500184010480e50003035400c0c425002ea0000e00603940c03a80c0e160050410740103540c40060103920140c0d07440303910460341c2c00110b02c651002d40300700c01c86019200043d2240d02072500003c01418940001030a441c840c10b5050307003a0403041c0100d6000c003100103000d81852501810103285980b2140b010800d120703e068914000304080e0026102d8074500401c0140680700c0ea00500c2e004075154041423080103005001c880d2400d903000f00b504e403034010b07910441d1950708050400603c0340000c240301b0160240144200c4003103a0388001d00c0d03038005180d903090203031076000b5101d80000c3d40038604040c8040307840190f07a900c1c035031003031802d40d40e649081c0350811850100c103030410541540f0304001005100d800c2030884446100e203204500382c2c2c0381540b07423300c906061500f02114800d84459080309141d0011704035001d0382e1003102a00c1869403180c05065684400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272909226 1250 272907976 272907979
    0x40608070806031015053a020603010e1e010e09161d0606070c0b0c0105131106070f060608010b0a1203020717010608031b10200d0e0a05071a09 63
    0xc11001404c00c4994007440004000d03c50800c405640c03a000103040110031200514810141d41410100a001c032040040c1000440400600040c0603004210396009c1406804085000c03100800d030610f90060644800c0101420032843d1317580c590504103004841079440d0b00e000c1c42009101074180490ba009102660040034044000ba4814490b0081d054000b8203800d030408000c218080105903844203810180c050401086d0f582c414252a80c1d00b126002000c81c0e6200045120460001e0885002804188021180c0c20703203450290501c00b46007440d590008050900c0d040d03001440725419004141c440d10101c0d0800e03e210340c1d8201214420159400040050f00301c24000d04c4840880e0502c0081781c6094400000d41e44d0f2941c0c0114515030280b090b0405078021140000c10703200c1c0030402600711a14004040c040c801801144103200d900145030000f488101042200110403590300c000812081c1038210341d241c06441c180f40b0b4031081d860044807030074100039a00c906820b54540844d001085c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272910476 1250 272909226 272909233
    0x218101e03020a1103040e0103020102060a02090303040302130b0301140108070504061401080c04080a0503090405010b12010e31020102250501031503150b03010506030a080711010c0b0108010204060807080603 91
    0x151100304400a40c4441c0102c02404003900d94585603400800242c000780660140c044515411030001a16008000b4011001d0303900420060003076440100944041b00c1c1d041d14444032080b400381140014004d041192505980781405040c0c3d00f07401241901e048415a009650800b9114030501081d11600d01600c40f00d1940c000584040394418041180e200340150f80d140e040035107901000c3d0400040e540d0980f819800440c10040928061140b00e0051061821540c40c00708071000e0703c0c1e40c864052145210391b110100004070326801e0754144110b44840d0ba15510f1080f90b490308070900841400340e05a00510079021800700020220000400c1c1480102d510f00e60980b6000044001c0c001c2035181c000007042c5088000002a413800e4007024880d01100003160380b1078101d00380b50844034028842071080d0701403111100420710a6088800c81d40d0491005002001c81900580741d81c54601001004a50040b0000482ca5012360243c410349810742d450000c1a2101c02c0e0445951300141c40c0d1030750540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272911726 1250 272910476 272910527
    0x4020903030909100e1501030c0306080d0c03050c01020c031207030203061c0609060e102f0d090b130501060801060518070905100309021215060d05010f021810 70
    0x240c910203e03640681e00c1c20625000688810310b41001c0c01c1d080d45c0030320903541e601030168501d68143c081c6442000b150714081181501d000d40d161303600c6e05403400300c1c000c0c401d07400709100a1620030421600007091000081d9607403251100115925401580403901403040320b0081492580300740201da00420000784050070740300c0b1510301d4590780440517000301d51041d034030351480001844501078070600818401c05490f1401c1202d40d1001a074040344412400d000386020b040320360031680300810116040410007c0d07240e10408620300000c01d6010006048100d49008219041056040d100300151040000b03100041d564021242030b03030aa802000e0b8031070303020f0b00000305020103400d846078070099030312b0010b0321580c2d21004104414409012040025143d60141c000c3d4200400c60054206200d030042129400c114a0512030318005001d19116111360309014081c840b00b500610718544005804540d03032403502d40c04940600804500302e008800c80c41030804000c1c0508107440784c3c1c044075886403e000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272912976 1250 272911726 272911729
    0x60a1d060408030f0f090907030c0e01030504150e03040f0801050601180807061b0f030509120601050d060c09030506240616080307200d02011503030c0308040f0f0f060605040209030309 81
    0x9030030440540d8030079217081c0071294590343c540720440d00a00c0c40f520b002903550044d0100412206500c000203040c54140018000040c0d8890200e82c3d040b0441c21001070700a0982018504601c541d038403610344c4410b10540854100b4040d84418011030090f00c0f4646448160042c0c1031004801c0c0c41026a15008408200516801480d10381070350080d9000c02910042c1e40d54031030b030004100c038200780c0008402003031441c1e160034900303580e1642c070801d00010801036150070b001610710304080e0b40040ae401d88504100d0780c2c41d8040d41c807490245900c0010b0f00e105140c1000f01c0780100548802c04000c0d03000c100c02022032410120103c0300c0307411104a00102070881070b1251041a80098001e200700b0440d1002c0d21a090440d242000e0091409009001107002001c802401d55a206c142e0407081c0016907410030001e600f00d1f001c580040e606091034403c640e83c80c01c00001138000c000c0c02603c000124140740c8100f07c2d4110010308140d00c40c403800c100c1c46440b44103110480c040c241c01c0d103406074410084405607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272914226 1250 272912976 272913007
    0x140117120d0c0c02041e1109031b191e05180601030e030405040207030e030601050f0a060c05010f020403050a03080c2a010f020c06010914040f06020a0e060a1d06040803 74
    0x2400c090b043c80100210a0790106081310080101c03e40f200700100c092201940c103d01400f0010078007c00c4035401c0070300d08030000c0d480b803070203500140940c181c030b0f50481856102d0204001d0041d07600800b0f11412941c40011240035040d00c0d510140480c0205408a802e2030701d070804803010340c00c1c4001081035540e074500540c010480344c441101548000e200001d01955140020310405202c0e03501c4003512103640b41450b28080040c0c03c058807800c0303c955412041e481d040300003400c550b028500000c1c40849410700301e004218000040844500018000c4280500002c1e1150254420781d50510b82d1b50300c92401260070702404407080c202c0003a5482c330040d0303c1014541080d4038070104000007806001d002c0b0b102d08a03402490300340a55009440100000442d91145520001402103445070614191b640c0003607040f2416001801907901180c0c2c0c03a5854440d039580c207520503025101c1540e540c1400409421015544540001010f0f00d0714400041d090040c103490454400100450a03c1004201c1014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272915476 1250 272914226 272914241
    0xa1a0d0204140123030703030c0f060608150915011401050a050d0203040b041403070803042a09020d060812180312270907120b060d140117120d 63
    0x7841034503910540005055040c0c41030003016820088072a595601c5500320600402d10a207521a400400080020a802c6501000c031194040d59561415245290100042c180c6802c80000b43c0314012005c4005588989180c1c007808280c1c04840c0d15030010382d20420000002d00614007440c04501c41258071f135000d02c020b0201c0e240182070507810300c5012080a801c80c3c000321010f80c0c0d900703890001c0c0001e006550880c22074030509000654609001d41d2224a014030004d44010400010250ba24010150001c994403044402c828900c220582e15a2100003941100d50301d40c00d07041c41c01e000051300c1d40001503004422460316054608062050348a901984a0755580a4050040c6054034040e4a00d21000b412401080101d511303c14652440f030f101c101b0050010240039940c204180410640c1004443c407030b41e03c05500104155818001142040c00354005050030340703007020381510528400303c4411f8182d030403001e01240036002c1c0c42704165841c060342c8121141c04070204068140b05501e034101d100d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272916726 1250 272915476 272915479
    0x9090b13210909020d02040906050102030406090b0f0702030f0c04050a060315020d02040b1b0105060406030f022e0c11010f050304030513180203060f010518060d0b09090d02060a1a0d02 81
    0x14a0307a20f609a0003641c2c8680c0503150303050b0b400142880b40c034005101c4c110142070203100446c1401d050610240c0700032011b00a580104801054070b01100c524401165001507029054800400c40381e0710346540d580822081610803030070300300054100d050714812841184c0e00b2447d903a82d03414aa0721188004d40c4a00210b80006400f04404904182c004000340030072400c02d503249121540c15003409084401c05004103106a0510904102040c8807000145815804035001d02c2c0303501c030a48000022a014488003c0c00d07045e11304190540743c0d00603040b0b5410034041c0180a0508010000450308412582c4803800851400c2c030100e404244540050541a03c02003607070000c183e120310310401068004400f095102e03400008004c22810923403032160207a1030038200341c3e0800740d501b0704408042411801117030140f80c020807903800207410f070740207100318090241000c01207042081d010f030380f00e03003111110201502c0783d107000c6000c0300740501c104000700069610035403451129404000092180c0c00c01a03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272917976 1250 272916726 272916737
    0xa0e1905040504030f121a010e24270603180a050a0f050d030507020c0d020118030f23100e0c030f071509080d2709090b1321 55
    0x400c0545451040900440c0070752a114801d80040d4001008881c0601080d041e0300d00381850003020818441c4919101d410900307041000d500c0c0300c400301d1038070615100220a292040848072802c02801c100419820030b6841580c114890004a00741c854040103850310b030000c400308005809001901520950821000169005044651209071500094041c140d81d0322070042c3e81b000030008104102909100780f410107000310300d45000083c1d15010034012080c0240c031514246001c5a1080c0e403806030820300c2c14141041280c4900b045201c011011034112000024414488a031840080708075051550380d40042051641301840b0303070060004c8048d0142c1c24071401300803400304d603410702c080c2c05007030f07031103001403041d1340ca850000c81da007000840100040c0180c03410140104500420100414621810b10140b40d000d01102596040401d0300c00c044050401d880208000d40c0e69004006400c1c060051401c560310703042185030302105008001007001d1030981d114107a1981c40c0f201502441489e0428 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272919226 1250 272917976 272917979
    0x14030a0804060806040f0c092303030f07050d0203031003110619121a0112150f0b071a0c0d050613090b06120307150f020403060212070e0301020a0e19 66
    0x1a140e068120390001030224100004000c840c0c1041d11032082c28090415042c041141400c2000e003e030320b814082c94000c03030a4600303081814a07859800b164410030140440344c1c0c440d0340450001a80e08140e00464050040000804110f4800001e83c1d000e420229000141d9600d15560484103981c883c21154020a06001d541e0521107400345404205c019038035040d460078911311500301140c40c1c1032602c041c41000c2000c0030300c01c0d0f41d010342821f4070596494000203452403000d0310001211a07680c011040400070000110340b505103540540f4141c1e10951107600c0f881c00c00404a14103a030304640103120158103220b00c14201082d5000b454019101901700014450072210345c1d400d035141080245c2c0c5881c080070910089081c540c42c150a101c0094001e107040901c0343c1c0d12444203210100b804e8069984541c0c800500002e20350484005540c400c41c11559038003003400c0384c0c29800c402c031480d00c08070f00740c500302940310b00f010700071500c0000180d601c4100205211041001e803403a081c0503a2001203c0000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272920476 1250 272919226 272919233
    0x807050f1515130504030c14030f0d020d24030318030f062408010c0206061c14070b07120315150516080a050306100c050d0509130c090906051914030a 66
    0x22140114001d6032041b03041a818101603c40e000c8c0c185181419a00030840b10050f4074400341520030182042c0703005a642e0043c5c5034003002600352204100c9a1407051b00036100d1304080300e9105000c907807007900c46414611428032206030030b211a10014002d5840c042c10700000545c1c5074001c030607051203a03801c0c3c44604501c0c5130b84411361101d600042e05a130764030005000c1c1590100206c940c400d2080321203007603991070b40c00400d100c035034030303000083c461403c004ac202c1e2070610500000e00a40a9441503c0c1c42e10001e040509200110f940c404010034905071130a01040000001350080c4c8200d0010400000700741c020864240d17101118206070f103040c462603c4001070f2841c00a04031290940d40d02a00c0e420042c04005205504003d100140700c00701d0180340008501180314007001d07c40b4104139455020b1000800c1207200d007442000d40040c54031080040c0c076500721025000741e55404030108080ca0312107045c42814840e042507200c0308848400308011040502c0e00c2e46c1209007001d000c2c0c6484100d540d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272921726 1250 272920476 272920481
    0x90302030d0f0e0c04020306060405041104180207140a0b0f060d05010608070521060103120c0b0708100602011103180a08120103030e040605010f0c020a0f030807050f151513 76
    0x5007260b032140d1100864000c44000300030146001c4c000f158114a0360600c000081c80078030a510505000e03d4561840c2c200c1620315109650080c008003400e0001d001d8102c81800c0298481282156011907209114000b16000134101d000039600045180e03940c1c031440c40000204030300500c040c4e4880c0e13842e0700d181d000030405e0050400a2804500800002d8144420030445907107001412b0b02076540031311500c507902d500048060440e600065154505400c807a4101c4100001000152200341848140405a5480304143c0d205007603103001650081e0b02d840c000c900b41c1e43c55034505c5000b88001c1c40800d01d2505902e1140c107450000c01c084503200d91065a07071000b80c2e0000a48220080d012030f004109068000c4013103040a00c1c01c8808001f16820003001902034403115020f6030030083c04541800031900c81803040d00140107102908043e5940ea860008413a44c0940c0c8100c03824040c9150103c1e100100007407003150900c20103008100c3d03070750b40a080040025501e03800c0368400b4080c1101e917824415403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272922976 1250 272921726 272921741
    0x1008090f15040614040807060207021917070b0c07062105010b0c010507030216060911040614010201141006050c03120f18070305030319020433091503090302030d 71
    0x9801c249403502d41400c1c01c0341211460f00c2d400c401203030000204000039502c84111a404c0398460f000584450403400402e007100480d214505030b203110034902241c080103000800d9000c0360f005040b1362032691030300451178031070040d105840e003070f90b004090501110b0300900c4074241020b54826050341e0880000c8031041918401e0380101100400002c081f04044030a0203195400740751410150301e00a007841150010808004010b00100d503590440000c00c04010690b18140e400200280802178464030b6400e00c0500c1c0c00d4072103000d50f20f04901e202416500e1a007d41c40f450040788440419490020103417943d40c400190900c80d80000c001030541220b0074201c0c540502c10a15050700640f500406481c6048061828540e403a44800e00030000540000b0840354014490403a6400041d401c065400103030040780c20140948130704a44015100c400c8440b04003028240d1031050030043d52204065640d520f0f50b0140c06000e6081c6060424550b0180d0458210540f280c8100c0c0d18000c10100c00c2022622213 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272924226 1250 272922976 272923003
    0xf130e0303070906020d0c020a03110112090302060901150f03110607120305060a08060f0c0a02070302090a140f13020105030621150c040b18040204030c09140a0504021008090f 77
    0xc03c04280034895040100415000c46030401c0c04842d044c82d000070350030032000e02c001460420540b800000b583d2107079084401e4640d005409009484152802075120001141c0e40c1e185980ba01000c0002810111061002c83d1860210386079441d0840d180d4014001403528481c0d008241005a070700000d140e0140a8800f802c40d03500019a424403c0401a5423419540003080940c007140078040c55804481c6c1058102860912840c0d0360302c1c2082060f405d080e00c941c40607501552540400402c080c02c5e410404c90640701071001d200b203a1f10002d8502ea1248281e65458030007114110040065014400558000038002c001940001024001c0b4024044800414025421102881d4150010400ca5540203040300c44041e0a00e4107040105801c0d0007541c81d040100d0f540400c41c80c200792506d074129005180c00a160040c125260142400503100f2101d41a0201c0a2407000070620340306d92040300d006940c0180502003800c00305500f01d694100c05408800140910384451020322820080700990640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272925476 1250 272924226 272924237
    0x1170c1b0a0c06080f1611070902120610050307031a060d020c1513020d0c170a12030513290910050a140f1005040501230d020f130e030307 61
    0x100c80c40c107060341c000c031640203070b081c05014014811441d1005c0c0340e0590041c18502d517884403140e40f540864004600030f003400150700039580085498640d94000381080503d11000007148c2c0c545105010100c92a10980c40001c4c2e418804100300b90702c40c2d0068001840443c80c040d540112010000d2002c0d4850360308600c0a0b64005141400301070f060005181e10541003045c4009460200310540740c204402100a10a00c0c02031000410416242503540c040d007606140b0014190121190583d90344130031100391880035130300042ca0429403090241510504240007081118000b650382c0059000310440240344540350795900325914020f80d540c161040400d0001082c0061aa4040c0c2c401c07603002400d40103805040001803c8041801c00c0c00603002051001004002c2d5955089031840c1d1059400865120741480300016101200e01034010b40008074030380d1407104070350700002c01c1041190107400940005c01000c020703030646080c0e40e141c03114030710351003012031110241c459260a40c0c0c4119401e070301056 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272926726 1250 272925476 272925493
    0x130c210308070507120e13051006030b27090601091506050306040e06090d18050901270e060414010c1d1309061b0503072a0b1003120e01170c1b 63
    0x540705009030211200340c7e1042050381041400307032282c405a40a00414140c881c0801406a203c1c0880d400f82d80c1c22020036850324080a6132000c14441c825940d90380c080c032030917001103809032080c4107100260900160900a40d454180d0640e0160001002c15602c50341d80d4595480010f4140305462003580c940c0054490320b041200f002c5c0c00d550b82d202c0300e4590748a0b20542880940c90760382400d0b0541d001c84000400b0008403ca0040340304107850200030250382004c480310741030303500000d0513130060784901650a00300c00c124a00500f2220540040c000040f2058810305190902d0840b200c85444060219802d86220b520381320280d07180d060003111508e65a40700d142403101c1e000c800a4100f551460b04a181d400d00040c0140503c80807441210f021b98204c4a03401c9000169042c215115030100d1600c0c06440c00410600882d24644000e948000d20050100d40e19480340c4094400030b40161510044008001000c000343c0c01c00030011700c400941004250b041e041032401105403141c440c0c0040000c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272927976 1250 272926726 272926729
    0xe0105150112021305060c03030601020c0f1e1f0203070510050103030831200a0b1b07050307030c090c080103031713020603130c210308070507120e 65
    0x1108010201890080d0258001080341c0c0e01c050446440d0304070610268541328082400380580720300d40e100b1076000710001a04030042c200400590b00c6594242c0a0300c1c520201d030828418480e41c00076403903900c000307980c03d49503400e02880c50307a00c01c2000150800101080c46020700c00d09019650020300503a001054440c1002400c03c1030100e00204d42ca0300340700c59450b5603030107842080003401d007101d00c13903001036000810008003084d400028480c0780400320040340740c20a48107244103246040f035040c0409485440740d040c40350f884030880740c0030740506140040041d0702003909414984000c07900d00520800258550b400c100d41c1020b94045c20301040041d26003e00c0c0000c0300c000f42040018801040010004030b500402d82d80c0000c141410100c1069460442c031018000c25020001d502006c0441403189d09010003900c044214842d00b0020b06081e00d400010740b1340b40300405001c5080c0c010404450029104501c51900480e075820803a08049950380c40c01400d4629500307100000d404800f400055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272929226 1250 272927976 272927981
    0x601080a0b01054f050103031101140a0b01051207090e0108060601020c010309021804080414030f030901050a180b0d1b120c02071205060703110a0912020d02060307030e01 75
    0x10082240c83c01c1c1c151260300240882004d480301c400d41410103101501c2c01540b40d204038039400301e05508101d01054000c080840060000703004c01d400007494051007000001c4144079114404000180f4007031960765034504040502140c2e550503040003000e003c0010301100350f000050181446840754180a4182081010f0404c0f0507480440e00b5407050b41408003590f00414011007c1c5001e1801150180150002c150030a400c60980c5584000c0e40c400c020078040150701500030b548003442803103c420414410195124080c42640300681c1041211030301c1c96000d10002d243c40041da007080c2044200466014070344400581c486080c1c0c40380000c10944445081c07160013084081805c40d0f55240e01d01d2240240a50350042c03a1000c91551045402d40c042d00801411006014075889003040020300d14009481d41000e40380749010900300b845c01e40c1840d00d5001603500345011541d403ca03500f072512310b820884045c148004d0b60800781c9040d100300035031114002548241000d031000b2524844440b491801c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272930476 1250 272929226 272929229
    0x114062107080c07030804260309010b0a06020106080601090207060b090a05090c04090330061403061e0f040f06050c0315010503070c0602030a060506071b050d080d0c0c050601080a0b01 81
    0x18000f9042042c100000d07005841d8941081e0880b85110007400356400d204500709140c0204074490b0000310811040000c15041401d6010b070985043c0c015603515070060f03080e500385020303a0300690880001231060101c00d07405042000d0060f10007207030340c603403400118020010035035600c111030380c44100300310700700c0c4080201c245520010b0301c0410a444003514000c2036026504124500c100501001a045400000050700749414940b010440141d07621180d02c0502e003400d43d00c90280c0a00d000003240090030580380080030480064810065070384000d0904183d0002b4001c8400c20320b800380450104a003803044034400d00c1e076031011682e40d0404149441c01240d9100c541070400100304100040305511040180700303035500c1000076849465503140c00014101d65003049420030408501013051002c0c0d001412800540d9028014603a034880041c4081081074400107000c0d003504000d094016852a8004229120640f03440e2030203da06941d03950034610203920145056024200860501071382d001c8960 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272931726 1250 272930476 272930491
    0x20d02190611030f0412210e09010e07050406050d06081204050306060d030e04020d0b031618020703090e0a090c0306051e090d030c050c100204090e01090b011406210708 74
    0x50401c00e48030f080303101314400d070701a1810801c100108a0104000c400003641d280200c11203e803905404442c0041c010b0b45004e0010348682d13205000010309401c8800c40d6801510540d1300d441c507081c205403041d20b46070322044601020540e03440c80010f16480a01c44c40000600c0d90001c945e980b0303c0c05c8101407400e80d01501145c86403805400d1003000070b0700711102440d4400c00b59001350b11130302034100e5000140806140c0b9600b6003d8140e6107007400140c02401019960700081d90050a03a01248040490044200050100d6014101403100d101a116010b038844096800420203a4447c1e441c0c83c507003101640f046070349544032410b001c0d4654040c1500e002c0d0b48144605050245040d03448551b50700f00c550802000c0c03594032101018124070407030803105003010220465600300d400301601c00007075100c1e100c0c541e941803404043c46107544c418001d880300a5080a000c480d10b034280810b18081903000c255495210a08000d1a10840000030304030001c24070090a84840c0c1c0340441c0080c290117001040c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272932976 1250 272931726 272931733
    0x9010e030c090708100305010e0d0f020f03161722150507080a0e030303100801050c270609120a020f0405040b040f0615030609030e0a080712020d02190611 68
    0x141071911100d072a9075120180c0d2501c0e01c003e4941c4e40307066014180ba6003000c0c28550078600118119100098641c6143c445a030b40c0f500311091060b4101d0b1200400e200f514915003040022803840c0341a407400c625501d00030b10450004000110610400f9030240c00b5000f00c2500b81150901c442500c900c03840300030b0403114217003000d84070303404130040c1580308581008040d2031001c0f951034601031190500e1880c003107000d0200d0341e40781041e00d8a03040010301403142808a60034000007401c40e51810094401005044215a58104142885009d42c51403c010103410800510603914650b440b03001000010440310041d0010403141d0060003503221501b800710307001e80e050406000005030b80a0189a00c940c00c04402c13040202da45c03410340090000b04200c01e00b9036100ca5004002c0c040541c0c400180d09110781c0325010020300400c280500000284551515500042d03010441e1364118404d15031402c0c80241142c00c040c40381d40c0083d5565414000030001c407005400180400c1e5000302c4034040c82c0003a40c004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272934226 1250 272932976 272932993
    0x17070804061109030a1e020a12050111070b070807022112060907090315020708070c05130e0c0409110406030515010f0503030405010e01031808031e0105030604020613180209010e03 79
    0x12030f60300c0c00898002069482010086c40070400c0011481040982c01480101119910b0108002e0f4125a0701c00350751552900c0c3c23420010142c02c0013298a49036120b4079003552039035020020b542440c0000e0180b0150f000d0601c4400710500b400c2e888181180c80d910141d07483d1504010700000c8a83c00814543c002c03004081440030348c0f9000510003040300d078845030301003001450803203803000380c0246900203090120120740300302003018120201054030307420b0700c2828001c0c2508800e031040e20380b6620001c1054204252860361818203401010005009408800710701d007501c000300e42241d049074415034194000010a0407072107002c0400f03d00500443c2c1c4240311450803d00065202e11440c403490341444038910101d41542d01903004500d000d1760842c00c5a01510641c00d2429003588101d41030070040507040740c00c843c00c000f030104084c1690000b4004150b5580c0c1d503400d00c03159500211518180ea00003074400503800c4100c020b2a03080094154015803240f0b8504005455450a4049944690485c004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272935476 1250 272934226 272934229
    0x20106061815050f0406020c0f0324070c08070c0807060203040f300606080105010b040e0109270302010608060a0204181a03030a020a0c050909030406050a17070804061109 75
    0x740c281038030351041142c800c11404500079030301c901c50000b240c40014004070300014406d4012400b100b01000035140070501c07da45004054550080c90525101d4400e000b010412407003540351001e91000d46070510210105403034640c4503003070f0004101100c00d8505818103200101e420311203640206600c1c0005d508041c20840c45840c0805c1e18003c011030350001140f840c14039184580b61526a56122030443c000f803c0c9030034900c1c003510081c0554151982000300026140b42c591013100c04a50800016170700c20390a1051513405000340756418900c5026003c3c12a05050002100c4c0d03c1c090311a400005541e4a000c0c0006d0400000a10203c441813040c00104200c04d420311a507034528290010000718144d5030f800b1041219880c60402c4e4051201044040340311b5000a90914801c0c000c0752001da4050b43c2e1410400034000484001c2c040e0307007003400704001301740c01075000d80340d01442410710111303d40c0c50440200c0c42030021075250002515035400c0c00240002885546c01c0b0a84240aa500c0c1041610 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272936726 1250 272935476 272935517
    0xb0406120605040c030c08010509150c16111507060c050708091009080304080d031109060412060204051504090507111f1103130210020708060a0518061602010606 71
    0x14001e45155140c00004041210b1201c6440185a01c603142c100b0702034035119424000c1000315460111440341428104102c16003454440c80360300c107000114034001d00c1c9040c040d5a207035241402c0351a5003480700140c0c8590303554131a0180e0140d120710b01a86540030350070b109094400c00d1681c202404010081c41d0041612501183c0c20010113030781e5600b0180321004101c0750741005900151a60101185c081081ca03004501441c10b00803650b01841610941850042a84940d4111940c05402044200045500c00500140050041c0001400d260341e9030041140351a282c290040009000201813000328920b11a02c6d80003581440c0c03c024000d9440ad006a0f82c40e01c04e002d00352458100301c9607140c600d801d504409150943c42031140d840e0f061503141019544000b4400b01d102d2680ca40807142c0a0f440041d00300c0441c0c800384003d000c1620f030740180c04010100605100003607070b9a54690a10001c1c20040079006060780540d590055070201002403c403040d5801c02c5080155040b2101160302401c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272937976 1250 272936726 272936759
    0x190201090906033210051803090d0308060a1e0f09150302010305060409060f090b0603060921070f03020a060609023108060906090607050f0313030e1c02040b0406 71
    0x340800b8000041c03003a000d912140e0301c8048000d0398405ca04001c5280b072000c0c0c01c02405110810604860740358901d002d1500c0e8010001c01c16004564445002c0201c0e05c03641d50303182c2115000d4000b04405440e001d52140b42111511171200c0c0c0004d5040800020300c292108500914155004110004603042d50303c0440400384006130405407142e011819907985c0350300420149030300c414100007256074400c2d10300c0a4803242006550b034600c4240014058100824001d22807510304000d4502050803c0405140b0b0799601001507443d9014001d00c0e0014162800030302c2c1d0039010f40c00034801c44846242c51429aa07194000c44400d40c0144509040203a8150203001180001c0c42070100d91b0803050984980c1b00c1c1103603c2030016110742000e0200800300401c40c503000319892020f80c1c00f81c0e0744003941666540705a039a602c2a6950400018404207000c00f84516503522074030300801312a01c03140001d401582d40001c20203e1014201542d411890144075815020f0804c0d03e06101651800107500361540f40c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272939226 1250 272937976 272938013
    0x1031a12010f0207060b0405060301020a0f2d081501050a05040e04021504060908281202070b0c0d0201061e1a0f0301091e0b0603130602040819020109090603 69
    0x80c504a912404082d0000c40c0c1e64142c810085440c1c0d003090a0850107428141c9045004034901404203415080600884844500a84964900070003110b0b0031a6401c68000800c4492140100400503d00c0c1004540000c152035640d0ba480700e042c0707c82c1108c404100d285416050000800411a0350b40e000401c0d00d084814040069865a0b2140046581d800328244407c010341000240801c01580010071602920100301c12211581007000c47c40b0848480b10b150485d03841c00007400303a80014020424500000e00c984103a0f0440e03a941e24002c0b079950407450703034008a03402001e030041d20700d542407040c1401480c2c0d8220901690012503600c0c0c0e2072050501a610607190b2181c4a1104c60410208951035a4211002c9542d6076a444d00e151009148000d805090307258062907005c52403000b80102180810005d10b802c0c45c540b80e81c1c091035410105020100c070066001d000c000740c2041e080c00102ca13101d0040d040031040200c94400140019019004501003a180c11000c0c000300380b41640072101c0020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272940476 1250 272939226 272939239
    0x90117040b160908240f04020a0b0f130f06111506040504080c0610170d081609030c030b01031a070c110d0206031e15180406060b0c06010608010501031a 67
    0x9000d00c0880383c2601d207403c042d94502c1000703410640303c02120380214003030540c1048800b0a443c0da0110460781c20043d9000f82d400488090b0a01c114100707c801441c004c0c010500003840c10024134142c0c400358115500107240042000d00410145800c00645200b1201d02c0b0050190402d08a035450402800900b03101d00442c0d03100300090401c046001102c1070740c1008411903101c0d1500500d40010242e1901030071040e0403410f007812070444000940c141d4840c1c200c0e11b54200d6176403000e031200a021154045181084040c0d42c001011034140090100034500407084200591304600b00140e00c5240040b450b1903500659003048801035010550540440d0700104007081284c0d00000600654070401c03010b0340c080e0300001405122408140042e201e0507154404860503540d000018140c0d14240d820103403c003c418120091a1055003241980244100c00c0000e0141e107911500140343c0100c0440e185640c04040140507140e0010103550040500346420b001004228016143c40302e015078800f4060355 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272941726 1250 272940476 272940511
    0x3010b01080a0e03040339030f2d08040503010507020c010207060c08120106080a0609020a0507150e0f0d020c03061005011110021c0f050615030702010f090305090117040b 75
    0x1404e00443e401907401c08618807a03814501040f10300b44031703094201c482c01c804134030501c101002400303842d00c00c698111440c0b00100c030840c0c4401031034642e9503682c1c403254444180c10200100f901859004290702514400f52242c1c10542454211600540203c2c259449000e00e020329030f90004a80c02545e00360314020800c2141d41c80c1c648140d028050344003403181c0300c1100101d4090303170050626105440d44c84060003150344e54040310b41244101e21120300040c40400404010030f0045404100c100044140009d0001030306e4100d50a0100c4958051200c1d000008140070003a81000958000d00007207010704424182002290b40070001480b929051010220030b600c03803410140000170905800010540d034a51b4610030202c10303500304948280c0c0c50381c5007070100d40422105110f40c6114030002b52141c0740c007040d510300055075504010942000c42d0340310440042c241e41c85001d4000d00e980f098030b030107850740c01c0072002400c80709004800c400a07100440170230007c18504600150401c00c2c0000e4600d062 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272942976 1250 272941726 272941751
    0x10605040209091306020c03070609030806150a0c080405060c01021b030406080a0c020309030a12031d071e03050d0305010e0106020f1c0201060506071a010803040305070b1c0f05090c03010b01080a 86
    0xe024a5002c7c2d08103010100d0b4842c00e00c40f50341c200d1048548603903030301c1070740d586c0c0d5204111040b02c0f03d05002c0c103207075414458403050b1801039444400c46800b9050580c00c160381c03000058413642c403058400f00340d40d40200d2900c0b42807844940d000f00030489040514140b03828a02c0040803103100802c402a04c40c1c03104945002e283c024000c840491101900b0f90320310320800d0501030f1042c0580c0288000107484c10440102106010b03070780c1c001c400c00f120003802c55186000c030002020025a07001a00b4009000000000200c08101d00001d400701500d000c58150f1604805018150741640504155001000d00c10103802c008104080508404035410210030021a4100c0c01000c5c01d801c059001900003840e0b10607c140c5250003640c1d00c6403910040c8140c0c1e250007084c0c0c0c40b401188001402548041018012a04424041c1020202c55079009040290407203811081d1044900c0ca944840d903104113000940009112540005e002a0001e00105141c000000d001c1d0200800d0a815665200b41d540f008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272944226 1250 272942976 272942981
    0x2040c05040914011e0509060f04060e13050d1d04050c0d02070f06150807090e011103070f18050d0809060c010203101419030813090606020708010605040209091306 72
    0x20785200b100801c50603107003298040350200d00303004100d001c180361310601082a81040380360054030005017406403e500e0b002c5c01e001242a901d02202e60083e281d8001140d60101502241d03c01e410003800304000042504010f0f0a10303000d29502800c00048141217400c1d65009050705901d83c20513a00001c280d42c9160341c0758403070b000c0c100018149078000282e47c02070041c1c20801d8001d03540640020046150300a40d130414031402e511420390070340c0001e5410401c50380c1e80c0d0702025001c80c034035001107620402d00300c1001d40341e03004580c0c4401094031580142c00055001e500d0365100c855141900c803032107041200040000b00300030340007025600005500142c80d150308083d03a0604203488001c3d51a0b0414410803c51108217010700558070f64481d5880003280b900700c10b4060705402c03c40035046c5060458451039203940c003c60302545030290480c80084d040c696441081c000300100d9015200b05410080c4240c207482099004c00e10130703401400114900c0d40c1d100700d407030b400208140192640004a10b03243c0007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272945476 1250 272944226 272944229
    0x80f0411120f160e0c04030308190f0908070303050f0906060d050a1b18020405100305130213020a020d0c110103050907090f060302100206090703030806011106040c0e0c07030c02040c0504 82
    0x70a0256030743d025074a646101c20310080d940070460184003590707104601c080340c1c0281d1102500080c0c4490104000251558680310054000300000c1a5041c800000b042a01c441001c1103400c2500092201306055040c4076541c2c2103803203030181001600304054204d81d5000c3c041e03c52441042111480303010410b040101101c0c02c0ea001d8481141140303842e0110800d6406841200c0383c0381c0c41c02900a0041149100f12415618010300d0010340262542c0700310010880103000138028000340c0300010240e81c0c0e002c80c1c0f40000194510160341c8140c0180024140800d05110f80c2c241706440012000142a82800c0142e0040a00c0c001665941c4c09c00310728036008042d40b00c4000545048412114250b080d0070040543e070084d02c90283e1804050401c0384c0d1103000b01c8100505400040c07040c03002074440e034141e68000005150180155442c154041d0420302c0c1518220f840f01e01e00c22041042003000301069601031043d404003402c1810b16240036100c0340200400030303c225525586030400d81e0142c0141ca0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272946726 1250 272945476 272945503
    0x203160e0904051e2401080f0706020d12020c06040b040201030e0f1203040809090703020a021204180b06040513090b0105010c12050c1006060804020406050405161119030f080f041112 80
    0x81d41c1e52685c1c5540f1817074640030f0065842502900024408100740024120700300c4225030f00074514881000e00440c0c850010071a0048120b80030440d000c49424200106401940100e40c590720f0b0b81482d03c005030443c1c000b007003150340c103070040305000c00100c20100310f441034007031b009001c02d94a69603858980c00303e1140304281d41e44510b1540900c0002ca03459400380080d032070207070221090807812841d444164010b5104e40b00c50004a0800b8044848240c1c101800b04080a000341c1c3c00c2580320000501031221441001c81042d41c1c50908905103c000c031421801000282001e0012901c0750702c403e000003040c0001030307041c1700002840ca1081142080001c0c035182c09003100f0001709407500ca00910859003a90305a100e44d00f003080101e814030300b610800b07000d036100c40642107618940200c241e41c89400304e034202407a800b4032601c1d025042d81070f40c01106210321a62310211068a80a40506034640c00760aa0340100c0100c401c010016218501c42c1c681044c0840c0c13881da03000945c1e00754514101c0e9000744030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272947976 1250 272946726 272946763
    0x902030706080f010e060a15181403160e0c16080a031b090506191218020102101103182a040e033a0203160e0904051e 52
    0x31965881101a4021000b140203d041a6a00c0c00c00412141090f140c4540c44142070201300103502140b2000c1007201480e0615081d2070114450340b5090050651000020740c1c250a60b0380355510702844200007400c28100403c03c0f0034102000c03888400d030300901800000c400080c80503041044d003c034142030a68440300d07840c3d49210b844002800791800e1940c10003c110501d40d00122940100054425207201038a040d040825041c4803000d4000031340c0e1480140415401c5184104049010741c41e00603100d8940002046090300c0024500180901d40c500e01078901440e50034541c402d4011260000e00203130b4500b0111091106031070034100703181c603e241c032044c1c061950204074883d113b1900d1255000c640c200100e0024480940d2648200020f2912000440039210104a808100008101c0c1e1003241c100d4003460448904080360b2060302c94204001d02041070b058003e5110b03101c0084040281d43d82e1480e4145940d0755039031510690b907841c1114130504c2552200d210100302400d000419040d41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272949226 1250 272947976 272947979
    0x8041407091401050d03082706040602090114040308041206020f0c010501090c0f080a020c07030219141206040b040611070c0e011205030406050a0201110a0201291003090609020307 79
    0x110040001d4007514000b407690300c0c0001a10b242c08003035048000e030542c46072403050346c0f402c00e00401c84221580d00303070f505010b190200d01c0000080200038031481c800c0400503540c48100c000989511050810070340d01c004104401d0001a01c03103001d03681121401d0f4178500320081c041c64480302a006e5021707624080100803551101910381500324604850303142e0001c20801081c0203045900b0301c1e9251126020403501400b0500100881e07000380203401c1010240c0b0342c0107843e0b60002d060710f0102d2580030300151128405000c41c04600b004030550308001c03240b9408503e011aa0192205401080074101d60011030014041c03002e6900240400c1d10001e050580c0da004524200040003554080c240150300300200104000c05d8030040c203090700360000000c40c00c00346000e50071555580800a5542103540b1210340601446006000c0c3c41ca1503d640c0000c01c800302114070548500d80000c2076070340007640343c40c1940d5490b29540c00c0c03036408580d989004541d440301400c1c81009404094030081d0180f00d030000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272950476 1250 272949226 272949239
    0x80316020a05040932120904091713060302160303050601020705040203270f0613050c041a13060b04150905130902130c0f0e030a0c06091404060807030308041407 71
    0x10b118005003494140004a2a114082c0c002c5902c0400c0c9072407036a405100c00c0d0b0361b03110540303000d0f103500040103102003140803255964502d42c40004400002d442d001040349030121000c5c0700003038081c0c4110700d021404c01c14424240c22030881824009824140e54201040003640b0070300405006d420007070001c1d582c07801c2043d41c01c21100c511560110a01e4204d000323110080801044220308542104010280c1d80c0f0713810700c0542d14801915040710760b4800c0340c0c44010151202c1c0555441c0200341407003041e044850100307000f0414130034040418040e140200603c40e20300303440150350995090010440c0381d50262001902d00d0400c5400403684141d04082c80c280e440d110b5002034248900c2507494803054100810110140c4030b030100902c002c2061143c004c05040d07c5007547c0078609000404507444504251a42480c00907a03400c9440000c00c208014040990321007408070150500346e5080140c2850039049549030030540c04020208841040850140705031841c4000d5206410030550760030903038421 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272951726 1250 272950476 272950493
    0xc09060207060810150917031201140102070b16060911010201180b040210031b03140903180d0305070b0705070c09020909070309030521040219080316020a050409 71
    0x2040100621030366101080481c03043d01c030325006070500c61502c02554280050080c0740710142111804200001e103001501c3c1c10b0349004050091b002001640d50b50405184001c0c1d151310580120000d840d83c0b1181011a99000034654122600c0d2a0a692104000e070000c2003d0350100f1070140910307041030090300500c05008040389201100740c000b04a4004400c1c0f44c00e103801052030019101c0415440014050300b00082e19045075880d510b000500e0030700010041d42c42c0014022100d0010344c1d9910030039020710182075640c3d000500f9800860904440d42d07110940c4500c000c90441c012010000d880042502031000d0340c00d0b495010b09042190329160358002c01343d4014200c103490f060f0001e180020203030800d00c2180c1c000740f40500104106c0da1411025806802c01c16801c8003001810841c0368031900c411800040c0086000c088803c590405004101c40410b0020f0712100c0300007214003c0182c44000000c40381e03443d1610a202685124500020303016081680c025900181401d00c900308011064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272952976 1250 272951726 272951729
    0x90302011803050d050f010b1c060b0c03070507050319061802150a0e040c0801031b090c031d010c020705220c0c031710051302040506040803120702190803090f010c09 73
    0xc04c082089036100c0c0f0000308100030a200d500b120701e2041005203548203910074003540c40810001c021070225070707403502000150320100352040c06400108245080010a00200e002840200e000340317801000d60321030f000005a12000184525a039140680c87e688118918468aa4004050510520014606103260360040a030100016614480c40308549080c1c49a1900d01d503130b9030383e00402d42e804c50741e41c46003052401030034401100c0003620000e0036038800e0290342924030a41d0390104084400c1401d81415802002321103000c0e90408609181e519400289030084032402c655031003100002009070303200e03c180d1070f0385101c6050800b1110702d00280c00c40c0703140d2070b0a0f10a03501ca141550110740080480303130341581e00014041f02082d04200c58607200c2c040901400d140c2000618082d51040014000d6101d6031055409800204030611400384241d85031758015000d00240802c00a440c01c51110f000392010020f004e1000032000c0781c04240200148081c0c0101d034002003088010040004e400c0326a207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272954226 1250 272952976 272952997
    0x206092b080408060106050304080a0503092b030b0103020408100c12061212030c0801090c0207051306030b060d111e0d031709070f03060f090b01090b0a060e031009030201180305 78
    0x8031000010000c0c8141c1c08c4902c0355401440060030003500c45000c60340b540c0042c0c11005a8480c0340c0d281d0140c0c1e410100171321100e040e1480600540c035480000a025150560398040c14103106004c1000f0895010440c040a16112440080c0c00129440152443e203040030748810060f1800c400860703050108040e40c0b45550080001e041e030710b184a2030840944440d085900e00003005200100002ea00c16004a0400c03101401961a00d50311180403842002d030030b8a003042c000703850302d90801c140040860b00c0740d00300000741e4503540652205d4031100b465004c0190102d01a8000c4018009800034441040c80e0b160704c020100c0e28248a18200100400003203007280c0c21744128500407816030740c4000340700340850301040501c01d6041c5c40c0d80c441c24003d00c000602c0c460002d44401c3e40c54002440c000c110340c00fa0016030000070381300056a00340444010a60414424003500307103008001640c00081001ca03203a4044000301d0032020302e107000c81c09450921080e108010b542441e800805030000040c2184480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272955476 1250 272954226 272954233
    0x1e0203070b0c03070b09071a090f0d0507030f0f0f08030a0b27040f0605010b030702010f14010e1e0a020a0e0a05090103080a0302090d031e0c0206092b080408 69
    0x8640005038101d00c1040b2014046600400040000840404c0800e50080100060313401d03145e9520351004040001c0310041004002c00a16107045103408091007082d118196451034103181d00e90b90315540c400e01404054071968001400401b000036004a500140390702c00c2000307550429515000c2d900e50400d80d500c0400074101640600503090440c2d1103030811101054418503c2140035020090036400b600c185d800ca1a10a819808203049002d464020031aa6440302da403854521030003421210388004140300181869000040580c0e041d101a0658015181c140d400d40c9070031174840300391104641c4030a041401081080407000c2c069006e41030002241d1a102403400e01c078403c0000100c20340c010158482060320050000c511200c010b00700701642403c005203021080800142031080385802100000d51010365400c281e1701040394911009218100348005203010781c0010058042c1820f09401620940d0040c09070828401c0900e001441c076a16403860003a007400d094907641d01c14042e1075a03520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272956726 1250 272955476 272955479
    0xb040f06051b07140301050f0c090411090d030e011701060203040e090c0a0b130509060d0b13060e0c121b0f03010f0f06080d0906020607050306010c0b2401050c030906030901091e020307 81
    0x1401500c41c3d0f2700c5040384401e00c6251071001400c0000070001505000300c219402c1c03109003020f841d0881c5012006000361111070248856200040c80410781d51b0031540c14506080040081680000544068407408841b00d001541c03440c030400d00d4a0301114030a40c3c45029441c0c001400301441d0024150204404644030100b0384405c1031012250056603802d801c01c905040400105243c1c000c1a0380003415000200c4d00a0f210382c42d10826500220716500840c0c010b8000d211031440d1221242e840314845a02414501182032000091000300680311030040f01c0468081180b0364082d405000c40c4420710404200d5a40340740c8102e0020040d501981a5078440e4205428845d40103064a1003180c603182d0044c0841c0d642c200b01101c41d5040a0102e0303050180b4522004009103044165510404a0640c0255a4507070214400000b28114802c5130602c81c0400c22049100000300898031140002e0b00ea03c1d03500d84680c406030340109403180000e402c02e465005141d900381c09107428142040e008404581816 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272957976 1250 272956726 272956741
    0x30c052a0609010215131403090310180f0c0803121506090904060f14090f0115050d0609080f031e0618060d0507030503030c04050a0b040f06051b0714030105 69
    0x180309041e502d9000d607100350b08096501001c00e00165212124108008801c00d96030741d04080c0e12420207000000b07070400308119016041c100034400c0c0d8021140070500030f104c03440306125455643c41c84040c00c40c03170100020348103005001d5075000080c07607610116a51005030110519000b401641e14041c5141e0360006000b041c41e1001c140d03201c0c6440103088201949640d80d0b09001009070265620183ea118035104c08611901c004c0c03580300b450140d0240188200b07251081c0d0843d100309032441c8010030100f10912103903c03213524074028640c3c4810009805000380c00c210a150003129250460384c60000104030180c60340d540e050714440e00811400000340c03500301c10003154604620b1018a00315082d400240c07107151114a1204180c080d80a40e45110f03141c0d03c900782990310494420080001c0002d0403c21410050800002400e08103030050a007402d045110319161458401d050802401140c1044550b805003280e810380c03207003d001c49940ca5620b25034407284524880c0460300c65480c09000816a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272959226 1250 272957976 272957989
    0x1020a050d0c031106010b040b07050c0d08120a0c09050105160f0c05100306050d03030207020f030a06230118020c150906010e0109020705070b13050a0305060604061e12030c052a 78
    0x6981f41c440d00c1e03d040074105a0681c5040d0001c0100341c0d41d030301c00d512000c02c15480e511501620207003d03141035035555004071010714080ca0301411445070180b4007401070080741c0e0700c0048501520b6092070300c030350380b490440c41c030001140d91151702802c4120b01c040349404011454052000301c1c1c0040da0001c0c00088a11030070350880b04540316081d001044c241991000910a5004003c0103200800742010314003a103010910b0802c2c9400100c481517035401c9400c4018920251404103412010540500c0750704144002c21f8100c5d03001c000300100d58021480f4000080103010290200780d0a00c1d101c2443c0c0703003220b9100c3d0b4a4000f03100f0b12060366684400070442400034000c441981d50008010300a0341d1404c2201d400507480160780180e01008a07401082c82e41d5403143c0c072801140100c00920307450615000304411100d81da805030990710010400b0080140d004aa0348040301d003000c800d00b140e0100c0341029180c541c401100140b0901030a0500401c00f0020f020b4000300060312040c0c00c0031600c054090105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272960476 1250 272959226 272959229
    0xf06170f030c0a120903140105180115031412071101170105010509120709180b160c0803040f0605070203031e2e050303120118020418020901020a050d0c03110601 71
    0x2c40e40c008050700c1d400f0441242200b1200602031a02c00e801d10f60b0ba4036150113405280c058484265142d109024551109403d90a00280c25000800c460700d084d90041c0020f00c2903100090080d9502c2e000500424001e1111361118200900c0e0195100f030746203410340b101007d1000007804900700500218030055038000090607200c041e141c80d840d0640780820010800b0303884022021034032603044081010043c500800441c601031b942d00000422251030000e61070703180201a01030030103800f105800e00c141d00c14200d1220036000b0762885d5880c3c4842c05d15402e081c150300c801812007802c100034065025030000c0207620803540359801616030038821a01000109058620003021882e410406030701c0140a50f0340d146040300c024908042c00d5540c03001c1703800d541081d9514402005c60000400080b01d009540c2c10420300070000c11480d19007851905061241715080e983c14040e0b001c80c1345c00303032a4000c01c402d02c00907400204a0300601c40c3c0e0f010041141d2102c0204034001100c00c4036849a90500140660 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272961726 1250 272960476 272960497
    0x20306010e06070f1b0602070b2506060e041103190b15010c020904060c140702030307060903020a1b140f06160206120a0219110a0206030601030f06170f03 68
    0x85441d040101041542e030811402515420011003280d8006211501c03241e80c01d042c1c1e0140c0543c401d00c1e054010b0304046ca50345c00035440c07600400100c40c2007142250318940c02c210b407041001c134050560034171000802c82d581045403094005070900c010300803140d50801d8402c1049045038541480c440c506101044c0c2c00400034100c138443c0010a01040000c000c0c80040603042c9400301050042c1d4000030f10041040e83d080d22143c0e81c6490080300c0b2540b0075420f40000306842002440d1a5282d408030b0f55900c46c1a0700035056507511205541051301c24008060710980002d541000002c0f107003d011014065442420116810b4140c007420303070b0504211a0120541c01801981017109200d03447e00d00c00300c5054103da100d00200440d00c10010800380c914010400b07040010307290018000d02416006000120300d06108100305080f90b50540081c01d500c5650781a03907440d4a036190f0100590150911080c020b144a00f00701d008624a80070181c1c01d0740003812102103405401903d8189626441524600c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272962976 1250 272961726 272961737
    0x101406100516060b19031110020d0206010b13090e0d080112171e0c010203010302030c090906070e0a0b120f0709030519050a02061b0f010e07140301060e130303060902030601 76
    0x790042541944042c4da050070290520380c80261285a070420004660012103054030110002203180c100980d03030440c4c40c4024001440c0e404910140a9980e040c1403003070b00d0070020005000115211001d000100500c004402030007451003100005440d124403910f0785000a010740e000003000c60711084c0c0034a046402400500c0720342c04112442050f5032001c20000c1036055405080320741080f61f0b10041c0802c03076502c0001070301c950441c8101400c0105821546106031062400d00640b040007242d401d0700100c43e41801c03510b00e08a94007040c800c00380c0354004035180074003051039001c001c912550036101d00d210719004e19032551009019210004180405005640007841c00d00e42401100b1a90700074502560445210461540c0002e819502c85129401803042c2005030a12001003007002d404508100e40003071007184145c900700c0f9650020341c407840a5546101444c00e045444c20340c4030708003400c1d115070b07200d885103840040303803058880b441401ca0009140050014013424188290f0b80038210580d20b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272964226 1250 272962976 272963017
    0x30d0203090604031106071b030b0702030a0f0509041d0a0507210201050a030b0a1203020f0c0f21011508070f03110108370e0604021807021014061005 66
    0xd100303640717414201540c1c00020801c0700e41c0c0030484040d01307001808103d8001003075250840c03901030740c0e1600140c0a2010765000748a404800c03500000c3d142e0720441a03142268840d2100300020f0064000e080c2d60703910309614828103455880340800c0b9212060701490840321090340d01c10304051204404800042070078240d100b40c0e401584a0b90042900320020710740030569001000c005500a90703140e201048c00401d00040608258040c400565a4040a0060095240200301140d03225650155280c841c1341d003010480c01b00c814010806802007030050003004a034400304040f1030348200500890342e251086620000d003018103610b210341a81c3c0d02900c035032103100c0018010743c2c092030040c00810010825000324104641903943c2014041c600314240b1594120410a18080700c01d140e40140c06a04000100009038840240704060b03109084004589540c51400072030403d0b0b24864108401c1703051000302c00d00d251140c0320742401810700711241c00300300c4100e03002601e5038840c180e010b10903c92410344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272965476 1250 272964226 272964233
    0xc03020c0d02061e04330b100e041808030405010902040b03030f0d050c0f0a0e0a090e0307081605070906030312060e070e030c100903060f0e03030f0402010509120309030d020309060403 81
    0x21312503045449142c0e1041c21161141c0f1302d00003032000c0d5245000940c8000ca0320100300b0402d000700b00c2e403444d06544a0806032008140108121071104245016580b80c9a002c20030b92901c80d0300c0f8405070f810001050701d0f8102864030502800e40005d050340b01da414098001e1440c58040204c40312a0205c800f00e82c40d10600d00f01ea44060280202401101c0310701340020100c41c18540e00801d9080b28546c2c494038525064010002d003800d850300301d079104070714014803558038000c00400c440006420107082d0351100450b04250440c0505500002e0042c09200340000307801ca070642040302500d1007030b19400b058056464020044a801f0301c90a8074000382000440d00990041080000c0084040c05884181608501080c2601b0003415507000045c100c0400704184005403040c5c4c0d480039041c0f8003c2c00001c942c0280075550340030213082e002c545925107010404580c01401100c901003409005103403620b60340d64101d82c80b9040803a140e4024020010074080051000c000c0700c0840308000c3c0101d00307090850305e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272966726 1250 272965476 272965531
    0xc09040b060d020a0603050a050a06120f050304120b0103050f0109020a0608190c0504050102210910170112031824110106090207051002041404110d0c03020c0d0206 72
    0x90540b0b8001c0e101c88009030158503000800b2024280984000c9130b0b50922040103003c0fa03c00800c03007100d640c40d04606121015011089428050304404204003420071820450700703601c606e0303215051040440f4000f0040110316000241240c2c01002560055220078014509840290200035401102490103209040c0201e0f100c0d0f0b00650b80203081c0302c0c80c546215600c0211081034000402250002c14200519a030410851600b10a402c9181c078440c04000400d841c0c60183e41c0005116090a8040d000400d1180c2d00c5d07131000203000d01404c07144d0b5a44514642e448115800305500150150f0070207042011440c000d401103c0203202d1141007101004013020600c8006103508003005001c0c82c40280704002406108003030100c9410041e503828862034001d291000300c1c69020040340c0188000c00c90310641d008000701034101038502003a08407580207032440c54070910030b81000da0352500c480c05084c143d0540c0544070810a02085451200b1409000e1740d880404550740c840d14128084144981001034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272967976 1250 272966726 272966731
    0x1180e010f15140d0e0f011416020705060415050705121e1219090b10060905120d0c0204140f04030e030f0a0609030216030809030d0e030c0d0503091009080f0c09040b 73
    0x317000c1e80d1200d03000115950070f6508061044d80d03540c0501e814480d032503400b20091544e030310103030008003201ca1402c070104586004a1055414081c0b40035500c00c001c90003036044404003680710059440c1c0c1d001001c100944c541005201043c1408120052142c800c2140700b00c03850741c1c24440c1c9048851b81c030410070f030181c000c00800084040c2c0c1c0360a84040054200c2c0c0c1c040d406100103a10080440e410000018454032042d40040c3c407404500003417020b9007002251508501406140201703c452071130003ca00030b000141c54030709170704407900c0403c0040e00c24046c800c0e003d140b19a03503010508820200300360341e580c15400800400d40107400c81b5000118103901c03404084d4400d00640e8002c1d00c00c042072110050b100c0d44161500c1000203038001040ca42404014441101400c10341c4004440c0f0002c00d0340c41c2d200451050203038404a1b641424003e04000b903d049501c0281440410780202d140208581100c0c0b007411401e100740c03c01480500c10114181c003420101418a003c1503403103848218007031a01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272969226 1250 272967976 272968001
    0xa150b031e0a0f090b0f0901020a08040b0426031f0513020d06080105010602030a020d090e07050715110705010e01140708041b090506090f01050f01180e010f15140d 72
    0x300c0c0700100101019001344a002070080e01886064a040c044541550a008110310f50f07503481004520000358200d50000d8006400203014901d41da19454401602a203100707246000c4e400300d6040c52440c0712014000e501c940c561420003104000c0004500c841903501e801003039030100707804014003055400e50303015217480102d010010420b9030395500103e00f120701c2a002000182c00000d1300c40c030700540410a030400741c0070615001000d0b616084a650700d404001d80300500700304001949a0502000360707400040800118009c05c581c03501d01e00226080d40c01280b04803044d50038070381d10f0b030750302d12041c400c2c43e908503240000c02109a03901c140881b0101030040044888503000900ea04a421480c11528040c0a40810008003420207004102001c54014901c02c07491650100610a40d1529040c140c0c910b602820440c081c4100e103d81501c003140141c001ca00f10035801400051620b41003030003035048442c980d400c1c81910500c01011106072400d84681035140404018445d981c03c120f0348001d44c071143c3e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272970476 1250 272969226 272969231
    0x30f07150e130c030203040209010e1003080f090a0e2d2809050c130b2409120604121805010e06190903050d020c010c02040e0a0203060a150b031e0a 65
    0x70456500b080390000e001010000e94040104400c50402c1d44107540034001c072fa83c140b142860b000b102007030b000f602c03404020306601c8041091860403032040152116494014a81c81c1c4294440717000803401d010403900412800c2400c1108150148034200004940015000d43d24080c0d60b0307507045d00007048005260421b0300c00c07a40c52a01c403081c034512403040c4541c400c402400c3d20380780c7c002c2005900401c0340141d480803803030410102100d58940740c421705826000300701c0c9010958a5941300b11039000d4801026081040c080c0d9410a0480210700c8510651049010200002185000f03c0c0c40300c0c45018140001c7c80c4080e802d0100d58040c80e070358102c01034000c1850b0f00e0302000c0815003000344880900e80000c90508282803013000700c01c0c09000351701030040c030040454200200000f000c9044550b4040d02881d540c03142c082158030103100110f071258000d01295110f0600c040700310000e0503512007404010401201c003044241c0100101c9008000755800d140b18920350710f108921145c0060540b03a001603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272971726 1250 272970476 272970499
    0x103020f01140d1b09080628020703050d0f02030108070e0a020423030d080915090102040b0408100509011b181806060306050607031418040f02040302030f07150e 71
    0x10042d0000c0042034426080414445601daa00c55000e0044a81c110140450320b581841017990015580343d11007032415182c0042d482014800012820303200c146140305000180384c2c01850703007000042c400d91549032810044410b0741d00061040380028003545d03483c1d40000714100320920904c14950b40010301090014a015610280680754203c4070540c0c4c2c520000103030380014a86010300030308142260a0608001501c0c1400d142600c1d45000120b10a9a80d0080701140341031809506880c05041d440d0702140e82c0d80e0b00e40210b80c4d81c0351850b1000c02d03000c3e401e0100280c0240b1041c0141c0040d0525030f9002c590000c10180140c038144c0e5010300402a05040c08000180b91700244072002c1003002c1d007100056160704050000b41515059041503010768001c105442c00a90b202c0349203080194420000e070b48030b00c0c6a885803108061000b60143e84142410100c100703036203180c0d004004a0313108030100c0d0011030b03008075429211441480340c0003002071360400a640395070140c9094140c0c05401450140c450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272972976 1250 272971726 272971757
    0x1d1f0501050f01051e0313020f040905070501051305030106090b12010605030a03050a0201090b010312020f12030c130e010303051305030109030225030f050a0506090a1203020a0c06050412260103020f01 88
    0xb1b4104039060580e822034080e0031410360170502091003c01d00103503018040d824447e200d00340c1e121941d1203824100b2100141c00d1031000170740300701c07103001c2c1c00000d00a0100750ba5407000702000c0c05c4032008040c131a054042c544491280c051003041c08079440a80a0003035007065441c04d89043e0003800b403490555403220304c1440040c00351081a80a90b10a02c25100c0c0c1d2400070800038a4032001d01016900d5911403d04134511084d036000b46d0368010b48003124540d45540d00c00700003000e07003001da0001e101460a03070004820560443c018103004680080c07030101691b503c0082500f61424018080d000d030b00828000304641c13484118400b071032240d489a80249030303502d980342064204c1e6108161016004490168100201409002d40100c8150b0041103481748d0350300e40c00100c0390300b038944905040e80040c0080c0f2043c0200c6200d82441e8000383c041040380781a041c2040350441040403400011340814034480207400310b1250001e141c80fa1006035101d6802c40e03090180da42420b603196030602141c40c1081e501c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272974226 1250 272972976 272973037
    0x50105070c1a160b0f130b06060306010512161805010e0103050405160b070506070305100b030403021509010c0807020d120b040b0405070f140f0a080a1d1f0501050f0105 74
    0x7284c0c8900d134108a18030704100108500d80000e03203a0410340080207654404280742c2d82900b500010116030003507481e02c601c1c0068505102c1e02c005141c00c01c0110b02000120503c40c40340750f840000a440d0f840b00c0d016a001210036102d0103015247c01710703001c080301d514213500c40d910503907002d80301d80126280454003002440319204c2c141d000e0b000046c0001120800c002c02408499049035450406001d18103011800900c0180f80b0300503603101c210f001c00010309040c402c1010071421b0030114524005e50414500d820b02802c8071801d500c0201b405c07030010401e40307440050144a582d900341da03640301248050103020b0251a4803250650b0107900c590400f6461303607481c072900b1f000301c0c055103607c18000001c0074050503174903014102c01400441841080324100700300040319100f1005242c220342a655500300140100340d00351103422014403125854058603c0054408035000404103402c0305012021700340340aa46090041d281c02549003190111554001c10140a1070006120070b0422401c1c80c070511040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272975476 1250 272974226 272974267
    0x715140d0b0f031902010e0a082113060906081608180a0611040f0602030301031709120604060f1d0706030504020d0f060b040f090b072003190306050105070c1a 70
    0x104d61107051090703021907030005907020001d10b0030740d1000071042c074091a580d207a0716102c1c518030b07035030b6004464200c0c162914411180c00654640d1034420039602d400c401081444980030700300c003080c180800b01d04400d06541e400401500d01d559210107070fa855903070340f8003e8540381400b44500e220790005d030b000180050245901c031402c10b1a109851702e191201e90030100b51305501000541d0410401031005c5055440701456044813810741584d10f82000d80829141d40380c1036001c200a00a00003803004000441d0481030030b401d4404018801f072441c80206035400318980c900710f901a1700810080002c14041e0b004164050300042c0301c030b0b4503100c40362900f4003c1c0004500071500e250f600c0160000c1494544500c0258231208501084a01104d07a2413945019015190034140400180c03003019003880e0001ca058401c0907001502c0c0c44512030020700801960300b45491000c282000e902050551081c0195100305402c08908940da903d01000e003210030440c400742101d031600401a90348143c0b6090f070f5254 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272976726 1250 272975476 272975503
    0x16050304080309031e031e040905090c092202120c060d230126010e0d02060a24031518050d0e0901050a09020f0910020715140d0b0f03 59
    0x10fa6a2402408143c2400082104080802c1d0800c401d955410800800c0d110035058515524041080c05080c04005000d1588046402e6060101f000070040001c24004080d5804ae00c0441943d01d0304208420100c0f10001020f0343e03a01c60310345ca0b00242c41d1098060180280003003c0d035522000c420045248c0350b00410140e1059512805c5007101c403070f1501110307204a074051046e1441941400b1040c03211003403560010f030f0449484403031004054400e50000c084201000d089404040700c80402030348a0f00216442c489161070240040303241c52092040ba9070300200d50fa010580181540c0d140c0704000e050581d00c905880d83c44e1400d0054030240031003010f03180d0140d0004d101c00c03150940c00800e10401040040e0284d54060010007031070b100d800d140c80c10344c4c00c0d05801685425664020100c103020f40045103901c1852844561129a000701f07245040d150802e00c00d01c030049540e9400c0e80c07100b403105034205805c4003c019480080c0410751000c8980b4000609111131340403404002480c00d1003907107080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272977976 1250 272976726 272976733
    0x10b03010807080718091103060a0e160e1602150a05010e060a261f0603050d030207030507120203070b04120f0306030b06060f0f0708190c020d081605030408 69
    0x52001c5030040040400500d04074004010b81800c01650700c00312850449183c03031140e00c82c6d5460040148400075680680d1020b02100c01501d0300c00700c0302d80a420741659004c101d000351a071010244d0b524080400950f108548502d0300c60b114440301580c5000c20307120003800c60203406031500d0410200040940150408400072546504040d00c1e0783d0001c42c0640038900c106c106110400007080c0c100c24120070181e0650084c421400c140300c0f0103003081709001d00710494030b007c805d2004d2056000d40c02007003501e004404945414402c254103408a03c68848003601140c0240325032400070f01c2002c2405011030891060f03030b04055440d41c0d0202e0911003a501152200c07a0342d248201c006901c050300d082c44132014a8140429442d585541801d00301c003500e2980243c3d00050071b28141280d000844e030000d440d14138501e40d81c4080f4144910513400a0b42000350489108508030241441030800002446e00102080312654042c5e944030019408040310044540d88180c1d41c0c0e010580901c0500000d0807400040e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272979226 1250 272977976 272977979
    0x2d2404120c03050d050a0e040b030c04020c010e0f0106091b1e0908160303033b0304120b09100203010302090a0e10020403050c030d0f02100b040b0904050c01090b0f0703080402060c06010b0301 84
    0x2415a107094687d20740101e01c1c118141c0302da55000520741505240c10b071401a42c41604e5081035016100704036606485114008145880c03800542c8444204c0d41d06034401c11805039100a5140e000a008441c00c00050601d0650300c261105154900d02c160034a040540e45036a03580c61081c00c2c01e1030100c040c6004038140c0d40070024107416004201040c80030032041500520079111500e146448001241444000c03040c040c01c007081c0800131180989a4032018010039881c0c1e1411070009040bc8480344818004e4108040c00c41e19107000781e0b4142c0750700501581d20f981d5a1711480e402018201c51034050f0380300e140c0c070791101e90040c1d03c000c0000e50b015202034510308600c80103040c54140301c546400100700c0500c141c10051030b40070400d07d58024070003d001c03420083c00c9000801800248900031f520604c80000d00081100001c2c00c0c4044c85000c0e211040303074566491111049010780c0441d01c1e0920b0007002164006480741d01481c2c2e0041c80104400d00344406840c10b585841c8090300303e12807a8400100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272980476 1250 272979226 272979247
    0x3052b0b030d1b0305220e04050c03060103150e1608280b010314030903030a030f0c0927060e010b07021305060a030b04022d2404120c03050d05 63
    0x80340b010400d00c1c0c1402580f0555030a0600210700c1c1440c40603007008804180719010000d41d03401443c580c103440704149003041e2281020700e0900b0f01900d08850130302c6182440b410508021407114120f0b600411840c400010703191859010b042030381c0340b146081c05107043e0038040040c50b454800103060360300018454100d01c0e410704603026a5400410790f0800c00344281500142d404a04141580e5018038034140500d041040315245004440c201c603810f00010903074200c0198140e00c4000c0098020b0b03030920440c0d5480c041134074140074030f0080001110300f40406030099a0380d505804c0c031481d281e03e00001c3c4640da66000000d50142a08409441c09000800f01c1c154940f80356580c14040c44114204054200900040c8600000b44070050035401144009415903403202c4d03140744031070803280380c820385120b004840205655245003124840d5a0b51840c06094a09402990024540541d9080e241c141004070841c2d0781c04c0e01107002c07240b60f0b280081c0880003883c24440b402c0022070039203c09494042c10300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272981726 1250 272980476 272980483
    0xb032a0301050c0f0f040317180603071710050d06090c0b1c05071103130e0c0f120a020f04030503031506070b150a08120d0f060b030403052b0b03 64
    0x40124800e0b03041c0414001a0a501d104a507140e0400200583d070710804101102c0d414021648060f004410ba03080b06017500741d05000524200c0824900b10001408040400c02c1c580810743d080800100070751088080c43e407025041c103422241042410102e16901c100090540a04071003c0312403e4850081c241089007503015440a0400f16040e94204541c2c2d4a4000c070428008080705035154682011922540c00b4019044100d00140e058170760720701c1c140020591005940c130402030800c64110000350022011030949092107000e00010b4074080c0000050101d00f0800762404080300ea00700140c0034180034860080004602c64806107450b803902d845076504220a183d411400ba2408101c40400144c940300000d6100464000401c0341071512004a0b8015005d81c209201c5031003804880d800e40b00c1120060100007440352003c0c00480c0e8040c09040c192030141c800c0400320401880840c000a0040e40509000340c81041c40403a5140700c14005242d52030045000e00c0d0403590b82c98140c1c40c508050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272982976 1250 272981726 272981803
    0x1005060a1e09030201020d0c06090c030b1b0a1d060c07080706030e03090f060703030f0507020106170109030804170d020a0c020102160506030106030e16031a0a060509011502010b03 79
    0x50501d0300c000d81c80d640011f900c4030161007420f002c00004001d018100a0b0691081c403800d41c0049140202035164030300008040015108885038014401602804501d048200c8030442c01543d1000c421481000120201440c83c41c4070a81c040e409000020703031800304011050080c00200700604a2500e04800981101c1c500500d418583d04100080140751b140d0024400428101782ca9407076407109581800c80061615414195103541003209004002d0341c1500300106607414903030101d105602c8101c5481c2202c40303c080041c0440c85041c00580864003880c0c102c3c400010f0200c040785406940c188900480e03006240c04004142135007440e8080d564100102a2608a200c1c0c071121100d0400c2c0000d142c50105115501c1056110894050f14003003d01c4425020f034049510780c807085482e40f03448040545c405a10303003641c0441d100010079060240c003e0008642000c0d00e0307901c241c2d080204041468800c03107021070540d900d070040f082c07440c0c608006d1514100161080200720036019800d00c010031030790 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272984226 1250 272982976 272983037
    0x108092814012f0c07031e02040e3909060102030c1c0806030d0207050402030601050c0f1b09010e040605040201110d110d030c090b0d110a180f0e06091005060a 70
    0x3071010543c4c2e158000f408600f030b0f98128840c0310002c01100800b81c02041604402504142040142c4865400001e00b00780d0820381082165101032850098034078201d55520b5070726900301c1c4001384403000d05000c231141d41c100c401841520b10b0109054251840c0c048105103182c6040c0e130301e40d0440310b0990f004d00e1850300600c044024020070b03035214030300071342d0b541444c007900740300302d0b400408140941e00030002c03070f0b0041d42007000381c86441111031302c0c551310f07105a4000700c28020465040080e45207418841141030380c5841704400c103c0c0d1a0782c1c84041c000c0200502c100e05118412680e0401080304029100c4131f800d240da00c582070700894103031940c02c1020100000c000d1505100c6424801e03500304803484240c0706200740c0551215031503014000a0442602c10b101303030340e0000a1050805502ca480c810174078540700304107850f9665030710480340c0010f4140705549aa444400100e4094a00300e415640c1040008040c414138640340d1002030301617440085500089101030a40c1c0800e41800e101d15001c0651 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272985476 1250 272984226 272984321
    0x204111e040320100e060910020f010506060c100c030908030c0306010f09051c2306040501060b0712120b27010806040803040f0303111305010809281401 67
    0x3e0380000706070a5080d1a016809120503180c0300b90654a6000581e8032118005080851900590074065100c04070f10b4039004d40c55090000091841c1050307411108100003460003000d9035542220803400505a01143c10201603e41c481040803401050185028040d01c1000e15541c3c10300790009060030f00568107031802d101c03008004204540c0d54559240017210b8003c4152a954002e02d03080e80c88400402292945c40060240c4d4806044006101e6200302d00c501c00130040c09866403194041d90160040041c0342c4251a07240c000c52a1043c514201e80c08444540072986203030500000e00d01c011041000c094601d0a00c85101041180700d610500520004025080a040c9621890107912008002a040c100007802c0d02c82014420790040b5a0724164444507501c44042e20099100c10708070703210f2240011101004940c006101003814141e01c114102005172618080f102455101c1c1d1719003081d56070303186611580304810401c1c000d602d03013840484000320b4442d1181510098600300c40403c10308510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272986726 1250 272985476 272985533
    0xe010603031d22090318030302060402120a080f0a020c030d08151804061107050f0709050717010911070b010b070519050309010c141c0f020307020d0204111e0403 71
    0x520f207100d40c8003460101c000304043c502e5040640304402100c0907000c05e403402c007000000703059002c240b43e80030328400c552510b003050300f448006944810b503074406001210100b1544c81c0c0c900c9464000d0050001038010f8540c6942984000380c11b001d8140701c0c11000c181c1d81800c1140e5603000000d010b0f03110300221104105420922000004488002c0004145695904621025580040036111010344c0700049407281e241c10380702943ca8081602c100c01c246400c2c280480d41d0b5a01030882104c03441503488003090241e10304a0075601a101c0c924402c0b0741180100081000f144110132014082c10003065810b51ba520646402842c03da60341000582c0b0801c00340c01500081d40100c125001d42d60b091030702c1c50059410b13041841c00294411041d00c2c0c248188158060705220b064070342404116103495583e0742c203c020406036200d01c04d659000b58840f941e48082001803829030b1102c60b001428400280c2800d04124072601800000c030107860ba20b00003c00c0c100100060300c1e000c00c030a800e00060440444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272987976 1250 272986726 272986759
    0x1207020f010e150601180803180d0f0b040c0f0902030412020c030604030e03070b07110a090c20011418060a1401090c031b0f030e0a020102060414010e010603031d 71
    0x12140040b484075003e50032400b0841581c0b064010b9030400c404081070506a41e40c44040d141c2e0796104a08480368015103039201081ca1420b10201c0c0881504450620284004c565810344092002402110701d0380c00a0030200d18407010444c2e58001e031111010040e52801c00303091000781210000e42c41401c6501406041c01692400300301160095451305004032000315180020741090701c05c1d0090b1300401004200c49083c072200e640030394590041900c13907028090700d985049e41520072102d5400c001c0b031040c10003000c0c0840070003035505807940c1e620000a544144041d100202940c15940c1c0c08180a0845070010101000d0200ca42c00107070400c4104030030007034a003841704005814410200e4030b44eaa0103c2010440c000c1d08001d6440c1c2c0500b000015019030040045c1c00304404c0503040c07000918141d81c008801700001a00f20404ae0142c00600741a580c0e0b40d10b04111071480003c0c110b05548520150201c10710074002c140240d40301e502e1310301c032a080074605403d6031a40c2620141c41889075801d4010740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272989226 1250 272987976 272987983
    0x9040c060f02010209030307030906110705061b0c1008040212061005060901030b030106061d090c070f021507030309060c0203130303050d0908030103050c03011b0e04201207020f010e 80
    0x85610381d08001148803900441640240980d0301c9558250100041e828101540121442c0980c1c40c1c1c0e880e003440740c5408600e0380c0d03664004d9001e815003041c02000002038040c03204120794484402c880840303140d245450003042415141d0035884c4042064070b01800704500c3c128483c202c0c03d9100c10000e02d4a8a006008a8014450707813043c24011000003503410b4a5074400e410000d005400900203001c81e9036130700c9009003401c48903200d01c0d0050102d04082102e525241c2c500a0003841d180c1c070450b00b030141603202c5000500c00d4440407a440700000107182d01c1c079440c25001d000342d54065200024007000300c0c2450030036109451400c10071904104070581d41510303400d039102d0540781c1520b0b00603151111070b42c1c5400103182e1040041c0c01c90b003010000200300b10b800030b240812280150024003c0c00903401614881e48086c202d481c002c20070403031035a58982442c3c0c0c00304034283c0010207201e244510813014071900e0390260080a910f044c2030000c03c02226010403250106c500f0000c0200041d242084d01140c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272990476 1250 272989226 272989229
    0x10f0c02151b0702040e030a020a03020714060d02030a0b030613060c0e0102150705040f0f030c0b09130203220803040311060106050d0b04020d1b02060a0621050f010c020a02090609040c 81
    0x10318000120f102425902e0380da10074610000c042045980c2c13103042d0000030b5510318110604500504c00d0304408034540e0302140a000c041302d00500310342d06014400c20800c1c0650030081422071010758509100c0d620741da003003059a010311000d0f1081040707080b6505094087e298114041d81c1403001c080100d14260b41c1c00a05103040260586503400d0980307520b88101d80341c2c441c950160311142d00200740818a0b14103d14a181280e1080c04040003896503034442c42740f180160881150700100940300e410190141c2d400030f580c0902c01d2000b00c0a03041184042e04841c40040100b03507076a50021007040b0401d80c10440000c2958004c1c8020700300ca604d8a200102588510318101c01c61a851f10f51406294403035406540d24080d40600500810700000004410f550b001c03203501c40184103000105da03015001e0321816064030940f0b40c808200105898404070b0030300c403681048500744141d400d000d2001d54207207c1c11213180304980c0580030180c5540100b10102c80003815240c410000c92041c440002c04a00d2000b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272991726 1250 272990476 272990521
    0x90318010804020f04110901230f070c05090a270203030a050d1d060403090b04060509040509100603050105160314013006050a06060e0904170705010f0c0215 69
    0x410380d568070202d107030019007010503900981481c035401c2804c00700901418134008280d0f14684031000d50043c002c007603107241c6402c00243c2740401c110071207083c500d4000c0c180c0c00c0c05081092040c1c0e42e150040b405a05080b04c00440541d075410b6a0040089490346c2e003455030300001100f0014010a800080d200e00c1350780d1420090050005e4420740a11041d04074603141c5a160380182c000780c03c2c0c171181e940c8401d003c5034220002003a03040c01045443c0000180c0313060b2040c0b5602c00381414086001d00004000c060141c0c021441100441e80b041d10707850082501070b601c030380c001058078240b9614415040d005040100240b504001018058405190001d8110340c40c110030a202c0c001c0705d070801c425050700c0024200188151744801018002c254101c20b014200900e400c02c41c19230385040855240d00816074081c0e0150704034002c940420072030b40c05c01030f25548032803500c3d142c40709650380c607402c441c08021028442515a0415001c017901031040da20402103901000b0001d04c2c02c0d24034030a13038441440c120f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272992976 1250 272991726 272991737
    0x1e030206011e03051002090f030f0a0609170d0902010306080d23070b04050105041a070206190f020a0801051503090d03021809130506060102160509090a060501031a09031801 76
    0x1071002c08501c541d640045400c542524130410300400c198002c1e41c4a800001c2c028000342d5500703010340c1000144440003d81c414046d1282034410341c0d81001405600070165848800030160224400103d4002c042c1518018800074218503544000341c151130140c0c0c044107441d04403c084000c07854000340240703c200da8040244c820300070403d004421902407030a01400c203c809e0020041004015806940601d00600b42c2034004540a0019000c0700001c4443e003005801c80c00104002c0c10403241c011350b00124640011034186000100a412a00b00700080300008000c0b0004008a040070000d03c0c183e608181e00c0d01d8076501c1c1c80702000c6e945000d00c42c0c8100405030f0000d8824221070480c02c1c2500d003410000e21960b65418039500140c2c000001020540d6a4018600800c81d10b40c000103140f582610341c2402c0720f0700300e131511080080700040102650301038020101c0030000181c5501c10140a14030619404802015200b00712080c0b520040601c0320300e1307008010740c0c41110020b04144091038403d00c0c22 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272994226 1250 272992976 272993009
    0xf0203070f210606080a270201050a2a0605060303071a0a0207060504060c0e0405041121010501030c08070f0612050a0f060311040e0312011406120c03041e03020601 72
    0x1c44100290000b034520b403251030004081000350703102c458540a403011030010302c150b840c51a05540c1900c501001b400700100214407010042d40214040c064018150034070381c207851242118201411288140822800c040202c01410000140720700360704000160000c60a00743c007036641d40310903640030780c0000c81401e003200003c1c03e40901f81c0458485913400413050100d0f00f06445d00c00054105008042d0201d15050304500081c107161150900c19900715a0224103e030043c0140008020f07000341e1125030300c19140300c1c0d05410409008642c0214407940791000c1d5589054881400c18500c0c1d000b00c2d41907040d001d01007144a078481c442c01d00c1c01400860001d440c3e1618082100140f05c8003010303040c4c86040860000500ca400741d11500c5118055074184a41c0b900c0854154030cd1045448803100e5841e0301c1e00502c04011a01080410010041d190514103d080794030205240401c680450711440d00108100c1040300d40851000301d5400e4049072081580c4559020b501d8050500600740244005640d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272995476 1250 272994226 272994257
    0xd030806040c09080a141015030623060603060102010e031815030705040902030c04090f0c03110715050603190605150d080a0f2303040209010f081207020303091507060f0203070f 78
    0x1d40ba1a9a01c000c0400288c841c400400210325007901c02540d0b114030340300030504520365945888070031344000da0042901d5a180390800003d504017421890456581d20304001e82040208002c0c2198100001031442e07901c0c00c0c03403c2204100b50092260080882401400803254204042d5000d50750110400743c1c8941d501e2020350420b006a600c560480c5040a45007103185110340e1009910782102d5805012410b81a5081403880c0f00d0448000c00030305003050f01c0780c80451964049074003d080101a60441c80c0c545607000c100406400e02500c00641d5802880040f400507020000100c1045e50a0002043c07152070b0070806015506502d0180005082c2d1035040c1c1c0d1140181624103803062a907514031403034840400000e50001c03a0100d008000c0b5100104000c0481e0409500301c0b11a4801004d92586d544200c407895082240100e0b050702c400e0000d0011690745401c1101c83d015149800d036120b940038284181994594142c460070f091040040c0550380da80000d03c1d1070b41ca051400c0c844421026484d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272996726 1250 272995476 272995483
    0x30d090302011103070f0905010305093c060f061801060810030204020a020c090105030c0a060f051c0b100804030e101101020a182309150d030806040c09080a14 70
    0x12900c3c400b031072000042021994114001d82c1112145503a1078080d80d03212401582202c0090b030b84d054090b0720402c0d50f03e5160400316024500d040e00450459035604054580c155000007400100c00740b1b41003007082205007603442254503070112040301c0c00d9075050816402620590818082c00c010003070403e000402d00380c1c610705040015a40604110768034807230424000d44400b10210040d10410070240001400c1c130300080c5045109500404a100d11841d0400540725000007030041e4052000910200c248090010b905003011107100d54041800e40084003000a42201140e070300741400856418807012a6215003009400501543d00714410a4500010348811656140000e00d540c000544003504651003400329032401881c031020b200310740e00d0301080741ca90003161041c101d50003820f0044144d0b514145009a800a600d00c0480810003c80303004110750481d03400e0103401213004c1000344001030405100d90f0748104407501d0021262030601551030b895802084024003600241c1c0301441e200c40342030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272997976 1250 272996726 272996741
    0x2010905060a06080705010c1203021b0a03211503031d04060305010e06060105030106051206040b060304050a111e090702030c0d09051005030f160e13140108010e030d09030201 77
    0x842100e041e46040246040641690b0144030760900a010000460b54060100b0160550b40482c0000c0719000041048009400c10808242504142520710003480b40c144000c070b22050180d40c03000302c0c22007035084940e810360b880760744801854506410b00a90030700d103002140070703294140342800210301d080440c6040840001c400d0390b031080c600075001082100541c4070341524541003040c1e42043d80c5030301c01500e10740400d2107008045070003041100142071000d00c5096000300000d100044a0a0120100301c1503001150112a183c0c0540401001c0c082034083c0d20148100485905505190590100350484d90240b8894060544d180c0820798480c000e0096400049815045441690100400821401203803082901910000806a030410720880440b4405c0b000681600134a8990142100412142800d100708002460132182d91640d180540798540d141000300100f01c040840d0f40c402031030304040c1e0008000da8075200c00420f820b8400310640312468814a0000785510050400364054882c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272999226 1250 272997976 272997983
    0x7050d1211040e04020901120b01030624090506040b040b0d0618060908030a1103010e040b06031608010911091b0c010b0405191a0a05060d14040c0806072d020109 71
    0x400c000c82c070407140d480164404e6000302c603500e400d643c4c0e0b6091b401508004000180440613078000510114210740c00200380011080028240e4107400b42d081c10400b500c64210700440c584a000f03200b201e2030980600d210310303082220100300704001301002440001c2c0840c001000180c81302c00421031801c695142d84281a0080d1080c041e0413039a14100d81150b20450311204180d140a14070755502e0718086c1524140c42201e400c2c42e040740c8441c2c40b900d0b596a0001c20f1194103214221101402c0c091a600c0d001c010070f0301d900045003103003551800710849030703040c400303180035054a900f0408a107070301482d001c4100044d44802c0342d59401341a0351501618011a83c01e406c0303402c101c10300039182c455040c08548104100ca04100702c000ca15000c441414101e070b1303e45d601001168080c45940340c20401450b07120812080000d01c07248450300c5a055040880d81503903000c0c042d02040240d142c1c01c0c407080c1d86c03090f280d1a21910120901014400c404141980211405214841d0010290003580525034483c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273000476 1250 272999226 272999261
    0x31302030d02070e1602210729010605070807050f06100b0f0a030b01110307030e040b0906030d0f050d0612050609150403030c03060302130902030d0516020402070c180606020105010b07050d12 84
    0x1b000d0701004400c6d0b2180c0402c80e82c440454519000070301003850300d4449c8005015080b107140e4a0590110342603001a0015140d0010800c00c01002480030081842c0d0003075a0006070030289000d0284559501c0305601010309a1420044114036a1090045629080090400041080030440125a268810203003107501b480006140c00034075801c40540c528a80c5c0466003404002c50140921030350040542c0c12a4141e40156000000a8007c01086114500b145005418450340441d81c909880180d8040c40b850b481c140d030300394180802804801d510030444001007402c0c807003281c0c42a0078444000c00207000c0584e02c001c00d0b0030841c8a50040c20007150020850316029200040400080c19503ca0484c422320480b00ca40d1041800340301034601c0840e800d0140201402150288806948070510803540342500300b40100700c0544c0f80b80781c58a00c5900c0c01000610305e040c4440a800c455042e00a082c180d2400c1c8503000020308000307000c03404101503140840d045400201c0c003034040c00101c01000a11513 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273001726 1250 273000476 273000523
    0x903050a05011e1e0b04020903010603030806090a0905070b0c0a0b15011701050109170f0102071203060603090b0105210d02031c0203062112031302030d02070e1602 72
    0x1500140e590358210a41041c090101d442c07800304440e91000c0103514104c00403201e400304001c81c0d1198481080c007800c0545002c0710940003908546e825003044020451403000d01440f401c1c40e09009501c000012010000b60986031200c0340c0d24941d520554800030340c0014070b5a02100c06002010a0580c000000c000380c0c100042c45036500300082d200700780003580a400074641600c2c1c040c2c019040700c50684964044505100e00082448040072420545205594000013000c0092004201c814000c098501030b80c0c94a000c02816141c040c1d025900301400c200b421800b1905805140f0f04440c0c0c00c07204591812424101d042c0ba00c1e02c2c1c207801c07070810300a0708060306860350003000a01d00070f8a4180401d1040000c001e1400480c001990500e410803858200212190310f0b030850001c020000c4421114120b05800303403580554403c40d250149a120312890300110304040144421120076800a001c90b20304008151301c81c000001c100030344003903400d8200e594081c000d00080e144079170600c00c40102d41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273002976 1250 273001726 273001733
    0x60207081b1f03110703030b090601031505011202090a0f0317030405060a0e0f06040b071211092b06090606053f060c07050d0908210d020309070e0612030306100903050a 74
    0x2306140c0303403541c1c0902e0740307040001c4603984270384551022200c1030401100309906110046400e43d81c02241d4010f01542005205c070a03966001c1d00f00024420b00034044446400e43c5021014010070182c06607108800303009110014001140040d48507100b80c45c0065580d0424500c03615005650040307000313070300031401030105114201145a2107581140c5558231030402c1551200111a500119401980002d03c281e29051030103140e1071742a0560500754641c018015001c40111403c59242110416a00c20075581042800d00170500240411180700801d480c89041d114003c240012070003086400351040c000100f070002e40741418008641080f240d9515011300d203c034960340f15803801c0c0c03160f00ca5100e00ca40003503c140300e01800c0d00d003400040c0ca108441d01d4a1480e0481401080718401407043c02075000c5540b0501c050b612800001c002829039a203800103c2440341c0700580240d004401040d0a4200c0c8032000048a13044042070b82c1c00441c3c3d003801e03502141c0c00641070b0002880d602805d5410001e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273004226 1250 273002976 273002981
    0x61b0803090a141b0f04060e010e16050f0a0c0215040902070b010510170a060905070f0e030105060f0904050c030607020d260403180f060207081b1f0311070303 70
    0x85803190104048180c90985036940e100c11108001242800c0c11305202180e080c2440098050500030308089910368803941c256212a400341c208204968400040000320810040e4022400109050141c5080101e9401c20351522807200c0c803c050008611404003151112500c520f842000044140e031103549841c0b24a004e980800e80c02d0b903002040300d0001c40c0c0d07480c10480482c40c6820030f445882000c1c0c0340711020502030100a28810410365160b10004405205d4051948211080c5e074801e41078401c0b015010f400d42c00c00e001500c0c0240e25000400501c0e440790240d242a602044549400a03500c629100707203040c035000c02258050103000f050064181c1c00240a00d00b0910a0311240302030303c00321001000c40c800709000e000b20002c010700030402203401035410241c2d8908410141d08499121050000c1d07925039075010a0062f404128100000301081c04910303065032041c840e03840350188010000300c1c01c034200c0909141a00c000d440c0c4501c0303140130758001c80c04003244e8038125031520b420b1b0501500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273005476 1250 273004226 273004243
    0x9010e0718032d020418020a1401050714070909080a12060605031b070602040b03011a0f16050a0b070203030702010e07030818270613090317060a05040203090601240504061b080309 79
    0x24182030f507800304d12408100127140905006942d02810180b1715101c0c80030200c110306802c1920700500c103010030460b869000d14440c1c00d0003a0141551607899000087c00c010303c0e003411101d0f0b14540700d418019130398014200e90f04100d882c200d88841070b004070000740c400d1040d03070700050081c1d100007800114407204d04051812501c40c541005032426801d41c1154840c4691840301d007004c6820040c01c145400003104006105025000b02c882d008090b80e11652411010b0b5001800350b0b0021081003c4c0d140d09028201d0308401c04800303401040d00d182d0354108240605070076040c001e5201030081c110703601c5121405400c4502c2c0203a0769070359021261100500001a01c00c503000700c0c00800f8600c0240514000c1c180040d0345686c07005091804503002e109060800342c00158804440c8070005010342e6030b0b002440c0a2003180c805800154503000d0080701180c0d072041c90310280c240302001c010b241e90300403041d541154414101020381c0b0b10481c41400035600b80740401804010040700303001117920000341155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273006726 1250 273005476 273005479
    0x10509120d0e190c0b1918050904031812020a031502090d0804030b010605070209060f040b040c020618060f040b060d06110d05010f0b0d0b060909010e0718032d02041802 74
    0x649698981200b900284146c8080c820f4404032580e0030701c1114410600d410440ca220040c1e9a4440c1d240d5000610703c140030740d01900000d803a000f00c0001601f002c10f10030010300e412627900701980b002c2d40c0450300900d4140b0014014522900b00f803128444190102d40329004010f01d01e00d0a0301013494507602e00e0700705000a43c0d0480200c2c00108946016404a456a507001041ca8817595126020881c0d071507245950303950007544407101c17110030313484500604005001d10340240c9224900002c20703d0600068103690140f589c403010600c103d04411101c0590015001340b2086602d90740c142c003081c0c00f00240d86006100da850712600044040941016003c0c80c030f000300b0103101c0d90b41d82e4a61010070309003e002d19915054200540102801c0e240d20850f40300c034019052901340403140780001c0100101368010102d944550017000704142e171280e84049900081c1052401c1c260442e141c0e040381424a00c0c0801d613080e10351207025a007a2036000b1500285074010400d0013503003e0a00380240121080358220b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273007976 1250 273006726 273006743
    0x2a060e0604061b080c070309030534120209100503060a02071a10090902030a08120f1e01060e0607210908030705100b060f0f090909010509120d0e19 65
    0x3c0903000e68002008194500703a5100d42c195140d10078654699404000204c00303102080500100207201406450300c880c7c2d51070000c004c401004002110011441c00440d5422442c03514223116902c060000d02e5070785038055800a049030744600021040c00056048113a02d4802c0000b0014030111540091100503c205910107050302550701c00020314070709981d40650380e14810001c2c00b402c04035070322028003503000800322010020142c480404540c01225284c040540c41810081c00700c001400440d00000c8103820b440700b0520000e0201455401806840c3c200320891415070465a1036500340c40b8400d4000b40b10000b11000034016921480c0d51034541b401003200c01c400042d102c2c5021041d90461600b03c0c01505580200c03c07013000050903100c1e040c3c0d40c801414096224040341da0760240400340758010b02e00340d840304250100072003031000525058490781003004100303008101061a482200d05000802c1d01d64452070b918602a2015400380d402a100304200103282d1800510142107642c0102540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273009226 1250 273007976 273007991
    0x803061914180708010501080903160c030308010b070c030b0c0c030307030c020601050111120a030e1e070f03081204051e06011a0a0503070f021504060504020405010503030a2a060e060406 82
    0x5100b01c05100b1034148002c01c02e10801000f5650040c042582d02c0090202580d01c0c100c0cac1e140c1c41c2c50703203208903a100344c541030b030701d03d101344205034100b80114094a81100042d04281e015600c0c070100c042c3c00c1c00002c18000e8031201003144c800e20a41940c075019071100903281c0760318150380028010100e0004480041c850080009160b50090a00d0200c80d0081000b501c00c40d181c0d0541000940e110718034a50805503980b604a50381242400002c032000e1604803c0f000116003110f0303213490300c4241c0c0c00101c070001c09940108002410341c004c481c1104a203214962090341c507401c02c642000190071030000810501490503440b0000444d20318180c500350801c9084183d070180c1a140d181c0155001500455800c1010941c01c902a0811040c1c0f0303280b034070440c3c0c544042200340700341201084c2e404580c10340d03c0300c092004600e050300030b2501500f01680250304202d0f8010f40181100a5030004c060342618030082615111200d00f4203070300594120600303012030005441c00569a08003100c0a0740c00c5480c01c2d60307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273010476 1250 273009226 273009259
    0x20c1606030b0a0905162d0c0302010c0f05090906010c17090301110c03040522020d0e0615010801140f030a050c03100501050f0609010c060c08090f190803061914 71
    0x51346d01036608811003044400852034144d4584501e0814280b45011103225881101c1c50420b2802d00c6071a180c0d40c40e05002070914019007590005075400007030028440b4880c0f4681d501c1f5098a0300020201c4424a26840d9040180d61007904801e001c1e02000c3e44a84040741c0740422001005420010390080104034032502d8110b4240c024111400c076260000c01040003180740c4002d1008a400300354110040742c80e50017605404990140000c621613944542d1920b46061040c08080d61140d04403404240d1304076000c000800700e110500482100344401d41800260762244c80708400d000701c01400b2150180900d061090b9038082c408070562103880340300c09ca11140a81d5000f698101e032405440421040e18170000c2103441d40160061904000c101488070020030000c0c001c480b220300e515143e100040c2450401d960038800c1c5204030b1019940090303104a4882c2224240c5071100760412000c54817a182c10340080c00c440c07951101c100812a00300c1c80030a2003c42c4c80c08851700001d007290000c0c0c0f55460010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273011726 1250 273010476 273010481
    0x10509090f1b03040501090204141e1801150306050105060403080703030b01050d1407090504291f020102030a0605091510020f3c06040303020c1606030b0a09 69
    0x60280d08480d1035030115500100008110342c0040b0200c2d00c10100d10348480114849400c1101c0682c1c2c0d582d154800201541080d00c1402c0312961502e01044040c903120844424080107840011540810000000d244010700100401d2002004000740032305240012280001e45050009036251460600005013610741001110200c076800401c00c0d08100e41514164000e108291220341444020007068480304182d1041c001d0340b0166a0008240d4140a8401003c112050f0052401145030680102000e2000e00c260b0801203244240742e0ba4440d034460104418894000e40869019200e24072190080e0f019009107204110318001000302c60340d1181001403804061322502d100d01d460b1407071825a801c0c9074480101034001d03801102c020300003140300e46150059007000cd1240c0200d0418400d00148090304100661000900c25a506480d8001490312948040d00040074140e0000300f55044074024050986100400c81d40401841d039208000f801034004940000d125007840c44001c00c0d91882032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273012976 1250 273011726 273011737
    0x50a0b0913060207050a02090103060203070206090102130e0402060708040815074407050715050702150712050a0b1807050a0e0310090317090a0201050313151b0e0105 73
    0x1015420206041901c0b250001c0d8000c01c0705031058042d00e1403031009a21a070700348034021032003440016501d05d042c040082c10504090301400c2540d0042119002c2c0360300304250031081d500507400c0c0241f103803664400680d0510589000800c090404100003c50001c0031847e0f0305844103001507000340e6035822400320b0f458bd8440350f10b40349401c0301c0c200400406ea0b418030081070300c0c08024107003605c100395800106001282121000c0015800003213036420410308010700b03d40b85980d08824040f600b050400a51203022400d488a13144403500001020300e44602d030310780d00c00c0d614140d00b002141405140b0501503d0300800003406100083c60a9100422551095100d621a42c2c0c0e00c81c20b1030745400049a1000f82d6240d03560340340c400d00604015200071071045a07400d41c400d441d02240c2012251003012440c1c0001c002041c41e0f040002e01ca80540d8209003225444420500700118103001458190900e00c1910458131449240c4001450500340304c0900301d50b500c40649503c099940004011517451160 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273014226 1250 273012976 273012991
    0x30106020601290d0e0f0c0a0605160605270a02010e010c0c0b160203010f020919120318080609070f142209020312070611180d020f0a030303050a0b09 66
    0xc0c24103800200318144040e109a1000040110782c41c06a805c1007851301080c0750b0503414030341102c1c0001409240202d800750003030030f00e8189982403441d050300c80301c0707084000328000c1c240c207480c3c0001804840c1c03c0701145c8140304114144821070b106540c0e0003a50f4941100d0102c0c0485c610725240c007220b41c0135046080030103038024000840603041c80040100e0790094001c2c00b1615100814a40041e5000c0c050210601040c1c0001a261200c1c9401c007c9285807421740f41d0440ca00b0035034117100d900a008055440b850301030034007110b440034403945502d001c9142e40c0003011380c0c0101d0301440740724140441e4440c11611003800544115496409140c021640c0101c2e065100804070b46c452a44101061091440215a140001c0603091600401c0c2810800e01d0182040480042c200b000c001c1030b0301c00c6100c0c51580e5048503051140c2400001c5406c4da06140581c413602c03080b500b560071952401c01503000c8a002904182070b445d502c0c41c024018250564400181900b0104108147c6c1030200034580700300d08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273015476 1250 273014226 273014279
    0x80d021e0313030e3606010309020102030708030705070609030507060e1605120f0106060f0315060804021e0a120308090d0507120905040204060f080f0705030105040b010e0d0305030106020601 84
    0x42a03a0f0039680403200780185038001c0c1002c11090054200100521402144c405d0541010380403503003820b10604009044a050510700306070000542d03400000c2e100c40300e078014911503507030f04e4060040d00d81c2d0250010007400c20b41800445c1041544c000060640c4901c690707420705c00b003c103200409480c1d1803640929101d00c900c17072a0400c2107281605480c0c1c40706004006642c0e80c2a1206402401e441c040d400220101c1c40e2100d41c103110035494858130000030008074841d0403503428010010b04c0c500d40588064816011100404144410103513035144405004040110140da9000c3e9040302143d00c0c0c0050b0041408040012160000494220764107069a41d445260908d542d50384140104000070520412641ca40701180c142ca840c070042010b80b03000c0e140d6080301400c08034010040400200444196400c60f0140042d60750400150f07070542d10100d401003561011440100d900c003540c10385042e8850100e83d4214107054000005505039070381340e0709407103241e0780350025050583e0a1480b011003184 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273016726 1250 273015476 273015511
    0x604050f0c07060f06080a050d09030302030a0507052a01030b03060408030402010c080d0c020c040c050c0c210106030c0509060d080d0c1125060f0207031101030603080d021e03 77
    0x460400a001c501d203c0c0000092920402d144442121001c1e040b000981d40f09100c1030090003010800c804020300c60b8074140e01150f0131a50005e459000390819041445408104130042090a011250101707410811400d855000542e8000c1e84a2140c01c0c0640864500514001d0505000c10309500c1160003100551844c2c0381c540c01101d040191400549503840180030300c03070000025000d01000d0141d240d00500c0804424001c0204607005a50900184a420403900e10103510100303403001c09500449801c0c031200c6d200344a0703902c11607851681507040d500e0400c1c00300c01c01130f0388a6808265401030310b43c506944d0303c80c0c081c4841c6c00780e28840a040c8090520025000521f6034009400c82c0d0194a4202698880564024a000b03d240c04054440c01089002d1004158101c0c4800c011f14441ca040361400c450b0b141701a46804040c04040c126034030b2241200c0659002e90050380c0110f500402c1e0729a0383c01c6004030f041c02908446078501d084a4601ca00c0103100c854a0305403800f60758480b50007007814 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273017976 1250 273016726 273016741
    0xd1509110c06060d08120406020703140720011206080a051605180901060b03010603140a0b01050a030f020c0316050c0105070201050405041a151b07030c0e0c070510090b0604050f 78
    0x4d100d94030032501c001c1c040100500c175140340104980690310500c5e0143c0c4640c1145000b5144400404242d0070b4294284030b5480407a001c41c0e00520421284103500e01004c0060004032034124103050900500d5003807520000380c0000010380c091103640160b0503140e03405046560300c0e185484a118450b0310440c3c0070b0700c8100c12015000d8a68000600c8030000607500c0c1d4420f2000e4550700700341d00480110341e40d85941d04500c00c10386075013035028036000003c002c2802d040d000a0700c940200b8003080d0070035a99031156031030380c451681110010604001217a84bd030720302c620a60310f5015150701c115a28041ca00300c3d0016035008100b65a03e4550503140c0718100350500041c0030050030f1034944901c0c020000c0001c240e0030707140c0101610141660b1a1202d64440024210300440d282c50007100003540e00c200d4007003010076890401d40094a1280564031020303101c0e242262a9030040e81c101174207500480f505c0d40340c541300d0756021000e054413038000c11685a407210100402c881301100c18480c1c0120090004041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273019226 1250 273017976 273017989
    0x50309010503220305210405070b09030106081509070602011404060b0105070b0c0408070b0301051305040302071a1c0b01020a0311100504050d17150d02060d1509110c0606 75
    0x8910010350462500d04000f54041e01070700b002c0340075000303d003000403200f061120110034400b41c6400140c0b04649070600f5a5103542d10840380c412040d102c0004154800342c0e903001e4111200504460003101c40c61011700c2c01d000d040650507605050b06100e55100040d00074018010a540000c2c68400040701d9611a04d420018150b80e95810741004020411b030030009001644140c003071b80c3c40f8200b00ba00c482c205110719142013129040740450070303010f000411075941c98403582031100c80c0360f00b80030032079494621b0300b0b034903007000c0b500842c40e810700c3c000ea0428441e0303c190203401d10b441407001080702a044014041c00b1540c10040486c01070b00921001070200740108007040018180c04100c85000d810800712030708071031054404603082d403c046010700006503c1643d03035050840303490400380c2600342041e0340c00031810540107041c0501c250001410070741d550b6030146c1310201e2040600f444a61304902e44006080c00078051000460310f441c0f0001d03010f0f1481c50a80d00c0c2c002d0501c004080940b60641007002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273020476 1250 273019226 273019231
    0x10b0a12032d0306030201030b041811040e0d0804050625080916060e0f030106210f02043e0706020d110a05070c0501171503011d07080c040207050309010503 69
    0x194840c03100d071440725540001001c956020b0b025540000ea50342144001000da034540803600344141c0c00e201810203841000d40020340c0441e44030218480c140345482c08036001e021680380d108254040c101d41c02c11100d40041f8028031540c1b150095495030f6450501025801c1107034022981840d4400241d04031300740c01510125000011038080381e6a0105055170014500c1094200000149050119000341d0405440a07810710b13108170000e200d107a0030150303481e82800c0c0b04c803c2c0c2600e0b5900f5801c51070500401003150946107030050070031b001039000340405146090f02e101102c02081c0301212034454104110f800c942c45000003241c81441d0240c161180e00103504464100010660b071041c04980c045261401400403015503144c0c19142e540030305002804030b4160388924140000c508040c03840d14828048550702900c05954448044505804030740100704100039841c4030051401d60343c0c0010340004101040b10902c034100c481301138030001800700303900885100070410b48c818440e500c01036019078055035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273021582 1106 273020476 273020507
    0x210201150e06100504030503030a1d0f1e010b0d05070602100b030304090c020102070f05071505070b060d030c0b0103120f030207020d0605150402040b0309010b0a1203 73
    0xc021920041140d0b1061001507803e900150040c4195009075801c5000c50303490f45050b0a000c8011325107140703103e02810002100300040c080010350300e0a07001c9960050310140750049041c42110100c0b58862502755240c0d40a080c80740c68562031228036034020b5008080c4d541c42d00d03a0103810450340390780d4821003500b08031242107192400400c40b812540c15890004210f4135152041b030090040d103034010070210b00e246450302070103070016441056899882d0020307501441d9900565451061410051441e01e0900004d0500c0c50489030310152a8000d080407813843d0b42683c0c0350443d908003604201e440c21146040c80d00c43c039602001c50340e010156814114030b00707402d81d0001780c180115800000d007020745460018018182c00181d180a41c40060015034542d9220580343e0590380003150318070302d590720704000b803491ba107413051170070044079411444544101da00761401c903144540b900010 = true := by decide +kernel

theorem cover : BRFrame.Cov 272841726 273021582 := by
  have h0 := BRFrame.cov_init 272841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 272841726 ≤ n) (h2 : n < 273021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
