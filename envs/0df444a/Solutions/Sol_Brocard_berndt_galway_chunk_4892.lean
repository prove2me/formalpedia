-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4892
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:04:18.532029+00:00
-- url     : https://prove2.me/submissions/6c43b861-7774-47d3-b790-b82df3fbf4bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 879676258 ≤ n < 879856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 879677508 1250 879676258 879676277
    0x41103160f0504080f070602071e06030911130e060c070c1e12030c031803150f020d1802031b06071707080f0d141308070501180b16180303 61
    0x1e05a4242c85030383c0102400f40a040e81c0301c410940002075000c02c8810a074200c910f42940c5404800020074501c480c3d03080d0403186842000b0700c501c40c6c2c1001c00f00d40d0282148140100c03140001400c8240d0004000a1b5207849040c45214640c0a01c40c040d80504183c411130319000c41c90b607404001c00c2d41030103000c0e89050204a85c0d444c00350118000d0002d0608018020807070b11480c04c2c060405000f9180880002c0d543c03030000e0601d80000d041280490394006a181400e100c40c0800d00041c104004010b9a066424807440079140c4d8107018010b081915000c020741d1807034042c0107041c10f01c01104200b0078941403803503020200d500e40c43d046562580c0c000f903d5082d8075100c4070080119204210700604039010120b0141480240040148440454001c040001403009d036501c00c03d00b90211060b000340d49005510740c0108400d00020710b81d052050000051f120a1175072001c01004036010103a034429000004c200341004d040c00340401200c0c2500b4160003400c020010352001a0403804006d082050522 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 879678758 1250 879677508 879677537
    0x706080907061404080307050f12040e1501030b040f0b031605010c12020a0803010e0910050417090609040c0804050609070b07030c060b0901030302010218011d06210a0b04110316 78
    0x2000d4034054904e545c00c0c0c0703545a41600b0700d41e84d2154034000d41c500303600890300d00600307410424044504944100c0c2e480c06440c0c0c0c958410b20007075140d9a600d141815110b482960040ea5140308000c0d005a0342400000d080c0d60f00e0703050520704040d0461882d0b8001901009000726a008070120303165a5110004410540c4100310481c20807000c103c0042c05250088004918040e208142d184114200320440314606424103406007a0307002034401902c441040b04d1401c011041c01c01c002c224400024120301c0c5030001c0500820110fa0110000800140004050004200781805001e40140d1220000d11049003410f420340954071130380400809003c00d100040f41081100d402a202081d80106016044d681d80c3c14068040d61040804080360166040e11810703a40c0a03d10540300502c5040c003c00c0c50384e820000344551680035040124940d08002c03d82c88a2045080c00d10b44030304500380c0049242c68812050000761191641030742e02c0481d0510401003070400820806562120500e0120310380350021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 879680008 1250 879678758 879678797
    0x18080318031204031e180b03070306050904051e03070809040203070e040c0c0224031803092e0e06220b07080318072421090302070608090706 62
    0x52035004094850030b000c2009050b0032030003542c0d04054a072191001c007401e61008840511206090036181040401c051050050b80400b5550040c0380341000140c0540300d0300000c030300003c2280e00304c40b02c0d84901440341e100300c0c00f04007600090924000560501d603603680d6404607401074003aa0350141e5404000501c19038440d000030500c0c288003902c204110000914010515510320300160b000d500c240c20390754010300808862960407000044138900350784a20f01901240842c0d02021a954801405850401da03588100c0b9100d07018a4100b0801d00c40710480145042960b840d071403000d115800d0016149600da0b0404c0782c2c1c200046c13903000d11500d158444240003034441c5030054020550080340c0f0004201c0204003c600915a90082c03541c03078500340d5880c1e5604d25050003484040c540c640380003030200c102640c030b08450501500305040c02a0505520307c4480d03c0d504102c3c0c00c02520f480884051640500102d07001d0100d41c50105201c0c41c1400882d03640d02403034804c14041011030400b1800040741e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 879681258 1250 879680008 879680017
    0x100b060909090607020105090606010905060708040317070c0509040831060302070605091b01120b04020a0905040509010b0a150903050d030c020f0c0901060e01050702030f07091808031803 82
    0x20200e5640c2d040524901d969610308403481c0d00558a454049a000080003410714032846050b528079030640c0c02c02d8107215103034002e24012500d1090600000c0000b614003110900c40103140c071411f42d2a00c0f80750424000c038803015030155004100c08400d00c80071650358000c6038907580b0120b044034014603001c503840c19105541d41d410079000c0d0360b80501007541545074000b82105070080030180f10944440b284181c07070300d9a020380744a14904403041c80301c0c0d65025030090030303444007030340c0001070400001030110b02664030050342c0c5000240c9018091103949000d02c2990f03000354940c002042a1792140021840c00c0a41c0d014500f003e218400086e818184500e040f54044c40c0d004043c0c803181e5800400140142c8040406e410140c0119207000081000014100007000802040d80702281d10f0b10109881008901c030306107040000401001000d61000c104054402e5580c100809420f0314010b0041d00b1141a80c03000310401944c0320096005c00d1001099940112903049003001d42c03203291020610358401e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 879682508 1250 879681258 879681277
    0x807090e1c0210060e2703250201080c1201030303110c0106030c03170c031611330903070509070c0b040b0f01062a1b03050105011a0903100b06 63
    0x2200010115515030115a04070304241c03041c0180601c545500306010061006c41d0725221071450b048900c4000401003813000d0018880d04182e81c50000c2c02052003064901a0041084090000e040c803000c40d40d014041a81c00210001c0c014140006040c01495070700b01884003804064403048820004603050085071040d60b140002045110f82c3c80c40c082c0d203c1081c502c4140c1d40e001c203000c1c0300070b44650000d084601802c81c0750050741c68485038482000d000d09075001c01f0f690f01e00400140c41c03003a45540c5400003d2001002200c0c80315262412070800320803031808078241513001400444142d8400144c0007043d42c42c00c0f1400b90255540b8282110064240200070b00050040340600c01400203409000340076201030040d508960303881d0842a580b104c02e4030007002414040c108000d40c1e159109407207189440c8150100d030084030300c0416010f0381076020b4200b6030b200e0755203130010002076140003808600107a480e900c450a00310300c000002d0300c580113600c110b010943c60302c1104259a448108540f400d54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 879683758 1250 879682508 879682543
    0x80601300615091a0304080a080c040b18030610060917010b03060c0d06050d0206030a09021305070f0315150807030908070c141e28030b0615040807090e 67
    0x1001c034002d00c9444640306030303600c500c4501198050701303207018101e0303209a41251040e4a003501d0041c007101c4901005102c1450180c0603c0007041011200005110019980903900d903082c0d410001c06085c40c2018000300c0002d06295410045580c01620510407030303844028640303601c645100c0c0c6e41d01402414126a50500500c3c08010b04038548402038a0340c0c5441c000100002a1910140045134040d45c0010351f020380c00b400064008410b503003148820500c0580080902c04203003240074290b502c00c0d40c841d030200d4002c1e4180381e52107a00d40b01c0d1000444558001d803442234030f081100c02d10030319510041c1e030802c01e8490000b00d403e406508050900d0798441c440c1d41e514002810410b5084881d80503a01c20900183c200c00b8103841d0001c0f580903c1d0000e070032034000c003001c40020000c2c010300ca00e10801e0703269105880902c04010310f51001c0300850141c0300312001b038035007041040302d1400300400c4030041c10000d200601600c0750008000c410348500703950001301d020b2001543c5103080341d409402051b0740c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 879685008 1250 879683758 879683789
    0x60503010c02030a08090c0a030602090607050a0c05030120091c1e0b01080a1a07020717010906180f24020c010c0206130b04080901140301060f0806013006 68
    0xb81d00100418481c441d903910310990361144904140c40c0c80d48801030b241d01a95250060000c03641c0e5034010540f090000340524074098485c0d81d45070600c200074030306554500310a5030412040c20203020706540034075040c844540001c8e01c01120f03411401540c0c1c07464040d69404885981c0d0160b000002c1c030005402824000d0706001c1e0382c0e20741410300c42c01c100484900300380c40d000154000d00006c110030700c154480041c010202d41c00320b845024220003042e9008510900c1d03c000ba04025a070840e50100b8030100012440c0712481c00d02805603092010002500d410005005001c06c0d1920106517280b44c0c005da0075490078040d00c2e40341d81e6a650030170b080007503144001601c03400d00c0415030102509254507002d83d20701d0707600c00002c001c00d84114030016000b00341c0702c400240050000e90090000d1801410320586041c40c5c0700d03407504c59070400d1704458040358144005034400c0750000c5100d6807114003480c000036440004a202404985207810800c1442215000c0c000c407078a5582103180074026141550990 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 879686258 1250 879685008 879685031
    0x9030f0b04020a1a0702180403050a0c080f0c0a060b060906030a1e0c1715030a06110c07060c150b06120403020c060c0a020a08160512151501030e0a030f0c02010306050301 75
    0x1075442145c040348906c1c260392000025003d0b036104a4496609920351500382010100b0a580820000030f040700c8103034042107203030782d1482640060041c1c1c1c0101c1000b05103d450704c1c54000308841801a046215405c20700551440c0d9454004803035000708042e0020880503000c126542e07080c0381c0581401d060f9820400c1524107540e004184040c0c540405c42960f1281e200c441407405850920688a0b030503070400b400c9800801e185820a02e1400d501602c407514244202c84103601304204c6800c07200c000b0342080d000000b07000c40c2e800000c149043d21181086500c40d0700000844030b00c100c120703040b000410040010107244c0280035409000b00060300461fa602d03414441c280d1600101c0208034403c084c012004a0842d40c0041d5400f00d0031804a880c4080a003001c040145480d0181000300080c41820b558958000c07401d00013074040c2841a07482d020343d0380d50500141c156860004003407406c0c2c1c80040340801007540400007012440650500e4602c8070810b00040700076103080e8004a815600300020b0072003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 879687508 1250 879686258 879686309
    0xf210406050412030c1b03090308040b04031b05100e011b06020d06060216260d0e04050a0b180703020d0509030c0c030f1f091a011509030f0b04020a 65
    0x8a2031150b92214000102140d0030f4003100d90741d001900011b8001100882450b4200c1c211075040760081c2010b000642d034958a0035419072203900400801c07100401c0c02c104011441400341c001c80038040000390058107000c0414440d591040c140d07402c00c020300851010690103101080070709261000c005607514000c0c00d019010350301c0b41400703060040c60404c0c0000c01c58030102d5101e141e100d458030700010251410b0b648074601000154070358503091694030314081c0844100b191122460168a030b150400741c40100300300850700014100c500c2030341088907503407850740d413610824085a11208100c0958480500440090103141001c200d0645010b06000e0513850000c0500401c00d070890454520960510904d900c0d100c40d50040200380d88000c0c041050a0200c00d4001c1d4003603564080051190103c1d00d80e0480c0040c542100785010301001c0c0180031802c9201401c030f010480e182000c01c44989950388001602c0440c00d005072180010001040456031550300042c01000c03944540900091090a40407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 879688758 1250 879687508 879687511
    0xd0b0109080102041212020c0d03080103120908100e01110408010506090a0b090a0c030209060d09050609060114090603250e06030a080702120106030c06111e030f21040605 75
    0x901088200300c0004800c041402118150384420000402e043e03c290b07601c0c0c5005078240441020f41c001d8125102c92a1500303c0d002d5580e90080c0d50b14a007551660800c910030022038911102044240d000502680310001105081200d003018005051912400c402d40144068400e07007030a10310014000428640c1504207501032042190140da1030303111076046c030b001c44070402d00140e08040403000251448155a000410000c0c4c20705001d45005c2e651fa00203002030f404a0b1040c6d625a80e10003c00050040c100007e60b03121013a84000d041d654141629011012102e507a200d2041d002000050f213291804d024050030f92215000000f01c0c40007401d04814540044c1c01012a909a4007001490720320b000148822140e80161803245055003c0d0240f001da0803001d030282000d9920741d14004002070800d07051000074540c5075034110000410b401e41e0350401ea10f000644070350a0920000c0e00035103001204440c4850132007502655501d215400c0e00400c00c07803049034895490740403007c010a00c882c6e034003c0b0703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 879690008 1250 879688758 879688781
    0x20603180f0a02150a1205010902040e06010c2105070227100501080f04140f060a0b0f0901050f130c02031801051306030e03040b0301032d17031504020d 67
    0x5604490451000642d078012102002e0362011911048800b43c0e1281401070222510518120701e5000000782c442050310020b90000c200694005800c209100200c41c065801450901e41686104800e40712540750360f090380d0543d040704a8080c2944250b501030340807115250790180c001680384254500d0301010280e070002c0c0400c2084260001940100c0222440083d00e1051b1201c100d55140d2105620411500400446030b490b5149220390b0360040c100802207801080e030000701818a4865512401c1d02e05061001d4001c1000700100c04242d610810b94074151142500c0d00498a02d5404c000380c00c141e00351000000300340c60410035050196001c00181203d003c1141901702c5501003000446a51058640d2640c40c013003074880910195100c0d4100038034081c00c150403a4209600c420000009600c01e910441d504468401030702030124030300c65914001000c1c10748020140c0060340758118410540d052540e00d4140000010350b2909669010686402c0007500440d140e1300c40c155000001c1003c001d40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 879691258 1250 879690008 879690013
    0x14090106241211041805040c0f0506180411210f01061b03030f0c090e0c0c060f060a090c111507020a0611120f0a1b05190c02060318 58
    0x90503006180c9000036001c00501d42da420300d0b400140d03011100240f40b005164101a030003000b0000300390960b00c0c4201548282c0180c0012241400e28000010314800d50040a0000e610f00041280e0751b0380c2019180d10105100b00d80d40c040004000040c0100440d000070144c3c02d03004125503600080d6034481e44140034840e001500c1e207407076201d0300c842c0f0b01e4824441c0d031000404003584140420814000403601c141309040100304d0400104182c0c083d9aa9405440001812071004000c1407401000c0c00341c10102c0d0110311880e18850b001d0b00d50315560000e24281c02c02640102250030340d1a4182d180d0001d040b40d1340108203004c03010030020000c09510349001c00e80d1150034100c1d03031490000c501c0385000700b0441c0c009140244031070380c419015040014201400000602080b1100c400c1a4489842610b440d121000a49000801031040360360301507109480c240000e11840d03182e0340000440311088416201c81000028890b000c07079044c2d2105000a401207004001d211302200400e480d900c186401fa401e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 879692508 1250 879691258 879691289
    0x140a060c080f04060c140f1c090c0b030c040504050106031a011d1203120112030908060f060d11042a030525020f01060f05010f02010b0a140414090106 66
    0xc003181c200c032040e140032840300240008100090030640c0410034050150a00140300300d10003113400f44640141e120740344544000105901c407043c1a1050103111081c0300410001c0e00d1454403009841201400350500408000002c550b03456402810340d801410001d009120568686200030050910503108000768a050719400181c2e42c00340d4240401b00940e038035032250000c20b9504108422807061b5102a00d40010407040c8440710b40e00c0081c0c0c0c040e160862099010320490700e402041500c0740e030f01c804030b46d80080c001d0000324001c411400350000000c0343c14000842a034202010440c40785c820840e4814649010002c582c41d4560349201850a140b1001c06c290726215030a03815203804549000750411811041030b80710181619840d82076446204035401c2052000880703003103070159040408070b1519030700200003641c0d00c1000000c8041c050300c0288032401c0030801203440607205008240902c2208a144c14030ba0f207c5904c43d580280040000d40458140130f4402c3e0b008014502440131890125035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 879693758 1250 879692508 879692531
    0xd0b040203091002031803031503062809020418052802090c0a0e09010810060f050d02121c0504050a0b09220605090406020a0e0328050307140a06 64
    0x30a503071241441501a01c0e00c18001d4603440003d600c0182810071a0460380030f0782c100c400c1308001441c0b0403040350a81540c40f10100040515059004058a508038030618145600c001d020820a20510040c0c230302091080075440001d028021801c4e1001c8005402d031032400504c0b10011f80011480400003120380f00030f10254007656440c15580d0040c4d0804440d201040d0308240b000002c04118280c0d00d032810030b8046e24000139006540a0380590080d9001c1c188086207152144942c000920017803840380c8900740f400e0042001c80c41c402c00041d00c2506159210100d4180c10b00000c81110b07074900d5a4050713180201c501401d80e401501400f0b002307000c000c0300444e000500344c0484407822070084c030504400a0801084045020003000c0c10801903d4800c001006c2c0c0f1194150f90041c0d100b08000750719590404d10050034607164645403407180d03200c00034a07204074203040000c0b0714080a81e03980764805200e42c10004e01e54031a0440041200c69000c2a10143e41400315013120301c244100d000b40300b40007095 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 879695008 1250 879693758 879693761
    0xc031905070609151d03071b03021005040306051005090f18060106020f07050a120209090c130b04051303140f0f04140a080102070305190e1815090907032a0b0d0b04 72
    0x1c40b034500554000c00021010451103810a03a08403072030f2086076140c8c0d48950100e040d288007840b00c0e9001c41e8000c101442003210601507154001032100c8100100d900e41030004150300e00203001c0700760a01514010402d441460400315001d010400111080b07540e4902e0020350b178152004601c002030080c0031022500746014020034048595411076403c1c0800250200b2051000141c5446001d114580c401d05158031610903902920801c0b2500041800039a0140020b07a5401414480010454080340340001d400c071140344181501c0340800380d01c03940300300e99500706841100700030b210f0071030007140010b402680707200784c03029604040d949075280640e9010070754240d0140940040114101380050184a015044c02e40041443c5103000c5140c00d0403031010580000c0c1500800004250310f1041003542840b1012a003050042175641c50061310704042c0268440342c0a0100070000b001e96130001c440140195004030504a05d000d10b04900ca03540c49401d8501d070306c00601f6146a03070408485029900c6c0c035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 879696258 1250 879695008 879695051
    0x60a020c2d0301200f12071205010509190e010213030c03121404050d020127090506030703050a140a0803070f1202040605090d02300f030c03190507060915 68
    0x707144003440c0f448203130700c1d041586821002180050304002d200741c2507000e0709000d103203005045a80783e0300d501000c0101800140e81058000600405203c2d052019101c00c4c002c240030314100c98240050500b80e580380080c068402c03202d45401c1942c0c13410011091258115103a0210792182100340c41c860181d407400c0d200584d90b111402005002400b00304810700381155000030991052600d5440c01310b400700092550100a4061000385044140a003d9004d041c070030140c0080b0200c0c020f01d8498034680c0d680f9551020360070010300d100407041c881d210080042160a40e05944205d0b029103038600404001c10b126045841280018a21081002503a0b500e1007109c050ba0b055a40d0315240019000502044207042c0c0e4040340c201d0304a162401842d00b800070742c51080f00703680c840d10805a180b161120b1410900340e419142542040024000608000088844140301c40b414124103010600302500c89006001001d400075082202c408200950b1440c0c008000e01c12200c1000000700b41d800c8113074035580 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 879697508 1250 879696258 879696281
    0xc240509101512030309081803070803090a171c0f030f0606080a05090c030712020906420a050409050f0420030a05030d061d090705060a020c2d0301 65
    0x5000c04140001003c140c950701d2100d01900380400c00208640d14a00280c1c440280d221401c0504076800d90780d0b20307040c0b1040b001401c9504c025428403d03070381c0003c1e20001084c441c455a000e561601d90480d40c80510107000700d20f440302c2d0042c000d81c1a000300606000b810820090001e03180980301f03900400c031481684265120350385d54444079070b60015090007d09001c1d08010451158420300b400c241e8003000501c0292100c0d410f4003009501e10b1040c04404000a880c06128440005541c14070326018000040242e0a140004c100358204080d00ba8030130b800101005048500010080b11342500200104215055100d0800c00da40c0c03200c4003418000001d172002811a0034a001ca8007400d03401e103d480d40101c10003030986a200c8050764030750740f03507034031605500d400703070740c0f0340c0800c0000440302041d04402202c1800d00041310720349468003e8844981d805110701c0355201241d48006030b0300c02c10018104200c05401441010034131750080c06414641d01340c04070118030b2031a9042c00f9040601455080d181c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 879698758 1250 879697508 879697541
    0x103020a09020a12020c0a0f050d030c02060118240303080f13030e10090e0a09031e0f030c0504030b1906051206160e06030406050603010f090b06010c24050910 70
    0x3458610b1302a60095075166058424600c3e0400810310380d10104500c944510024160911200c03c0074080e1800c0030000c006642005004200c00d220700c80c1007031505404100000382c80c00b41c07002c600d03034a0070a410002c0b1801d8504107010040580003940c1c203004c0c40e481c1c8058489903455109041402144410017000940010381c102c0311418040040314107010030f801e02602286e1940102c0051020455200e414241c46801e1603051580000c02064200300c01d1902c04018094218098241c0c9050038203c1c0030545c2e64454145034078032403002d81e0061a4407200380c50303003401e010300200450441460007180d1145030a10020707d51030b103024515070340440030b001b41c101a591122040b400b4800d07406501b040c8090241a030109594640045118500c41c20300010385080070320038142160310320b6150071180ca29180d03a0401040a9041d01a803202c42440d00c207203081d01070314081e007014880044e03030600a11040e4591008001c0d641100f8800d500800484602c0405003c50f9400c0d2580d58401c6044030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 879700008 1250 879698758 879698777
    0x60f1203070b1b0f09040f050903040b0304031e17240405060a030b070f08071404261606080c130303080a0212010303111c050a0c0f05030a020102030103020a09020a 72
    0x3280c0041e4543e2005800e2581c026000c03070780140d41c00c070340d02542495000c03940001d05034019280910403020034a0042100308182d01d890300303810f80d60b4030460164412403c1c0201c00039080501c46c1a8104244030381d09034540394080c4c1e00001a200d104411141150144407800080002400001c4450303202d41d00419507140908030802e0000410014200030b401000c048800b00100ea40d03080407900846440e134071160100e1100100031b2002502400030000c0050740301c4130000c009004015102603403100b019900c0410704006090700310120b089641109070240b0000005540006803440044174154bc0b186100d079030300e40a4000f428414042d0a6038028001e11090000ca80f0a00d151584003219200041c41c1555080203181e00607801d9104400040300000e043c902c6071001d02207801034440c803152585075030003201409089030043c001403604010b400d0071a0018071204000b03010429401005880d920010410002c0c081d42c02408260700500d141d010005080e4441d04c01c071100444681c1c0c0ba07441d207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 879701258 1250 879700008 879700013
    0xe0c010206150112060e041703010e0606090f0d051b01020303010807060c08040b04150e010206060f041107060e01050a060501050c0604120306260c0105040302031b010507080f03060f120307 83
    0x508000101081c10401c06209040706801c030b520990b4046e200000301070b00300349003d00e00584e0b082501c1d41c2403106440203100411950100541c2260051411140c4940f2014007801066188103080c0301103170700115040040003071002c04a50301c4c400c00d02000d0208000300400c40160303a248020700c640c0303100740d0042d6410011284108461100a88561010b03450a6039901c80e079841500f098000380c50102c001d0303500c1c49846400000c6040b0440d001e0004e8552031604a000405064486000c0c2e40503c0d1a40e44e8480010129401c664000b50b2090b401c00c04050365080490003082c0071580407500e58602100403403198003400039101c03096010b000030300f01907072661340f034455a08484401000f03054484002151407040101c00d0310301100e80c20340c0c40e0383c0c0040b0781466a141c4103002c02a00d041c010200410b01c050b0f1008540c003083d104140c400400d1030740401e00100c07003612401c030000d0060b180110309200502c1e80c1000550040c0b104032007641418181c80d003000342d604400c025003000e0340d20420201c0c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 879702508 1250 879701258 879701281
    0x1150504020309071e0e06040c0c06050c090411090f03030903100b190605070b010506040b0433090e0f071d040b040c03141602071a04081209040e0c010206 68
    0x2e004a83c0010b07205900d54480040d140c03540384032140310720420020400e0204250050351141d202404550502c07100104a0700a0065510307007001808003611003001170140104001101c0d040c04020700200f05800080d0b604020380d800c03801c1d205200707421010411180749000411307100c0301e1100901400a91f280904e240e8000c0004000e00303600640e02c4c06203984200762128941d0001e25094484a84d1039072245468445070405801491140742e09010500440359401c01b601c0984088010021008044140c03040301c01c5c1428182d5061b40f03600c0482082e4a40e03100c0071050842c0c4000408413499100c40c140d4201180301142c030031001a4140030f41040a04413212070102c0c080001c0c0000661403040e0b4040780c20784046402c9003010a40324581020520399110f0b03950b0740031220381c203030350690b41031030718025220402031194009000304c00f810b201e4061500c20468004010900440c0d00409d401c2160144a4104020b01d503c55454040742d28034800f00410509140c540582c0540010307620f0b141c2060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 879703758 1250 879702508 879702511
    0x60c0f0a120905030d020304111f0e0402040b0d09210c061a0a1502070b09090c07020a15210c0906110127050106050d0c030b19050403110708011505040203 68
    0x119a54462010038085034084c002068030f05501e0502594074074080c204614280786a082c441c0c02101041c0c40402c0d00d03c1c001900186601d154a49a01c0e48c610003030020f4082d008a0704861492030000480b14a114916402a0907852060308407005074110b0070040601d00c681000002c01103801c142004002030344951100b4074a4800e034201e07131440c030307681004136104c01e84540190a414100c2c42c081508183c040041d14010142c07988268a805500c1001c20401100600110004000401d0b418115070301c0c110744070040c04403030080a040d000385140c014280d00c10041101c2c06000e0680211050110710f001c0c0f4420841c0035101d1b0442e49141c02801c840500e264241c00505543e501141c001c0c50790084002c042c03150700d400350301c8c00b0520319040080c2104c0345030380100d01c00c510401c00b400c00110000703844d074100c80e0840f05d4100303665101444010300307a0b442078419112a10740b808004c00c042d0002c140b4800540500304480d1801d032a101214200c50b50002149240403014808115910b0b0940056 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 879705008 1250 879703758 879703787
    0x7300b030d140409090c0308070317130f1401060308180a050901030b190f0e2d19030203040506070f0303060e012313050c040e0702072117030a0608060c0f0a 69
    0x6c2d00055525103400005411032042140000c001500b54049040104100d41e00301c1d00d481c2805c94028040c1e07407520303440e0141090041c0394455a07160b04a00c0034003948918007c6800c65000d998580ca1076516074012502881c2c45d0748291034090000c282c9041c02400181a654010441892903d0b89052182c808481e04600ba41d516220102004040300500400e0050350b0300344010034010310b1301040c0c140f90007520303104d92480c026200002094008002400302e0340610076404681031081d02c2c10700f00e04511968000300c0e0440000140c2c0780c10007201142c00c490690181da4208901620340c0010b1401c20020b10074141b10010441d4420703580045441c46000901d801041100c0c80c03010f0a00c43c10036558100c420b21a1100082410803002110700402584500940f0180203140d0a00d455049064280c01c250b40f20300304100f144600b00074a03c8440346401c1d0403034854544038074025200134003034035042c0103100a80c010303100070580c0120040c050b14090407081c2001828803124180c112100c900e14000c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 879706258 1250 879705008 879705023
    0x402090d0204060b0c101401120503193b100e0a06231603120f0f05061c11061e0309030a081303020607300b030d14040909 54
    0x56400580d00c1e403044030b00600b00e04022079290171408120038240811600c181940c41c0c00c1c02680c400480d02100d003103040d1100c602c0d11949401c0b2a0409500d580107440c449010030a0780203900518503045600556039118102000828a00c2c0a0502440300c81440b0396031154141d90321869442e1505800300e6401480d1450095540c240180c00110260156032104000c0b0340312801e41c000004070130340c460a4200700d0303d190030f1405183d0381c41d00c1c190f282c8010010341001409910380c50140442c0c0c0050541c0f01c40d14909101d0403000da000300c002810305450062294001a000066103100032500c140e040e5040039541c190101d0344c0050002561080c0c000c9a070302d10580801c5400c8480d00e0f4007650090590b00000c644802d1031500240040202402410788140d2454500d800139600150103030b07100d403252500b280c00b884404004608052038040984500842c1c07a0760380e407800d00b0380d4009075090408a0132140100c9081c602a01e2422801c1030740381d450502000140588200b0f500140c1d2414810303420b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 879707508 1250 879706258 879706279
    0x15061e0e030a05011427060402090402220c08060109080c1c021c170301210606150806040507030e1905030708030f0405100b01120b04112d1305040209 66
    0x68450851710801d080300403803000101401002c551040400700a18a04c0012020100760410000c0c1c0c1d0f000020310081c801c660745e01c0040d0071500c0300034110a80601281e00380102d49074201464014120f0200d1281c00a01c070400000c05962090b041d0b2022224808042d03d401c00196041c41407019981910341c1200400c20241c20040c1c448040010764040d49800210314210b030380c6440c24484076045504590301ca4240018040e00d048590310320313184207449201c4281941c480c584800908000d510801d030003541034650001071604000c5051181000302c40400803039452080c25012154203042c240301c0c55002d01044483c124002518480031400390045906003c034603078031482590b0007240c100f6000c94190041c001040410400a1100014003105002c0d590810000924000408640071402e54480340b098101e071719603a12204c2c0409404840c030360382e02003094070b407010080541c40d0b090213200d401003e840a0801c400964840003034440c8661200e918003010013000e900181c0d91103900240411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 879708758 1250 879707508 879707513
    0x90606010504061d10090e0a02040f09050a0f061d0c0403050703020108071e0c02040f050f15040e010507020c0102160e0f370b0411070b04031704050115061e0e030a 72
    0x520100800c0a41d200e05190b1f013844400820a1000741c09000c1c4d15005000612486204240e901e0035920f60303140000d40c55072184d51800140c200560318a8040349018004243c2a05030180381c0c4e6140804c0c040291180c4420005248074820351001403d1138114040c180010340c0300e0502580c20103214a0000500c1e003a0205c103e0788424440040d00114004004510450416000d00c1082c400c0f8500c04122928200311006100c8400601c1118144000000e048150380c580d804030600d04c0504000f0803482c5032185001e0764034580d032110300b40503116070361010519842010740300c01594a5000306040a88400010030143d510181030494101b0003a995a1540c40354650000b040580800044400c070b030b0901c002c01c0403914504581070046042103120b00201a0340c0c0106c0305c7d40360b0300ca80ea5910390b41e00c60800b210412404031052351805401c40510007489015001920200c0e0a8135000c09a60b5848100303803410110240c030303403545248694480003124003c00c040c100d90b0038068107840e0b07030001a1f07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 879710008 1250 879708758 879708769
    0xa0e04080d3306090b0304050c13200406090b070f08090105160506180f0a0f0305090a0b070203010c05090337030804050615130f0609020d05040b090606010504061d 72
    0x4803598240c20860070410420b1a03803268840d0300034107201740314510b142002d480e145e403a03c0f405982940103421203d0000304801d43c903800351404200304048181050030524042e201b5501c14404d0000086400d8800303d484d608032402c503654541d114119901c1c404c0d05541d0070486410024007141804801c1c8030000c021103d5000c04c50507103104501901e00d03460281c41b44502c00c40750141d1201c5c3d42d44208001d04ca811000140319018641141002c0c00e161107912381100d9501c510321101da000383c801c041c0090449156000740140701d10860007440000111241120940607000d1442e916a100d8842c048403180075101c2c0d807081e2802d03421a03110b2100c40800131401c6201c0841e04400041000c010881131040a1120303603085039440520384522400300d8001070840d84c5d100c0340c51405076652644040c040ea5039500800003040414030654039000c42c1080c2100070101120140d030040c91074400203121810103d0214400c0005031a480d007440d00b010001c645e205000222080d00c006e20751640034166494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 879711258 1250 879710008 879710081
    0x1b020414010905041202072d1a040306060e060f0418020303340b07080a0609060312020c0a05090a02090109051201060f0b1e0f070f110a0e04080d 64
    0x70b401000c90941418603014007001005000301085411140051040540443c000716804240d26a407410003005071401100c1c404981e8801c5400446002e00303910801c0c4584060f00440e8002c1c2d50800c8043d50381c03a10b011044500700c071016849603100f4500015498541d0083c12100d0008030604100c07100e41c0d01180c60742d40003482c510324810210f868002031203400c05404203451000314407040f40351403949d247c60b4020b40160056041c80356002c000350041c04c459221130020100c4c0b00050100980c1d0b400c041c60391070003c990580040c000c41c6000d60343c41c1003205443c412140301400d20312560f5a206401002500040159810485d05010008150fa41c48a009400e0322100d40001402b41c07600440586100d4158800000c4c02c0b0705200041190150a4803040c03402170710324403203580c1c03156003118504510079018000c000c501980c564006001007110407003464181610404110b07900d5141611543c0340c22600181081c50030000c40902454031340054000301d040e10f01e1a02034185070300c0103100502c40b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 879712508 1250 879711258 879711269
    0xa05061803390c0306010302060f130605040e07080906010902090a0b1b0114090604260309010c030b030109050714061c1e1b14040f0303081f05011b02041401 69
    0xa00400000748228424501c0c2d0b040b008000200b00921100000c0303626440e05120203441104042004900c40703100c81c0031160005810f00c660755080d078446801602c5034109000310031460000038000b0740000d01a42e4441d0140b048000148000e80c60034070400701950240442c44d40280e1202ca0004518402c0c0000d050040c11300039104902c0da00d400c160340d084602c407040c85040c4169203400c2c0311304000082021034025400c8640100f4425414814400311440300220041e48003000042000443c019405203c0203506c5036820f01415900030201400c0e551000806085904031390410004804201c180e8200d420024211505101942c1250204107031081c0c2800c54560b02c980c12030310a41503214142c0c1608210500402640c86e01042a44e802403403610340100b44510044550701251040d07040d00c00070405100c83d00107542d1645401403804038181e41c2c100b0040b441001000305034461604501c25110180d544d900c280c440701e030b05600380483c000000ea0300310b0341e58110390b400002c8410381e0501909 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 879713758 1250 879712508 879712567
    0xc020a121202040b030121021012060b0d0c020f07080705040f1404150608070e13020102011d03070b06180c030c040302040c0c021809060601030b13051e090a05061803 73
    0x10701d0135116949540c000c91081c21410901f100d41001071360340100c2091074121034a054010020400b40c42da000f05103540251640e1403002c1040c2c00308a43c240c0100c092240b036982524022416940305c0707580c6a089000c2c40d5090341000038240020300303180e8048038812114000c0400d404ea064114400c3d0044180c805582d2a0040441c0c0c0c02c04081300d006042c020800c0d00c00400c1924504101601c14601c0901710700300e0385060500260641e03100f50000054076594484c1c046d08200034800c0c3c2c607525804600121405681040061306500d80702007074180b251034408401c4c00581c5d407091400401d078401071184c00846000c0c0001320242e20740744034001160320307503460300b002440c080d0040040302118500350501d00d036010410401a94801710b85150408420308000c40e100c00f5150004442101d455585480c8624040400440740e031054088d8a0710062a824410b007500e440c560700d921000c44e898064055070101e40401c0500c103070b801030307641110b03400001d5a0a140d80a94410300f8465040340e18161007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 879715008 1250 879713758 879713761
    0xf200a08060108031b010e01050a02030610140f0c0f0708030a080a020306030a02450c070b0402090c070f061406030d080c16140a150c020a121202040b03 67
    0x141001455000030382482001041d6562400c00820365a2180c0172900210880800841e001d00509401c000400e5031050024841e80c036003180724200941003101e00a20540545210407070450041e000810300a410343c074054070b4490680a0080c0c50750181e80d40d080711f403180754a1020034034809d12255024205290182d07684106c0300c08007d043d190003402d821aa18810824018580e5001481717211060341500c050740c540c107000141041000480a004290900c610162840303100d02c21664001240340300709100d500e4503504140c0e4628000c07107100134171500c00b20002c100903103001c13208181e000640c14070162914180e07a42d210080b04100008640581d114000c00c18100c034480081d43d03103d8020390040540d1100d9403001809940050300416401200107000d000e40100070000c1003013039030010691680c08020054030342e42d0784e600300d0341601c5000211011802d4107815008106c442422a8010030040c040ca880701c125014680181d84103000d0182c41100500c3c040c2d001038001055036000340741d200e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 879716258 1250 879715008 879715073
    0x10602060a1a090718090e01020714010504031704020301020f0d0911060a090308090d050109080408071202220e0712170c031603090b1c15030b01060c0f 67
    0x81d941901c0490105901c850b4240140d915160b42940d446050b515180f2045000040006803a1031140c12001c03440c0d0500c0b505815104d0150014151188540d101e0704440170484145400ca8005450041c00100c0c40039461040d00240c6415036080750004000515081f5070780241d4005611035441d80364000e8640c00703c0c00178440030707c5d561084580c0070740f842890f0040003400104070f0708480c00010001c24000c00e17007002c95181c029044c140558080c0003081036110320b0500f2501a0464440c400c42813280d0400807914102201d5801ca40d2a409844806480c01d00889035003842929100b84403159500c503140d0b56480c01c2081510010206044040000503480c10b01f1080d5000010b00458a00c004000540d0b03002e44c0082100c2c040308030103180301d88445603071034119482c0407154002540250082442d121174200780040f106007405a1408225844880425402d00340f060f20018011003840801000b4460240d02da5010036071041e00c250105e0301346640d40400c1400c0c10102614683d81802c0c80d61038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 879717508 1250 879716258 879716261
    0xf091809120807050313061509020408100209060d050c12010e06010e0105090d02010c02120304031109090c010e060d0603050a08120c030f131a071d1009030204180b010602060a 77
    0x81c1c0094038076042d40d00d4079000d07402520f144800b82050683d68401914103040c0241c80c0d201c1c990580451140405140e80c800d080e00c041d41003070142041c0f0380244a26000c0c1e00610388201d0f1911040900140d080080c4803c030300004200086c110446c3c94402c100f4040b00103810014a4080d0012880416660618034001003140c2d941400d55814071030108586070665482c1e0440848560b424a800f10101032180301007011050b2034000c05050703100118021082100c04031074600f2800041d03031203c4140d580c54410503610240c2c01086408030724022110011402c0c80f60080c002e40c07902c2038011909030b540e070761110310381786c4404001d0343e40382c0d030100c2c41c165941035003486c00780c0115045070f4450a50a00c00300c0c4d040f107080083e21210000c05400c007040204100030701c201034800c403d02d41f90f41e1b41e440c2a6102415180f0705c0f002d000c801e800300c01105103540c9011044203107405182d54408104908550a000080c107035403280210100709200040300051507101c0c218082c00b126400b43c9810300f000140d090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 879718758 1250 879717508 879717533
    0x20a060c140306090903040e0c12100b0d0c18091506030b0a0b0c12210a020f180310110a080a06030807020d031e020a03121b0f091809 59
    0x1042041c1a540c421102141c1d00680e03401c40380031030740000c032500c40042103440c42c4103660184001140f000e08004600c84a00068980142c806414403d2079541c144400b03400b04003401003036082002440b440f685e40720305a115050440082c282090b15a8200c0c0030403030502039507031100e20319070348034442c00100214024605000303003c03e003400c2c0400810b13070000440102060050410b004d43c00f0526045090040103814184800c103028956611010b03000200c40d100f1020780c02c00e03c0803000340410080c25031442280e07142e0b004038a0300f9003050398184074410b106a004880315450b11644040142d0392149200c0c001c0003940c0c0e4440300e039403004c4108001d80048801000508903601d0210200041307828101100c402560444e001c850050141c5002e448001e0200c10b4951103041481e0b40e100603640010303c071480e090180d180d4080080f240901c060655507070301e007206503107003c0c8111004083c0c050785a18030981e81a081c000d585640311950b604141d0207010000000710b07120042c10041c0012100d114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879720008 1250 879718758 879718781
    0x250e12100f1b05030a110403151803021c1101110c0d020712150f060320190e0907150306150206060a0621020711042712030615020a06 59
    0x1440b10491100611148100100541d800d00c94000005400207806501c100c01d503951006d48503403a6038070790500d90704000071001004103407480c0070803c0410102c40c2c0c0e404403405034158000c1c4000e44e007000031544442004194001400f0599448612a00742030003056080100300007410b444590490b005840c124241d141c0c10159040101c0078031107140c185c240584015049076001c08255640d0881500030030550002e080c000f0700c3d001c3d0120400500804206210002c4144480004210410840f206002014952111010b408104461000445001d90100e100410385850a03500d4410a042803040c0b519080020342c0e80b4004e100c4030f1516800e0104603480c610007007240b4980040490005c86c1d050040300188103191030250941070182c0c3c007495100011510030b40d2103020340e10700190030084d0314040c0c1d84110b0030300d61280d4a8441700d9050660080354032446410603a243d848185483d1600041c1c60109503d40502003120b0903d50000c130098152039004002d40e80f003d007041c00032240e078031104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879721258 1250 879720008 879720011
    0x2060601053412030504021e210a0b010909020a0e190914010204090603020405090a020d0b04060b120c1807120e07030215120609250e12100f 62
    0x303140d650865403110141500c1e008020341c1c400080200c500300746001c2d00c40041c50302d200d0b000003103400d541c50b81001e80540c2c0300369403950b0111464081c211a003001c0c5101a6000b1414690000c0d0055250000035200d0f400b40c01601c481d8010303901c51100e547c80076080752112603164440035045080c001c003540014002c4c00050390b010304000ca000303940c880d590208143c41546a400c8501805400c2000501c1000342900071560340e03550308000c10140030f4610059204a14180014001140104d00301d08800e038010100c44240b4600d9480b45001513010b441a1f8150b0303505c00241d2400c1d255040301c103401c0c07440c1100920b0004c2c1c0300710800c0051340c070039000c000702c251020003400f81e6150440484c141c4400d46000104800c410136040c21301c0d02c01e0603400690b01c50028441c0021450342c4038000c16052031000c2041036540c0e500320a10a42c07160560700c200d0303916412508000e00b010510070300300b00041140b82c000005852400020241105a40088030540184110900c50001442a41090b540c0c2d14030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879722508 1250 879721258 879721267
    0x9070503011406190b04060f0e0d240204050a06050403020423152403040218070c03201203070f02060f06190801020d060302010801060206060a0302120a05030711010206060105 77
    0x1400210ba49020700b0300790144c0841c208401e0102d16281444025051110740161100d0791a4130041c807040e509a00ba5011a0341c0b00b07410506401d1000030704a5070707034014945510303c000e008034000402e0b42c1003e0881403158280b1000c03c840d6103140304080100300554980340c4071350950041004413050103806c900d134031007096506c503071021903030320029070148024480c407070001d81410114204a4204030003501244142058000e403803100300c05075002d207000740c400400064204582194100044c0c4000011401d428281d01c00a0b02c41c10b500b036a214089506a001380b030024800c186411a5046001b4024001008000c401d07548600245002c4d02d40b0320003085203060208225900d94400b52070a4040c540e903031304042c1140104140c03003000741110b20085688030b1001d00c0c6940206002d0108031b0028000c08000030b035092000440d240210300003808820b1482c55942005240b4000c40e1104240d0300690b208030780410303014000b030007c4a01840180c510f2139541800281045001803149050002c10311 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879723758 1250 879722508 879722531
    0x2040513050a080901020a02131b05040320040f05190b0402090603060411070f350a0c170f03090c0103051e0a0902090421050405030c060904091403030907050301 71
    0x581a5585401c60501503036400e40784e00407030900107010406034001141e01c11900da14071255004083c05840d449c010010b10396000c0c0e08a65511072131001400740e0b03c814546091003290700310040c4605000502c00a400c0344640c40790b0054440441321a21031100b000d0300402d051040d4040c3c0e00360200101e030210724245440740020110700000d440e046c000c07aa01d019080d80c903a03c41c030885520740d8200344010001102c91801400c0c5400e094480f100c02c0004000d10100c42c4034004082042031150481c0744e06240b103170320046542240c4e01034145c0391b403811980b641440800000080000d008499800d0b50b40385444181c103840c25560380960b82c101841c0070f003000b8404001c20400b440744180d1118034007568482109002c041c0100c9200a50b000c8800400d1100704003116203040d036803001e081d000c0301e00c0c0c20752404150341034082e901c11180c00da0400120f4a85078a80580200100c80c80203000250030541c03501c801400002e080618949503000205020001d081001100e00414040300240040608031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879725008 1250 879723758 879723763
    0x7020d0b09010b06131e0b0427020a1407022d031902060327030301090c0305060301060302030715110609071a031302090901022209322d040204051305 66
    0x14440d41146d28009840100020303204c1c01850001c2200032265600c0321388410290b030307484040e01d09040c554003609103003200e00c0c5014029102e40340f2460301c0e100d80102e068510056164040b1100300c2e44088003200450000030020074500224a401d18444a403a080c00e051502c1d010103815007100d031300d240c2185d24005a40319001c4a9001c0c010300c2c42c03040b418082c150242d00b8248050744040d41c0740404400455084850740c0180840d100d2594144003940310f0005040c222545408003a4041d042100f042c8105078541c1454a01d119451070084030001d00c10048909104090b68031324511340040100b000b03030344120b030b61101e40c02140104062450524a1611000400100009016014890000f1001c0100394140c84408010031000d201c400903810511810760442d01981440c1482c010703880559a44071000d040d402c0342400340320106066882c401820070700000f811101b0f52101d6000d51950954641c440b00040d84140a620304541014410401610002000e0b42c10285241c01c6c0c900110720300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879726258 1250 879725008 879725047
    0x1050307090e1b0d060f321b0c07030506371509020715060803070206090f22051b09030a02011d1809070b09130c0507020d0b09010b06 59
    0x54203c464682c94203d0f01250503280814806840640360000ca00c0700c0c00300b960445080103103402e040c05190b4000710f260201441e0042091441d040708140001c180390032804401041c00c0c1448421414002e461164510b4828660000c8800d60400d03130a104e004590807070303183c0405484001d802c0c482c09000c2841c0040b860101d0200b10802e8566031001c14222140c1c0d03100000d401c68090540d9076a085062032212100340240701890035180900014052002005940625034024800351030005418100401c00c0210514260700200390314180d003050300ba842c604658203110103000b00e03080c40d00403460b414080180c0201d01e008402000a01103a41e40483e246802d5542428040c0c1586151031013000150741c03090344590412481c0036109550342c00000da25114405400445e401c1c986c66010390701c0c260107510b20550b086140d810640034100a030383c0040a11542600d8254204507540e0002881c5090700c09080d01c103200d02505200c00300000780580c406c0c5e2076082e01c100d403501050b1080c0c0703c40c030342c103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879727508 1250 879726258 879726283
    0x60f040308071703281b021b010809030f18030d0c030f0e0d02012d0c2d021c0515010e0601111e0a1b080d08010305060a0c18080601050307090e 63
    0x7070394036409545c58194030002d01c410a2041c1c0b42d00c44110204007a42d51040391285451401c45001c0100c099071080c18414815080d02003e507007000d04080e03c192a40d044403414400c7e8812520707001215440030062803040c404603a540c3d80f0050b0043c01e010b03280074001030b041020800103c80400380c0b5110038003e0f201259081c40d10300390300c85001e009000015003242c078291500c106e240003080480d0344071400c1d002c124001d44030701001a0b05080e166a0429200d030306000d0403651001103502500d0f0080381d64412890841d40404121401d03515641400410b200d07403128545100c0c010301100c12005202036110400382048002c950b140d199450340c0d032000788810021220001c1401c541e09400b44680c14005501051114203040d041405100d929164068040726203e0035048584480c45500c0e8607048070340140280000b61200c003001c4019044d0010b00c00b051126861000000c0e0a580c0702d148020078654010b0f00b4554103103410541401e000740d1020850a0801c2d61800e03194401043d4000f4150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879728758 1250 879727508 879727561
    0x909050718021b1014100504230106050714030309250503030c0f0607020321040201050913050402011d0612041a0c040816150806060f040308071703 65
    0x60700901107010b071251050601000f000c0d86581103101d5400514008081040740c81030182d10f000f803600c00305200b01240c078650155034040c010003036804e01c1c0d405034980c108140002c8140311a004141d1b920700c10301703030302800010340000368083c01d003e2243c012050343d000d080051851400c102c03a81036904c0502014040d40381d410403021042c00c0703040074140401003d001e0250703520350720410b5030075441300e4001601c81140e0107400c00050b00c091000c004c0328084e10105c20003034640b607001c800b030b049070f0314000f031040b4140641008134260a65610f040080282c0000c0c0d07000c10240303401d100040c0180c035000221008815201c0c0f428290355289010340361035a8021040030f8850f035aa041411040f00c4c104130144400c10b28000348207520f0001c800800c1555240030481d0b50040000c07010184062944c41842401c400501c40254480d2240107000c2c2c0000700103000b1030030b03c1c0b60703081062792030780c010b910032078403a00006104010080d407454940743c0e80d80d04608150035494150000e048154600660f140d82c81c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879730008 1250 879728758 879728789
    0x1e1008190f0e0f0d022a061611041e050408090909071d04030f21020415030b120c060c031c090b060306071b030210020c070f09090507 59
    0x120900400c90501600140090041c205104045001440100c07040740709030007900e4840500c0c40c8005040c02003441641c2c000c100800c40f1010048640e540030b1a03038010141c80d0301c5400703079a50350032000d041031070714100d1101d4003603d981c83e044100c044a0341c04c003030056003440d101ca5060400b1603100c85400d480310001003803560342c03440d04101503c01c0c40541d41d48020200c0a03c50001c10014240041d20025024441e40d00329496141160305402c0318001e00142c1000c1000c50894811400e65010780e20a0003030503910310504044c0000d80c1c000360014040d00010a495503001d0780e1500421030080c005958410b40092081c50260307c030203c0c0e0394824040e440000e034802c950030f01002110741e0754044d06901e000e40c40407240341401810036030109131030721180b000201d9818600810000d0117024291140c074550b040040218404192440b81a030560003001d900c0c580f41d180c2800109141400540980354541c01c280c480d000800e529004020160b02d400c0501c000030384001120019a603105244800e035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879731258 1250 879730008 879730021
    0x11503020a050c0102030c0301081b0d02011b020d0311010b0a21050a0f24050601020a0303150b041d100807090216050d081518010b030403141204021e1008 68
    0x1070310581c8400c1a42c4c1d80b0000030401c00c04c182c01c006c2c5061ba07641f1002d640101201d0340010b224403002c07104c0160f0001d50407030f641c00158043d100c5900c0c02000d031044d00259a805400090a5221014068022030810541d158105500384501144070400311054039006080c61b1324034079050b640f80c1210702080024039480713040c01810000085000c1c2c0c0105048424900c614052203814440d80078001c40c0115941c0143c10000346c0d010f501d02c10141a4010040f81d00192411405000b0414424184003486900800c090803054020b1000e820100c1c2c02d0010200c1c044002c1445110040c03030700340e65880c5150f05001501c1c000c14800d088980d820000368851030513007038042c004103d814004220384240d20307801301071982140ca40d61088140030001c144800300c00c400c0c07284442504040354040841c0000500481c0b074200c0181d07070810f0003803400710560300c0c94107040da1183c0d01c00140154290310400c2040301318544611102c400c8005403000c1080103901c40c004c2040e0a80c1c0581440c144010383c40003620 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879732508 1250 879731258 879731267
    0xb090d11100203070326060411090d03020313050f060403110a05101e0806030a0b04050a1a1b190509040b0a060c02040e2410050405010f150206011503020a 68
    0xd40810080a03001041d014100107560303940060400c40103d4402081d203019881c0e80d0303481901d050403403171950040d5954102084014010031070710000095092200c000603442d0585051000c0748242c004581c0c0b030826011600c01d410030769000d0381c070500d1940d00006683c4c0300c450a503011654403104810b02110038800142601105400241c1c01044501c103001040340c0c02081129500d8914286440841c54a40c08680c0303130703a04464840c0c15500807080840058a0b82016071360003401401528101d403025640c1c031444104480005640e840ba200c10700c40c1c0261001f00c042d1100b504242c210745404000900b0005d44402451010248400804c40380c8158443d500122801400240718201072a00c030803001d001542c2950003a4001c134503184114220501c0025070300c44140b0040350030100c2c203040442c102c00c072a00051102c5040c0c140340c0000213490325180200e078081c008503030354200303443c1c14410350094101400c2ca0160440d40b207140100b111a10040c00c3d240700c40b10b180381c01350382ca0480780d0003601d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879733758 1250 879732508 879732533
    0x30e0118080303070305040605061207140105090604090506010f020312070c0f02090405010f1a030c040c09080708010504020f011e0807090b0c030403030906020312070305062b02040b0a0b090d 84
    0x74280400410051100d40c9079010394460fa00c220703410082038030b6034810701c441100e181005081590154200b4040480ca0540b00302e81260705240c242d00c2c10b2403090208009800c07940c42000c1c2203440d58140b06040d83c00444592580c078287c4020f50802d4114504070049a10140503001031081010042003071141d588100c014082d0060b001c0c1d20542018078145000b000e800e007441c0d014034503081c19000e2440c032040b00e058404000400a00802c98001304120051015842140500c982428000b85006061001d24020004000006020b150600500150301240d482c62810040364070003542d03144070406003a4050002c14980361240d40c0c0c400d42c05485001c41ca0b004082c1e00034001c0713407282e084940040104140c81c0f10750b03036021129603100001e0380c4e83c0c01400c8250481030321990004c1c80d1b25201c0d0b84220f512001c010881c01c0c0d104c0d0143c4c0c003114544424819208114160080d110a5040038050707045176100a4801c44001850648200c40c51701900b01214450102d0481a105000e000302440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879735008 1250 879733758 879733769
    0x1603021504080a030206040c060f08150d1a070207090603120e01110a110a08010504260d0608010b180907030b060a032a090606090b090a08011113090603030e0118 71
    0x40f0420b40721414007964580b03088070101c40d1100b492002050040c4540c480326206445a1281030340d94981412880310100340781c2c0081e800002e00b0500c80041001042924008404081107004504021000030b042103d1500301c002d030b05081403400c1001038501102d070340d182503151405140c500d4100c00104c0d02c00c8d50860180015201e240c4802040c0031009034070a4030800202c812910a55489540038243c0d002280e01802907503d00745c0e017450300c160881c03603114103805a08580c0e00d0504900700c810221901a0403040c0142c1d540e42d4040307c1030614140d0200503405903c0086620b07e01603c0003540c1e08030360b02004001000d080085406610b40b0f0850071b01460f4400694801c40301803a88044c01081d4010703000e0742c880701d240d0000903010803a104007010ba0301c141e500c20115030304140e035031010303544070070314881e00030a0365540011010428070405d03400190b8244070590703421500c1c20304001d50395107802c00345010b45062002c01c0040c0e049403809081e41c6081c03c14129020440801c81610200c0d40d104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879736258 1250 879735008 879735013
    0x1f0903021504061b050309120c04060f0e060d05100b0a0b0a0309031403040506040206072a0510030605100806060403050307110108160905040f020d0923160302150408 73
    0x240c1e0003201c0c207400078009031081607a4911400c032841e4125060980c4145000e0300c5500100141e080b1070514041002d4070020305421141d074090380c98089002c0303403281d501c44a1000b800520902c015183e032100030341c20007811100c248400c0825103c154a802c000d15189442d1962095548aa41c4412000000508103d480907480e41102e0708040e020300703140801100040c1008201c160040080015640a1500a00107020981c6c640e401e01000394840300c0141c0b00840050030100c40020341e400181683d40d080f800740598140380205200c0413240c0f01c5039003014981080e409204589a16458407070074021454854000e840c0c0001045840c4601c0d0006406400002040b1043c0a42c0002520003440c0c20381c2c0e106829a81c0701940904503845031541d0001451642c42085149059001260348188080c0010310b0310444104400440300c5844086803d036525450501d0300710003940c0c0140030881d03040003408a040300c00c1048511400b00c2d002c024400c2c10007894050000d520281554040e0200104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879737508 1250 879736258 879736279
    0x70c061b06140f0709030519082208070504020408060c030402060c0601060201200a1d03190521040b071e080a030b100201020903030d09050f060408040e01080105061f090302 76
    0x3020b1080e608452004603480c0110228602c0340c820107843c41101d40000c00392005440b05075985e20111410101900d8440080c4100c4650604080803524080ca035508100d040a14000c0a41c0c2400d20a9000030b01c0341d1f1050204001286020419a0b406541c242803e95030ba690340c4001001c2d4003c0004071811071145200125440741c055100982d2196a0703006001e00980c10840e068482c41254036840c000340380004201180c280000e40c44080f1000202511401110780c0b052211401492a05071010382c07000303003c62964006412070000c0c000c04c0d8904a80781604096800b020ba02c242d803001041d4510340c11181c41843e00c2e070b0aa4040b801d60041d0499660b00020f04018003810404140301c1c032800218849102550052085802060f4054055807e0648043c4007200078007468009860500400e04840d42c0d50a0501045110f03621130b01c2001e4889042c95503040a5520581240c0c1c116858981484002e0369180c0810f0380c61451001d00c1c1d11507802401044501d5001c9500c0250050079104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879738758 1250 879737508 879737531
    0x32f040603060f1401211509050c0403021819061503180b07050904021908090616050403080715050a0c03110306061e1b0109021203070c061b06 63
    0x10010800c548440d0340034060562200450509806180f043c1d040c00c0c80a144010f215500070000900c0c401b448201d01410300a5116862041d074202002845482c1e0300f0903418401c11b007091007800e8002d4140ca002d40e040500f1640030403c01003200103407483c5205041c000400200305c441c1c60b8405115200418045240d9900c1d00c10031410100d07460101184c14070300c6070100010340c0010180020b81012081c405d40d290244240e907282e00a269094109408009200411030302060001e1441d1031a80d410340f0914281071018240b10001d8030098404220b000003043c0709900006880c04d90303800c8941a542c0306103d20317160780e0715103440754441405070030102008002078080e03000c0c11500d851a2030503c01490042041600d41c801103031400da111200380a90110050f035460842c403403020002100749090902c04400c41c92800038032007079580c0c0c0e442e0329503007045041c0340b40701e11101140c0704000d50030104039a441c9888040b550160320104641c41c040f40300e408246203144820550400001c02046009a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879740008 1250 879738758 879738851
    0x504170414120a15020a031107150b030f0c10030603060e070f14011218050a0b0105180906040b060102012c0105011e0b03040206131503110c07050103 66
    0x200318061150008142c0302e840b10a001c645041d00e164040b903405903a083e07210180b0029000200100c1c00c240e030360390403590300c0345031000207001e02405840c42d0b44410a0340341c10030058030715010016010b81c0142601801045001681c0d00700000b0071140301c601c3c0c24880004a00130f00d100d5102078165401e2017414210706601050802c01c2d65211809030880940b603106913403008000c00807860000348003080001c4c000c1440e6208401008807200c40000960711901c030507141201c4014203681c90000c0400404c00d600d0f01d05d0200c003000b502115900c03910301c0d2502c20039072a00e500800c00703401d20749404001407880c0c3c400c1d4841c110031910340c52401201d030910fa0380031420000300d1070b08460640c6481e0012403811a900a000d6650100d000400521814030004480d0340e040504202e80209050100c8210f402e90701400502401c0058050013840900c400001e090360302d0080c100c0200401006084401c01c800310301c200544400b801e000c07400c40090f54444561980440c3c22a00c121192100c001070311524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879741258 1250 879740008 879740039
    0x30703091b03080712052a010e0114090705010c0c0603050603010e010f1a0405010807061103040b0d0f050f0114100e030f010b0a0e31050703050f07090203010b0d05041704 75
    0xc1c1003403030300b07990b4012001c3da13640c8a0200d41d1101404142c5280980c47e420600d4140410704900000c0380c401031001a007800c0d103d40f40e01d068503074214401040504007040141d54003c210034031b403118588140741c490b0fa1030965580590010507031120001a40c54809410010380805000000c10000740314403c031400402244c804426500d1526600c074455181c180126816140400041d20510b8074106054942260728a140c44003400180300c0041c5403411100a802c0c1e1001011011a02525041c500c00845200400e000e224042d00001031000f10002c0b0202e0074400c00c15258070440b199a21402e56141501e000c41c02e42c14454010100709040c0103400035900c060050311141c141d19210b040c006251803040300d406030721030711110300d01201c11141d0030000040c42c0e9000903609040c0d5540c856504085080d08242c8a03584595a01c0300c200e5002c01000e4010f040020b0114215418014049860b12031a043e2580081c0c50744049814051240c0c5010700c4201c1003c049a9216540c41002490200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879742508 1250 879741258 879741263
    0x109050919050606010311210603240109110a1e030e16030c05030601120b0717280b0a0311060f04030f050705041e1104080706050408010f0b0105030703091b030807 72
    0x280303a12441105103640a0b9440041d0082c280492482000032000c0c01c200014027450340b40c0706045140e8074189203000360165466410002c810f15604020001040e07030380c841c095500003407040040514140c1d2090119998401c04400304106090340a000c9010f8108440d002d01c0d50701411004150f6402010f400f402107901c1403c0e1b62145581d40c4040641701c000900c62000e000f000303050007400003844000c0d019840000ca04204c04012928224030612010841e079841d800303045501d9800d030261070050140e0700003005980070b00500103010045185060240320042c0010042440c80e5050754400051340c0c3d00c15110200e00707840ba41c2e6030a151172019210310007036502e40a0500d0204a81c2058010061500000e0440c01e52141580f0013110040140c2c0900b800f84410500000c02c2c25a000d0060b00010182503641548450130854503608480c80c1d040c00c0448035145c80b55a42043e40c000055070361205941c02e0000f030743c000a00744841907817004544a42e45a05501000c420070040e031020f1715103d070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879743758 1250 879742508 879742511
    0x6090e100c171b04060509030705271017210703050f0d110a02030a0212090a06110a021807020c01031e02090f06160201121401090509190506060103 65
    0x450310030010342151034040c003074000102d52218044400c0004082250480252050036141c500f40740d682d801d040e0020303081640000c41c0018441c03042e150400100c0c1c06080110344000800720b5955004010030b50400720028008000c10011700300e001d448004900410003841840c2e080045119110b45440700d0a0203036500880c1c59120354140e90b40d4100355090719038192201840d008061400d41c030079810594004003607a840c0c2d11150030102c601e101400191450b038000b5a190542000040c3c24622401134171402d8403001d0146a10503a9280400c0d82116414200306004020024455050150050f400303500709910291034070a000060746250b104070540e50a44d112003544100444c15100d40720720000c4072494141c1c1c10751140080f503008200c01d03000148a500760318604008507000c0d8002c4c507000e01e02c880915410030255600303e2050866401c400000300503152400e004c486542c0c406009000da59690b80001942c0d4280806c01c030248441040700c100b0003100c80c1d01c0c0a6968550480303030b050009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879745008 1250 879743758 879743773
    0x114040311060709030638030c0402090d082104032016030b06010e0909010902180c0703030c1b050705130605180403091a03160c0f11040f06090e 64
    0x59002c100c0ca8066005544c1e10b0110b640b540d00c511018042828003001e0316150014610310b4403e4035003116403d07920200014940619040400d42440c130706808c524000d0b03004008010469640d00d9030f07400f201e039210042c280c9030b512945820b41d10206d0020300c0c00c41d0f81041d00c1400145030b000003d6560070503c00700510144d0034a807494a4031010740c1540464900e900baa4240006014006040c0c2e21040600d064080c1c034102c00009071007090207982514159664001000960909480313103a094030544045240f1810010403003001445000760240070150796079414402184500d00340321310710103556115149801d86081258403154148103d80c400e00f00422051390302d240b1030041c84d0403a840101024520781c200451503250410041084082010980001c1000305c403c9001044d98a03498a00e9912071408510b0b800e00c10480c5031300d04c820301030f080310480005010304070102903459204040364817916501d4003140c090001060121003103070030035071f0100e0b4244c8503602c0428841542412aa0710 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879746258 1250 879745008 879745037
    0x3071707060e10030e010213120c0801140112051929010510110106080f06072c1c0819090b0406050322080409090b060a0806010909050304030501140403 67
    0x19051482c0c00c01da00100100c0708100002c0c041e03071000c000840400005403500100040812100401c3e800c9a054585d0501d0803a0a00c4000d2010401820383e01008205002d08200620402401480360b59184032030f514407030700ac000060004c401010035a0307540200090079803414042031100c518040c80c00c81040f00c520f9a2100001d52414102c0c0c2c005000c590b1015900c100480b20500c810041078844d64030b40c4800a5600c1c0208000044030f50400064205410b10b40001051003075000b08108840c040120140a03048084000111319041211040200482107d00c0e0034801410390010300b40c00070104400d210102c000c01500c00258840d0340302c04100e038136201d101e0004e000b070b4001e840006a0900018000e000404100740907802080144170162042d552400d00707642c050703001492020b0f15131078207a08000070007204a400100c11100310003028208031f070042d80c45e541440780300c0e2159180ca82c1c0b0814400103200312409103030044008d0000c07a003c01d10b40491003c003a1822400203c00c1f1002c0d022 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879747508 1250 879746258 879746267
    0x82b0c08280f2a0506010303200105011a0d0b0904080d060b0c1513060f06150e01020604080a0e0301020d05250c030e040f021305040e0f03090909030403020307170706 73
    0x40e81500d498820024555259940311850151080380d000c01c20f0307012080c0814070421002e40214402c2e501c3c0040c800204848221403580898085680c0e0304220052240006100c503a0b030740d00303005d0a880c64440320a500d486016181075072003e40c20804000c1031006018100c0300600c28148100f07018403905a0b2401070810701c5c8076000c0041900e4003c0c01601d006e00f070f004450780d5040200720800c103121281c5521120704950524508503a05961400700300308038440c0300d240301c80e1180103040c81c90080307003800e0003c1e4840000800090007010002003811605000d50035209a00001030021904c45ca1501c00341c03001824191070290100e040c2c0000c5000c0d4084405494861f40456a2103034070841c22541c0949004082c401400da00a44899058100c030304c0600c0030b40850324000300789007040e84c80d00d014001140c01d01c000c000d0300c4e0340101d0501c08801da0000300f101e0032220b00780e1b01c8c4225907568101c0541140520340000f0b40c14001c0c0c8a00180810440070000d082c0c004007000d0301c010940d107020942c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879748758 1250 879747508 879747527
    0x30606022107020906031e030d0c0e100305061315140d020d15021209060f010503070b1602040207080c060f060901360c050c07082b0c0828 61
    0x2007400700e003000a60014245210744580248010b0300316003190014410102c6480e0481400c0d80705a4030104020801722140d0103480081015410584506208500450a281c3c0c1034090709041c1500c40000c00d610780c0b160104640c0310b80304100100800d080c03000c0303078010140d41ea2081034042d03051455016403504c0c220b8200041143c0c018420400e00069a44583c11410007980003d40309034280040744004a003294507174440d841d098080c0505182c004407681c0ca064042e0401402a0b002c440180442007a050480c2c0644040c0503441c80700c0c40d002e10020b0b020717101d1000c0040011002044090031010009400790181c15000e60461540d950305042c8990080244240060b000d0800503500361000d032441395040e00d800c043d81201c06070b1401740140c0b007500c00560b00d5100042d00002c0c04401544188441c001900d5400044d08909036202d00321507658a5030704034084400c81840400701c4050103800007a81d010303849200c4945407002203a52035807200c9695000006540025840d40b203103485004500b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879750008 1250 879748758 879748813
    0x309030210031a060327031201091e0e1b031e060906070528121109130b030c060a02030418020901090815010603050606090d0807030e1903030c08091003060602 70
    0xa070015202003001082c903808441c041c191030b000c1040040e0002034008e2000780a0b1a024001068260a440404c0f14007248480d403030003241d14240da0305003000c1c3d02041203081c941c1e60541203842c200c2c142000a06014840780c4408803200101800480c034a0702240c0c481c0702c1c1c02008140c0704c0759501c1060664a51040d003000030405941c8c8001d542c1c0481018090052140780f43c6400600e100c08103200e40129414082c04500703000f03011400e10013918280750840e031540306a080920000881c1804256200751141c03d6274424140841c6060401e4406c1082da0000c03e40d1003038500e81340312070f03500d01d40003903000e8083d0a00007440801302042542002035031130744ea03071094080e0a4090b8a801d100301d004141c00303086181e00c081b04100d01d00195881c0c910b00418a8010b5007030960b521480d107070260995220130071303650050b180c0c1c0a40c00300600c0a82c10f070744100d03500340c00c0c5a51000090320b0b00b150303240300d400d0100c4d601c1032540f00018502c42e0706a104005070344907602240c3c0402e82d1b242d003102c5040d0101008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879751258 1250 879750008 879750031
    0x412051c020d05040b0310090e01050a110f030f0402040e1605011707120e0c0d0c0e160c080a1b0f0b0f06030318060705151605160209040309030210031a0603 69
    0x10070004081000465001d071a03070740e01c001c0d62038940d01131f02e003991275004910010369100c43c140a10030600f8490f400fa0b905a0180b0302d894030f11161500c2900380030050101c50f0f14600c08001600b5500c85411000400200e002503c40d514807141c03400e100f0810502610b800500d8103200d050b41030a00302c203120b01031000c3d0348403104880b00348180030028003058080704000d4043c0d14100441c9846100d0400c440c280708014100c00a410840c5403c03021b20001d00e10418520a4000c0e035a105030898803c9030341c01c1c1c02030640f50340d51250102c146d4400071840309151a012030081703038400380101d903d0440300082c4680070950058683c400c00060507032050700c0c02c1c2c0e81600104840a104c0201850110341c0b844060429820400700d0f071a107a00f49410340c00107200d000794010401a07041141c0746920b90781445c80c20b040c0e0a00389442d4804c1100c00080e2070090160540401007000e1502800b009402540c4c02044101060384000c070043c0500020740703603201c0320311100c0200d41107854401d050b01c1c030903150790030b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879752508 1250 879751258 879751267
    0x60b0f04050424080d18060e01080c04080613120e03060105010513090203091f0615050c1e0d0e0103140721060b09100e0a030602030703020412051c020d05 68
    0x3040000c2881e5083c0d998079032200fa070b0a0b900c00210340e40107001031085a000d801107401840c2d01800c40f400143c0d1a000c040c000440c184440c41d00725103071048001080ca000d4108d50381e0001c203a07013a40b107145c0098050b07105810400000c80283e01005519a218510255510070101f8003500d506541c080a258181c0100d4014002540703d40007411940044a516410881d9178154400c00c0760700c00e4800c580a5000080e036801c015102e624075407910300c01010208031213850900400310611843c4103400c20080c00141402c000001000360003000d056a180e203407080407002e189595101507004038980420508203848083e58003034840c615441800c00f084d07004075601c120342200c3d01d07805100ba081c02100c0764041054032100d648604005002c0504441ea07407074840b20200f00440400e901d68104000500040e02c82c142c845c400fa02040b070b0b40c0040301603100d8842050580c040c5c0100d402614480d03d41e081102c2c1481000200b000710324880400a0748030284048040303840f030400e03420304c0011520400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879753758 1250 879752508 879752519
    0x2030f07030c12050a06031a040b010b0d0e060a0b090c0a08150d0c0f050103110a0509010e030c1c060c020109031d0315180601170c06031905040f0303060b0f04 70
    0x40040c00d10700068a40340680e90210711502041381c02c19100802c0f502c0c0d4070710b01071042181266000f8034140e140c0150148526007555254504441402540766810380402c1c0d0b503001c86510f0700081a01c40000301a02c0c0720b0310382403254000908981d856241715000c20300202e44411800f50484280c4400303540e4001d0165030702a200c60703500c225801216000000d0448480c080b4482d086104043c01c150a0b50803d0340b40740c0700004054030707201c1c018004001410840c03c0c181542280403911030304ac007800c080080d400310100003400d0031044c1c1002a017140824001c5910000e904000c04c4404c4e1181104101c41042140100c0c00c07152031680c0100030592401e001c5a0106d02e0010040503d40010103c80b40c0c0342c025070012503100426a0140e4084040c00c128130000e020600005014184001c50500b000d01241143c540d01c00840185a008401c00804103440c245c030f241d00158160f0108000344050700340361908110451507448291f0000b450034002290000c0b01c0403ca9020000c280c440e0b07400e141c21318 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879755008 1250 879753758 879753761
    0xf020706031107020a0b0a0f0203090a050d050a06020d090204151d1008032a010b03120706020c0307030905011d092d0406020a0e090c0f1e0c01091502030f0703 70
    0x2d04030740c50b00560030701c00e0340016078a40d141742c0d01078080c0009060711100d01c6503020749802e410520400941d0818819a407090312801000c100302e40d4201c4000c0301c08019410110f00308200e8420161045000140360b01c4003022540044000d180b00703503420407501c071130000396540b000024001c0320719280110390394220071160a0b0400e070700f14203081140241a03554801d401c1c40c50f4009018a03400d04c02016040c0c403105209000030b281c041c0d010009100e082c480d02c00007a251600d00e02d50110b003103004a00041840020ba0594407101c21100880c3e40e00c8d9154200a018194188186400103100f503042a00700026900001c00c4290094404d5a640e281c2406004510001c030f0700c004200031000349808407000302d06132940c1c02140507010043e0f8070003c84038020030076045500d07894092075902e820700c481d6219007821242d0284420481c10b8907101026200c4071609200c0039502160314002c1803c812442040d44008080783c80342c2c2c00c3d4101e098881d00750005a010803591044a080c4910014640314000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879756258 1250 879755008 879755021
    0x12031207050c190303091419060e0c031f15060c020d08072306060301060e0402460611030702040b030709020403061e0b060711060d0f1505010f02070603 67
    0x20101591011040740860002c050780061003680020f8480c815042448407c410108100000b200070b0400c0e101d52170f070b4000c80352101c400b0085c00c090b51000d44440c00700d02031103a651601d03802000e032131250001ca0000782c181c1e540010140d034a40d01d0304452001040035089140c04540c016140d00e100c0301416000c1115420202e1f0090324426802c024110001e4800e00f2101d0301c0503907228222101082c50504903203007840041402e0700a81c034020301400390445e100d000b280c0c41503049608071249103d0031004200342c448010040e001c803046a10050102600c44e403c6000150a01c11415020b0341d01e0108680c0340a10003920741d9540c004101100141c2060f070480c808200e0301a0840c1d010741d03647c10710002281d1240c3d20694243d17594a01403190b1025100384802800c520031001d02c070f244498030005400f88268500280541b003244551007040d11440c0c2580c1000107100070401074066104d00301009000c6c1500c0c08403940240e800042001d6015403944103421b40d19a0060203c2c0d820404c2c158002c020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879757508 1250 879756258 879756277
    0x604110d06020c011d0303070207090e010902060c0a03120902060316110d020307020103060509070801120c0305060703061d04240209060403110102060a0b0303072a03030306051203120705 82
    0xd0001000003140d028001042c600b0420780000a4181c102da09010408450820450503500708100b4041c08a41c00203054083e5040c12000080f41c50b0f601c2403c40c014500d03030000075080380d40410441400f950100311a40814003d41722041b80c002d1402302c62044580e1a0300007540000140080340021409101143e492106424400300078980380e88a1403a100d40d51280750010b0b4000207002085580c1b601605000f480161a102581d050205d806040f590050003101c4031801c00815000520410754908001190880706441700380c18200c40088c003401080c01040c00003030751800b86111000307810f01100e2103107810040c0b001c12031a5040841c81c0303081c6a101c04241c002d4091052000d1940c0d400c00030f0000394819075130482503004000003e4103000006001907030140c074100b42c601154401000f00c0e105180e2184060603029000c020041b034200c403c1c02484044030080e8008010150150300c00d01c1500d004a0b980b00035950304a28256603072003204201c4910007030900103d103030300380104041c015440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879758758 1250 879757508 879757519
    0x80c10120f06170106032315070c0f08041a04080705120312100e07051e0901020106030c090f14010f0506031012110102011107050304090c1e0f030b0d0240022a060411 73
    0x1160f40341c1401c0800015023390f180d4000207000c00c9141c440c510311141000c03600e00c01504251030118025150312442c0300301170140c0000404e1044440d402c3c0101e500c1e01d9841c2c04c04618600344030542030f0004a49010340d400000c034072400f05070b0450140e41600e000c0e0741c400100340000d134107603d60809160882400300341507640b40d10b00800050040030001000e0403641c60300052041021481c0350650f4100d04014060303082c41da005000003000001d0364829200c0035078900d980c80d1a85402062034043c1da6100101014015880808220903910100000c2400741d00030b21944258a809001a00c606540101303554000c1000700440c1e0380d180c020241c0e42e000f50500a080100c3c100411034224009102d00300040c1c5110141e000e8035402d40f146106070241030b90720115041d1168046481c0348003240d0410310600701d204004046903080140d9124070407080c414061060000607800001e500a007030010b50303126008400c03040d14045541404081c1003e04024601511103880c2c02e0314031b400c400e22041c1c204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879760008 1250 879758758 879758777
    0x190501030f0f170c03030a0501060801030b0a020a050f0c1b03061003200414010305010507080403093309080c061602010c060f050f01080c10120f0617010603231507 72
    0x80014040114144e0065540e80c985010f042040307680c160015001d0001000c01440804d00c0c10700416844070341c02a0060341d5031104001604c09005060403060070080001d104a1690300100f032850320380e48040c81c00c00d00869071004040c3c640c44101e41c00700403503081d050100302040b907028929240035242090800140112008201903c2e0142c044c160b40c20147c000400401400344561984803040749050740003801d255030010251105441610324030b59440790340403004175075695400005024000c01c4104a0884440035002c2041c1d803080d0705072402081190300316400d00904480269060407040c6400031b44c2c5500556642000000c140da00f2035580c211040c103030412b403140d11300652060400390741661504150901c0c1c08040d4a0107402224441400c01209800103444959940c203860f000c07401001148140e0001c114a501000700018010324007072001d001944450b00f030324002c48810030b1404011445090f034030228a070344c0302140e00204415281064025040c1c0d000183d524124511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879761258 1250 879760008 879760043
    0x5070309032a0f03030e042d05180304380c0304030b060103020c0a03110a08070c060305060a080d08040311030a02011e0b0906061e12190501030f0f 65
    0x441c40b140721030549880201d20081c0d00c002ca51004440100b503001c4401d2041421941c0007001c085244407502e02603038890500940c3c00040c4450300c0d200d2050212070004c008034000c1d0301000341000f80c88420340303001c200c010a9080c00b4007204580c1910900c8045144070001542160300034402026500c1200c04041e0b000c1225a0300341c030041c0315000c0b11a0040d61124103600300550520009080720b4103151041206000e02100442c2c125081078041c10136040d40b90826140c5410080250801001010002440360400401c4144201680c545543c1004039641d800188903810b041d50064134a168803600501042610410055501c90f10034500b042d104108030b00e00c103103541c10003144240541d46903c8100d00012a21816400c0044225010710940790041d0204003116005440309005142c00102107030420031401d40d4035404080218400e6540f05a451240b8014006590b036060507607074085045584006030060301d05881e04a01800105c41c01c0760b03500540760013505008c440800b194552030f0b01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879762508 1250 879761258 879761273
    0x40e0a150b090f0f21030d0207030302030108010b010c0317070905040207151413032703030804050709090c0510031d0d0e03011505060304060608061303081503030a0507030903 77
    0xc0c01c40e85440340d16008104100715140001e5207049000d80b14008180c07519555117072154400c04104141184045400107659086211b49420030090340e00000c1c01100301a810740c001c5040700d50520081111751389000045464000001000d8005403031301040f002013045416207107030000b425040260100e0790b56004a002d9800480094031001c0b103010005c10f20101a001d808208442038020400d01d19098280c441c05000120014040003044000105c81c1d40001030300e0b0804001c01c81c030003003d5039079234039008000d42411501181c0c10f000d40321000442d55004e000300401e0691015039016014100028000d030b103540e41918804041d00c600b800d02c0e0216044194200150468020305511080071801070821842c8206250003689442c18100000da0900f0f4804103948089400366680d89640c244400a0041074104600900402050050003100c000001c861035200740c58803c042c4e0f50300b043d060382255101000342d805070810070181101c244070384002c015503407190030003070320080d00d0307840310b49 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879763758 1250 879762508 879762551
    0xe0a030f0f0c1a040b0f0c160809041121131e06061719080d020702060f0a0309060b1206060108090708010e010207140607050d02090a090905010c08150303040e0a 71
    0xa010f03903034040038402401560803003640d01c003891218040c0796040002005090b0310413401d00d88a491400d003c490100301d460703004c50b81c08490050003072210011140001050350300c042007144901906003500c540325000740c400988240c04811303400c29003c0d00d980f640c0c41004500c4501414007004413040c440004e0303040c404c80000d000c032515142c2204410b046001d1411411a01c0c030916101d82c207601c0c100003688141185d4034421031120160311000a031001c50f001c1d0003040301d010700110001ca9140a07250341984056022405080203010b03040c3d0b80d4007405200134105900e110150401030002d82154018002243c000c00100e0885400c5a52100c43c242199426100d4440c1039400141741c1e428042184082c800640c0f0b42d5000e400c0714100000003400c24418581042c2d1429000300f414100e5a81e82ca020f43d00801c05000309004a992624086008110907120071010a902ca00883d2402c20280e59842541d030002e401076161509000300c40c258814010803a0204a8031040075600d910b01444072503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879765008 1250 879763758 879763793
    0x3140f070210080907050a051e010513080303041101050304230c0a06030603140601240c02120a0204150807060302071110021501060314040f0c032003010e0a030f0f0c 73
    0x1020f0906013140c0b40c50801150b6400980315039400700c0248050340d03422456070301d001040c1c01d681b0241003a1030010381d814003c050201400d006800c10009500078080003e5115030700c6888075801c01d485240c01501c0d03070700060b81c0152810781044070f0a9559481304090701031407171200c0c0c2224561079203400060b04104007a008074001903268282003081002004000d80f22900c02c0c800b400156040202d40b4800c410044510303003c55103034005460600c0d0248030f2104404d900500400c84103031070f07002c1c4650f440842034800c82c000d03443d00c2e6501d000d00c001c460f50002500e902e20040d00d440381c90b0500840c041c0d00319840039200c1888a8100962680c2c40c03c0507144841c0d280c0d0080c0001c01c940e003181085042d01640260141402c203c0b296400c0c40284540540c41644030441c55001002070805020f00d40403504010881c2204500800060310080466404000220f009108514841400b580c403500000300040124081c00f110b40b416a0181490013840e15881c48c01502020203074941129421907204c41c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879766258 1250 879765008 879765017
    0xd330504060b07020f150c030a09080c0102160603240303261b0a031d0601180905060705210f0a1a0d151526070303140f070210 56
    0x4010905090045400400350b20903010708120050b004100b8082c950500e1a100c3d20013140c0d42c16081c100c14007540c0300201700004580e100c4004820180c040d10550144d035195214489004c8102d61000901190440035490304100c45490810700380c0182080c29000d450a980c1c54490714030000f05041d101000318040d913200c54004050650002d141c455280700035141c02d520000304440481461078590000303101e020551b5507420813a0040b4028840b404001060307031800300c01888912800255503050740c200004403883d411035800424211100d0300c40085c060b80003800021603650280c406800c030071001062884403142c81504450000070202c4621080c8984e1905000030541c50340300c2c00e10b43c0c1041d0380c40f45195a40040000b80004290013009000d00014010782c005520150082260a40410744030504a83c80b1150b16503407203c2804c81140c6085d055102280f01d0b2400140c202c21290991100c0f5520b0310201480816035110852030701481c45c00b0000f440058a406000302400c0c00c259a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879767508 1250 879766258 879766361
    0x315061805040221071a090303031303020c040204060e09040c051008010906050904050a110102030d090b1801060e0c0c2109090703050705090d02190303260c0d 70
    0x1013141440007000e01c2405a00b072080181246034002501c50241c690710601070503c844c02c46962a0310f40f00760210583c040c000401844601148e03250000f00c0c1b584282c00ba05d441038042d0701400100d00481c4258070010325a2485040a41000c6011a8200740107a54000c0c0349a10b6101103a0003220f100040d034001a100f400402419410748194409400c0443c2c50170603604150300c1c1d81da0340e40381030700d4080c1032560b07a0382040940313a000704216000390020800500c01c00c0784c2030600200d55002203c80d103030981c0040d140c1c210f140c8018270038601556150008a400b5442d14407030151203403c43c2911169501c54420307500500001600702c031a14015460340f5035641c89480c000d01040583c00b81c2490705250a02d030522140ba40c101c0306442600e182034400b02088103060000a41983700011410f0441796000c8020040c107600c125007015895290030f03003810a1fa5201c2e992142c908040b07c4080500b0303401d111000c101403582e0805000c401802c24284c1d2000b14562140070103035819074280344000104007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879768758 1250 879767508 879767513
    0x209060421020607120207290d0e060106020d0212030f070c080c030d020306040c080f070513050a0e041211030403290c0c0708011a0d15020a02010209040506030313031506180504 78
    0x1100c01f01070a45031000e240c00d45c40e201c10450651854070600346042801003030050180b1110362107101c0c807446100c00c540655035550380c0a9181c41c02182035500601825513044003500000048030300401c803281500c480d603a6405401c44040b192110f0444400b00204104e00310000300304090300c420030303120100603542c1c00c100f010841210201c83d02442403110f02c0041119000c400b400c03055001c1101e04003d6503444d0000040940c0701c0050300103d901010002c00800e2049480c42c41600c0385100f4249409900f082c0384e410b881a0200880201460307000700014000103078000c44140082920b06c1e0350513214420089840b014520444500c0504840800c0c01d0030741d140302304414801000340ba4000c02080141440d00e103500103019803681e000d120038860200811100031b0400780e075213204040071512041c0d102d07802400b0f980469103681c403541c1000003280d0700f03280c0841165400100c8101c002d03007192030b581c0d8a1041c010321800100c0c440b0399030700c00018240c0c49152070250b104000c0d8000501880c091 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879770008 1250 879768758 879768763
    0xd050d080115020a230c0a120201090f03081e04092a030e0c100905090a0605041103150906030115081f090203070e0a06050a08030d05010902090604210206071202 71
    0x2015441d08640c0003120341c1c00400d8469060180700d0680402c441c8600c84517845a5107400070002e0b09a421182040000800c0d040081d00e50950364401d0340da504c0c0c031550382c5003810031420300c134040900486002c0100700c0020305145c0c4184200182c5518181c1016511011042100c01410902d041946034420a42c003100019103c0303400c2e40c1060900b00006103600c40082d58818403200182c1c0245400c1d07403200c0e01d183c01080c1d0240203240040c0990000c0c40c000481c0c9000e0b1000348512130041d400d0144402070106a44240d0380f040a070203c0c1d00076070140003410041180d07000703440240c05541c2d844a40341a1409054000050510b00c030091030300c8198800b00ca0304032149070000a424914168040d401698046501e0b000c81b0141c2a5811264030b402800300c00409a40d40042d5200d54904000070340c10b50003000be410501c40c50307541003119aaa03488a00140c0c441c0c500000d0384408104028041200b00c07481030100c0190410964444200c41ea01081840d40302000907500552513058400b40142e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879771258 1250 879770008 879770039
    0x5091003021903020a090b041205101808030a0e031b0f0c0d03080604090204050106051b010614010f090b0d090317061f03140903030103171e0c010e0106030c0f05090103150207020d050d0801 83
    0x159034041101407194943307070b500702074589801861150008045500189150440303104000725205481e51240c5060210079840360144400b0300b180611b11405440c1c2d0808940c058800d480030380003100d80c20031941c0c100c90320000117142681c415503a1061001685803032103424060146d6454050303440034060621712501140b0a01c0000c0c80e810000180303d400d12a410150301a032081c2400f504140010030152000070580e00100c00c0050701207488000240c503608441100f03030081c0c0314104250041001e03089901c0b001c8030701d2034008022106403200320390043c2c10b485080d81700b49400980e50124001f154102d5400740c0301071000342e201000500c24440034808680c890400d051a02c0c1c6006452800c00138070700f02d0700e200c00150003000700781209500d101b0340068200c5030709080200210780e124a0a000d015980f40900c50740040400004506c3d420a480ca443c107030b94000604c2c0700ca042032050460082d40c404501240c0142d1030401c00c0c80041d82c204008040781d820360715103110543c140010021003401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879772508 1250 879771258 879771283
    0x10e01062c01080c090c07050f0c041b090b0f070807140c0303041d0406230103030306081f0c03090206041205280210050405060a05091003021903020a090b041205 71
    0x34079801008500400919040c0d000016118006250707100d9804c00102c1c0200d40c1c0c007824a02075290200081c080104101d45020300c11581000b050f02c4e51b40012101a047d6504500407940e062010b1200c40032000281041702210900140b808c0c28643c0d034000d0035000a1310480d4220044020030841c00d00500c4861048601a0011404c0a180910b03541c1e03594820b08041c80741c4031400d0b000c03409009650304266800c454101da808015807001050080c0c1900c00d201c241c0020386481c00120703c021010820484d80d03090a40f0341e2506001683c0000001c113064465801415500c525900040c0c0b2140301400c001d001002a146a0046504200d4240700c9001c2404030850060310250b4a041000800030403401d4050300d4900c01024005800d588900c500d8100e03941c05139001c180700e6802d0340d016004090b400001e540000f10901c443c1d200b03a0581c01201810b04003215050b0301548260b01c29400340a80c41480d11313008211035516180103000e0340c010b401520340815074a4948051190410a580305901c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879773758 1250 879772508 879772589
    0x50a054b060a0b1309110d0e1b03010b0303040b1c11040303030501080a0f06020306010c0b1006020f121225050304260306010f03110307080f070903030906080603010e0106 75
    0x1002441540c8040d41c45c0688034000c0d03a642440305108007540b007903d405500b000b40804c0b0103080c16840316a01c01d001c4034514540710b564541d9001c942018007070600305100190003141000e00740001c02003d0b40100e80700860318440c04140c910600001d006e81c0035104400000159142e086050040c01d0b194140c00140c03c1c5d41c0311010600014950002203200e86800807030050716901e400c40100c0750004030b02c1000c1c0c2400510024402c5110203e50708a08407443d9400320303003400042d80300f056110790191014110303070001808007005140d00c100c0d0302c95100200c07846480e20348180d113508800404140492000054001c41008100288000d62000d108003024403040ca1051889800c24644001003109040100204203c801c1600980140040031134094084c0d031a880d090324002c00d054811901031055800d01000714119902a41c484400d40342c00d43d03190000103007805810354411801520301c5800d5907a03027119070040c2100784180400f03000f010200140c4041c1e40c500051058240508810800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879775008 1250 879773758 879773767
    0xf040b0906090c01050702040b0a03030306051e0306070e15030403170606031303031104090908071110091509080a0b012c0f0703020f0307030f050a054b060a0b 70
    0x100002050100f4500074640b25540d1013881c40480e020380141d10b48903400108003c000700407d40c1507080001600e40540d0340ca080c1044d041c8944541a45030f0a015800d50816000704220b2442011403045503400501803403007080d49060417400380e62049a095000518003a98085007100b01e000158100704200e405030300794104504410030200541100a0606a9900441c80a9500307031042d540208060842002081d03c00c3c03c2030503207903000b80c400300c84920304981e121030315150070016025100c41c1a41c0b84242c2c40c0c1401c00c8014503904004080d400c2c03000220b80019200c404000250301140b00d03d0411182e545007490303408020001c1c00c3d01c081c0ca5000d141c180b000e09080048120344c40110503100300116100c03620150028410300380351241c0c0b04000410002015010380025081010140080056030b4440140e00125071050390425102803662110102000e41c0544411050105050790300d042005264040c03048501c40d01195007551a80302005420318105125100030000135400c103150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879776258 1250 879775008 879775021
    0x4140103081c060f09020c0c0a0e010b090109091e1a0312030a09020604080f100501030b070c0201020f03210c0301270207081303260415030f050f040b0906 68
    0x2030b4091285040121051440c05082850054002c035008101c0307140d24100c3c841d20386216001035030180203540c200b44a40044840390b03040c0514200c044940c0080c20405507403e00c2c042c280c0c107034040c140b40c42c1085004035010415616a10408010024003043d08007100e03130080c00302c0300760340100506883c005003802510300503450101d10743c625880043c12880e039941d0780148901c001d049000c0e029400007408140414080c00000780e14120030880800c4840044042c0c82d04829107c0901004007600c1a07407011880040c000e0081c01810b0744140141c82c1c100714a14012442d5400640c132603003072000428811400c3c204c210481540003015025014555818030103011106a005040c040c00c1c00e60150489000c0001a8180c0300c1ca1135101040940e20b04821741d6401c403083c13040c08141d900d607a01000100550450040010075500d120f0030b56810b1a160420141c64484440790403414580c4540204020582c036104d018070400c2210410006403d1909041543c04401004101182d002c1ca040c03101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879777508 1250 879776258 879776273
    0x231e1c08090d0618080408060c1e0307020c0d060203070f0309022103070b190506010507031710080f030406180303230c0f010912031401090b0f180604140103 69
    0x20100d05960a9040b50a6071a0403401407651000010001c1051040b40c4204103122000344225009101180d074642c55840c403036600b502c02c03140d40d0704060642002c00c0000114110207150b015045005840324000b810001c141d002c8801001142c500d83c2c00000c01003e65001211008a030f0840c1c17078100001d110907408659640d14902104040700c0c1c2c40841c1c18a1f440082044501d01c0781e02088042d0641084600501d11400350400c01e4095410480011203652144066580702e81e010703510f0b09400205404128008030f40030f03001d10030351412844080745081c001c001e003109107080c41004558039403812000401c00200c03403100304100c0d9402081000802e9124002d4a440903128800e000c4245000140c203007035102e910140c0c00e00e4055400d00c0d0045038410351283c00c81c1da001d85454014605081030480455103080c9000169030454001400003140a6008000448000d40101c800c0c0c00403000180354004d00b68040906445404204440707802e0a0143d40b1100e0071015540002d5410f541d41d246 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879778758 1250 879777508 879777517
    0xd020304120605040c0305030c0f010b01110d080907080a240e1011072a08010c021207060609110304060612080d0b01020c15070b090313231e1c08 64
    0x405070380e141e00100b070600c176160190500556002c030840356104200700d01540c85007170f40480301070503510f1318410301403e50040c600d2250140518028040380160b11000b55150600900654140d22a202d03022030096810005d2081081c001d82000140004004080007413918030409149024141100300350710316800120341c1c0500b034144038003244607030590ba2445902e000e001c10280001c2400100c60800e800c0d01106562501444105405030684075034104d030907600743c002c03c1030041c2e000d111200995004580030706440ea00c20280071a00c03a68410380d84081e20a146614a520031002051104100c4140304400003400c41082250100500382c4400015014998003909032580385c03040d0303040c0307a8400d000340880b00b0002049000100c0803201c40000b03507000030100300d900303d4a83c0042145118004203417152000d04950304652035040c10982d0816440c1e09a00010b20603504001c450617546000c0e02114904200c50314400c1c0da2030740820411070f0359450071250000345501483c1c40104e084d14040701e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879780008 1250 879778758 879778763
    0x1802070c05040b060a1b08040e070210050402061b12030103050c09010807030c0e13020306010b21090727021204060b040c301404060e160501140409020a020d020d02030412 75
    0x808405d4007141b141e80120f0400c0043c801a000200410715070317406044180180c4041c1d007211300116400e1000780460b80161006584403030103101c81340251507180900701401c07240c4800d440702500590f20000180d0801c0c1c00444040d0031540020810b8280b80310740030b00600c0e641e80104800c42c6191159040f0404900460590840801c0001c40300160410704006483c0c1c0902203d20300d603900c010b04107850f0080340e17107207000500405641886920800500380640b14510240c01283c2c60190780c1400411b100e0b440d0034059055000d10800781c552840a0304074054160110000c2d8a450301d8071404407031034484030604c150f20f072030060002c80354010b404044a940113039950306224920800215101030303c1500d84a21414030007040d1005100703000f030034010341c800d80d41030102c10301c5403034220380301d501000c07990702d120b0000b8204100030361144503110401d800c121802e5103801d03100c3d81103600b603910803200b0101591110f00891801c607410449000030010501c0550300301030406250516200c0c008501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879781258 1250 879780008 879780017
    0x30309031112150a05060402070b060f0d12230a05030a1a03070803120903031b030a09060903051b070501020d120e0601030f1101032a02071802070c05040b060a 70
    0x8810349034498859516540d15180c2c111100d20005090300000c520b02110341051032030500c000300c5d02c181441e000740d80c88250b209a807e80f059403200c0a02044444c06124194080365a0401402040c60203442001810f5150348160f083c00c455a8580840c0d026400e0404130b2031800c0000c0200d46070300100780e80e009101040e01203144141c482e081112001175200141d4035000d200000168480004010f01e0900c1312100c1d1003107150f44d10440b141e20380c002280c12000e11020984180019002c00004590204200c0320007e05100e080e103440040310b80c5640102c010a0380050349414404100340c500c01c1d40401c01000385202414000000d403180d03000c840f00d07000d1001e2041d171400c105c40d207034003d10051400b00d0f080b0307030351903030749051800503454a91010b4035181d1010b04180040c0d4428041c3c500c5200044081d0742c1000e00320802d17610303c52440c40030882140141400031401080803c1003030920600d203035000d40c49090908180c12042c0480c0d10482c81203181954582c210303159001a641a070f81d90b401c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879782508 1250 879781258 879781283
    0xa03061e0516091e150504080c0d03051e0f070812090105060f010c05071e0626010614120708100503010911060a11100911031f0203190e03040905070903030903 70
    0xc401c09124620303007105250046855616020351b600901500c100c0703c0003411921440c1b170340c80501210140358070000d40010410080035001d400d2240d144040d00312400344039480e103600c0341504929500040401c544802c000502e6072100c50610700200e40111f0014001c11290502a00003444410320300015030500507082008014082c09001ca039005152580035518801c1d05002164103904150044002103584400d40e101c18518034422003c2d03c01440035401a140d08184050761040d01d1414a40d443d1031042100914802c0480340711070092400340c17a004010b0802c140b230403a00150ba90402c5019a151100b10800306044240786600840c0940c1c0556881300c4034101190015101811940240b10744040c004404056510050340d007805200c2c029016040c1c102015200d10707600440c0030100b8001000080d030300d583c9a0007141c110907282c0c1700a04000048264105440003128a41c2c0f850304040f50030012407043e401007036801503e5280c0485402c0c11a58050003a056034040509040301100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879783758 1250 879782508 879782549
    0x60f030607230304050a0c0b03090d08060402040305150f090118080d06051f020d0f0e1005040f0906090e06010e0711011812230909060a03061e051609 66
    0x502d02c0e0340780b80071804030720782d24982801c00c45e50700d981005044640e00200c59000600040b00c80c1503902400044015042c420f055260403103c1207000742019a005a08201c000000b0340c003089802c0141034206074040480c81c00ea0310720b0011345030007804281164101011261105580803e4601c01540440001d441d440940f03100c81c020310181e08800d07040124845034850207030311400e000000c41926400c80b00007040f4110200e0b02207201900101c045680001942410f10b40903c0480ba48111898901c2c201950ac0100039162201c0781d21020415aa90105004064403030184c481007104000007800d00d9454042803011800000f000101002010361010303102c8007003900400043c118540080e402c10701c850400e01541c28266503207034040f034104595980740c000b0424441400410800c0100d0400101800b030001f02180241140d078401e01e0080d011001500030b00c58103074800203081040c40300c00c568110040440e034002d800d080b0001090000000c51a81c0305054005940c040804068040c1004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879785008 1250 879783758 879783797
    0x120706020c06010b180f010e101e03020703020c0316060516020a030303021804141b0c070807061b0c05060705031204060f0b0d0c0312110d09030308060f030607 70
    0x1090507555030300620000041c1540304201812090900c0c12044e5140c400280401a180c00c0c0c591406021a6203119031a00d80d2130300800c020416501414841081861400070101c0007065070149804607901180c50001e0540c100940300c1004000e80042c240380440801c05554010f072442448108000000c00e030600c075102026180d483c59014007031035034098607440c0c050080c0d00311086c0b0a00441c205507515407035180074040c4800d052038800550034141c403a604460481c44c45407640c440303650010403000f8890141007102500810380807020345206030901e6001091160448200f0600d04440500000820780030303000d003401c85030304231981d695584481c5883c50442c000c0700b1020005401031003c101c00c0c041c81c0e42000e0052010f61404020019500f0100001e00c2d07002240901b80764071040040c0001800b8425140c0c400d04142401940e030b1032070510301c2d0702d81866440305c04001030a40b0003c00800d81c001c40f0054000d282100c04c03444200000b03020070f0b9070b40b100800c4141000101c0c000000b20001c803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879786258 1250 879785008 879785017
    0x8090309190f08010501092702360708070206010f14010e030a060e16080c0d03020c03030a0302122203031130070206060306130305040b040312030501080c0312070602 73
    0x1054078480255030b0f2a81e006009050034400d54181900b0a41070340d14911341c40c030b007003071034144039280395040243d4607002d103c40038501d909501c59030b4602c1003a00b1000900400d80c041e001211620240f010300e041c82c0d00030701082024004206640c400350050101c81c19004d60f090580d10b450552101e021605401241e01700c00340702c041da405000f541c0182040c40069040241d0121484080302c1400a510303100102607151841140c0090f080007800010313034504800110b04250107441259200030607000001d044d030b84a1400400843d50010f80c40412030f00c880d002681c0308000412030080301d600c12541001404100c0303001400c06958101c8001403074440015180261150034150b80301c84101c1041540e0b032000c2c00c1e400c070713201090383c80011503807407000481031700c01d00300900a820282c48038044400d080d1410b4804030140030f01444003180000492014000541c021904078801c04030280c00a402c490040c0c200c95010f411165940c00203840008044100b0036601c8603c56031000d69081000c0203004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879787508 1250 879786258 879786269
    0x80f0c1023190c1103060c0706050a0605031f270f030909050709170601240c02090c1b070501270b160c0b03041101050d1d070f060809030919 62
    0x1040d92902d4050750041c00040420300c2540c00c907a1141440d410182e840504441828034030310204210000103505030012074014007080d0000c82c1d0a602c940000341400d22000388500300c1d96111003030b00360200990151481064120f41609007110307510304144120b07500504040c081030002d0401100301841009504014a4804000c11840c200782c5002081101c003032084500801210700340c002c1c0c407840410514100c90348a08001140d8100a0768000b6240c107264560303062012a02410015850b031451980c401c00000002c6940d542108100019201c0c55120248490b80051421f00c001d9170490302d010842c400102c030000c05681c24414500081d2499008580111340106041548040044000c200c49100e01e581c05181c0da00c80c401040c20f03001c1114007401c070042d0444201625401000285100d82c1d40440c003051340313540c103522600304501c3ca0b20301b00c50541c0500304c10840f403001000248064130312450401e10504104840b5940c80c02610301c0c1c14494800c1480e00c420101e41410624010304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879788758 1250 879787508 879787537
    0x2d0305060f0d0b100602030310031118100e010e040308040303270f110d080a05030a0b0607050c04050601260c071a060906010f05072406080f0c1023 65
    0x24843c0303400c030848403082c4d84050189503101c001052190021054a210341e600c0601440d52501c1c5032503e4a140e041401400c1d04141c07000c1035080b00840c1e4850a0303210349110b000a0390441e16007104852400016441a500030304400144400240d00c4001c0d40d030040d82514000ca42007030b140240d210340c50100c400c0e070707601c00c0c4002c01c00804000070b00c1070140043d400390b5252402d0b110914240085000b28610041013a0410000c9400c11401a0007454001c0c142d650005000d407100004501d080d4002802560140e0156281c0004d038602402020b911907028a00611140744180211010408102042c0c540c0814030b070000d001580c2c0d010503149401d81002c04001d0404ae0500000c0e0020816146035028042881c00900303154010100003003e100c0302d60b181c628040b5192a480c080114090f250528031103010310040d00c0301d07031901a0f0b9000c0c04038100070b807040d4542c91241a1408802c14805400781c00400078090031a9004200417030750311514013205074084a02041001644200e500200398103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879790008 1250 879788758 879788779
    0x50708181212090d0c03020a0b07020c04240f14040e0c06032d06090406050a060302040f0e010f05010506030402100516060c110106180b030106170d2d0305060f 70
    0x580030180b00d14001d0540c0c8051300e245000440040b03403461410100980541d01101c0d20200040c84c01e802264015050301c15940d032888003600240c10303200ea0140400301c0d54520003440c1444c114890740000145014403500042a04d05241c44124107102e01d2031510a50361040840b04411301845072440c1c0c42402031920345d40b80b9003600ca100840d4a41c484075410511318018010b841b1202c04405401084010145511542c40d90b03103090103440000c007001d40c1c07030340c440f01c00000580b120b000d00000000305020100300d510122507824219500b000c0758064840c00c00004001c0c50311202c044a40098040e07c0064400c2d600400c25140d510440b0714840d03889026000c5e034001d01c004e070350090a00911998501e0b41c0007000f03140003401d032039490040d502032a4403102c01c00c41c41e18990740a0f45007490098004a0466942c01401e41e1020964480c4215508009034407100284d0000d0791540c21021010b2500f072420210061000c0302501d600890b05041d40d401c0460314640e41c0015407080090001d2002c0c420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879791258 1250 879790008 879790027
    0x6091403241801020a2001090b0405062a091c080403050313090b030d1b05030304081201060f0c030e041404120e04020430080c160501030507081812 65
    0x2420488440c900004403102c100402c00d018000c540790707030710b00384d0300c0b24904200212901c1411101d40564034540d03680f00349200010f01001240351045010364080c1420b071802c003e00110351203505804a40d03010350080f414a070212441e00741d91510209480e02c3c0c18540304414408201c151900002d080080003040001c1045070000082207403403001205021b00070303030303038810b0005488a13016160380c16002012100b00a92003604603221341c044421002c10503401980303070b10f0708552007500c4c02c1d6050400001d14106000c140c1c80c1d40c80c01082240781c40c0030007910310345005104080c6000001c08006014a00ea425646c542c0c0000c03007070702d11861240559007001d00d41070320360159070340018010072a16100165649024803c5c1c0c7d08030350302d500e40c100d0131940c01c0014100034280000340f0444101c441084002081028001d800541c1000d0000c02611b290700e0f1004005030340e640d000da81010b0800c0704005641ea405a4643d4100c1c0300501004074055540046d00c0c127010840d019580d01d45804140f514a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879792508 1250 879791258 879791323
    0x30070501090201090b090f0f0105301510030c02010b1e030c1e060f2802070906030809010c03030603080d09020405061e120f0d08090d020706091403 65
    0x240c1c1d51003604c901c98580e031755801040c0a809203d10841e80001d12000c020f1040c1083c00d03041a40c0310b01450403d207030401c01e03a12810002480002c0004548003000341c0a080602c0c0c56100350001e416055182c0100b140d5000284014814966070080603100c95095103168002d4000256068000308040003419640000701d541d45165040e80b0f01c82c1c0f152065038105410280f20300000400c0e402e5130340d000c41d03030610240314003a807100ca40001a1f1104000044100480d40703005004440c9290340c04108000883d0000d150608641102180c14580941000026121800c442c031041082c01c1c40022902c15003826802898a41d2019007000c000003007101c0c0a004c4c3d0303441040c01781d20850f401c001d903032100014040d050361300541070b10b100d00154017140c0d120300d0040507200919011030708071100052980501e03401c0000e078884550114800c007082c003290010900c10000d05151520040030132500d40b40e00104001030300d100341d540f4038000800c00310f0962400d10001c50f440c14800c000e4500e00032241d00514 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879793758 1250 879792508 879792521
    0x309020f09040b221e150605060415051b030c060c0306010503040b0402060c06010b030a200a0c020d06150911092202120f07030b06041202091e090d090f05010230070501 74
    0x450101100201c1c90000740184600c8041e650041d102d141803cbc01d000c00903500065004422060000070311549210301401034054400c0c070001c2c0040c6480c1c002c005043c0d4035010740502400036240040c0100440c5076030003c00d0b268004d4224400052503202d50022808522401c5070007a080d00526002103140100440194051980030b4030801c01000300345440c0d01d800c90006000007036090100198039a01d0301c81c8151506890004115050198155070703031100700c07103001002a082102e0300c0001c0201e0301c0144198542044903c1045103440c120b400028640341c8465000c410700391400d814503507a0302c8980c0c192030907401ca071030220a0300d0070840804d16584100316038240001c0c0c2007009800450800c0001e44003110410f0b04800e0451256501b0441e4007000244103103481140da4640c91f4000e0074030b185540c0140d500f41c1c06405080c6030f00c40000e11080d2603030401e031400c5071405020401d41e60300003085c04940e095464544400800b82c5074841810492132040d032000c090201d003200c00d0010650020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879795008 1250 879793758 879793763
    0x21206041a06120f01050106080c040302281e0302014d0109050c03060a1b03020d0908040626101e050d030203040e01080c0a03020105070303060807060309020f09040b221e 75
    0x1400b4540e242c0ae00f48125102e05d000c0250003494200a03518007902c41e0380181681c0c80e400502428182c0c41d81d80300d41c0d014103c000c115070040d0511a0800655170040040100142102c400702a9800e01c2e4081030030702d1104c1c0300d41408481c100da14038200b0190b2424a00e00d115403000c004c2c01120401c3c10708039603a1050010851080c01408042042c84003030b80300ea080c942d02103444200d50f4002003403081e002900700882c0f120303841d9100ca0b03c10380000c602400a2029094980743c00e4810307501e1000200004940005070514001400240602c25100310b440e1001c80d07000c4410b080109a049003070071002c1c1c401e54002504040502c01c0d1400301030b004000350082e0b07030945036243d425030707030390742c0000ea50712a01481c00360000c1881c201031026512560040882501074140030a4040d6079001c0f207450031a055201d9000241e07070b001180110703d02548011030142c021200960755042644070140901c0010704020364840d4000d03504500014a68030b4060215004203403a00d40201c0c1e01e00309000300400407000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879796258 1250 879795008 879795017
    0x40f06030b0a2a090807170d0c020901090c031103070f021902010e06031e010608010602010e241305030a0503043302030a0f02070c03021206041a06120f01050106 71
    0x7a48420544111180e004655418000501c3c0d0003050b04000c00c0010805410000580c001150500d070410014008005d00700c6040b00300d0355207100103420000c8401c800d03420080b2848002c009a61420f44403419203061400005907810301a01c01d6004003090b04030040c0160004c8100034120b6001070046206a15a80030340e40c500c107107210741039141c0102080c002e020038010180d0004c20308010003d180d00030904c480115405498050859421b90240e2100c0300141003c0014400c0c50381c20700640494921040042010a181c240b0111028007411b022000c20100c070300c002048201d80d626a024210341200a4a96484039440001d2044d0f0044406813182c03442c04c000344c104d03290503002074000040041510060040a080c0d01030203036001a29010550b52603010070f003e4444240300814499124100c280b034003614510503c181e60b418048041003581181e01004003184840450120060b01c50104900540c2c2c1e2200041e9003c3e080c07480060544118003181d910b0000540c0594141d50540d1103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879797508 1250 879796258 879796261
    0x9050601090e0f0c0307050c0f060912040b090d03090f0e07030510050609010806060918250804030e04021326060c0a08270d030b010507200f040f06030b 67
    0x1e003200b04550a031040c899050f0010001280030041602454100083d8a06580740141034068145005001500c622544c2c10a01c02d22502550420000b068040f42c8070780075007000e190a415000c180515030606014400500e5a042090702c204049006031000601101e01e094940d040c6003505e00049851101003890f0802055041494951032070885100415583c83c00c00b084004540807a0064862600a00240b0015070030359141614512400340d901400d03101458540c82c0c803404156141c2d0b0001d201d43c10034200400c40b6501c1007020b41d00941500380800b2044c0e4200c0440c000344114108106461050b1001050041105140c080c242c60030400d0a40d10400440340c4549072803040e00d8882441c07030308102c120b050602035100a540500c400c8000418189030f6000c0540c0c0c8102501004115001016040426170701440344480c0e5030005c1c42c015052440aa40e45065070f9004100c40c080245043c0c9000c80d203640340310001900748400780003804103130142000d0101401c0c4030302089821510240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879798758 1250 879797508 879797519
    0xe13021f0e1905010c0c0302120d03050a0b0108040803041a010b04140102122a07031101080f040f02120316110f0d1505040c0b03070e09090c01082e0905060109 70
    0x1a80c0003110200d0b820720501d494500707030042d150301030401822110b40c01c00042c0000582d40300d0003411003050303240000e003440f1244400020304030b910041c814040d00e481c0010b070f02c02d0780e41c0c40303da140d511507481880169207884034244154201070214034580c0100008001040e00750000c005081110704003060000800c030180016070700e6903408445601404000d1281070b404e0303844540601001c2d105001d41024030100c07600f400d410400780d030300141d4847c3e20481d446540d95030b11810031540b00b0030340315600c1000d00f0300e5502c0d001c1480030f26101074419884c01207541711518083c012034000e907001c1b1800440920003460702c100840f0007070402c14826900618081420309060300c0389082c413581300c0c00f052500f80c0041c0307441008240203070054501d001c603d0404655601058000c43c018039040d1164605420b80c1c40c200001540028092403203500f04660a20003079801051840e0890320401c03280f800703030004a6615441402000f43c00a88050380080055100000da204900444007a6100c0c0100d54550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879800008 1250 879798758 879798769
    0x70b04030905101d0f01120515121207030804111002070501090911190e0d0f060b01051801030b12030d06091401050d060c021f02121f0e13021f0e 64
    0x11020104c84864141c007040a04c0e080c60000d03a0749405040031818a41c41c01044400c4a108907104044c141c0e449136520803514103480390aa1051030794004043c80c0c04040e40f880d04071b001d1a003004091084c042c01060030000000c8a2840e6208040c2210700052803401c402940c030266840748074003042041c407020410b0035445c010001428400c4040790719080d0611746540381e56140340203040801411601c1004103640302ca01681d44503004815003030b441c20950420b40304982c1c2500c0560b040c00010864905106080808a00d612209007000101c000000000c208104054914202940000181c0030801189540300300e050b5001410304010941d408500b2181d080e00a00400d64000da100300039600041094004206504503481aa8080306514000440403405000b40c3c10740301d9004140e6811142640d10081e52151003845804000780751072071702d011000081c0c0542c6954540c4040003d03600f500d03101d00c462482d50f001e000503101c0b210b1480202005000002e40400240365034508800c0751420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879801258 1250 879800008 879800027
    0x80c03130312060914090f010212190e010f0905071a0412060b04090819020a0209150301060b0c030403020901240f030b040c0504140109030503040614070b0403090510 73
    0x560404902051540307040e54038103105080000a2030b00e4010215450300240621040c4050716000145141800c01c0454140440b80103100e81c103a00c10710030b204010140b08a015081140390740000c5a068203122485d0291000c070084e040e45600300840d40002406544c40300d08054041c43c19541415114482c1883d00c84040b11040d070b1740f02003840b05022030310704100041d174024441e400c00100240550003003410f0b1510084103464214010442450080034120f80305407142c401d202030003214100341d00044c0012000f40c901e1200c2c0342c40102007519a1003d501c41d001130040d9010040c1c54488c1000265a01d5002c1d000c128005c0d4a041b00000e41100780d403605142c2203440156004800004400c11902c070201c0c0c8040c4010180c0b2089409500e4aa510132103a01c4c5050350f484607a110704151400c1c0b40e80310600714180c1045034034402000410f0f404419070b0207841d01071518441848105e81520310034054208094030407007280c0c091100709500201d4007812128103607000101881900b07415165203d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879802508 1250 879801258 879801271
    0xd0905040b0d0803011401020f0d050406030609051902090f040f020c010b220f09020d0c2d03060e031308010e10050f0612191103060117300a03020307080c03 69
    0x2013400144217840001c0c0325000001c1062048404640c4410011440c0902c138018040100d034000805001090385809040040e101c1003000b031000d03090000503424003940b501d01c40f031481f9030301207241714041d9507408090b000400010410300410712746008880003503105860b881d0182d1320f8035924104174201182c94580f0035003a980c00c0c62510613500ea0b0309001c2d0441c5000e004116a54140d80b0340103a030f500702071142c600d005014171003109060107041000d6150846095252000c244c031207500442000c007269040d00d07840344010404604600d2158514020054954151440c40c10041041d010540c08100802c080d0b400311618024100030140031a030b010348100c0686802100050307103c1c14000509481940345200701d034428480032010180e80150314404448580c4140d141014502d01080300301d01509880c0507074691560b20180c1907541d20350011001154004c60351a80c107100d1140c1e0a00740b012064082890ba0304c0c2d4001c10b0003070003988211030b07405c0420170b410f001c6003080200c141a07d11940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879803758 1250 879802508 879802523
    0x6080d03050c0711031009060504050706110309060c03040f18050f07050d200315010e060903150c040803040f0603050f16050912071212021513050f0d0905040b0d 71
    0x22640c803100505004d8043c0c250709840351418210201585226135480309000e400d00080c54189450030038100340b044d9211100b00005011140040d110110480d1042c00040f01c8540c4c0d10840b40c45010b0450050380c0c402124855008000103032055030468080800c0642d510070012a43d411042e40c0e030402e020703038090740091410f203e2001118099800450059004008100064150241140103910485801b0071845184031501540e5801c40c00c11465410110703001806c00c3d10781d80100741d40b251210103000c0992764040114003501c40c0001150003070100d03041540e41e03071a10780c019000200d6841c4190b0300060f00d071000041c10044c024118900500c4080111515000e40460440362500b0110000394004550324260103103a8042051200418980404054001c02400c0111402404150800c150340100b054000c01080040300d1710360085022090740702d40000d508295141071010b01c0f08100324460300d500500c22540081c0c1c848d084030011641801031a0904041c0054020020300040222 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879805008 1250 879803758 879803767
    0x20c0303060103020a11010c030e0f0309060708030709030c090c08131a0a06050d0507050a0617070f11150a0b01050c06040f0303021201030f1509020916021006080106080d03050c 78
    0xd61081c0c0090981005c0ca10b0083da581140722411821204054491008259120000290342070f083c0540000b1480b400040c1d810a00b520001c2075a92140d060300614074100080000c00f424011f85031200a1500922050485600d90100a0013440e140c00100003140840e000501c1e101016400308020350382c41202c0300c102c0c0010000c010302c0744501500e40302d070103134907110081103a480f4401c910500038003c070014402540351409000f00104183c00100070008c890542011904c5009511034100c40945001208007650080444041c650000030200c1070250440070001c0e4004018401c0c000c01700050100100403c0c0743c0159150301c117825080d405c135008000002d011400181c1e684800c98040e08001d4940042403c2d04484440d0036001240c85005588915042c007248980120740254001700410500100d50001416000c009040d24810383c0c04200380900b85100703008100c00c41382021018000d1903101d0510902070a41070080f800d02c4d00c500540e006d003551080c0120f50040350241e440c1e078500f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879806258 1250 879805008 879805021
    0x28170105060d15092a0509011217030901110f0306010f050c0a201c050610050901052215140621070507080a03090311070b0d0b01090504090b19020c0303 67
    0xf0b03107150070302175420407526809600310841051100403d0340d000f1a200d80614248402c00c030f650719040e0000752220365100c00c200d000540804c1d00d070201c1d03410742c031256880c0d03076400040d6805040e203c40c0d070300c0209030082106654100444040c44c0110002d0321104001d88403044101c03818041c03a00444100d51100f480300010507610101e0312070030040d46410540c1d914400b004503010220302c00c04044001c506010082c140803080c01440c1d00005041ca1a09041c3d10f042d0002d81048018003481303100e0610035102030480c126069516800b5a1281d9040c4004460140b004400801c1071081c0c041d015142617010410b8a89003040390300c801d10201c181c10107a444a008411072920060011007440401c00148002c03449082c0604800c030034a5a0125541a46180042401c43d20640076500340e882010709111100c1c0d000191101007411490024510000400495001c1d003264480b6401910381011801804440228680705885111581c0390040001c0840812407148040811030340e081400810071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879807508 1250 879806258 879806261
    0x314011109010e24190315031103100e060601020d030b10030509030c010510091b0c0b0601090f150e01171f03060f05040c0506070203030928170105060d15 68
    0x510401c06007244d8525103100c2c0100c102c0004011042041090100300e80c0d004401da08010ba08502c010b28003800b000141c106440c0d07407040c40f030100812031200d200701c04100340c80c10064004035014900c82400326421664205032106000d030b5816006008100c28101100d00038001c07104c0c0040007030312200c520241040218010480a824500f450004204520074500d003401040d0148540d40b060224051030b094800040b16102950034201d1001042c81404950708038a915083e240c001400e15019981c800040381c8501d00c2c1d40120080c1d4921a00209400e4104844c0d01a095942e4480018400c001e000658800100820b08202d25038210001a0701042000764440c0001e1000c2d102200309032650340b004107845100b180e24048568480411051010007180c0c1401444142c500a191113043d80120b5102c0c171860300c1460150581521410400f00396801c090a000740c4846680d40310781d141d20802050403c1e4038200080d960a250100f66180750282c2e510f003026900c900345c0344502a03d440c0c41070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879808758 1250 879807508 879807527
    0x2a0b0a02070203010b0303030c04081b031011040b07060608010614030a110f0402032406030114040216020312070303060f0506091c05011b080f09030901050c011e06031401110901 78
    0xd825541300c2103030402c5d40e203003007000d94040d011000c01c0300e8440b0b0404c030702c6924201703983d1201c0c0e0348112a407800c511b0b036407404101230054603c0114040707060842030402e8034040c800c076408110715120020380c034820b001580c2d000324140c511040c0207000c01070740c5c0d01082000001c00144164181c004405080004814010b051040c07100685520b00d44070700c980014049070030480d1003003c125040e21050391070f11f0b0110a5100c0100702120454210750502c980401c40741d8261614074001c85d400104400d00c1c5102c041d282040e5540282100c000c1d203005140091342d6001f83c40d04601180c2404000700303100100ca0304000c148c0740c4c00b030f10850400d84000c04214030005003110a85d41c940b0b0407680c0d0030100c0c500307008000c50030f00c0742d00e40001000103d240c01012408020101901d11a411042c4040b1a002004840c6030000901e4903a0310707003500300c80705401009140d510780203a107114040c0303401c500420703013100080307a01441d110f002c2a410208014240c5500d03c8000c910440c0404c00c01c1c61660003016040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879810008 1250 879808758 879808763
    0x106050d05071e050d1425090b180114130b090a021c06060918200304080c0f011e0504120809030405040603050f060601170105060a0318032a0b0a0207 66
    0x40003004d03550301c08100118a800c005641c0c8480101e000100302000704010042441e80d4100b003030700d407c0500300d80c4105107003a0050301c003001d4460804407841e81c1c402c0e20300c6c000301c200074051507100e50b035451088503442451420710380206121540c084c81c10389984034407146928064169802681c0300c1513464001d41c008089005014020306080780e8011061003040058503041d16000116814001d003410503001445000100605200c1e0b07410f06480b041e4240c3c0000700400c8001c0d901d80d156803400060602a0040089003485081e03030350008c02c03005402a4107400e448000c0e18019103508007050094030812203024194081448000c0c081c1d61196500d69413007003011060340e082a480c0d100007415188940d2040d1456440818264141141400082e8110301c00f400d040f240c20138881e0b1049a03110052040f036100e18008560324242e10b0094000c001c0508450307a051100d008a4a0050b0010300c0244180700a2111151000e100000f000400b112158002d803508869907503601d030480180d4003a4204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879811258 1250 879810008 879810059
    0x10060f1b060906140606070c0909050f0313060906081510020705031501140613140d06113a180503030f0f0702030f03040609141e0106050d0507 63
    0x25010400380c0c8500d11180c0e108940c041800d6160040c0c0713444009018240d240705990070403070360700020b04003041c0c2c0c41191082003010800d0785d00303420a51b0920a4a111005d41e6001c00903082c41855901d00200050741c01c03c0d01c8050034243c990f41c00f182d1089080b544c49082003641002c03082c1c1e0b85029003900c03c079240c0380e204403010251200080ba0901105903100900e56194000510940d5000340460000342c800340c60860908900c00031009021000d80310f0000325034264103984080b074035002845040113410040501c000903251a0549883c0e102803460600e015503500f041c480c00c21510060040c94040c1d07203001c140c00ca61030400000400100e8114030b41d82011200e0766000800c14000f0710310840305000c0101d101d29000c50213a80005009102c001190001c0010b50310a0321901c094940054010b240011000c5035841d0200b00303002c58268420891050f2140c07081d40210b881c880038800c22045000740001c540c0c0c1c40a20500091000c0d005060350420f000a0080000110300f81c0c49181c4550311 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879812508 1250 879811258 879811307
    0x7060210112a010c020309120a02060304150f05040804051c0b06100507050d02010c110604171803011e1404152703020717061b130801050f060910060f 66
    0x41c0b80d0031600001c0034100503030004903010f1100d141040214102191010241c00710810f198005000d40c80000c00040c05000b1004244044d464283e101035080303211203800300000c1c10942020030303268102c0c2c800e6034032803846140441d9404001880c0c0d1070b600c503486509941d49841f0b0b1000c1150441c103107000181004824452080884c104118411841c1119000040c0300b07482d06a004040307540040c41c00156500003c01d100000700400413402078403582c4444507480300720b01c130103411b4110b021505240c0c2c15820145401d00c41c1c50a00c0c4d0804d80320079001800c00c0181c000b6042101c0f0799000300e80180001c0c86600d8100f40302c15158205941040a04a000171a6038038030f11a1002510503110550042e40111801c0c824a50490012a0340301000001810079103030841c100c05080d00c07480013140400b540460b6a43c0102c80c4142400058002d90000b80200e00d80040302c503454100c00c031a454030800903030011941c0d10048403850003d41708143c5e960500d60010b41c0741580c5400c3e103101c00e8040c4c10369440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879813758 1250 879812508 879812587
    0x507031506270e0906010506040311060a0302090d060b0901080a0203060f0a090c3b04020d0201120609020d060b07030203220e0c0a030b010f050a0c02060f0c0706021011 74
    0x4004102030b1003003810540c000d0604c3c082042c64100141c0000b806024100400d00108810811810300e0360000ca4100e9500d041303070b030b0045010340540700c0000e40201d81503000c43d040040d25003160019940c01d844e8240c2030780e6191221680c40d01c2c0742c0c4005e90103400200128107811103010085038001da18410100d1111013680c0c8898000b01d49902c0304404002502c44648846000b004007050241c8400f80503184481041e050120040c0152000380f00c2c41204804c0c00459014200580d42d120051800304061640c0e4100c20000c1d510141946c000f0600e004004202e950400c020b480307041d5050b034000c50070b1221108510b06ca605a841500505100d80e40c4009401c00c3d02591283c0308210802c90103444880401c0040c00340c4000e540100e05002284c0e54141d142030b4818182d5003045000e00e01450703050610700214445214610f81001c1d044070015803034400d4000000c0c2e035012102c16508903018000e100843c401141d64644162f0710200080041c030f1a01060306180b50300e1420524243c010541d1901c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879815008 1250 879813758 879813827
    0x5041b0303080714030402100507020a09050112170a021207061103071d0d05030910051210030210020102090a030213020c011a01090605031e1b1204060507031506 71
    0x5500441c00100c15104200c40c440d8021034a02000b4040c441c44d0b4114200b5a00050f07080710075519007010088040398a17030030b540c1d0701402c04005018009003003043c0e586501c1c0d04e006110200e81c0548000494080000e51180044229165842c5030f902400341c42c6c0310784441011a9000c50303030035039030a0313141c00031483d501d4000030045000b40055280d4001c1505082d4a90010032078661b8098412040d0000c8100842c0703020003100d00c0703082c00f15a5101110f0791304d041a1098024030003a01f0b02e407002802000030744c00060f025102075a0084a03190020f0511100880c240e20810324120341041c4071080800041c01c00030203104c180e8198003000750800760082c07a05070031910024002d9131031103482d030030f011425600915402c000d800e062411629600c3c3c0700d4601c040b0000e0010b00d0300100c0c01c108001030800c0780185c0c54049000710001d08284d60300020401596000b6050301c1c01e82d0014605804105507070700910038a4080c01d86a0b50300500e19107441810f550030030f2440c00701030b00303805203d01c10911007420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879816258 1250 879815008 879815063
    0x80c090405030f12040b0901151502210304030237030c060c0305040b01120f02060c070317210114130b040e030d0b060a0215100b0301180b0a180504 65
    0x4e040a02c4003e18107070404108588001d4903040b0702c0d07450300540902a403a020a0101640d1000c1d46021062520800480c0317072054460400008006d03c079031059420140360001c600581c06582281d0307a1a152504508410800c101d064610004d05804003d414417034822507601c00707020381400600980180ca904040d50020400300000a41d1003082004000a030003500c0c4c09001d0f02c00640780b01e00e046503140c1e00c1458401c280a84078101c04204103005050411048c1c02843e8000d000e540c00c069020040c3d0300f140c0000b42206003000d01c0d6000e1000b400c0200b0211812108004011022030741c0c04000d00c80f0300e00904040181481e100c100e600310a880368014400055541c1c0e0040d561051000c41c0d03c5e04071100b010341d8900c108001c0080030581540001c0c880b103000c059450300ca141d9221903c01000400556005081c8800c0c08000001e81643da030a42d044a10b40c8088140915038004041080da440700b40248201b14101c52490228681d6a07400550701c18070600d1408607011950407405165401e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879817508 1250 879816258 879816277
    0x1202190305100b0313030c020619050d0c0309030906080411120705120d1403150301320423030d020d0504020102070b0f03040201111009030e030c0109080c090405030f 73
    0xc5410510030342e0712402e42540014500b49a0080c15414080c8105d14012443c907405400c015004030500c1c00e56846000301c41d01103134407001e06200d80381f4600c80580150000804a00b0300c51502800c050400c2c02806411350207a8036550b1403401c0340c1030000648050401500560342880ca91042100076120b200301c03650f09996030001000310910302000c00c164641030840d28007240d0409010901c441d0b400c20317003104039840d080c0f201036126600c01c1450450380700605003050f40340d82001c028a4006c0005c15440d8880324510382c110b45d50304400007028039000020342d80101820300c00c0030254008007070034001810703880040060320314110418402c1e02c160707000a840005155a206c0a0108541c3c0410016006007140c24140f41040c29981104034a030000500203418402c400b003020100b51420301908101c2001c41d0010040c01006050081c484055075800a0091180c42540504c035070054000f202107401d080002d1810340511001d00503030314005803003124548801d220a251503c0d80802034600e000307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879818758 1250 879817508 879817511
    0x6041116050303010510051305061b010c0c1a06010c03030b030a050307050610080d02190602070813090c051216051611010201050c090306071d0307090207050f0d0206010612021903 79
    0x50400040040313070f660742c40c08071091100030487c050f0b0b5011103044623800c0f00c00445156449110110070400301900320b240d1020103500e000750044885c1d400602c165000c5000b0002c200f0400600e66001300b69000c19140c050100d1a500c04140010b0301c00c1d000900c1642d0058107a6a000b040fa58032203140d50000c0ca0102c8483e0445001c0100c82650241504002d04c4800018070102c100f141002e0740742e03014074100d41164030032904038400f4803000e60112101c0b00d40c00000c0559554440e0784008800d01c00b8041d01411a00f04006000c81d2807090003941e9140c01c003d400400c01c2e03160700410401c4514034001050500c80f0600460b81c600d007102d4120594103001e00c48190366108050002402c655000b07140c0780743c403c070038002c9040c0ca0300c00041a40e48604982021704501421284203c9a0340d01481110341c50300c2490701c0400d43c40079035000792601521600449202ca9425034500c1e8480500040040041c2e101100410440f4468074038900050801600140b400e50115205071845031180305420109 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879820008 1250 879818758 879818761
    0x30d0302070b13080d02280509040e0c010512100b0c03070c1e061b02100207080601120809090a020904020301090b13060312050a11010f091403040e06041116050303 72
    0x45182d00c03a05502c41945200407050701160340d00d400c0c460040c5848010060340c0400c46200c1c9031450414603440115410760300241080d951001410390f0b11866583d80114240a6290465a8001113544002005071203060820403807012602290000808411071007a0022000980302d101c00300500801d850b41015607503c0c052400c00c0440c40d03a03079520925000c0618540c0f840411140246802590740901d00030143d0180a0b0035501040c400100c080d500c11041608050040c3d000549035088440c242c0541f1002d80c0c3c0d6560740602641da600018028640030800094280707010070210742e00003d003e00050034400c145001c6422a0030907000413026a03030b202481d1010340380100039010303541e030390704001e000c01d90442e130751080c0d04154882c403841844030201b05600301901880301c2d6500311081034000c00201410110b48006004075000c00c0d101640c1d880310b04e1203517240c0801110203440c1400c4150303100d520b0b9002408001c000c44041013075048002d02000d070414031820481d10b140c0740284001d503140e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 879821258 1250 879820008 879820013
    0x4030b0a090516050102060c18090f01060e060c1002091c0b0601080603010c230d020c030901090602030a020601030f0f060e01290d0213090c0f0617070c0605090c030d030207 76
    0x10112298030f8003001d018282ca00300400e0380d00040c00d903403046150340100c0e19034481040726a0b00f20f000c1e0303c11a03805060704d001c20080062003403503e4100d400e01c1d80d4446211000c5400d0200910a601a40b006c607080030507a01d000141d1a0001c0206207005040c80704038a50880440c8008800d01e081102c1d002c0106050080560380244041c0e044007048000300080c40601c40060501015901c0305c2110800080381a8102030340402500c980020400041d0360f26154020459101c2c4d0040104a000c5907244002044991002056400e804200c5d00100400d07400c5498a03001400780303070402c03103420710680380c1440020514000d0b880c5454802c1c0000c02c0304031a2009500490300c013250720f2803038201800340d45141c070307519649014042c94041e5030203008246508807403005000f00a4024080101c64080000c3c03120080f02590f00b00d50b00d6070388460a20743e002c0101000400292100c0000a1141174040f0214595511480d002207401085590019a003004270b41040f02c0002c07601c000c20340c0450103205 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 879822508 1250 879821258 879821263
    0x4321c0e120102120a0216320c0420030a021303020d0305090f01031a06160b040c0f0905040b0a0e1f0c0e030d05030115090e0f09010e01050c04050d030504030b0a0905 73
    0x2c000781d0f030003000e506103481301440402412104002920b5203102500c445890340381c2c0c81c54400300b142d81c2c144030f1030206000b60048c0d90742c081c40304d0061301030343c0381c2202a0802c0485c202e111144002410141d441c50f200c044a9402941110041e143d0200b0002d01c0000140d84218801c1656842521440c2d00d0343d003143c040105e448585240d050500d804c11189851420046001500f00321084801380d89030303221f05000b03042a5842c420010000a444802c0c002803224005189040301c1010340000e0020341c4607040d02060301d0060b1401001030b1a54008164100102d42101e184e104407407088800f11480c4803041600c5216488081007a03030f94426100e2070880d84400008205002a0b000b8400c00100c980002c2c054481445441b40702d0040395440e1300000d10030000744009052002c001c024506040c1f091403144901611355172000d6190002d1102038070b4060107018403078803083c060141414904014001d01d000352400803001c00c10100000b00003d808004094090950f81c42d00103015091854001e2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 879823758 1250 879822508 879822511
    0x210603030201151a180d06050108061803030112020d0f0b09070504150e19380d150e15010f0501050301030804060e0d080304321c0e12010212 62
    0x4400500c684107104040c0c08440749050b0030210052166074403098107040e5038403085e0f059510391180300c02c40098148510750b00094161045101034504d1601e94900c031000d540000680400a80c2007400100100c6031000c100300300d510b0010700501c1001c0903a030346004405001840446000580b4024081485d804015a00183c0003d49081000078988405c2d40020900c502c50b07507941104070303000540004100708040300d000840c40f40c01c2c002c1032603101501905051100307500340360401502d44509000d5618044c400021000790504000c00006c0c0c480b40f550002c0c5085840c00c440d1500640303400c54404112404401c20505800e0743e0710b50404c0e0034000d98000c0d6604c0241001010700061000c0356068086608860060604007104181c801c0498081001054007400048000c01004140007000380c0343c40d82450703004900000c2c034801c0c0f40001200440404030266540c0110100801038009a0820341e80c1401414035030b2a4000c1d490004454001d241c2028482e650080340303590450b04582a040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 879825008 1250 879823758 879823781
    0xf0a140a050123150a180909060c05030f04060903022811030609060f060a030210051209010e0c092703040e2809061e021209030702090c0307210603030201 68
    0x100c421140b40c40020b40307820961304020a0010b4000382030324160340220340302240b01c141941b0244070300f0f580b0001c10700144690b00003654104d06042010003202e11a20489209103500c0d1070b0000030351981e0319010300034845220128250f11a080d0403e2201c1181da000f41405007103e890480c000c000341c900b600c101c0c1e20035501c0b90b0007540000140000002d02180081d8440324041d0440c5056540c3c0703001640e41d180c141c0c8040e410111011a041900b903001c001070504030040ea001411a03120041c205007240c07102d508464141d0084540100249442c1c0030264008981d044031001062910b045000410004a0b078482caa5200140c10403c40d000b20081c2507024144143c1100c002d03206040c0c1003504619500940141a40c511840041203411341c00203190308900c044091500201d00400002503110704035056071030500f040000d03058a4004100e038281540907002c03e40c1e68490f050000b080750400b030008020320510030751840b03a40000e000c10340078100c1e80e0b690205030b603031842c20068210346581000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 879826258 1250 879825008 879825059
    0x90207030203070b070912030302180d0309050418020316050319021804030c050715021204080a170f030a0221040b01060f050d060f090e150f0a140a0501 67
    0x80010a4002c820785520580064000300301d07079a100307000c0303c050340c0d80c1d04081c00d0703007590310091801d00d0380c103074058000850402600d00305034449074200700307034180c0486004000a40240c2e0620050410f0381084212040070f88641584600550002e0b04181c40c800901e40c10394003800301082686010003015515204092800c4c0c1400d2090b00070480054120300c200c80d409122501180030035120b1010440c0d00b0350020300380e6050070348517103842c400f800407224098018403d078000e00646580302412502150301d280010003070100c071a0b840030f40c40e0004071401000401c0601001407030340ba040009600c114524000140d0b05d10a00c00c80f4031b031880e02c2146e03101c221001c4104000000d1600789000d419140c0c9418201e058840400048807903118642400c04d450f8184a00001c20100446091064904240e014050030400401c420fa4401c60308002c0304219040c0c001041c51306c15403101c02500302c040070074049a207100710400304400300c0080d15822030700b965580c010080024035500d0882c00c00c009100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 879827508 1250 879826258 879826267
    0x706150f03080a0e18061f0504170309090f06130915050a0f0c0903051c080106050c070b0406110d020105240d050d090e060108161b06021c060902 64
    0x10030035280380320700000344041000180803514038000e660300c515030303a0003c040c4c1c200801e81003038801c02d04ca004d1324160300404403c1c075000c5261300c684100241d920025542c4a045c50714207021042030301100c401c1c035001404100f001401540314031100c04d21071096003024221a061400a020000d94101c41c514426480c004000000a04a110301e12010708922004125622060140341c02070039203482c401542c516100c59400c40030340003104002203900a50a40350000e211072420038030420300b64107450000d405c890062040c180a41302070301c0c180c141141101e0503039403209405415544039402c0480810b14449484101c070800f04408818000d03148000d000a0512160112600207102405079245695034552502a110261511030300303600001216036607115044003034004003543c043e14511116800000d401c5501613908180900b09900026811892104003160841c060040402005060642103400300f480c1e40090038031090442c2820324484601070ba41c0048075503960107582d12500502 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 879828758 1250 879827508 879827519
    0x3371712150d06091104020a020a03080603161701020c100209031606050319020f030a05101a0f03150a03032105060607080309071701060302010807110a141908070615 73
    0x1050b0600c00d0b81e10003008581108646070100b03203204003803049034100c1c0c400b01c2c10030216540041d001e11708501075110900941c40710030034952075400c40040580300b02c6290302c003088504058010304a01c0a8013000060805811074034141c1009480301105100540210310514646801d02c6180400342d8124400d80010b4a41180940140001440b440b81080c0c200f000041191198040321840114189419a01c0c5042895100103003001d44c0d01c034410f900c0b40b0f0400f2a203d884062001c0388110702803691400c2c94030115095034541e0004001c68014460a02c1c41c46040e01c500704010040c40c402d8690b10440b80c50034031186120901c005601c0141c3d401e210901c140358803950110b94181d1740218a0a80d40c0c0c0d20258490724000b41544a480c074800c140c000070300c0034003040d484403098900c06d03a0f81030541c0c1c55440003103440030754000b4881000e03045003004030000f40c582080411a0402042030301e40b8984003d42c50210039140718426600014001000d9081120903c55100d807508440881c0020a0a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 879830008 1250 879828758 879828769
    0x507210b15011106041a0f041e020a08011409061608041b0f060806040c08070f0c0c1a13090626070b180109050337171215 54
    0x340911891510512100714164072070048440c1c4203105108072100303403d00d454800044c900303e610041e80e5455402c0411b00d901380d0b450b48140500d4024541a00e8001c3c0700341d070000c4a0000401c101e900030110342000800040a0180b600540c40c0f0950301002803615020a0341030000003070030342000360400c4124040f055000410701e038100350060380002d00074110080c0420b130905550880940c400b200c500020745030398080505071007510300756000d101d080010f03401660a00d400365041004500d044041403141841900380034030a501480714200900d544e20301c01c00c04110355000e070400f1050002101e58086a900e4081d000508201904022132032800e041003c10000c08003801d160120f000703441e880c1100080011a024146c40b0382501d5071204594060b0080d160a02e200038042520000005014600400c0c920705074002002c0c0018041400038a40e41148440c11640019001d0156988045090108050f04054450f50b4030742d903c840202a0005101c0d0003001701030004400c3c40c00100079210f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 879831258 1250 879830008 879830011
    0x15090309030d3608100902090613151701060f0305030f07050708060c0408010b090f06190b0a03020408120a0f0302032502060709140607080705190507210b 68
    0x440c544406044840c0c1d1000504012040c540c2456503145061031840710f403800341d0802242c03000000c8910078682e410100c01581c400d044040c0d030010400b0005042814140114401c5c41c507110342c00141c6102c0690082041183c03034100d2102024070984c0300d2000d507000d10034403015101d00c098441c845880d565031140e0328403420514000d01e4402090340b500704401000540e0103030800c01c040e60f1a910f00000c00b581250030a03c208607056092441e007180c46c0c1491058103005803903880000141e66101c07401c0c014000790040d0701f11001815540d00180003e0220040c105500c01603a0141c0c0e0346192000d050318002c041240f02e0000b41040100031010740e000003c0d00200206400c003d6105da81d030001c00a41130245102c1c01009405240e0064082d5501040c018446d00c00d41d01c6030600b40c0e03120b2240c0c07145000032080013070b000041004500c011406410240c140c0034864000c81c0d06801c40300d5654004101c4090044030142c0c40048140300f80419280c42110700c011009041440c0490b64031040440c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 879832508 1250 879831258 879831283
    0x105013c0501141315140a0f030e0307080f0301030c23130923010e0c0d0818061201060306060f0e040b0109051810050102160e0601050d0501081509030903 68
    0x1042031072148442c5590113559a4041100c08004010350720081417000f030001285003c0000c04c003000e4103401e03103196416240300d0041a40d844440c1603004c0400d070010000d4401a40d2540310900000c00018441c0f80105103900640513070540303030752542c42c1807401e444803070300000f06414803080c812240d00c41425410341403120072102d903609410484d0014000381012000604901515030565030041040c003108410000600020030039405040e40c81074484941c4104035510100c208420b0011400d188094120b03505604009480e513000f403400155164020700030341c08004036400040010540520812004040c2030401000c09948003600503c0c010031074000300d106075035400704000c040e481480c40c8805407001405008038040b03071404689104000321500c503881074200d4400b003959403001c22410182c1d01c0041c00d0654080c1091002c064500d4000c140c00d0401109001c500c401d15842c0c00303298020842200a042603016282a654520030020210394481e1b004200300da43c5505d000034011a0801c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 879833758 1250 879832508 879832517
    0x21c03090c080616210c0806090f01080d0c061503240902010503010e0424090c080d02150a090501020417010f090c0b1c0504050606030d080c1c020c0105013c0501 71
    0x30300c1c1d51008482d008030103900c0b428103486d104020000b581c100d98124003c60341112003249030b6a541c0081d001c1018240949500794200508060489011b220f502c403a90303100e1a008075201500d078003036448030105944165020207580381210b0050100b01d010512000401c20148628001900080d0507403206102d0702002a101900050a10000302180c6c03003d0080c0301540c0d01c00c2c000c502d400c400a84450035041e25044204200045e0010340051134514500098018200c920040080056024001040741009507101c1c003003600003c1081c40200054103c010814214015140400e82164801e10445140500c0c150400380441ca010141310100d80000d07004030347d1030310b000041e90301501c00320150b505101e0404c410700082020120b240c91203072406400701c6402402444040300e0a1405940050700d0324001c001038100c0300034101002c0746042e403c080151a00507002d000d1400c42c3c800341d0283c400e0543c1200c40003641c42c010791000c007004803140d1550f000c2a02070001852240daa6100b09070501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 879835008 1250 879833758 879833777
    0xf050d0201021606110c01090302030606060a021c080403030e0309010905061602060f030603390105190801050913020109050904022202040810020c1c021c03090c080616 74
    0x581c801c10a807030950080d0b60b907501d100f0740c0e2150060860f1200c0c00d500822030242c41180341140d4441c030095012a40c008000305043e441e0042442510751110008504500440360210480e000d0380f42c5a0703150394640e6850003510300d050f040c0101100c182e40c0e40e2405a4000300166200e6130390050702c40c0300b03640f07013240d00743c0d580c4401c600002085004a4070007034103c4070106811800300000b0001c6e40c450704084d41504c081445150110050030806a081080c003805200070341501400d210043c018004107040051416003c480bd0614029003079420f9800118030800611040c1041e04c40543c1041e18074185025124240e400130704520704a0003071030300801a650000702590384004820802c80201d40400003403000d40050900658414081c0003401d10491201120450700392003102c8003c0340400160040d10070611100c020151010a00d00c114420144e804100141c502c020b042208007035280000c00c0300140c80d019411385400d910842864000e9810040380e80440782d40103140120070319004440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879836258 1250 879835008 879835013
    0xb0901031e0629040605160507031a1006050c030d0506060712180f03021305070e06130513060e1305010608030a0306140409020f060a050702030604111003060f050d 72
    0x61074040c10104018100b40d800505840341d91420440c41c00b20009030043c1c12404009494144103d00c00c0c6030000e0400c110451600e14001103480c50307148101c080d680c5982e81c0c1d4a402480c841d80c05803284083c0e4501c814021581c003440304442c000c1000d802d001d41012001d003007468890003501e0034131415944031000100d8070740c0c41608540a00e50300103150400491448070090a101584107085c0e01d940f40d107000411010100741c11a401c49600400750315000d00c185218202821001d0110014044040c0c910803040d40c03040007514545510f04036820b4014a4141000000070240040349003c42c5041c000b801807a00c2c0c01041b039480703403441c1c00c2900543c0103460140d004122603400b004090002103071080b0410f6264004400721002c99141007801d6000000700300444003030a500030340c01254503c1005040c1000c10250019600302c4c14070a04001864010070708181e0704a07001c84801001200f102d103030380fa10246600c401c0074140313001c01000b8101203a15072412040d0203207a10460024121408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 879837508 1250 879836258 879836291
    0x30209150403060501060f020a050d0f030b040e01020903101103010608061203040e0a0f0b0f2b08030402360c04090f0b0321120a09050f030703020c09010b090103 71
    0x24082038140ea840d0750700e41d0703410054020300c0c0c00e0181200060000c0d1030141032910009204002c82c0d003080281801c40d0401c1e03c155010000c40498000385a10b03003061003003580e1944902c0329410060400540c1d206505020181803041000c5a404034902d00314065015503110703410f03207040d03807007a0410290a40f0303a940010340d609844078046005120026000c18055100502030b40219415041886201d005a24103001d0700d210708001a00b15802c112171101f245801080300429046801c0c14400c0210302c005000390041c0c4468003511442c40020500c011410b2030300310160302c3c40c0711000d242940102c1086001c0c28100703124209a08012110204200000590854004240103d0b0800ca003a0503090714001030082c0d804668400c1c09044901425402c800842022070f41900c99a18035164011142e04540742d0098103040285030b0340c1d14141d0001d103041002c4be090901c210000c5407129440d00e4002e04d4170080c00081402915a00010400130070500251801010b003400c01090154a0107920700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 879838758 1250 879837508 879837529
    0x9150203040302061305040c05210a0f02180901060c0b070e0105190c0c08031305040f200d060807230316060905040510050a120503041a090f1807030209 67
    0x307610680c000b68500c01100308462910440d0010343d4207000da0340700c0c0c0e2000e80700c9008200140a00e180140d241490118284ad00143d000880302d200084014002c40e0400498111700c19900d003003019800221541c0c60100e1540d401401c052a01210418042d6264502c17204041d01724018400103100b8100541c1c003400a403035030400541d850000c080040744000300ba03c2107990007980c1403a98400041002c4a001c4119030122180b101c0b00c402070351401381800003c010030003009141d0b0b076482c074912504980190790100340303d254448554444241c2148001140c00d55403040d41301d5801108204020700c12041814100040b04110841d1403103100040307410030300300f00c10303155038a6401540498100d130001803650036144152002c00107a81c0b028908001c4881c940116640402d001d03600304000c49101c02e14501e41881041900d042a03a1094070000008209892031035180e00480d60f82d90905018192105000d011202c5001c41ea280754049920918060032040800d50001001061b0341c6072185d401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 879840008 1250 879838758 879838763
    0x109091112030f03040611070803041a0c0a0c170d0605100e0d03030902210d0f02190f05031c0204090e210c16031104050601020d170a110316021903091502030403 71
    0x1f9546001e40e06d040c40c911303403084404603110011400360100c1101c680703280a1186e10480f820701d1410840342e5082d101d038210010101c0340103030210b030143da41c100c0c0b020140060b00c81c0014045403003030a181c1003100e5500740107050f17030421003540c1c200116a0764040b03400500c990181400280b24009002151a6803800c580c6040c4030001a005829a2140018080e6640300d07641d0310099800c04081040743c85141d0034410480f035106042d40c0b070b0007184903450400301d554842c500b140e103054900049042002514120551000c0c2d000c1410411071882e8010b582000c41c01f8409880a0b546007006d00030344a907800a907000c4581e000c181003840e02d800700600350900c0c041411521000b9903a1030b000000d100c0c0d0349452401581000c1c0402d0607540001a102c5806020b5200d408a494805c00c501d00e41c0c0c4030013040d41c0c0c8160307140e803c0d1a81c4c841100005501584039207141c030b100034043d01006803400040200d04141902460280408a64008a18015501c07280c418204081d03a00d00124030754010368001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 879841258 1250 879840008 879840041
    0xc0409020c0606090c040803040e130b04050c0118260c0a030501090c05040507080106030c0903060608060f0c0a0c0f060e0d050c0106090207021c17030109091112030f030406 76
    0x5a1150307900095807912545048600340016a0f0ba0740143e50310303000c1c511804100364400d1206000d10030300848480e078854800b041c0c8002ca405291100001e1260076203060381c040d000728013080c07125640200a842c480010f01e180d5455240303800781503420400000421080039a043c4c0344017000d05c4042c86000d407080001821450707580d03103a082c00c5000f031003070007401c0314210103911002829040502555204601941320724107985c0c41d002c1c044c0c01500d0983c203004100041340b4130110015035a442000090141140107040d0352030101444034030071102900c10014501c0502999090552201141180a510646d6a10b810380039143c008050840031042880c20f02407030341c8800702a580701c00544140802c0310028848a50b86210f044124800e003540650403540030003a881d6640c121000420245104003200b14581c41011082000c60f04282c01011324903031101d04420900089151480e03041608031000e02041301e040e200b580e580d228600b140700c0d8074075021002400b03002d01070340507201c00100c1800c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 879842508 1250 879841258 879841267
    0x30605090a02030d2a020a06210204060c02040c030614060a110d081b0403050d03050613090b1509010b040603090c080d02010b1f080a1d01180210081308030c040902 72
    0x140c282c90501c99080d0290749841c1240d100c0c8003418174448001078002e00504c0540d42801d00440b06140400301128a07140e00810b64072140080c2e01c0184010417007551f1f9500003000d144100700549503780c0f011003c060601c4014010541080e030880280803044a20701d035280c1d00328074291904842804120424001e02001e900400c0c0c000403c01d01c200f2400c0c3d9a18100d40c0c440e00360360018022400040c00b594403071000481041c1c000e6000a42100300149803120811660003c40107039a10b44804a03020b904a2045c0100d175841c590804951800403190341c89158102225450f25004900c608d10070942c441c8010814802500d070b1540281004605951088100c070b00068042d1011445280c020411007078904001082e28202080031030362644c403500c0c0f940300c0c201d03014094501c04506001350703000b0303c0c860b4401075024801e81c00745202029072109151468010082101c84400562007808490b4003040035084850800f044602d82c454080c44d100e80352000812202c9c007640e04080c0c0c00510000e0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 879843758 1250 879842508 879842533
    0x6080105040302071d0705030c091e040608030403031b0606080f06010f090b0d060c05040503011811040b01680d02091504050c0c0f0d09030605090a0203 67
    0x410103445140070f5002c03990a00c5d52400c07001c000c24040e40d42c6001d2a01d00001003582c603482900116009661401c025040070a00340024403d080146041081c0b68903a13a5101090b08090091800520224001d14185413540d140a0504e203180300a6503000e0029201070010844942c0c031080241961404a41c610704041100d583e9034a000e0040c1e1500300806071002882401e03a0181d168450130181800800d004159540c80160001250b4102400400c1c0804126a1024400d000044207094243c0040c0391300c90601016040e09105801d000f903051508521060341c200c240402c3c0101c000d148201e0100340c03140b200e452144c06101c2150f543c180c1c0141c20140082031305140aa5165040e440621880d51040403650300107204100740d0001118031081d000340c81c0502815074004080f155001c25541c40100080c100ca0b82200c24030400744001c80c441100e049d0420035220036480090003055011040000604032007a288001001030f07850307000103103034400f05010841040b0781c05821502c01800c0e07407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 879845008 1250 879843758 879843761
    0x6050f07150e0a06050a1a0f030a15021314010c150609090803040b13020f0d0602120a1b0c0b0105090702030903011505040e0309060f0c0715030b10030902031c030906060801 76
    0x1041541c0403030404001c03500c101d4061060740143c2c400c00502143d0112030300240300303080f23080c0001144d143c000c100c501c2c0045030041d000100c0a0740019401a5122070501e00c81102000c0c542116501110240406130942d82101c174445080f40c0020110b503d10009004101c003801360307504010991400d0200310010880508061802144180b200052030307940c402070b5220360340c80740001940c0140c040024010a04041030540708540c01100090300d042c5916500b01c04500080e5501815240d4807261814580c41641a8403006c02080c90f003292541f8040e120711050364811b00450748101011004503020900810850f02402e01c081c000b0b1020068000d01d03036514125521406015508242150b1004040801100c0701c0d8400140410705120288010200c00e4000b2240a00c1d240b141220104130859aa0020341c5200c040e940c0c00b24000403a1001e03c81d0224508054a05150801568030010383d000304582d180e003085a114001c1404112408502130525080c0c0907105c5454507030003181d0340506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 879846258 1250 879845008 879845023
    0xb0403110901080d1d03250e0708090a03050a1b03091e0302010c08030601180806090c0a051f0e0d0803040c080c090109240b030a0f020406050f07150e 66
    0xc80e8169500ea0380c8800844d22100610b60740d500040c1c4143c01540000c1c2c107912580c4041c20060221451500802d0201924110007484005041d101380c074100501c10f071030540341b6403040382460b1083d91400e0515140b030365890700304402070501001081d0a01c07428400d0240e504c1c1d0340c10080000f810102141005080c8100314020521401d00c0e01c0b54190800480780d958004499043c2e403070120501d0341d82c841840e1508003501e02d40c1000320008803481c01034251840c48004c0e1500d10050041c80c00c1007a80700b440c2c1100d00307100602648101108200541d5002d080c40844031030308070406817400d00e40390202d884180000c0c180e03500c402c0d002240024050094081c500c1644505a605101c03034170b401885a13542890506e4940c08112180180032881964000f104038201107540344050014014903416800d00540240030110340201c01c005800003e40036a9003003400c5100c00f1032400e4142140105035100c2d038410401c0385140010100208040f940320050705d027404081c100a80000306a443c0d849260 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 879847508 1250 879846258 879846293
    0x1c050901090b25020d06020a180806100611010f06060e030105132117041a070c03022a03030a03050907270b1c06150611060f040c0b0403 60
    0x610507002c00c5082e9004100d42c040e10318092840034660074034500d1500c81d9510340049800c200c400c00c0c600c0010706540060512107945889181003001203d01c1404c0310032580c0d104940130740c40042403089180d180d1040e5429204140742c40b207500e4140c0e112017800b401c40088030400380c51030315030b0001e680c0d81e02600000300c0800413402804252aa000421a6440c4040d40038110802d0080134200c0701041407500409500d040c2082d00c54150f480081c003001600071101a105c1020f02e202d103031810030040c200c40d68008568140b08821156584000b175a407a0301034040300743c10481096004000c500d840030041049001811240e0340c0e0b11558008024040640e01155544548007022511000e556207906810141d9680d0400110902d88400068240100055001520362a107026020910b58040c0c100d14040c0c0c1c130100d202c100710241c60b140c030000ca1b44080104400b03c0400410050003181c12900a0a410002455074545003441e03000c3c100c0d81e0f0304c104000c0000040004c1004960b042080c011070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 879848758 1250 879847508 879847517
    0xd0204021b16090203010e070507150606090e0705070f080c0a15090c1a1206211f090f0b040309080a06050a061a0a1404050a171c080c0702031c050901 66
    0x80d0383c0c0c1800e0302070340400c0c09640e11a4440d000010b02183c4150082c041550242c0d011102a20786904120210303102501324400140482c1c0060104620380e01c1c87c0c94108000d03203405c0c0e20300707440fa072910004048542002801280001020b0342c07004420800f0705480f44d00b00c070800030000e4104070080d00420380c480c0200c40e800740305100010008911400442c07000c0e4103884492911100003a0b0603900440106040e42c00360b10000c460a013040d09484000b1840ca910340140b009032066112490b14550b04c64a80880505000c120740002d9030031410b5411b41c0341e01c0304030a8256110380c0f4050700c2034a42c1c0d80101e091446001051400d03c43d20390007160007014010010090f154a41c0b02c07850308d81d51480c3c00d205180c0c0f0101b000c1400390f48100c00f00122108482e15880c00e090b210000220760344802e5124003140d840750251101400010701000c200301d03a81956031401243ca8081c00303808031a0050450b80c240c40040780d40360943d01c041c44031880719040301c0b008099400030104090480e801c01404e150006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 879850008 1250 879848758 879848803
    0x50c1e13090510090e01021e1201140d0602030c0c0a1505010e04031d151c05060405060a1a0d06090c17090714130e0a03180b03060d0204021b 62
    0x80703114050150941c0b494903c00705081004410290406080328020345d982080a194000d00f0386088a403282c0140c0d600c1e50741d800c90382d00044000c0e40180c1005016480170f1600c0c44050395a007440e001c10307543c8408096169541c220503030304140103408e807111070341c0205c201c00f5040255002a0b50f031000040c140401c05642c0350100c60994103012140100442c800f882c003036108040c410024110750300002e000d100341012030814800360760009409141555030002e481c0d4114061406101d80c414415141009540f6182d400210411510300c030b1048818a28514a0949480102181c3c15441e100b902070002940d101000c800518201c009000060800b80c2100760410380600300300c0c091117814005201c0b150800c0c405181d80e1800d030186650005003450090300c1c0c0c2e1098042c285010308203c0260804403507030304020340401c141480c00181d2080d00401442044031400580360040016581c801c0d1443c014400b040c005e10a00a0504942c01ca000c005c1c041d5a000003551042ca0075802840340c0c42c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 879851258 1250 879850008 879850019
    0x10806010b0f12090f0a0302010f290d1502030103150e030a020c190815090d0f0206151315140a0503070b0a020102071e050714030c04050c1e13 63
    0x1800740c41c407480d80b00d00080104245884000784039507048001e070426581420009074045190800d00f942c1100541d44030488040c005601e0700c1210400261421000807419410801300700e4035050003151031042c4403100a00042c42441c5960f6407003011071040071540e070b586a0400b00514003154079622801410702254450207600401684c4800d8641d8008040d0780100d5800c0120541000e1081075020006903800103070700030704001000d01103660602c601c0c2c4500303045145e50300300307484409020244821a440703d03c110b40d000501c95808503c654800040381c1030800050300307030f11440d040080f50904141000e0a0385a0300c0030401c0407589807140c441070380d203c0f1006101d8003060320310816900d500062000c010840c041c034020701c07a1141500c00185011600c8e52901458607803442032042c1004052070301c0d03017080740c00c10002c00900721155040340f14030322107000240d444181c881418000c0d5102c1c0701046225950034142e444414000120641079414407071620040e03003003040b80304d842c094400c00c001003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 879852508 1250 879851258 879851279
    0x915030c060909131104020f0c070503072913060e0f09011d25080411031204090c02150703140f07020d110a0b010e0f0a15060e040908040e01080601 65
    0x10710b010098050021552240701241c1400581c0b001500c85a0b0f00c8440c038503a41d5a140300501c0c00a42c56901e150f01c52000c000903510f040341c0364211a00a030300c121014402800080140070782c1c603c3c2007110907a1150588040003503401241c4100c903030101c480501003440394101c01c161800311015601c51884010600400c034140c40288181c140c1100c041a80d40064401404199400300502c445418020f00d031140611090880401000010f0021801c0c0310803ca401e6a03800290b92045009007001584140c1d8010340d4803079031103440e030030300c0d920001025002d00074000b42201002507005004640303400107000c0d02400030004d200d0a1100050001100040704075151401030749194024900c03c40c0110003038070300e039030100e4140b074561180340c050700700007001408424003134401c07105001a20b041a5006000440001e0001180b8078140000f42d101c00101c0c0070b600d011101c4510f003401041c81e50300041001456104400b800001380004c011403020750f42801e42e4129041d02048444503a0390341103518 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 879853758 1250 879852508 879852517
    0xc0910060f030606120b01021e0606031005040804090e19060c020708120313021507030201091217190608120711060c0c010c14010507030e1b0d0204020d0b0915030c06 73
    0x3000c00d1725012042400d1007690b014507250301c410300440719060540300214440c50172403290807010b540040d04111540c24240b02d94102c0560420f014801c2c0d0030559100304c01802140100310a075543c2d41140e0100007000c1005004034201040c41402d0b943c51402c05d10301410040341108054030507002c00080d40d100c00600401200400c500140c215120f0b03011700300c0d101c4600c96003a40c1c00b0915417100384124841c2001030031581d01ca5000050380c108c0d60b10341540c00701301404421003405924801c1042500c2c4050f0941e500401b030704041d200e1040781c0080400100000e412044092190741d400b002004241070003489000d0064078034a15003200c9504001447c0714004052003250045644032403154090400036128502c10003502a111003554100c034216001100c84000083d254480c018040e00144802c1c860301c1c06084e0707401142260f90006ca88944003a0030002e0045a0001d621114940c29a00c644640c8400030420303002c0d42405509048020f40c4030814610900a1101840d0b591504c0030494 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 879855008 1250 879853758 879853769
    0x3060c111209060f0409060e0f150d03020f030c062a043f030315140d050102040905010b0a020105070201270c08160905010504020c120c0c0910060f0306 67
    0x4001c90380c00910300081682000106540140c0240070207407001c204400948041c058200000130b12601d4002e00a5050402500494094448100740070220000f4941408900c00c25616211141d0741c40c50700f2480d2101c1c1200000c080d01000c0fa01c0030121314089005c1e4040c00084034845025820302100b01c84450000e107540c1c0c26001d08000800014101c1480b40481401c400c3c4001254a464510030740c0e90f26006002d04940a00120080105905440751840b2550210352010940f401c2c207051483c9401c0b030003c62807203500d854010000f00242501241d0103804818000c9c8000e503903640982580d42c0200740703004050b508090024a00f82d10521610440f29401010310003400810840820302000720360040c1e0351458100b0300880c451b80108061401d450326991301070396403441c001e011411070710180c01c1513102c1d0b401040440000c010002d20134042d00901c20318103a0b070718680c03524185000c500d0646a0f800003080c40800140b000c140d03200c581141c160340c0784d20800e130040505c21001c417034050055 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 879856115 1107 879855008 879855013
    0x3030103030918090c05011407020a030803071101291201151e050d06020306061312020916020601030b1911090a06080103170921010603060c11 63
    0x942d2250a100300702080089103551760500a5040b40c0700c0e581c104038802c0c00e82408505100100c0c0c03121b0350b00411101401e07a4038a0000a550412510007002c00c00b41050030200c20418085c0d2240e00f403118480c0d0840d89480f520600e03000410a0340e160b0010311070111805100070901c0348086003400080c0d0740030300c0c528000541590040d0000855003007401000200082c2e1a80203d003491981d118030091303207954903000030814070b001c0c0015000503920410800200402142403043d011030090300c80c17400d140d465800092010640048410040c0e00c218010004200d01040150300305502c0710402150904209901c41512821792200452500010342003000b4035003115604010203132030420101e03943c95510340c44940c81c940c0c48580e202550024045009550351150482e11041081c8180c0c840e03280d00c0b4007140200191300040750450301c1c05055281c80e07405091241c2550070072600 = true := by decide +kernel

theorem cover : BRFrame.Cov 879676258 879856115 := by
  have h0 := BRFrame.cov_init 879676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 879676258 ≤ n) (h2 : n < 879856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
