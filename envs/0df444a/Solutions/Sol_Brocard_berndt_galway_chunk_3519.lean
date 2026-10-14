-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:53.985736+00:00
-- url     : https://prove2.me/submissions/98a6b7e9-5c66-4135-836d-f0038280de19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632733812 ≤ n < 632913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632735062 1250 632733812 632733821
    0x1b160308132f0915040e121332090c09040513060c180614070206030703091703060607060207050a020907110706020f0c013b18131b1701 60
    0x1401540c0b22850590344409001c41601c040d1060018800790500701e51040c5026040354180300c000380b081da40c00381c0e000040c0c0c1100e81c001c44000c4808d01e800d00000d109901008014000c524082c528201503243c0c8075001d1410001c0b0914103500070302c034140024070261011821602d803848082d008000d24908014a0041c090282504690b828142002e6806481c0316282c800340b040784003034985404ca40350580a641503030641550400014090044d81c000d6a2142d0140d8801c81031610b003c60101d010740760001c80941000c10342c0401c54401c1c414801d036910f03000309492410b9405a801a03a0b0750542c1000f6103480d019000080d03010369044208144d10741e105640c0303915424400201e9182e9515243e09030b843d1500e821034841158414260500c0662048540c819030040b114104002004154a0070741d407114032541e00321640ba000c00a00b61070b4103100e191007080010151060119082c0f0405509601c1040140030700415400d501c1100300328405141c0c3c500501603484118101140c00728507074082d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632736312 1250 632735062 632735123
    0x31b07060614030f06070e010c050124050901030f061512060c0906020c0d0813080604050307020102100506011728051506030103030206010603020a0203070f0b1b16030813 75
    0xa007040d501c4095a04002810701c510304c0380710000d001195202d05048803da84220081c9040180c035001603000324800384a109400d0440400034044000344618100c01d480d07035030b80154000c00765800100040b65013500d032101300c04e501540c08501c40c0a10310180744422019040f03444480d039411011400c01c0b500b0341c03140b011100544c6884040b19034884090382c9508d4034000380341e00001c3c41044000095030010082c1040ba000c6010701d075400b500d406c0c640703103002c404980131502c951000603500151368040020309070203112a041403026203040706c0000c00f90043c0c40c5410007403015820100d2151001d6402c10240e000c101085103080120560805001c1c05003a03d604448070f48032190920706091180440707050725095001400306c1e92804c07000b18000d501c689070400460206100000008404034102442503006250528150609501008070408030380d061490070f44041081c684e030150705814840240d509400c00090300c2c0d41d14510111140c400700d2005042401500506c1c0145200320203c1c50032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632737562 1250 632736312 632736329
    0xc0605070303110405031902120109030206072d110c04020f0403060605031203041e0206040605180405041119050a03050604120e09061e040609020d0e1c05031b070606 73
    0x48510006602c25108038017403650143c01140032284801c814100d0b90480d1807020702080403160000c06c149007100d8580303404500607000320302807040071507110034000703e400c45045101c0d21180c04a85100307107440c00800200c00740a5803019449040d0814018180c01d558040d2017590386120b1009400e105038013500084032001d19112002c942404e001400034469840b070740e9002d03e140c465440ea81c0e503151000d2040300c0d040d031350042600e0040c7c0341c00c405400240016243d031074840c043c00c503210300c134030795803810a5008510b0481080007265424002d1000c00e2401e5820b0541f2040071501014544001e401090304002255000000c0010014000b07200b24003940552070600c0400070121085e01911174003e5102c9d500c00302290342854006049503440382d0014103420300d060f044011900340c40070b80e1312240f040c981c08500e842001980e4024072007802c1d841d10142036a8101c542c0d61006a400903513003601080760102c001240c3e5000c032032041e6098407010040c192594801d14140d00608503c1c02401e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632738812 1250 632737562 632737571
    0x5150406060201090f020f060403140a0209160906030e25090b010f05070b10030b070c03030e0f1506010207050307230604120b07020c060a260c03010e0c04030c0605070303 75
    0x812a2041c4504a0b20685c008610441592560200615010303640d07a0b03039078000001c1000000240300340d4500d01e40c8100d640c01800301c184050040000c03601e802815403501c1c400c0e0f03090f2419040c0d840700c0c101c015200c440c10000707007003a124680c03145001d21948010840c1c0d850381c1039480400c15840040d908940d40002d0610500180000450b040c509e260103001c04101c040c4580d10020312815481507002c6081c0240301d20590303598440c00640c40c0b0a6030110040b0310025180742c01c2c075616019603800c01082d48014102408400c6806680e0540003a00c44203413403000c0040b8809a10902c00480104001000c807440c8544800d405c0700644400200990b040640c40c41400d2142080300c1980c04407000310003180448d5181d5107a030409040000e0a010841c01048004140341c1e440b54040c182c008081e549003128010400f00103903c034910703d51400c4009107410f04000e41c100400c400c4a05640c440f0800304442d880300020440b0301d009640004154015024000c10b0440d80328010340340e480e009640900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632740062 1250 632738812 632738819
    0x1303050606090c131404110f030f1803160c0509040507090c0f1d0d021e09010e061c0f12080f2a071a07090510030501060e09070c0605150406 62
    0x10b03480d21654138020084500080c04110420358601d5442e072265020300041054040c0307203034428480d80b02c200243c08081c03000c02448044012280e00b05e80c0704000282312a030206508441994a02411395000000004e0040c0c82e410004a02c2c104001404060800031003409c00d4034001362a00b500340201c8208500d800c000d241c0c1c140c4a04100d80c0d0458031901c0c0c00f22802d082010b072980c10124480e2480d00300c0c411418800050300d9030b81c0420071640c0040d10b040d0748458028204000548113a100c8581d03c036264051020380d54846001c8014003c15083e091214074041c5444180e00d924018090003010314210b420386125000800c1c0c5106809685907034907250b592809440041c12091550901013a00407500074000a80e0b100904e9010700500083d440c0c6400449000c800351001c48030080080c1d110041041182010b515030840142e45080034040d660400c00000d0046410282c0750b071107440440081100140249a010407030307038203d50300f031041d490718840c030b072401000719000c0c580202e18020000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632741312 1250 632740062 632740081
    0x606010f02010b09040213140705040906060206061f09120c03110607150c02160902090102240a020a0309120905030d09031e03050405090906071e05030a0908130305060609 75
    0x90b0b50480010030003419900c40341c00340b14007007c0102c0720309a455a601c0300b881c00003994820720351240f0030503601d107643c6905042d4902c055a10070307400301d000d41d0f21038403d12495545000c58400b109070340421790210144041012140012030340e01416a583c400303522101030180c0c0d071407a84240da008182000780034003a40b06211f000d2144c1000981110366101800110b406580c010181200d1a84101c4030700b0540c60380f12094030b944e41d0303104410066000500e44402d58040c01100400200c00e02d0700305501e003000e9614040c10030001d08100e46a9030000b080078690740203a00a60f015600315141da410441010006400c04000740507107131207440380d1280d54a03514818945d081c2904c1d48424244085004095880c0780c15071039100480900c541030001160a486003407840d8403411f001c90040c42e990600c45006419803000050400115403050b281d0701d0303803030340050849420051140c400980d20782d15040107449030003400440f41850700e80f040c0000a0010006482f400381004403802e200b241c0703901850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632742562 1250 632741312 632741321
    0xc191805011a0918070e120a050105060a030314070614040b0f010803090607020d150e0601060f0207051c0c08010e010f2708030c04080d0518030f07180b120606010f0201 74
    0x50b558084081303150381c0c0300381480d0384c1420380240843c00c003000d00c4000c640024081541d550f03400c40090b8068024102402000d0181c1d0340c11000039191010300d5402c5071002440400c8200c0d00d00401c000001c1c0e0348040100310360010b1038060401804000500b000c0c607018400210950780c284071120041e0010a02c0d050100446604607002400c05240840310344c00e0100d55003504006403a504000d6841004040060040885007401d200103010958180301002d05001003c02ca80800c661000206100c0c1da100e14160609990f05601c400e0b41020480c5442c1d1043c00840c1c200c582039508003000c0086608054020070070401d5208400d1044c642035081d040200386c1049502c500b4440e0000051001c503004500450304104043c101e00e1809440d42c80c4a881c0030308102800340002c40000f80c550403580054803c15076080114080e01c103440b1244211541c0c0c1e0f50034010150080c0d442d04907006204800e40c803080700c0788000f900c08101b40a104440d1500c6110444420340070403805020414074034410300c05d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632743812 1250 632742562 632742577
    0x1050105060d111608070b070e0a06121d16060c0b0705160c080616110607141308010b1f140a09050d050a0302120c0c191805011a 57
    0xd4103004001000c1c80c003a044404081e1000c0c03e041007454081300d6204400850f041c0100b030f100340d8030b0006241c4150f104100400b003100300f15004c440e0710100d0b51441000740413a80380c1c1c1360030302d00003000d00c5400740100b41240a40c0c0b640191039071007855003100800c031221401284109014141c1e13a032001500c0702c480c944401008070520400240741c4074002c4000d840000d07204042c00c41c5e009030560300c06030303085d6640c6c22410341684000c0070800c64850181c11500240001d180059920700304610322555804080c102405004805841c0c045411a08003036820400420040c0e45003190340d0740c0802e0081201e0444107008032032101c0c0d105c01c6101e01e036458006580e044c1d95000030101d05203140359040d80004c0105401c11012200c001460b80d40c4184006880e80145e001e4800f0b0882858040d103020628140841d180b84180708420401c080030505604950701a20f00c0c0000c891f0428206003010040d0300300d03d440d86500000c1e030300b40d418954003850684040c8040e041d21012103102c051018000d445 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632745062 1250 632743812 632743819
    0xa0c02070e04030203160605040605150d2004020703050d0f0e12031f03061d070609271b0212040510030e01091709010314010609051909150806060301050105 69
    0x9003000244031001e507059020b40648162400d10700841e410400030741e0010029900c01d0f4aa40a0200388195841030316000514100710f03085d10402240410314030380f0000e00280c1080d02d4540f4521030499030001c940c01240c80208115030b074680a15014240d50400c2000c40080d900d401e000c54031082003841640076140b4403000a141101c0402d1401c0107645c0300130304104401c602010b4048100000441e12805544100008071303a0714450120a02c95100d805e92801450b401208100400c41c0c11821010903a038248000c00c209941c028108404136612495103101680b400c0c540440c00b94a944800d07050101d140c0c03e0302c1e490345407401e1880d058050b6020316640511040300e0401e40c2ca020781c0c0140030405c1200d002007203c001c0741d1510070074460301d030340b045000040000f104c090715a071600c03480708445070020030a0b0107941001c000504c201407900903903028a025800c25041c1d0125031003860010f0034413400500c44805a0031503480e10f040b43d44901c11261103004007044c000d1506005031416110081d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632746312 1250 632745062 632745073
    0xc040302060f0d06030512070303200406110f070311031219030b010e0405041506120c0b1b0106060c0b0705091e04060911040e060303071a180a030908060a0c02 70
    0x78000300b040342d0002c1070590120b950307180000000342c42409511003e050550704643c80e0900c608024064450040900d03849640884041011004100036070b81507940074946070b0315001d903e030100c910308800d29503090071610800340c00000304070710103480c03425881c0154103540c0d55504040440505010f190805420f8405c20190350321814860340c00803d01c00c405240c50002d0b41c00d81d030007107011108140c0301034807410080d041031400d00b1803074003602004140c44004024000c21a8498500910301402103013845000001c2c880740c0f411554a40c0c84091203104020460649d85500180c55415a0078080311003c00c0c96000810503405401685c84040014280d00e8045800b11180c545190304494029030042d554440440c203255148034070504c0000328150541e849051455800b801e000003001c0341d1180d030040140400060400048151000d1803602c1a501d41c0c071000b45011300d00c01200b00203203945c03040039161000d050784101050203c4040100b5980c0300e8681c0006402910028101d51015034001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632747562 1250 632746312 632746327
    0x70207060804021309030206010e0c041206090c031205031f2d09020a020a020a0807260319081e0112150e06040507091b0c0803090a0b0a090b0c04030206 67
    0xd04032031944180f00400400384000c110130804c08450040700160016802900140840d1900910207500300151000c498102840d00d1040d400d284c80612004286548940600c420802807042c42d8018661000041d40b41f5420342400034425003048468401e1441c4001c1510384040500900800f5030384500e000e00c042598042c075950203002038603a864548607048400046805192019141c0384000382d020b00501007984c010000828207541000c502078000040c10801041d0f0582034019026405403000100c14a140b60507041d40100c1d41000001c0300d0300b01c40600740079842616540300e120114889041c90090301d43c08203020388d00340034404c85100c20910340000700b01010080310a0f1031442d400441e03200c29540e102420321909481c00c40c0c96a0100000f400122050300851a41130180e490040d1080382007200201480300c0080041c1100e00000045500c1c10010b0160b980b0081c1c00012001c0300b41001c01888008112141b01a01c0854034600030946001c4201e048070200d903001001d403401d2089 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632748812 1250 632747562 632747567
    0x70909060f1419120506010b0a0203031605070b0114010809011413060f060f03030206070302092413030b09160e0c0318102007020d031409280b0307020706 68
    0x2030700092540651a40000f600e00641c1c1400340c800361080292081d0200401d140061074601d040e04584591002070024100355a80001604e81c05800d400340380b401e48605420540d22480344000113860400500000705034218001c8201340241d50aa03a101482e548840d880c50890303642c109807490280241c004201600382c00702e2036407151402a0800a01c510440031400226011540300003410746010008106041e0148546580310031182010b5217030202080004160205148100c3c60400010b1100e9a100340b2410035224034813288184480e80c40d07100c4c2049804960f0444840441d8400d8101001c1e845420162101c200c54031907800720300b031382c80381c90081c1e40c5508020302280d244120401d0310041d80a04010103d840000300c54000341c0068005484401d0303001d03a60311003038410810040400140c0701d03a074803281d0791a00b51805040b4481d00740c0c0360802d0b92080c0e1092740c8d4000c460f2800b0920800903140510345054007114486c10322070b92000c800e2a40d0008031040030240e081114100007050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632750062 1250 632748812 632748839
    0xf05091806150414120f060402060d060e0907050a05060a02150405030c0a080702130c02031b030906040b180102010915111c020307020607181406071406070909060f 72
    0x400800300c2280070606140c0030340a403c20b50101c0000901c946904005050080740c8001c04040c00014040c0102508070150341c950020304001d0044400003007912000340b0a91204d07015181c401a4940e90303003044000c0503038880542c041d06200f00c0e0b032400300050368680b540455214034115009040100c441102554817804000c0c42518030740401c1000d204e0101c0b051200360741052103840141d40b201c000b0700501c840075000514000d0101c0c9004880420560000b003075400c480c1c8007054a03a1003404140038030f81103014900304a0b41112021a012400c0b2a22201501d1194240000041ea00c038668004a00b84d4503481c6001c0c100f251407101c2d907103a0a00380d401c040707000300045400c24130303051125129560180094045414643d408024040603544c10f1004540141852500041c0950303445542000ba00303035449111680b10110100ea031307031a01e40300195645240c0004610ba01c1e1210b010443c0e403581d034125801800030b0304100c40480c18803001c1c450113017901ccc2c0c842e02d10390202d810300c0d14005401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632751312 1250 632750062 632750071
    0x6010f0501080a02040302060a091701020f0d090c0f0b120907300c0f140d0b1501140a050c0f2d0316050c2d01030903050c01050c0a0f050918 62
    0x44e800300301c00700243e00d50400400100401e0341e03480c0840344c507040c20180a01108290305400307034010400c5030580441001504d00c00e801c0004001141c1c040e80c50040380c00b0101e030b80040700d136003403c401c0050503c1c00200500580440e0f04415002c6e613a625012684036806c80c080c00c60b0324001031040240071004500c1800c4038643c80019220460f54980f10301d00c0c68040340d071089051001c1c5210034428803407542890608801c0a8540004c07904203540c8416039190000e0804d0b41c0031008003200d90040e807144121900001c43c00f00030303503500c03036451400414640c41800c28004e64455100c4103107006e0000121003420000c0c000184010507503101c185400540e0000400c0c0c00c41c4414080e024200600c51040030946110300c0061004101000c244a0002000c0c007800074114a054480c40003c0d05030551303100c3c4454240780c00201c181040c40c060315217004101c0d0410096180c03034200101102c0050040c0701900302e54a03442002134110100700e545202d1109666000b02c0d000c000420501556480d09402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632752562 1250 632751312 632751331
    0x50c010c1b030e061e1308060906070509040207060203040f0201031b090b07031709151e01050f010323010f0b0901020a03030b040b03030a03140708100315140f060901050306010f050108 81
    0x2011102a45600c401415044000400d5400111700c580220580c06c000000c0030940c020301110310704040895218100100201c05012001034851003a95440c1e044039055540101c0840d00c0b0b0920b070904800b840d0403041c007240403a00d8100c2004c64417400c9035010f6100711070b80d0740b4081d10314180071400500e074000e25001c03003e0080301d4041c0c0044103240700106103e030503444003c026080e10394000e00402c4002402008417071000421a0b010034103200d9070300741274441c02e03140c1d00d40021409004070f0051001301c01c46d81586820030317850a040c441d05040541219100620394541c15126241621213100300c140c814050303448040303048002402500704106468000300006080c01888000c2821a0300070341e040000a42d840188144d104030340f14400360840030600d0110340303074a040b17080c0d40c0303207034485000c00303810202c010008010442564208056601c2c100a4100381c600704800d40385802041503606500c103100c043c0c000b2800d07007000500981207680740c5003405009841d102c010b40b5a054040d121045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632753812 1250 632752562 632752567
    0x1805060603070e040f0e0309011d06180307030f030818010b0105030a0b010905130e01060f0602070608090102161a0a050405190807020909210c03090f0f030d050c010c1b030e06 77
    0x705c0101c0c5202d0312090340b95410241d543c410346000018100c22884940c00203411500035076180617111142594101c2c00c1014240165003400710000e4945050341d0320051480e01c0403039101040660041003039010340404602c011069a03189009400da50f0314510050009805000080b40240c043c2c00c035a640d030b2010304103803000d9522007011074444114001200000303501c40130700160300c080c24802e000c0202030150610700b409091040003511750314280b141c4000c0048050125550103002e504030b0302c103462100c00c03462030343c1d01510f4030800740b0056a10324250390323040d1800604031451501603507100d1170788603002d44110440038408443c420030004040c0c0d0441001e000d00d01c0140c4490000c07500403194000102034064a4030f007035412040c0c00e010b83c0b96060b0010301c1820301001002007034510311501107c1c165a440c1e00c2a005c511882c107105103941d813511819001550346a041402000ca00100400901041070000d8042e51101055a05121401301c680721600110388a1000c51905800c0201103d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632755062 1250 632753812 632753831
    0x3030b0d0209160912020913030207090609090b0f0f01171509100b010c170306061603080123030303041217040309080d1d040504050123011805060603070e04 69
    0x9410503012600385400034029083c180c0c6803500003100400822010300010039051143d400b20320407a0780a0310f1b6280342a90780c40c0306e40c02c260003404808090000000c0c10000e0503950071580703016086194060b01c0112029020840b94915082020306c505a1049443c6480e4a464810f642031007181034000300d0341c042d0510201c0c50721600003600e80520f84039070040c40e40d0340304042c260048880714800e5506004bc080314100009100540501450725001c003c00e44940d1a14003144640c41451201498004900f010904054010703c80d02d06035105003c0340740500a4403655500748243c101b07907840d4194018800140008c01c0c00e9400c6800008a142508607164040b07201c5041c00300a44084002c501c01da1410b00c021031081017031004280507454982d183c0c4030415812410350010b950014040c0d07807500d0008003070010941194023640c03001c5d1605400c43c286014070012401d400c2c018090121100046d10050300c4c02406024003e40c0700500b054610b8450100c01d41e04450003d441030342107515181c265 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632756312 1250 632755062 632755069
    0x60206070f022509050a061508060103230f1f0b130e1006120b06030708041406010f050102070503030f0909040303090204150302010e040c0e1311040602030c1b0d03030b0d02 76
    0x1d007a282c070740401c0f401c901420302c101901030780e60092410841c1460280c00304002d814000300c0000d00c04041c20044650380754800120003900d1080042e443d0060248510761485c0e02c0448014420f2100c41c250700c2440c0ca803050a40519a1031000301c1c18010300c441d0003806403180100c01012182d05121240040c595581c04031400000d0440e20810500b40c558402c00c03496400100c990341503040003808000c1107091000158031800041c01203010003a49a00080c104405040382009011000d811580c1941c2e40702844039070045035000d514014058850006100d0500109031008030305d55825440c140003450060041129000704182c0030036072240d00120141c2c8903880795510802d80e40581c0890785045000150441c0003216031640203928061284909507808120503254003000c4518581c5d0808018000000c7d0040d441120020a07001900041c02500003000308031982c1e4201c02c2e650341040040a01041003c2d500d520b641050202041c0c00002c1d10036840b4500d003040c010117024032040c1e80d8010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632757562 1250 632756312 632756353
    0x40f0213050c0f0a031b02031201090212040b040f0f051608030403050d05090112020406030207030f0509130203071205010f1a0301060f0c14031206010305064509070e010b0301060206070f02 83
    0x800c1c02503040009c00301503895410740002d0250001c0c10b015460041408003c08001d480104042c100f2040c441c0410b080140442222102c10380001e90060700c010942844e5444003048800c0b054501a01000002c80c4c2c1c2c00801681c04503038018020744441c42542e001076850790b00010860707042005000e24102829030030300c050000b6007859600180c1720070395860082c006123000d500074010321500340520501030f600c4028101c40003210240160b141d85407450251401c0426081c21405981403000100300401301c400107004503081104101c080f407808039045a158442030154000044c154191804428000d914801c1c1c40c0d4030030401810000d000f1004103041d5080180039400708048a01440050740c2c0c94041c0b55002035080745c5c0c070a2039007442c4400b07080741d0f01e540260705000703120b00c1000700c0000c6940314840c240882c3d451001015180040e007103600c91f038081c02103210741d803c05000461036402d02c006a034162101500107058070b8651300c2c41981c6c0070300b00804c03d0f421807040c01e11005000544020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632758812 1250 632757562 632757611
    0x20c120705030c06060901230118091512080706051003080a020d12180609020a0314150907050a0b03190c020a11040b0622030803040f0213050c0f0a03 66
    0x50758903002048040380c02e105014001a2046e81c1407001071003c2420760800403440020b209420008002100041c0d0f11440041040d03911503098403000211400036030044520164000072003509240c884814000030301c0006c20140c26a030007031245200107540f076440b00350004050103154250541d00d94500c0700a90012552a00582103112020070700c0e80c04c4203452030440702c6050240415482400609042d40744070350050400b81d20f500e003007003d42d1140c0c80342801540c0c110720310344a07041514a00301e03034500c40c56105005013885070740001c011003404960201582c00050200c40c200740f031b1402d003510641026120000400007003030b42000301e001070311030714001c013010f60060007a02085040544100c0d220b942c0f2940190b06026074600c06907600c0c1c00f100c507503444da1540502a904000320b42442c001554000901d81c95000040c04103211941d03604c00c40c414030844218818851560b08001038541c00d030740312025810244040c40407400c0d40c0c0c01800f554205854005800424001c0020200c0722215 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632760062 1250 632758812 632758823
    0x11103060607050f10020d0c3209150c061b0301090f021b0c0102070e0c0d1e050a0605040b060a020618012301090c021504080d02040305010f0b0f01030c12020c1207 72
    0x7e0000c19001d1036002d2810140c000f0b040460002040150000400032104980100d00a62501468003081640d054400325003020300410590001c40f22450441d60046845054174414a4002004e0307040f8207203002c09403000c104030305066928000c0d0b20b10160210041e1440d14135000c0c42034441c403aa8003985d50001e0702c0f0f000001c06400110a00290a0085941100c040c4032031410410480342c64601c100c810310150200700103809901807007840c01101e58a03500302d5280b401c0c102400440c4085070050700a0318812901001890940030400134241b00c0d0440d4000960400c10000d100e22541c03da054660480316030020a003881c40042007212400c05a640d490075810220051000402901c80c84d10000707c0d0340000d0204a01114801700644001000100088800a01801012842d0301954015a0b000d40240000c0d215103141001900201070114080c502a9071101c03071540c424003603003610f8003140e1108403041d0014101a8003a500c0000b018051b44500c0b01c142000c0c0b03400b0b174010b200c035a0041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632761312 1250 632760062 632760067
    0x2d15022808060f010e0904020105040b130906060c261303030819050108120d0f02030703020a020c010305150405060a0e070f0318021309060605040e0a14011103060607050f1002 77
    0x400000c0d01d441e20252480d401819510000c0c0b48a1340c000110701c448540844080895507114401218107110b44d4100c0e00c541040400c0d011000b961608481c81541c050071801e0021039111907045688011a00c0f000c0d14a110b01c46a0307802d10b0500ca41c5511107070a0f17005c0050300c1c085a20b075403002e00143c50740c000c8000642c5030081007407501034121040740760725a412090100d54035000c260790b40c405403089030921134000011208411105d903404000442c482d0001076403203152000003e4001c3d006010b031400940a0b0a003581542c1d03100b403140a2040c0880d03040101e00c0d0b0708400622006000040c400780d00054000004540c1c000343c412054442c4d103090780d84000176911410000c0c1070326001c608103200d5110500480f8016554a00c40703054004480e00c0005240e009428414050065a480650810b00e41000c44905040104155540314007c641c91507000001051890880d10112580f00504c401840800c9041c0341c41801461076038000c008031a8451003440c401c600740441080a180100d500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632762562 1250 632761312 632761387
    0x1305030412060f0501080c101209061b09030c06030209040b0a0306020307170408090402070602090d151401080309041d0d05190c0203100203090a0b090304032d1502 72
    0x550142c4102501c50f4102444103500d001c5040da81c40c5000740b02644100b841e0039081808034031030202d9844c003030355100c82481480e03201e0a0260080010300b0058540c8510500c0d58000a4080c02c240d07011254000300d03440f07002e413130054200d0094000c1001c041e4807d803288130030a920b59608007644061400b400c40181da03401c211001400c2001488810224801c0701010003000c12420300c06e03207101040695016036228604c1c5001c40091082c44d040c5541300c03001600302d20500c07040180380b80c140d41e060b030390420580401f100c070020845000d102d0306080d90301c05c000940d02030520780c000c0348010b09107034482010554803040160904090854000c0040c1c008900900440340c0da09100c850358196007403984440308180c003c41d444440701204203a15a80000104881030410491080800c0d084070444107142407080720152640d01500c4243d903880944142d0003403403482041d00361074280700d0180511100740d040c0d81708400c6403200051023182c0340d802e010007001070b00406215818504050401d00c6242d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632763812 1250 632762562 632762573
    0x3070b090d020705030712023001090b0a0605210307052e0c08070c0c08030d0e250e040503040f08160906051c0206040b162d0b1305030412 61
    0x5960184d4031030b0340040d400304080b1400c1949120181c0c1c06903110000303111851703040c01d000c60894820a80328100d000e05c0005c420019480110424800c540c00030454551800d1a003e0f03070742d103000f141e500c85203c5d06002c07814600c0000542030661008203607410200300f80c031002d060030044452004510709041d06103504000703c84503c4010700c0e14100030481b80d480450000c00c0003074010042000c2c010725000c078009211070b1011407002081c50310103c075030b030381400c00750000540282090188148501c0d05a104160386e402c10044c0c0003c00301c1312130340da002c2c42d05082c0c00301414003610560b1540010400440e07000110070004014110500c01011840590101d1114902440e40f00344500d03481d0400502190b9140ca81e075182e40102121403000b89551800013400706d01c600c1d0720200f40450b0010b40101d115a10030648218180030b03040f11100402c1c20241032640864100002801c0c1c011400b49000250755002c0d01d40e0000840d44a48140790540d983d62480c40e07000d900810603402903a07044408218 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632765062 1250 632763812 632763823
    0x30e1501061805030d082d09030702120106051f03060e1005030d0e010e13020903060406050612060c030f090f0609030316021b0f0d1a10080d120e03070b090d02 70
    0xa007134000b89140f090700000200010409006c041c01c20130000000c2e00d100c040c40f0001c1c00e642e04081e04c414a00e0030320300f02c51139580d40302800c00ca002e40c05110405040b40c00611a0300b084600180505880c81c0d000e84001648000a801020900d40e9420000c55240c08141c0d596200c0c2c0741c4042c4d0040302a0a010816103016402d180c0d801c100022101c103038090740d03848050a13000700415210318000f0943d110206001c0d0080004e4160544a10410031080c003081c3e070411400754074292025503145424103d0b036601c514040b03450840c0824200049140c901c4d102d05215840307030300311059502a42c20081340b02c7c1403010944814002d40c0c030100501030b924241d0300c421042050b02c1d000030541e491712801e04180c40c00f200010940300f981101000034103515a1121a04541c1c0e100c0c81c4446414080d090858209a050300c0e21300d00c1015000c2c010814601c00950705602da14944c8960440e040c2c80350014014148240741c800b007a0005220180000c0d02400c14a40120107000c06400c40d03640d0504000d00c1c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632766312 1250 632765062 632765069
    0xf150607021f021014010312050408030703081801090f0203011b02060f040302011d0a030201060909030c0f060e03070c050906060a091a070f03050306030607091401030e15010618 78
    0x284410042200165504203802c03000201540d42c0942c944216881a820400c01244e0386400d1410a42c06140400d110680035050720302c00d0554986c90031078032070100d81c94000c90007411003a134810008c0d84c0c003003070240c07560942c02600d0511940680c04040029401e4940d225130807a085251b031014201189020b020384400301c0e12101c1041c1181400d00d000969608010b000380384c012081c40302090034076200b0f420900510701d80100d68007000d0380d81248943c0d210300c9404c0580055182c000702282031840740c040c00816542541d02c00c40b0703d42003621056203c04175084200c4200e6a1064001800360007400900307141402400e01c1c0d08401d1801040c010178040052186100b0038040220251194200302001c041d11002c4a0410403032206081410851040180c050902d0207102811000c06a1140003188140b50a80541e1030507102ca0001341c0740144035008510406c208030320740120652096000d510075035040704c210f80c0d8440807032640006641007030b0084030000c3e111454403400246c5029051005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632767562 1250 632766312 632766319
    0xa02010314090309130e06042418120207031e150b0d1e08030109020a1101050408191b060c1b0f02120a171317071505040e0f15 56
    0x1d0345411035000d40c40384244440c407882105100c5641442e001c4641c810040020b84008540e624102070510460311900c94052841c40229242d4540100c00540115200a40c40585400706482943c1c1c8846a5040441808086110f00c1c0c1002004c100c100c046001d000360a4a01d440754035041d400d11450000c43c040c001070446080030414200707a218200c0703520101e41c0140c070300c1c050308070341c240c0c4a10391000175480a005008080004582802c03664000d003c41c1c0325648404140000030a02d480c01c3e90070448018048000c2400a0b81c000c5d5a2189010040b012a14010030344003003107071003140707030004d4200c05840141e0f44420080c101ca4102401d950032003412904494500d000d9600c00c108586c8281e0000d014400400110060319410030011210341da005c882016240a00e2081032000d4012824090241011040018446001c00025801a007142001d400030b14140504404120307101c070110700800c00d003040001080b10018620340d00410001e2003201c2d03181042076500ca5038200c5071101b14031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632768812 1250 632767562 632767601
    0xb010e150a0305120715021804060611250e400809010903060207060509251e03050706030c090b120f150402071b0602061e04020f060c0a020103 63
    0x20602c00a604c54146288200c01503417401285000d124a4492004501600c0d00104400030400003a1001240041064404201e51556100c003242c21180f811070641e09600080011802d44011107140018001d034190903c1103076950b2540c0c0940008100d6001441c0d51101c18001402990100c411442801c3c92030141c55540601042d08103481540000070110800003464144a034000c0110707000031904408115103c14950821074041c00c0211004040d40c0104240d52005460078412480c894080c0c1d011001d960b414082d080c2c01d0801d1143d0074842411203900c0004c0003420401801c40901701d41e41c3d000c07a10240380800030786000816081041d0304c00d414048040f400402a00c11944074000141e5001c454440003141d403074500405074110f070428000541d000620003c0f510010305400600d04001c02d00740c1d0b401d001c80c0c40b0141600d0f14445c54000c04602040303c0c003020407081d0002d0008150001e1220301d000002c1e95640a00540c0030107410090901066603014840c1e590740445411103910f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632770062 1250 632768812 632768819
    0xf030a0207060e0406051806040c030c0f0c06060e1006030606050f0a0c062a08090a0521090d03121a0f01050a0504030507090e1903080114010c0b010e150a 68
    0xd4594110780101801c110700e00142c61020b540700e170801801883d001e8800d00d10118103610050f0b490408440090143d03041110448038503200b40b107081040300050303580074103035003010340c1c2283ca45003001c03001ea0701240c8403180400c03919060743c5243d00a1000e41740c5142c0d41031400718040e050341c143c2da1000081c813005121865452485804491005906107040d04d400d04191600c0c40007040b412080446c44103145524864040c00d0310303200d80f5455203a44a18046a480c82d4030340342e4075480b040c00201180c01410f880489480b0074400041d5103000c105140381081c608d40c0203e090410046010b4001408034080041e03030301c985c0d2240c0f09408600c5840386040c030758813101040040e150303900302c24100000040ca140101d80b0135416034015545c08019100c00554440d00c0a0251403140d00f520864000c060300d0100d90803204001c0e4000981c10703210b02d8042d80c43c0a40c414000000301104906000b000307501d42c0c00144607a00002d000e041001c84146039402d0513104040800750070410603008440905060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632771312 1250 632770062 632770067
    0xa1a0c0316030e0d090f05090c1204031e0504030c0501020c10080a06050a030503031b070b15060702060a0804110409080d0b0103020903030a020106140604030206090d02040621050f030a 81
    0x140da00c1065041810141c1c001c00904400400007849042e84501800242c1c00c9020b500141e441e080350304200c0c40e400944c0d00c0c0c0b41013081103501550590b4901c442045901c182145c1c0d40042c0d94400e01070308001011807089402e41404800c101441000540b000030180b00b008551072034007006e00381c00e1000f40060f0304214042104041c03c1b603000c07824040b241c0005040b81920ba0040c0000d40700c0508854501903030781c81c2c0300e036603500252034a03560b0b96806400040e103100300d4015a03600300c0e04000d00c4031254035070942250301060ba6060682d00050100520005600e40344004d0440c90640c0e9548107252425080c20086200303040300390f9100b24202021500400c440d14140ca1144869980000b159480800141c00a108401c4e00a815000109801d184a50107500c84012103114144142c10384083d107007000841c1c4111b01000394001c0003402410349500b0011110545d007440588002116a11038030040311500b41c07a03800c800030000c1400804100a018070240034440b9040c4000c5040a2084802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632772562 1250 632771312 632771317
    0x30504030e0d0c1d0939060417100608010b01091a13080f0c1f030b130e24060a0302130908030a0605040c020723130e0a1a0c 55
    0x207480c821400e481e200c00610803150410310040040704406210000c11315000030a50408641c1c2c3c086501a400c500355528400611110340c0f17281c00b0340002c4105d2038070040201c00e0100c40070400d07044601030001058014080c801480c40154103001031004d00e4401c1d005006540b819041440c959044ca400d444243e6004814101502d019203034592011101c0050001c1d0740c080d4120207416203040b5000060f003008041000c40c4151448019100c01403116414056000780e803020007844100d120b102454054421313400004219001072460300e40e090000c032101d0954209c1c4010aa250f0080550883d1900307000c500030550071070000c041d035100d180000004d88001d00610006e40502110002c0301c000b8000c03a13028841141c0e001110783d4481c14520707201c03001000030340039607805140383c100c07440c1d10300b03000161150032a400220030150401c41149040303d49070303050651981002e60301502055444080c09030304140c0559000410703034664141845260b542c0844401c03000840108203001508440104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632773812 1250 632772562 632772587
    0x60c030623120109080721050d0b04181b09090c03020d031823010518060d0b040609200418110903010c0e09010f050d02040b0402040f0b040f0603050403 67
    0x414801041034501103114040c904a42c01065460702c031214007003040303060250452500680c413509003c07a903450030b040c9a4000c2084040851824010324220f074080e50040e03102c1003000b0f0004a801103141c0803415001030741a0089074442c521074410324a1400000c500740003400b07514400c0c0040452502c580540000e54080a40507506007640881410700500c800e401441c4c1c184014540683d031080e0f5041030252144404201c0c101c040c02080d4150710407015142442800303051400d0f0300038200d003040b1040d449144110080341d00c03400b030140d0542d81c40c890007005022403a0081003004802c802540c100c5e000d034401900c6484141300521603503003242c0e04803802001003a8001440e140f1404406614000c560601354150b082c6450f00b0b680725488001c20b600d1f25825101c0d02c000342d80761121290084201e00070540c0001d09a4200d50240c5080d4101c883ca1040240005251a0300c80304408902040742d0020803100000240401c40501001002c000408a0385003c001c103041070344d4002c0c00109141e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632775062 1250 632773812 632773859
    0xf070b0702060a02071a0a03060942030b060a0501050a02120d061703120a02270a090212010617040b070e031f14090d08070c0606150309060c0306 64
    0x1a80f141c030078000c0000388040c150040b11110402e044070068076060340141140000079003450400110394890b03000e8201208850546000140241c41b0303443e01c0d80080020f03400542c440589003011882c500d20410300654010328484c41d1529000040c48220030301c55011a0420101b044805ca205601180c41c19030240e002e407246640e4010225480d0240c06c1310340210b41c4072101c0d600040800c100000080c689007040b806610200c0d640d6421001c00c0303014210b8403120052440260041074071000318504a01c2500074000d5003025103808695049030004e010b003a00650311440103202c41070f005142030302c8001300c4025400c558600741c1d44138552402d0242048003809400e070710340561a03801340002d2020705000380049520300c8074101840302500600c64100f4001407201c010400103070010900f840031182030389458107143c40d00c201c1224180748070f55081e07031150b43d0b40102042000b20303000001846000340d50041024541030511904440d00010083c0515107031041c200034650802410090108458 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632776312 1250 632775062 632775067
    0x4030c0e0901060b0f030105030c010c0b0114031e0a0308090102130b030604021204030305010f08030403080906160615030201110606010f030c1106010e0f07050c030702040216050d0f020f070b070206 87
    0x807580360140150303070041d800c403903004607124169080701d501440c129036040f000c6a440004110045d5035005440c0c0002d072511140b280180310004914042e081e100c50003508540d0400c0d00c00d104104041794484c9500c11030b811085403c800e042c0e001800641004241c4021840d00c0416403840c20300d0755280c441e51105103000b0000940a50ba5075054598030f00306244816103c3c9028540140101424000c10900c113605441c08100001c0010680d030a0f258085940c52502d0b0001c000c00055070003614026003d494400414000100c040c0214019022041d51030320388982144009801700c0000700d298850303035100c181000300c140c1e0300403c0001040454240000d444404c0001241d007502c0c800f074010310034425100002a10000308030b0492041c00706030a03414064032202e40484191180706031080d4075900c280041800340c50554003c0040900c601401d0800c440ea5070341c2c460400b695a8940f60129003a01e0040b102e80da018045011440c00000c081c04140d410300c0103070b07035803401108006402030300c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632777562 1250 632776312 632776321
    0x300f05040308010506160b07050c0d080604060617010320062d090916050c0d0e040e01110301140609090109090302011506091815081e03031b0a12050702030405030106080304030c0e 79
    0x5500b00c030031481964054400c1e99a4042f8050507031907080d62001d004910349000081c006d80700c0c400340100ca118000c003502c0e1592a40e11200030030245501006c042c810341450071800e5a443e000184110701c02c030651f0b441d07681202015820400c0001c007614290314010004014135988000c0c44030f5008030482e400a95902c0c039841d08482a0090051032080d074810b25003004000c80d00922041046101240d090040c00280644582a142091030301c4440c504148010710506880c01460000c0b40740261040c1d0610090300c0007d49400e4082c3d001010b5140d0b103070b41d414207040d0b0a02841c0a0240e08802c062007051500f80000c0441202d032051480c0c540028100108500154000081a01043c0400029951a040d072152600e104540030840808000358403100803c2c0441524850352080c14a0503610040681054050380900c203a5400c022070320b5941d202c100ca0301c0c0304441c0115504d038010341d00c60342454241400c40c0d040f500030945179030040c44104005005445050b06803201140f040c029900c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632778812 1250 632777562 632777567
    0xb040b100f0e04020c0c03060a060b040e1f060e0f030a020a05060f070c1401020f0606060328050106090816030503030606070f0c08031c020a300f05040308010506160b07 74
    0x64124403c0e80a0b000240c6110510b0b4001130380f1300d21107012010f55025403502000d0404403800d0340b107049010709042c401005000c140180d0750707600410380008000081910202c484100d0402c0c0c00040200c0c00f02c840090090038a0710300881203800940080c8040056034000410600291242d18400c900c0010b66041d501d0380d000039680f030745910001c10002c0c1512000094070508a60b980e10740144103c28404000e0040010f509000b40d074060910381c235503265040c034050740d01c015802541191500d001c0c0c04408420910900e402051a40e0310082d01d00d05001019060500c2050204540740d600b080a02c04640e010040300d070445000c85031542d8030700700e501d00301180640401010b894941820000500100044001c10a962107100c1a00680c501402c82008901031410b603071380011002554081844810707140e207004070440700c1918048511450f071880c103032400c02c1c810142d8030b80c462081c8010590861503042c05401e0441c1e01c40d01b05181021241464200454094495a035600214501c0d90 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632780062 1250 632778812 632778827
    0x15060e1509040b150a17010e0106180b0c010b030d030903051b2803120c0f140f131802040b121e090a05070614072003150108010b040b100f 61
    0x2006014104c0c158403421120550307401c00031110707010442c074200c420031104810344042c4c141c44039103c0360344003030b402c10004880401780303299500d6002442c410003003070100c4554041c0444031540707000881c0e0102000141742c10000711030ba0a009040c00c0854050009410100b620040700315980808803072614481e03c146040740d01c040f45049030200d42d103103030a51000c803200100854043d03140d5000d09012000c0410464001c22178100000d5401b508000259120f200740d2110f0613220158103050100c41c40090391668031881c0b401120843d4039400300701c4940c00c01801180c00c05003490450806141818145941c41011000e00300e0f90382c144c0006142c000c00b041c00381c1caa148000b41070202854140d130000d40d5440c0a200507205071040303180c0010781c02c0c8500d0380000da40300c0303000d0903504058042da60f0b400030031008900340d46040620342c0d0004603900c00704002c2004850010501049500d040c3c1541c1c2180d240c2215640138a00700130300f9103501d403038070509541602e01d10302d0851a1160716100456183c3c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632781312 1250 632780062 632780081
    0x915040b0a120e0601060e0d03020705041a03070b030c07082503090905090d120225060c120b10050304020d02090f0601110105040f141603050115060e150904 69
    0x40380046190410958000c0c0c8400c0d04004440d000c110400504000a660340310034401c080001e0b100d080c4400715400e020540d001c0c202c1c0b2900403103500035104c10006060324201c0641c007020b00d44000300388140745070030001c1100528031076030514034600f810601d02c15203204124010303080541c0000e0002c004034038101388201e0f0300112403541d801c0300c2041c5402051a1a103100d000207003810100814110b44e008141440025981d440e02420406000c100b80084d400c0300c2d1190b480d50541099040032800c2c0d1a081c0700300f80303108180c0065001b21059020700200c44250f0300b060300c145090812103036512014040d42820000303052054072540d4074400a106c4012141d8003e401644040520001c1c4204c01412030080a090302c421441c0c1c05100c18407400c0301d00458001d03041c030100318083c0c40842d0a0f00c03100c541300d00505050751000804148440030916040e8002c40c0e8603036464076450800c25002c04031784094101c1d450000c2c414401100051000d401c0014010009a00010742031400e0360390b80d0000148 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632782562 1250 632781312 632781329
    0x80c160e01140307031403090f0402130302120106050402030405010b010f0f090b18030a0311010c2307030302091504060207143d05070501050f04020306070804020102161e150203091504 81
    0x10008a00616607c98102c1d043c40f9008084042c565145481c00e8000e84114260100c01c0c128040c2ca181c01300200c024000800f40c505569600d0040741d01d80340c0380000e5100700e005a0011405240000005109009440c004801c0010308810584281da00c0b40b241c104803800001345c1c907154069828240180702584480541c1071103001c01c1d980030907030441c03078185103041c1c440d0003008112100e020a4510f10752940c1092405c03045400d940300111140005001680c0c042c3c540142029203441c0410300411580e40300540d40c2d500030400b000701070780c104040740291100d020340d240c200740d999000c1204100915036000700c41d00101060303050b14540034249450500300d0710218048413005040640254865201502c1650a19002581804032140070901840d03000e001080103036901c0320100e4034540c0c00f43c0128118059040070301c0403c481c95406c54003070501e10607802e6010042d00d140d503a0741d84080d8425059526114420036038070307801100350341044030103580041d9942c080403082030b582d10558110591 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632783812 1250 632782562 632782583
    0x90f0b090c040e2a01020705060706020d0606170c1c0b121c030b030d091203022d061b030109150510170a0b3109080c160e0114030703 59
    0x1008000144015841e114004103204c010f822682d812182000740d0305560141c2d010001c100880e0809000420140780591401424501008800801e40b00300781d001800040d483c1040081c4501f4a6085c0c60300945134000b8189000041e070389440404074454440c00b039982d43d54040713824a49481240f120020000000d558002d544209944800a0b01582e1440040c0ca40849203609040008501082038155100c045206141250344442d1003040c003002c80860243c0d021450300c2e800c011800002c070001c4151204203401c800704025280c040c004040c240401b050f21064000f11601a007182d054034080100404c0840c2003103420f00340a18154003940d0429041480c075000240d001d8002c400300c00344401c4c0c0c0e07840368441e408023000b5074045400300da41c050f14100c0d01c440c0800744030080c19071b014a512821001d107140034aa403400c443c04180180e92482c8001030407241100d09020751011180da88640345072040c1001040e81c0489014040d501d03000741d00d01d41210f6035560811440000b540d10030301400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632785062 1250 632783812 632783831
    0x150e0d02090a0f050c18011b23011107060b04020702092a070b0f071e030f09050102190207090e1b1809160603020703050a08040204150909020f04090f0b090c04 70
    0x4029a1000c407803056804401300c8a111341f584110140321180c201e1040c0d016000506440f40400302c01031021102c80d0007568140314804000070b0040115245400203000d0f01d03a003540c1402030a50711101c0c500e6104c0c0e441000070000507543d9030100e542000f00c80806140001d41c940540d80d1005c40018140603503c008680f800401031a42039030b0748121400e02c0c1c0b506d682e89500340d00341d5023040ca900341c0c18959600050840c0100e1702c25402498841030000002c218034070340d521460b089910041100041c40d401303414050407250104001d000418440c0000c105689040050644400c800c41c0404001440000724410a0781d504080e05924000c500301007909007405400b00e941d030b01134881300d100d21800020001907094028801c1d10841501500c3e058600340001100715042080104200d81c400e03624800f85a03d6451036034bc0602404401e1000203500c41a40100031020710166800c074480c1d42491900000030f6564010316a036140c1c8401c03c01c0c03058a814501900b01442c890283d90090725202041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632786312 1250 632785062 632785081
    0x2030a0e030102132d0803030a090c0e1e0117030a030b0a09020f031b1603180b0307020f060a151802071709040f05040209060d03030e07080601150e0d02090a0f05 71
    0x241041803001e85080203000c07909200c3c002c017038418030034131340a508140001480b41c0d209802240d0302503c941c545001062301c1d551108241ca40603142c010862044001c5103c80d603a000d00c1d00c5016143e000180540180f490301034070ba40b0f100b031089110400d600c032043c1c0190b94a840030003401500c031600c010342d20786100700d1028006400840e000044c0301425607030b044044d0745038422903240c205a0840b40c02100c074941c0301911a8a524a00f05001d0350740b80c01c0000301c1c09103200285000c3c100c1980940028400031b80c1c0e2358644040906541121894008e08018100307042141c001151201d1085088003d03504075144000e00840c803028062400c3d030411812a42c1c00d44004110200b0b003228104840350400d98403400704c40341107400035007190300f00004c20340c00d14010f041100300d40c1c0701e4a000300c1d846808458035030400000b5402401c441d88080014048020a030038920301d01c40c50f62170000398410341c00340000d50408507100068090416840030030340587d000d4102850013040020244000c2c00c244050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632787562 1250 632786312 632786339
    0xc010f061508130305070b070e09040302060601030b0315040611070f0c03020913020a030b0603030714010b120f12030627071806021b030a0c0b0904050a0c02030a0e03010213 76
    0x100d00000e10402c0c00142400c811100c0a1a03490b010f640305414000d583d541c014045901030b15282c2403001400216a0507910115003c0c85544264003030001810540009416104260043d034425048503110034040901d00421030f0b032042c0c0158002c150350300b1406420341e4034400c440001e4000d02c41080f11500f40715104401c80c00701ca101756400103556032540c1011282d11110f0400a500c25003940080010845541050303421042c01402d40c0d10381007080e0b1b10320025003e41c4400754201e9445990103135881c54010103032031690b00c050024040c0c0080f0306890548549900b245e00e511800c01001156054890500f0b41c510080001812000c01011410070300241070b040710488005215407610000e99440c51902c98100c0d09a0b0300244201d450321072200d8a203100d00540b09405118443d000d90115841d00741400091041c286001c0d50350141c002440181c500040407612900e0401c40e2100440b5400802c4880501072403078581500a140c6001038064480c1074048509034940c190042483d4034121b20703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632788812 1250 632787562 632787599
    0x212f03030f0420030a030f1214011703030c0301290d0f0621150e03070b04063602041407030c090f0506070305070602120f040b0601230c010f06 63
    0x30002c1d6110700052816140492100c01984c041c1c0200f103403000024083d400c80c20100c00141002042440202000c004031424600440c045185070001040003130b940c0410340f500d48a256029500d10320b032001094003c1d10041c40307000c03802102c0cdc1780100503180000740004c0c030112603001d0b410b944850520802d80036003480d814658415103404000100310228003c01d20840c2462034215200c5082c2d51150742400441c2c0400312803068032440e480c09111400d0000f06081d41c8070301c071800e00a041605049003100c64110900801c2078400140750103200150026004011041d0100300f407054036840818083c24409043c010700140610500c007034030742c040e04225044501a0f407218000d0350b4520051341288064480c05070003103010401900032030f20580040c199503000e1a409850310702c00c0030280c2821901200c20300004500d40052004010303000b00c03800c0c0c00c0785c4241b130030b81c03826042079a06004484851034030014038180041c581e6000102134000340b904503001e40702000070994407072503400380b60034404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632790062 1250 632788812 632788823
    0x11215180615240c0503070302011b080c03060d0f0f030201050105240405010807090b040b2104020a0b2505030a081f0b070309031e212f03030f04 64
    0xe000c1100b010b184820320112140300d00004880506400c00210642c20101e200c02005090052440490b03010801000c03d41d2280c1c1c0002000a140c0c884d102000c66404400820480c3c43c90520942e580703410705072600070310104c0310715211034100c0c45c1140c0c600400c0480208940f0350540d004042c0768040d4000c038122002603402c103001000c0d0180c0707c45c0e0410011286404000140414001544550311039540326034107051400c0c03282c0e02e034100340c1e40c0798016034801030141400240d038880c0c0f030b5041503401c070704518003e5411301c0b00e0a0507400120404054022542c01c10030100d817003240485890380c41c20700ba401705a5480b40303402d40350400070307200c1d4422180d400102d0f042d00c010808460402d4040182c040b030005480c0e02842c1042802e9255500084040d0100101300001002282003000912440400140740d400b82402e03d00d05050cc0b0105c40140c02801c62980003041040c5410610164403150f9a0280f10540003110b180c003040b02c424014179000c280310101c00c0048203600074010a00460140317 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632791312 1250 632790062 632790071
    0xb0604090218070f03020a020616090315020309100e0c0103050406020d06080c1c02030d0806030a0c0801021e18221409060912040303030c110613021c0206030112151806 74
    0x10609a061f0310543d201100143d00c04000544501080410040c0410544c07401c440e0040d902d80700c2400300035282c42d078822111380c00800c0c0001030504001103800404004070901c030000c142104541c8807041000840c5c145178940b0300050070860198100c038600380d1080e07420420a42c5546c4c51960b90300140140600a0f500000004001405120750000c05540200100f0700041c4010044405a4000e80000d41620030000390400040c0c803421214040c1400303000041e02c8800040b28404c3c20007200c2d801c0300c06401c0800074003080c0002007680c020818402e50710007000880f000b1403107492640c031401d0814640d01c1e01e0b18980e44010788241d524011201c4000700ca100352104240b981e141d40b40414100d032008410082000064007a8024036088042410041e1480004a10450900b001100d080d407130f08213100e118004610b410014107500c11820403190f0170311481540482c600d0722042c02840c3c1170b41c2d0450201c00070410360042c05a8240d034032a1061001c02c020888400c1c46650190048a50a003170 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632792562 1250 632791312 632791337
    0x1305100302040303021b0907051e0a26240f04050a0504021201020a0f0c050f010c0206100b030c070f24051e0405060a020d0608070f090b0105160b060409021807 70
    0xc00c0740c0d41d006c44100078103004035521a1075054038254441184d8800000741441046001d101c4070b0050b019070031041e21984020365400c0202d400c4290910588003241c20300600b84904440746080d4900141030070349880008060b0103000401d015242003440e0390060424041140c1022941c011a01417842a14055a42d81e10050103c0c00e0380070300003048000038010404404060f00c5409213000b51800f840590310548111507075942507540c8201810b001d0f90100003440f0303010303590703607421070042c2000c480c064103609080c0745d0018140300d40300c0007034642c00031580201e003402000340450f000000c0810415201c000210000d02c083c4c03208480000d80f4854040b90f008115121f90921880380750b21038042c1443d541e4079040d0307a0003900300d48010b5102954440011402c0c4034104080400b410102d00d02c2614189005180c000359071401195030704000c0148038100900b4042e61005440715405100c001030f9036941ca0118000f80105040070f035100b80414280309010f40400030341806a142591030341325281c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632793812 1250 632792562 632792593
    0x120411040b030312040b1504020c011e091a06010201061706010503150618040507090603030e10110a24020d0b032112040c0306020f0a020c090417130510030204030302 73
    0xd00c91521001113030302030014000646002c1d41e1503002082150098038075480c3c00105040382c109002c00100c0303039911608444004942c000e580040d00e100740c0280000d0546968990101510742d00d160711071504140490300707a078000e4108101030000b40c81c0045512003000c9074180d640c8028441c01d40640624030303046d6207842031030132054450311010341900c0494404294860603408001d100341ca490198880102e800742103409910000c0d4004e9640310318403511282045100e0010000310014000f0810403016002c40106148a201e40c004103450b40644015092604181550061001c054400a98030300c4800682d8402050a2401c0c1c003150000d12191030b42000041d08240140305000e4140140e00344000d1010140754403610800c0200c100941e01e594a001703a81100d07030600b41903140441c1a8240980c1000100c1d1100411190707040b03a41015140d2a105000c00c54240301086400101800e94203640d080d40c10007404003410050860603098401070080d0850b000480050148000071102c0e030301c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632795062 1250 632793812 632793817
    0x250302040b0f0304060b0303040f030b0a0b030a0b0705040e0f09160f18020909040b06030d0219141f0e010e2b02070b0c060109060b03040f0611120411040b0303 70
    0xc003401445807401400744803030740b12034000600071540162910051155520140b0142004103003a003e241d9215081d80303003c40e2010320060405030110701d80300300c0002c1a0340004003010003940017042c0c007035540c0344d00703030111a01c0c800c40e000540c1061010b800e02011620f40380707107980324815000c142d41e011001e15508410500c0c15110300220b9402100e024000d0760001c400004810864000c0145006082c0c00420301942c41180c0030307102c0c80284020801242400d010000c450f1a4520140c15050146a00c20200a4085002800c0d40032410760f02c10841d01e0400a400c5000c0402e140c40c2c1681020b104c07044040d0518403d01e842c1542006140b0360269400030342c5140d6200006070805070a43d00782c200e0030300801317198103010071441240b50014040f1840b070010541c1813000c801424035503043c0241d80f000d6885650181008040400030040400e010340c1e402c0000c9503000001040e401081d1000c07101d280a40401c1c1c261424204040c0402c0015116403046005015103080c81040d071071b42c08154490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632796312 1250 632795062 632795069
    0x30807030c020a02150424031d10150302091503010e0d08040602070302010b0a08150c03130609080f27010e010c030e0301110d0b01030f02041d090307050625030204 72
    0x140d1222035103d0040c079040741d601007060a1004820f0800c1e60710403a002209440e2401c004610000400040080750302d80521041d041300106a03400c40300301e40d20400e03618203100301c1c2c401c005a500d12404581c0004401da2a004680051400d0098242003035000d00020902c40321a209601e4554440345040001c42c01035480341185d140c06049540795221240694045001142195610406070a282d42c41403d50703000b62a00000a02101140006031110200050031400400c0c4c424020407001c8180e10600c0541154440004100404240340c412524016048a4075940e000410480c0255050254403100d066400c10030031040d02c00032006603011104041141c1c009004c0b50300400202e802029400303201600600000356039604111000056040603015000194940504c0340c0c0a41c0d05008030032110241704002c518203841d1600801c00c4c40d607200c54141912300000c00003104800180705540703100350020705480ca03500e005074640e00242002c210210344510108074240403144030380309a9095 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632797562 1250 632796312 632796317
    0x6062c0a18020402070f0605040305030403020f01050c0301031e06020a0327211b140606030607050417071d0108190827130b01030f0b0904020d021219030807030c 71
    0x7040e91540901002e54000300d020b0b40c040700c8046125000900511440307100e00d00982d903c40d01d030700b0645002418090240032040c003ea0600e014801101e02a008507411070340d0080310200340c0c0141f07106804500b240224054020351021520112580c0c058000d50002481015074110380d0310078411010f54094015405000304214900071032804285003c1c002c9542c000d820702c8400c0142460031050344804a820480b003400a412226611840420007140c000c0b00450141100703192207600140580154828060300c80d43d40c4803100d51380c20742070140401070220012152040c0020655a020aa4003882030b143c2511508a00e2440d1081241c1061409988030601c1417400390003010900c492404029203510000c400d1010001d070342d40c2c2218841c2c4407911484007003422010400094200c1c0c41c0748221105490030f2121524503603036400349296103c1da041307840450982c95400810340c108880e11300d0000912503500e030554500400344250311a60301c6980c50301c0302503035900d00c11000d450039080b86101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632798812 1250 632797562 632797601
    0x150c150e0105070215130209270a060c020f0d18050303132405070215091305040611090120191407050607110114160309050a0b120109020706062c0a 65
    0x42c5050003980750000c042447d0441c1d080030401070814038045030038a92149c1ea112680d001c041145901400c401400700c1c1c0041c0c0068010f28a00a841c0c5a800302080c1c01c0003c410001c403403550012020303401801011301120380b60300c070803101d808112010703029800002048151059160006800d030001200c0c10395038540c1812440d5080c40301070f01c40c001c6c81001d03401040c000d460060f118200f500e1400c48031103c000c51541000d0a01c0b0045070f0410b03860340c04000040100d010035036003010b01070305400460040d1400014410110a05118640d1440c00d41029203402c08801c1c00300707010b5111703071508000094401560b664010400944900840203003a89400025803032158050004540c0011014a00500e000b21609222110310036483d42200030506101040c8040c0c10a2044000039003968071000d403606040310f80380c0322099014842c0f081411b40000707a41003004502d40002703000304010003a407130344081c03240104e2035104030903580c001c010302110000408000c045e010b00c15600003800c80803d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632800062 1250 632798812 632798851
    0x804092d0e1c0c02091504060f050f06030a0b030715020c030c010e060c01061e06090909020303090d050316121112220b03090d1404150c150e0105070215 67
    0x80c0341000d10500c0b402403040c0410f405016843d42c040d0603104800854005401c41c2002081204071041904a04c007010400281401192074031050100350707000846440391256520f00c0c014025144103111140c00d4042c180c1d0001d401c000c282c1038041e81c1d08003a003c0d05c0b12100e103141416582c0c817803044114001440c1c9a00901e40e800c00c3e4004049001d01c0b00c0001c1440743d2520036511240c0454030024274980b540760010412198030144020140803007401c11b0008500580010381d5900908030007502c990400c0880e201000010001c84d840c0501140490403403841e0360400c000103039480300b001c0000c00c54800092100500c04190f50b15000b82c8036003d02e017084e024490701c400c01c000d05000e180740080480008650912120702961003401040010320910348451002000246480c2d1001c401c0c92040c40184001000d071141c4c4600290145044e0640b03c40c981060905140c402045001d102d1030030298000c982c10640045205400c03603002c0f100c140c1411680c1c20b01c149800c0704c2040c1c00c0c00d0341c0500311 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632801312 1250 632800062 632800093
    0x50a0320010b060922110a090b070f110a18060302120f06040803100b0408030a030b060705030706020d110a0c02120a03170414030d0b0414010308070209040804092d0e 73
    0x4d0516841700c0c03021100380b20300c1824040c00c99089038a660f00c5503001040100044d40d000031904050641c7c01d000e0b82c1049880d60314409404114040100711100c00200c5e03007116103a0ba0b44040051010b4002101d8070104080f0b1350000300014041070340070b6103900d0a000400040040c1c403201149510008121654403a04e41160681010300307950b10514013a48001200e41c00c0c2c9018202404da04e030080d595800042001504540c0f03002d000b00d018150600000000c50004419143d400d0781043c07025030b4600141001d2030040224200140781ca100204080300200c0e8000327400032903035200f940c0000b1078240c0c084103542c0e52241401c000700000e821b80c0c2e100802210b0071808640140c41070715484101d0304001c1d0484c1c00c40d0070024002410583e038000e007417040d10f81401050080c844545842d003445d415611402010300c200320300039014894400102e4100081c0c00c00300c1300146000c4034104940d02c40f409078219013614100c03541107107410b4120600481e40640c4505181c02d000040184000030059045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632802562 1250 632801312 632801329
    0x182f19050423040b030a0516060903080a050307090b04080c120616110a0804150e010c021302160b0114031e0a03081009110705010c0905030606010c0609050a0320010b0609 75
    0x14035822503200c40840b038039070310200040e01e1b500b032064000d44604003400d052000003409541c00603042140c40c89003000070500754011611484058a0492b41ea03548406d0240ca040003540d00c01f48548100040004900502240e1002d450343c00f212903491010340c0810466039000103440c0d8204031542c8444a040d141e005500341c1c02d6940b95201a110381080750348855019030450750140e010004003a80070030700c49a00c111800c2110209081c4494040c80a80104103000c9946c103218105070b6001851214000000c1411404290b00014510203582c60390411500c0402409034280240b00b0045441440040c142801520381180c0d401050380103496102103451540c0500481450324a040c404100141306001d000e00b03100109886a581d03019a282c50303801c5803502c094040c00c001c11200180482e5402080d016007006007403800d201107800c203003807007002040a000001e05600c10305514804040d044150300903c1c00d06005100904a0b0241e003c600740c031900b90382c1c03640c0075000b0030080c0d00030300d0032856 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632803812 1250 632802562 632802629
    0xd0c1a01182003040308070906050c03040e0a0915270f060b0105070615032906040c03060803040e0103060e0a1110170f04020910182f190504 62
    0x5050142c0b0078110504030702e034015182900041c608408004141d500720301c4407402417030310386081032912844e445002d49070b00941c050f5003803c10b036100110f68600c0c1d50390040c100140d0003884032a00c00c501c20790500e0040c0484130105070f264084103540c60b8101010b48a0050098100c9103006494000ea0f03103007401003001502450600c03000703110880214209220302c61700d18880c0d0001428a80c04c50034100244004140c00b4101c1042d03401400081805e8510002c1e0009000d90b804140e0203070800050300030f0700c02504922958400400d00003503c06030000340c41d040b2400341504010140b82645140d031507960810f405042020007038103c0301c1e641802da80211411569143c010202c110148112444803c00d41e80f00402803006020720095240164900b50000403c0c504169010729205c918030340c400c00016800c90315590341c0c800c1c8000d03040c0011200c2e260381000340316030813a0132801d03440d00301a00194400a0640c140c0f40514080d00c2c0980c0c02c43d402e480ca10589801141410300105028082595 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632805062 1250 632803812 632803841
    0x1b06050402061e040503010506040b10080c09031f051003051c0e13021c0b03071232010609021804050619140f040b0a0510050405030d0c1a0118 63
    0x8140d44030f07503c25800500c20f50031200006030b80c0b985402c04150075200054405403056140c0002c262141e80d0b14460044900441c1c01e01c10b0756641d5148001109005007040300b600360183c0030113900c00c040d4841184000b50020382040050b0f4848070300e04121507085000042c00c5500181079070007180748404241ca403401852a03d402c11594030380101c0d9125010b103104500356600407a2002e10203c07554001c805d113030001c010403c1090340e2000000d80d280f40030b2244102c0180d13600020720a114803400c0059031843d1508034040703200b160700303a82c183c82c121103d034201075940390034004100c0010900890701080d04104403c040c0300000c0d410000104000b400865000d82514030982050380609104e9004180b048201d4016a0001043c40248003400303036554403851a001030741d0f102e03955149042003621305c2035445070300c80f52814900741c4880c030032078100d280d00d8407814525480b450f500078101c49411b4821010341c4521500000c15040030030342802505800f44d0800c01c01100c00351560701c45103404500c071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632806312 1250 632805062 632805067
    0x1021e030f04090e1e06070f140313050609030705030901050a020307060603080a090503120301090c1b0b0403090b030f0c13090908030a060501020708031c06170105161b0605040206 79
    0x80303a00380e51503441030b440a080503464480440614000307004000d100d44a80880ca10031704070b540c400c2c58a540000306000305010a1440886800d403141c040f56084441d074010040c1e50341401c450913805100e0529046541e4070400c1c0008400c010040103030340107507610000845c00d01443c60015220354210740c034803404600c414000b40000c103445020340340045000e44a41a5140c450b034000030038080b0b668215901940c000810b00c1500c0c0d841b5012281101d580c078400185030f242510048400c40280c544905812800808080c00d1000003c10b440c01640300e0b40300d10100603640d0785040c003940011224219940e0748100020f50000c00381000700310b0904042d0401d00ca042d00c0b582503c084840d20384060f255010b0120401012100a10500015003800d000404174549051001035983c4550324101c0c0070507100700705803600010070703030003950240c84420748000021221480450003032208941d24140e0304c03009600301c407986010302d0490040b00e007064801d085090060301d81c0700151078060012a00314008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632807562 1250 632806312 632806327
    0xb0f092e050408090d0c091a010e0907030221070314130201080a1d011505030102070803040602090d06020a020c030d0f0e0d0804050d050703140d0e0907030b09310201021e03 76
    0x4e400307101c0e0419200f0a00c01b00d9043c100a50b14007100d420800034002e0000d8a07640382c0c4143c0c0c1016040c188080222110f83d055030310700d0f00480280c01450b540300440000f500304400407000900d02170b1320800441d5020030404420704180355600009480a40a444400b5040f9000d548504409a070241c40124045000c80c203041d425640c608010215400c00e964400020101c00c05c4d1640c0c240050408400035402c0c1241038603031000b1813002410061159500068414580c0c40b101c2180328450b400044c115200c01c226400691107a1020b81410302ca401361014a04c0800d0144540003244842950b611002608030414003080000e03442064a401000f8000040c043c0e803800096608140f0500203010301c1450b41c40c5c030904e228064007402c3e1890b080b0b030b80d07082b4209600441c0003980640494441c003854a482d40c0c1070b001030010b03601564211040608000d1505481c29003a0058079620802190008a030024500421000030700240142c0080070f0110002040f030681403540d01c014400e60f4a00010f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632808812 1250 632807562 632807569
    0x6110c0a0801090302060f090606060a020127020f22090c0f030c050907050f07230a0c080c0a080c12150403171f0315090b0f092e05040809 61
    0x480781d200001c103039115003601040590510416407c8217031903050310500e00b0201000750311103200900d04e074001c220204500142314400d400240604101e1301145000502c8c00550140040a80400380e005004415421529041102c07110410102840704400d490460081050103032404020540d01d90403080d001140003540300e074000c030046100340a003c0c0e03458030b42024411243d200811160900c038090041c9401800002c0c2169030060f4014640c420f80069141c5828601c4100010035030144600b0214804010b400d541e40820b44010a04403a14550724508105003036a1078002d240844c6c1100c1405500c80c180504100c4050005074146c900310003002c520340c14450750440342a80060084000c0060744882c1501440d00700e03450306007103503c5416031801501c000f840da02c00140147c0003526614001c3d040d90703100c11012507109018000a082148142101c480b084e20000c9450154451405031030184081080390300380d80080240040440c494a000244001442981c070a1320030405001c82d5034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632810062 1250 632808812 632808829
    0x40908030108010c0f080f22140f100204060e091e0408070b0601080c19030204170f150f0f090309210d081314070f17060609010b0406110c 61
    0xd002c4000140e10003800200408141d50103162000303020341a024000302c040348426460b0304c0340d01c0d0a10307145281500c00000c000c1079040304000e40507490b0201c80351642000800c1c01d060386042c0c40225188142c0d07030380700c0d0000c038817a6119030f00115100308508501c50904081c0d903607000003951004080d05042014049181004950403100071100092481c200000c40c84010780004080ca80340440d450b20102800c4507118203001018500700107007000021600ca50100c502030003416042e031900400a800d00c0c0e0792410210009011409544040c0215080340080d0a03c1000110340d204016102c860040050602c05040b05802d40020485003005440d101040681070b4007035169094021240120343c0d041c243c0f200750601c200a0548280845030140040025203180c02c0b1071070030103000702c00f41001d203001d20340d5005048000300b1980c005209162400f0100c40d000101042c0e8403269203000070446210341c03d0042140b040c0060009200300c070700c6080d031014001c0a41d42121120760003400080c0d0420b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632811312 1250 632810062 632810069
    0xc1d120738042301050a032406020c0310050603070510021002030c04081501230307030c0305150702010207080f2508091002010b0307090c20280f060b0409080301 71
    0x380d03000500700701c50100c0f4180703050283c001d256a03241210409000070302900c6a02090010940c503801014441841040b1011144802802405809603214006512210310302c04d114464061055010013104090140500c1030340001d0150100604013010024844244203801045101e02e80404051031843e00c01140201020305034031380c9035450725030300b2440c00041025880820b14070f10010081d40222401c0030340e103011000d00640d032805540012900e4144550f00c003400f1403103400d600005100010901c40c203021140030101a481c1d484c000305900781e02c9102001840000d040020300c10b03007d080d101a004403100e800c1400000a8004500075401079000815140c0d680b002501c0070003480c1601d81003222490600007840401d0325400087c4c0c0710021881594611502d8003d01c603685e51185c0c86810f02807014410030140e24100140309070b5213004406001031080c800079103816902811118100741590701001c5c4988801c00c6554600241550780c0001c0c0c2c000e6202c5404a0010304d04402a40c040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632812562 1250 632811312 632811419
    0x408070e060f030a050705062b090308010602060103050601051003110c010c180e010b0a0e030a030e040605010903080a0e010e04060602030316090b0d0911040c1d1207 73
    0x5a0900d2800c12540ca070060140c10700c07035070000c501301d00000e50100d0840102d4074100c0310f07691549542048604c140f5a42840c034400c0018902802070b0600259004100c00350280d42c820107641e80340d09040c0d94910082c040900298000310040160385031007024030b0410011890089041c00c0d4603a0070407040c0c0c014030740c3c960303031651601d0030b6049440e030100180c100340f104500c05011651030b040d1218500300040c0100360602c1800100303541c01a0081d02030031520075018080381c0412210341001403604807428103440c4a6420700d00001251741c81021880c06407030300408224502405210241d5072132100d1144241402040075164843d44c2c0c0394840c3c40010080b64010319034a00d000d01600941c881c800c000f03c2d0500511000511110203c182501d1090316040d000040c00a1181090b40c04090390000781d03a0300c2030521114080c90350384800d2888150000b80c0d6210a50180d03070007040136001d40b030786610440c0e601081c0b0030070903083c0b4a03500e00c400c01d00c0c045400308215586600c4590300010140b08480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632813812 1250 632812562 632812589
    0x705070b090a150203070c0204020d1419140403120905011b0908010b04020310051e0607080405270a090c0b04031b0906053f0f0c0603090606060708040807 68
    0x9000c80c443c0071401003064180110303d10310300400040e142c0802c4000182c01a5400300340130f0001f20380ca0b4841e144400c01c0c0301244501c1d2409000503500c112520800c82102410084c030802e20711318004a080c0260717416241c094410130800d00c44001420010016074696488503104400d41003500034000c1081115610004010b0030903844509507803c0000f030a003e0380c410400c21001c7c0c10018600c1080d07460449095440d4002c40c008104103224038039003281c3c054400200a000c100c0d64100901c00c80b602503d00c5844040c01042550250305003585e030107103201849001508480301540801b8105101d03403960fa0070705480350b0540c3c0c06508190000c940e826034100c4942d000079511000017000b001c4401d801c0c0a4a0300f020081a14041506800004120102c04e1003004403000380080008010303420007030700c41030341e212040f0350b075040901d40007038480c000d0001c007100341c0c14240d048070b120b0080e10000345899121103080c031240c0e031701101084d00e1410f03081c0004280700c14107000d11001004103502420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632815062 1250 632813812 632813833
    0x5010621021b34090213080601080a030908011404060506040f0504050c04050c0a1e030605060a02070f0611120307020c0303031e060a030515040c050d05031e070314030705070b09 78
    0x111030041010036000010403034503508040100e00009000c0d44c00a10025890b0303d44864541400c0400307820010280c0200400462120300c002070f02c0c201c250090b9103001d07119645812007403c8856255407c0340c0410800005408900240c00458000b0405400041c480c00040100b40480c5c1c1c2c103a40444041d000303040420090328141c06000d800c100e60b603c003140307840020800500710b081e0300700060349a04114135840104501031303031082d4010300024000c20b070754a11a503002501c1d4074150103588038500c203070340012400394819004006c5c4628004001d25040b0789181c1d8030711294000500c072504510034070f12140415182800031f540540910041465403030710380e012200161000914481c01281504802c00c04904001210400149140d0141c00c00f0b880d00e040901d45080550003031900809007800900801000200170111584915050080d00110640ca09550f00c148540500081c074211102c0b2614001d580c0110740200c11800c141346002e0740340d5207101111078125210003081d0089140070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632816312 1250 632815062 632815093
    0x6090a0c1103040603090c08030a1b020a0302090a0f1a0a0e063d05030f070c020d050102040b0a020f16030b131514060307030b180a0b0a06170105010621021b 69
    0x208046c1160401450410f0300103240140b042041080411000d404203d0040039501c406030f0dd5030296402510040d8585042e59070900070f07155502e0051051480c1000c0c642001d10031035498144d07500000c281340802441c144113005e200da40034100c00d0b40a0105d03150f5014403204960581034a843c04003400e40000040101d41c0840d2504203054400d00400700f0810076448610101241e2108040c149a040c010f194004a4920404005d000f0200d41c400580410802d0a50014145400040d4201c2d4010392005181940303030300e0003010801580000f4201803001401424400750700c03034510703441900b644541c2d4070f40c07074042070704070001c41004c0d9035034149000c4001404054543c803650076030040c0b508910b10b03500c0c0300c0d0394140180310315003020701141021080c1200b4442e54058070741050030903c0a0a1402c1c20b103000701454401c0c840043c0040c0050401c00030103024203412628144c40710341e0b25181d0400d0803041203064a00d455000d65007002801031150500c01281460b5a120000f0003407801d480440707 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632817562 1250 632816312 632816333
    0x30a0c0210020f0904020a020109060c18050102030903060a020a3b01050315100507051501081e0303011e17010501090b120304052815020105010e06090a0c110304060309 74
    0x220300841d801040607244181142c0d04807100d15400740c9006139a03d48085081b4010451070340d00134001410150b90050540d37028080d2803005100c45941c005243e07465005994038880d0b101e00c2c44d0550000c00010703641c3d004540c0075003040c070564200496905180c1d103040800409165941110080340b022110310301c0711b0343c21215080c40080c00c101d407942c00d2a8045040428202d125075100b00c000c1041581d8640c4107000740d480c103950040841c0c42400c1400d5210002d2402401218031601c50146400060300c010320040d051449050041c6141d41d0906030380c00408584034851600e45000310b040002c2501c8038000211306002d4010001034994100b444100c25203a140716414415a42640c0400b004040802202c0855404603440d0070300b1000c100101c158100622071840d06101500300000d051411002d014203a80b400d42d0007004070340e0300d89060018400c0d094861035086040c2e800010f44260003039000426600150506440900701c0400591941c1d005030041c0300003903103c080003020400c80d01030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632818812 1250 632817562 632817583
    0x1a12030705161409060418050c0f150a0f020a120305100807050a051e030a1a060406150503060d050f0d091d22060203010312110706050d1a0402030a0c02 67
    0x100307103560b6450a000c40d01d400c1408100a84224525808100305070398a500a425900d41d08070126910b400d00e00b825510f8040e0046814003801441145028506e0507a64008112030f034081301c6400c0c90601d00302100d608038420341502c02c0d407083e004c619021803030340850b60000c610079680102d10b500d0849904400200c50b903100480a0b80140d009100355943c2d42008001c2c2d820545044048100c804045284020048102900b5000346510300c0244200300c0c0c1c005a201d03511a030075020703d4843c041403000b240c8007441490b00800d1203081c01c1000314481ca00031908524020103800e244006030300c5060038128070b40360070341c3c042d40508220000b42d50080580c8004104840031003500000c00a0b1130b140409000b05210440320144134485402201c0c14406868241c00a100f103440c0d685a10f000102108844ca100001c01d04150001145d403400045207820b450755991181d0034603104040703030000f41450f60148411041001051350068440381301030740c400c804811001c11826001040030313080c0f455032903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632820062 1250 632818812 632818843
    0x4050312070203160803030c090402071203200924070c060e010908011e0b1309050102270d1104090204180201090b0f040b07030c020607060608071d04061a12030705 72
    0x1303010048070b030300070042d290300400b030a8805684502e0800050001e10034418020012211040d4958001340d055020502d8501030804020140c0910a0391216a01801290547c00704038840c140c2c3c00041340c14154045218112a413508004c4540c0c2c429140c1e0380c0700d401c480c0020304003880c066071a40c2d1141c400c030001d12800c4004c00c400050f058400c01080710004444030382649075594402c2d140c8a801031103d40c084803040c10042e03d0740c0381c030345203020394458611052082040c40b68500b800710701004001c41c140d0018001a000c0c0507959620041c100c1c15003050f40d0007541c1d0108000543c980d8002e003002c209107880c00103600c1e001440054070340d200716040402d054400740b040c000c850078180210f80c15501c4141c1c1003501d600c1646011110060010f50003074101c000480e003d03080140a030410010f60380d10034240d41540741c540d00d140440e988981203a03a0103c0302034010801103141c550000c404811100c05132901d1040070004500c9540910011420340e40c00050f204050103018001015400f0191 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 632821312 1250 632820062 632820103
    0x103171c1a0a1a040504090305070c0b03010609052e11010204170f01060e0408070503270a051903060f0605040c0809191203152c0f010e0408030702010204050312070203 74
    0x40d85200f4a0049000795400303a5030740c000d00c10a00d4091410384405640c060070b1785c45143d031507401c00c09503038000b0b02c190000328040400c046040d18003c00c080d410307014154400040c041400707803514402c0c09903242c40030500401d2003403c02c030b0600a000074005043c40b105850811140746500a2502d02c1070154030680d0707454002c0c248807001c030080a030b0380c005410000703850300d400c2541446810b52254090031012119655000342460010303807a51180c03007800302d03201e0745010358810074882c0000600d81c00c900c010b4041c030010320000e8001c0d80712030380c0280e08520015a07240c50718045421a00e00b114004045502c2c501040b405e040c2c20005940742031128022144d001e510f90382c0d0002c4c908450013500301419100c02c0520401d1103405c0000006154140445085841c001c0203600a170900c80c0d0798080035105200040c000640b080761046c104c40d400b009034803003583e0f5600c7c2c55025400c05007604003155020040042c06540800c6110682a1005940c2c0d1350b800726841050b181c100025907080740e18811 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 632822562 1250 632821312 632821349
    0x5091008060609280506120a080405040e0a02060c0c09150306040201030209240a090f05031c020708150a0f050702100c0e0d050105011d0103171c1a0a 66
    0x201e09190080030070b480803c5503845503c6004200c550003103400c44101407441d240c82103d100c94200b140103200076250106240c000c0401b050f12032641442c042c18100042104000500705640038190310a0080c0503201901000da000400c1c41d8030034040380c811540040190140d40c6030003019141c010512150360090b06580300d0100362a00c000501c00780c145540490700c24070315110b000724001c40aa0386a980440800900380301659030b084050071750002440f03030002040c1c0030801c8a0030f900b43c903401001088a11840340d400019a8618824602140940c09000810f6032082010094420348201341020700d2603c0d000510840700c1078040b500c0b12504081c148901140c02040c08012405000300100b401d410419040e03a00c41e00040007550098075403600300d024000c040d0f00c40d506a41041e12900c160520051000c01c5501007804044d00c0c200c504610070750b504817071030010a40110700350742281401031030001c4a400c13035403280b0888034420409031802c1031342c0c40c100000401810548415280c181c49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 632823812 1250 632822562 632822579
    0xa0311070f020f0105040b030709081b0a030b0c0c0316060c1e080a0216060f0c0905030d050a1407050f010c18031401021b15100b0708090f060a0306050910 68
    0x1030000c0190090b0f0307500000210701d03441102241c0181810720102aa41c0c00d10f81002003040b0094400c681403030003509110342080c001c42204010b2040020401060582181c036420f8038042c014100021025040200c820f600105002401034540c00c1e19206842070740a003895400d40303010000c0341003004031810703d04018120b080502c1414101303c0c90000155901c04803454000d10031030b030128441820694844042201c2a080041440003000003130003210070f00c00003920980e001c2e0140c81d82c190409010b0883e4541b2030005404040d00070b281401045039040c4d500c3c440c590280c1d0050303d2603000500b11511250090142d425010802e2030282c131101a4642101c00c410b01500000704070032000340605c1040780d406d40540328110307000e50007522054a02d1026a03903d08440000492174a209000980d281110b607800000700c07010f0014040c07400b8030035a0f9182a642c48031050b00e51045180c0e694269603101d000103030042071010303140080c05504040400c0704008000b40302200100c80342009010811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 632825062 1250 632823812 632823833
    0xc17060a0903090b0a030605062715030412120c08010503210301052e050301081209150a0c0b0405100e0610030204090503040918060c17070f0c170a031107 68
    0xc24164201c1e8417295103960440240010740d20842d07020340049100c02d42111007040001c0404040101014081e0681d4140801c881e00d030700302c01c0c84040c41400014007240000070300da62000241c0c81c02440b5100321212000480c3c3c4005007840006d170056006021604041001404a11001d0012540a40c24580303c1170148814000c043c000d00d2107550081c50f80640501013048c10210b44001c22262030176060007022074200348520082c603c600c0e44003691105819080710000340b00642410400031b1002e030034220a40c01521020108151074846102040c00300c1842c0740180e1040d0081c00b514505401c024090721010b100c2c01e00c25801403030034032191004101190048a03416038020076520f4040c14400d0440c06140d00c510300d200d05000d0b41c007202c18903210040c480c80f8440d0108010342c180440045921101081c81819906a200041940c40e4000c0803185181c0e00b003840c000c000c801090b542c020000e26803c01d0650b00400104200f10150f816000f2107803106603c0c16060700384066138907000400e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632826312 1250 632825062 632825069
    0x1923091c21061205210406030203150405090a050f2e0b060c010b1003023a0c0507020a0e0610080a15080a02090c040f0306020c01090c17060a090309 65
    0xd85500000c1c81d501d6034800c400a248800402c000590f034802da01c00d480340d0300b000212104c0c015030320201c0c01d5403c200307890365010030016185803d190502105070001d602c041c0c403280d640d8000d00c3d440c0c500c030b50300d0b03010b5140706811500c0900004003047c50224581402c5000c030007400c0e00403180c070000d420052504003854030444010049840d0001151000611108032426081a0b000a000c40e000b00f05403c02c000e84d11099451a50401c1a0300046080b8043d50031482c0c03050610494a101200c8210069076a044900030310300c00030b40c45c0a041d102112007011450012030740201e000000d61400c5010030380100002003000e01035107400000075103244480740d00d000500c08e05901040030284a6400a40d40d400000701030005aa250b0450944e19400048100c0c4a43c2d9800009112200180d068504480c014121108114110341e40c10307010b5001459081e0032507589101100200d5440401c2b80d0040240a10b82d0f20703202151484103007803600003440308110900300b043c5a0000b0f40c2c800145801c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 632827562 1250 632826312 632826317
    0x150c080c040b18180405031b010b09060d170a170105030d170411030613050f1605220204090c1229060d0c0206010501110f12031923091c 60
    0x70f6076003c0c000600e1000d08800d005401609000805c001c01200000522403021820380000526400411460995042040107604252520086142810051400c6666034426005211030002c0a48078155a400140c03120001900340e000140f008005d45040034058070065000d030400c80c290000c0541041075231020f035810642038a0020b0180803152800c070701c4400000341920700c0c504000980c8250791034819000d81e21406a04064401c4910006101d050620070004001c1c025141808000c01d041c0003241900602002401d50f03104145107200401c0580b118480003c1c0701c440502e0300907c01c40c1e1140c0603100f002e01c1c08500348182c40e680d101c0000101d11500040b01d400c0903000c00308205000c0c00504044c81410001c214240d2074010449a046c0d41c42030703940e412804a241001d9039101c200136990f2980e40c02c40702540c01700c1c1c1e000f600210f81c070001c000c0112140345c0c42c0e662100116010391202610280d8841e101c070800258103003259402c02c5800005100d610300604a0305a45002d441c0303644103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 632828812 1250 632827562 632827597
    0x15030c0a110a0501020703050a1b0201080601120f09080a09060c1e03090b03090a02031b012f0a0803012303060703050414250506070305031504020403150c080c040b 72
    0x480c1d80c1044011a140e42c03100084d9100e500900c0e0140140c1c020143c608081051580c0310003100302281d0003a81103540503541e108407034030380130010341d0381c0c5c04c8900e65040c1c60780d2600d5000810000030f00070040c24a106001d0070744d86158410004000c020281c0001c0c04015074030000102192015a02d20304010100d00415000c000030714064508003010b82c000d1000300004003c128234444045800b0054034002e605440b000d0890078401c0b10f4003500100c01c240413a07041500c8010340c400d10603000249401c1d81140380310700164690101e103030485400086410340000801400180c080500c404214004281800743e80d180301c00000b40c451000520310002c055175200001c0c1480300c841078801075048024203480c2c02d80c1d90340380511012901c2030f128012583e60050002440d0400c5000c541194ae010364401d0700f540c440c03088010803161000c11403548a0707000c0c0400700c045120000122042c01d02407100040060031090007420581000708507030b258071420303c420041c409948049401e07901100d02d4404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 632830062 1250 632828812 632828837
    0xf061b0903152003040606150c0b060f0a03080a140a0903020904051e0304030203060609060d0b1b030c0c010c0c03020309100504030501020409061e061407081c05010515030c0a 77
    0x30003031000c504118007544840c90701041614510f4020340c0900e00540d0244095519024110804c00b1400b5440b000585d01c1c1c1e0b0702c0000b007542c8403995900440300911105080001c000050401003103900700360b07800b200c0007440c0040079030060000700188580c02d0b400380c20896a00780c09000e6081c280f1019006645000007d404c100040c080c54850603c540041498555000340345a0741c0c0e00640400c0340030303114030404070783c4a15008200b144038110042051a03102d6007a500d409601c207000d0040108801d001081e04140d4450401946c0b0440130345814a803100040ea21603401d40302c040620200b4020003600c1500070aa000c0211000b561080c3d07828101da0194407011240792065900c054800e510110340420790f05a15003100046a4008000d0700012101284150f509603445c454540440d25030720502c8501c210183c060000107020b03403030240c10040450900a0b07900410400b0b000060742e1100107000700d2074000080045614078030413180c1140f47c80310071144103200f1840408284a51000c686 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 632831312 1250 632830062 632830103
    0x1209070e0126010c03020a0e15090d0804080607020604060c170136060302010f1106070c03140304050f0d0c05070e13050307030c020a1403031209010609090f061b0903 73
    0x1402c1e907001e0000070007900300c0054006000b074008011081c0051142403142d141031804000700340003060544043c07442d001180040220182c9410411981c1c18010301000684007424007109218400c940c01903ca0740c641440c0c034804503186049003000b48001050307800e0083e032203820317250705403000e14046100d0052007070354141e00e0404440340c1450168080e295011550015004803045038402c3c3c03141007104600700c00035542c00c049141148001d1303000d440041c2c28103210b42c0900c07070b006029007404e45020801011141c900d50007290700361005d42c48040c01440458082009a0b502211481d00c901e01e00d82983e02c0c240c0702d020600c0b40650201101000c2440e000700f00d0842c07000694000e0441e03617100194940a403031302046180603403044480101c001280e2291420300004d9500040245140c8002d1000c002d178500f6000c0d10f12486da6680e40c0c00401c80c03a1880c403400342c1ea640601900e076409081480c010080e956144401004c400210341009003546d00310540c00e041d00c3c0c0c4480c1800d00ba0000e450305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 632832562 1250 632831312 632831369
    0x13020f120a050102040305070b030601021b04110301031406070f02030a0e0307091b030501080304030c150c0c080129012a06050c040501120b03120702040603171209070e01 75
    0xe05410300400d04024100700055000f44200c03880740003036030344450740c401440d00240000c81d80140940c1000c0d005554000700c0c0c040d07205041c0402480007a04d007402c030000101541098008841c0311561443c4807120010400200e5808140d03490001a10f08400d00029145c1c061082102c6c04d2100500303041d00e05035810f001841c041c140c0e804040081865454200c00c1c083c0301020307000c1c0440e2601001149030340020080701c050f00c1e0802e20024180745000c1c048400d904900c80751408020102c107241000841e40000100240f19a20012a0710010b801c070f00f018a115a00b25040c195410680303640459800c0b90344a14151200d000c0c503500012803890744900c40c0180500200410b183c03c0420455030282c002030001d5400c283d9522030207a041c0c0e804001200d41e008803069242d4000c1039040102032284004141ca2032016201103444e658a5580c0102d40040144042c8020310209a440b41d4109952801d41c0c404610310052212a02e0204400d001c2d60060180c102c2840110780c00410820403140c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 632833812 1250 632832562 632832589
    0x150a05090306040c03022e0e030c030d03020c1b0904030804021201020406170a090c090b01050903070f09150609060c0218040c030c06030209060d02090a150c0203060a0513020f 77
    0x10b4071800c1c0341514054031000e9030303804124885d501300104101204c104032403140100000d00b22105130484003e40036601070013045102c65040c824036106030701c01e490900c212160403800f031718050384406803400624209882d00e41c4100100a154680542a03a10608081d0b00550036040c2990710391610700202d24443e2810800c3c0a59600020b0001803150307100d04042100c04610198482c0c030740b01c0034030407400d5404401000c0e100c641490300500c1564a2940151024401410120301e070203d5040400d040c00100c0d40076850781e001c0540c00f001008200e00079901a40c629000725080a81000d070041c00c12840e0307019410821148010240454a84a20800014080e545043c5041c685443c104030501454002243d051011420008426005c0e009903400d0150090540d81011580c04080c0d009401503c003181d880050b6000005d50241032544170140b001503540c96640403c0309006042c50407202074804000d0303610305020001b002c281840c01ea0030055040b2003d032111411280020020b510007807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 632835062 1250 632833812 632833819
    0x10020c090103050c18090303071d04060807140a0612111608030412110a020f040f18060b270a090804060c06200a05070c0b040b04170c150a0509 63
    0x22050100000c0c0044e10340c9002c603100e8804510344041c16a03042c1c4241c8503017036254420b001190206004500e44841c600d0a48540d858002a00f00007400356140c0d0380c05082c0c1134000781c506000307181c0f00c00c190440454040d0b038941c00440c03505034010403009104d04111070595840380314800d0701c00c1c00030454003140d00004282282d00054108103000d94000c0d20200c8443c09201c41e0004014014100c48001015050252014142c2c58003402002541c03645000d0f03100d55240c012080b0000e491140ea000c00303440e210314002e002c8151070110116080c102005202d55035602c1900307440c0d501c1501c51b0700c001600d83c0007140282c80761900040a08006840100464000720340421120361004245c0e0f0160f025013010311558030203d0f840b4090741303054085590349280c10001e204044d4000d00051801ca0312a005e0003594954070041141e168005030040c01c141c200008080040030b001c1141650300e5103000028116907054403000811100382d03180d40d40080200402c0440895001d4000d42d150101c014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 632836312 1250 632835062 632835079
    0x1827160206040b18030a0e091008030a0507020103020d0501080105011a130605090607020d06021e0414100210050c0702010f030c2102070807111206010810051b0705100f09050c10020c 80
    0x911016011056a400c1e0364010031403840000d40c3d602c9c40001507411140c080c4c01861508c0380c032901c05c917182c0e07001c0070081c0d0501d6000c0007000d6000d105489081e0003403071490000142541000d0400c0a00000c2044118a600040c01031586901104204904813403072818115503032000d24001c14581c1c0954040a5405200300401070305102143d0010182418078182c409a650500014101790b4000d03030140c015041010f000f50001c80c02d001e00092080b250340e004a43c40c28241c084e5400640b4011140c010044c0408a080c408550b0040390300758103007845003000c2c4662002e00340d005050703010760003540d550081d0050072030a10010b954110b072240f540042e001a903642007130420b040b811113001071031806102000602d0301404000300e4268141c07048075014022120b0a500c40c00040c00c8054400900b522240652100f046002030041c00d82034800c41c080d00c0e0158441056074210382071100c10061032400c1400b008006072010584804950b421513401d00220100242240b60a90b500f1540b038010741c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 632837562 1250 632836312 632836327
    0xe2101051005010206010506043506010b180109060c02130f0227030c0a030807050106050402040e04060605040e1905100510180209151827160206040b1803 68
    0x7100429030a45600f0b80071201c450f6a50300c14865244103d10801c0098a110840001048a28105031100c000d05030a1181003c242c10145428288203902020703e034080065010183c05684503507014450090070109404c0e482d20002602d44a64a41c000f441a41400310541c0090150380c407000c80003100010864440c840e1030b6480011481003005481c2c040041407603600603240019040d5030b060006040c80030b0705403844e5151092a08201c0c0e0440e925526000041004e032a12301c084d000400b4048400e40440c24141094411142d150308980d00a600341a00f041d1803060008000404c82c80e045c0c4103103441801c904155050116910b1407441c883e0404003446a2204580120001d80350082078401340c00c00d0308041e030800ca00c51090010b03003100d06041d80c0b00d0200407000c054000041829540034010440b0b800060051600050720001d032400c0e080c0312010100c1d001c3c0310b070740d2242851141c44803501e41254003079070b0b801000304010441c0f0808000941c0300540003070100821001c000407070345c46841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 632838812 1250 632837562 632837581
    0xd0207050f01060f030506060405010b0a0f0c08120f0f010609050607020a0e011d0f010f051002010b030d2a3f0903030807180303052101030b250e210105 67
    0x4c45201c01c3d60303180b1488020070303503514282c40340c035040700c80441d0700501d01100640c0079901501c890b03140c0000d0110500c1230341701044c101ca0080000e542042c0c1c81e00740c1c501c1c0c108080303c00c87c50094241502000700c00d006202a51f0000d02542c103072801111841d80701c0d07007a44001058000640c0201040781346202c00042e401a10620b400c100e05401c1f6048400c03681c40d026164a0284244034010f030025140d10f0401c00da0904121003100c5180520001ca850045032000c00d24101004024500040410710b0301074020400d9916201d4550513130402074140e0109450b55040030290643d42003003000c84018105030741d2128282041642d0042d000181080b20054014045201500c000c1c0c011034295000a020a807080e41600e030140d401c500d04007841415500c0071100368106130b5024001c0612130100c006001c030408400c0f4000e42c85107051b1501441c0410002c00d030041c64a0760070b0b92452200d00000d40e0903801c00c124078802d07d03003690103980103940c04128449202e612148070030b070380d480c1c441880300207038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 632840062 1250 632838812 632838839
    0x6032707030b090a03091a19021c020d050702061605070b030f0f0f0a0f020c01022b090f11150304060b0a080606030322081e011107080d0207050f0106 66
    0xb8001c039264034040c2c1d180c0011030b445042e00180100000c10800003802210720f0707a141c0380d10380703842144184d00344070059003410103030350b50100441c3c050380c0700d8800600c40d10462910034241c1d8030b441c8007a00f84030640c250054241d001c1c3e604001d02c10700740801d4000702c0c100f0a1903480f0b407894015048400c1c40ba61103420046c01e0f8030964013403032950310b4040000c1c40341d01f0110321ba9020300d60b2810290303011383c0c505010500601e200840900c080740c080190500e100400d00143c80d801408007020806040610f809050310328040011000032420144280040741000002078030164200607298481d00500000038100d584030755903500c650707002005020a0016640c082806010281d9441007981c2d2684105580e6601c11540254580d00411540b4007005030009000002c003162030512007281d480745c01241c20701c41440d00c0e2840b440f0741031403808000e28003409044000303102e5502003494140c0b140c640311200d200712401c1110300303600010342a042000c00c101e10384061584c18001c00042c0c3d1903039007820042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 632841312 1250 632840062 632840069
    0x602121905090a1a060d12090603050a0b01021f1407110d0c02030d0f0c0227010b130b0f0d0f0f060503032809030c0303050306040c0512040206032707 66
    0x140741c440001c90000c4000340300e19016030008108141441504209000f120b401401c1682101c61001d00200245180540c40c050311101d0b150942d8882c1460002401c903030009154200003400c005003804240d802040360034a138200c1c00440c802000e1101c03040c030054070b030010f408580c1c1e8030b00f1002c11104c1540304c088009204682c0056a0a40c07808581c1182e02083c41200a549900b01035103c0701194098481118401801c1c145264801016000681d4080c1c0040030b0341c0038112000000000200d04d590000c1c0948a02055981002814600c942c2030350380c14010720100060024040e41c3d600b141d0019100d2115820f40144141440140d8400c00f0340440c0c102800b00a00340308011500303213004030035150381c62003400c140600741607100418881400461041414448114004804200d0545110700558020713102c00f5640d05001d030510080301e00d81c4d0075020810405020290340da0300002d450f150000d404070f41140d02c0b034485060303060380c1c401c0d005412030200640744102c519103000842c084044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 632842562 1250 632841312 632841361
    0x1e0c19080103020a0e04030801051903020603010b0c011b020319050d1803030b03070308031b09130c02060601210b031f050105040f140a0504171b100606021009060212 73
    0x94565070988400445d1055a0081c0031400f0320300140303c43d05041d0f04000e40421040e01c940e030101c0d030301d401095950b402030300000710400000403100038504090081c04444210310701e40807c00c000e1200025101d000d0740c07440003103078040240300b440b442c0e2044064400a40000908001483c1c102c1402050710544042c128003003401c01c45000d50525020171128212504980890700d595110055040c08055101c5e0b1102005001d0014101645400c4064003004210784e0340007030003086c8544064540140100800d04002003001280042070218010f90444866880086240005800001d0600071610300c580700400042072206501241508114101c60041d54108910042d01c4080701c26119104806032024283c0c4000c0388015007142d1050b5402400b420078106e41b515207540141e8540d100780083d05e0a803409510031b4a0120040c0b269031028612160104582d40c0b610501a44410800419282c09039030307010404284034040c0c044980b00c115001c1141d201385004c8810705021100c0d151008007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 632843812 1250 632842562 632842579
    0x120510060e09100b010f03090c03120c14120d020c010e03030703060608010e01060509130207080324040b010206010915030f2d081227010f0f051e0c1908010302 70
    0x1c20f40c07000c1c4240e01e02e5100c107968200f0f12008910301500a00440c7e0b10445003010200e500002091b1030b1544554400380075034582a031b0609906052051040030720607401140c00c440010580f580c0b814040b50b1013888800c00160715920b00e464000e00401600d603411005000c008208403c0e958550300980940e5220703100e600c3c071640c85070034800c01e400090240c9404508100195009490641010301c1c4da51074080d03016140c12100e6480e4001504251503184030381e411030a1050f60104004d10051240c4000d6900b0000d00b800000001d58a032010f1141c001c2d641da440740981c0400b9401c00c1c0e0351015580000c1c41d48503250061070a04000c1110014010841d0521403171803018140030101d482a0b590020101030511004400d215108031010b40301d032414902c40305e6090400c402080f03e4200501d1107a00000740f00c3c0c010700000003038a1034243d954010918000401000d40b4888036010f42000c001005808551741c1c54194072454400c54451070340e013624044216014940c45030b010740c1601d20980e074411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 632845062 1250 632843812 632843833
    0x10b030f030a260708102114030702210a050102070b07030509120f18030a0b06270c03150315011a0301030305030a0509031e04030b10060207120510060e09 68
    0x50080e9409030102101007148012071031081c440d139500c540001205030049006c03a0ba46041050340441485107404520a40c505181800441c2c604050700c0020100035518250503540000e4120b60b40380f026140c1a903004004040c170308003c010948a01e80d008000311b544503464105802c1b0000c0c21604a030000303041c50300150302541c012554560152104802c0c6040585103038003258241c10540322400c4242040d01c401003513940070001461120702440600b20581044401d000004074492124941014000104d14104151003c25540001900005900c03500c03800c0c1c0c000390021059487c0307541480303101d030381b4004a01d000c03c045040300c034480d40301318581ca0300000ea062180000d11012740402c40900000f880001c1c20b80005d50b02c4121002a01d280220114144514103542050030358081c1c000304090042103507000c10140c00180015030300520600d009402582d4031050b001f50b000c903080320b50142c1c0403ca810040e8406207284008107208058841801d06250482101c50200d80d129498086 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 632846312 1250 632845062 632845097
    0x1503040507120201170a0b0901090905011406180c160b0a0b0f0906040e0a0b0c04060306081207020123031816140f012d0f050f030a0905010b030f030a 66
    0x244200c540c10307102e17140402d140e4401480f4480c1d000f45028420364403a160b00c102a03039495051806458049400034200ca440e090050848500014401c50130703503070405000c05a500c800001c440e903401410013a455075594403850741035004142d2901030000400341c641007008005848140300b0f4000b100c2c108198a000c40811803004a0a810030790001d83d42408076005041c55048051390351075810807070f400c0c4482682d401a40001c21915400c1041000c05e06010b1142d05005000040000740002c00d207117004e0700b058489501ca44030340241030200c1c98600040d00c04081844500c1401a040256141d1900d07800c900500b00c040c1d641800180030f100c843d0707c0c0d50703040515000190f402d0000c080d4844605407051122f207101400c08581480500482013150124444a4a50240005110b01c0d9003400009001e0103d008a0021101388641404121211182501544c0d4001102c21010800101c1410400d0051800160707c5426019282d850b80503240b0000043c0210617055942140020004401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 632847562 1250 632846312 632846339
    0x121c210203100302040b06071b081608071716090b010f0c12050c151618081f0f1401030c17031b01021209070510110613111503040507 59
    0x3848202c02950818405410203a00902c12118040c18041c40c0c550035480708041c0b8104144000c02d00015132200b801015428400404489496040c01c000c0508110f100782c1c40d901240114018a440182d40e00d80c10744e810801d01c81ca00700740c503461640d0540c41d01c6010300038004401d101d6001c1004480c00150782c034801c11880c1c90300c41c2c0015518241a0008000b12215403002d0850b09a505c25a07540280035120715021901401c01c2d0104507240108114015242c20f22385029001851080e48042080744404034140106800310101141c0441e8205580c400510900480380043c511b07002e1000b030702d10141820681079038000e0b038a00c0404d6603504056203003a074444082c01f1031034009202e104c007082500038011010907256070007d401c0ca5842000384141c01d000b1a515655070303000510802a134242161010f181c50880e1034400b018908001c1a180e0b030b4840501025400c020720504881841010950844000f07070091101040a49942000313003039400c1910192402d0213010000140328084401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 632848812 1250 632847562 632847571
    0x6010b0f0d0507090b0f04140303090901060c03022d0705041b200102070f030305070503061c02150d0605030c0f030613060e06281a121c210203 63
    0x181c60001c09092010203440c014190340b050000740030000c540d095070103018101025131028581e84445c5022203080c1503820514a5501907001000100125150711140c0d605440450074260a0084a464201e1a0411140ba112810301c1141c1d000c000762503021144e21081c4070004219004d80b9120400c12003201c45d0024443d02000080322680c4417503005100401c10303140920481342c94a41c075400c0702400e903170242c2d00c12140d00c803034201880308140e0140710392500064030307107842d605620b0010003007600601d400f01c4610b1040c0340b6103401011555503a00c4000c1c00c840e1451900e403984030f82c0c00d641000d00b90130300956103c0d0141d181e500341d29007498110140314040c002e005088a40301c9842d0032031011243c00c000c0c0c03041503c2743c44603040d804003080418042c080b83e6404000400011a02c0d0007034072854602d4454a505112500e07a0701c911220001e2801c241c1140c0c08900000c1030b454007440c00ca00386c071401d8503007520383e8446041560480c4a0079048040da60b011a0a02089201c0b14104d06c400c58 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 632850062 1250 632848812 632848837
    0x50f090618100c03020703021504020307090209060d060e090f0609030d151208250b04020f0102031b0604020a08030301120f02010c05031309110705250e0408070506010b 74
    0x1000800d00822209080d800c01c03911801d5a4401030051440720560b1480803d840101e41c0009405007096410000b0103188005001520414281540000d40341c481e03510a841015402042c09141559000c00301c513040481c0c080c08009081d515110503410150445984c196070007a00140419010003103440c500c602034002c06546814404203070100100200c5c6011a00032000010210707a41c0a20441005c84500a00b0110780f50441c0c40910500c4050280c200d910001d5180000070004d030012091541065049940c0c03504144c00c0d8004030700c1c60040282c040f40f45c4450282204409201180307440c0214000e64030f6014454407440b00e10359906c82807294a200701a01801c40001c00c102c000c00803801441498803003070804103511a2451034101240101c4080241c00041143c1ca4040c8101072021030203142d0b6a081844503205e032134480c04084103580c01862000d035551354000008101501504945c0e0081c01c0c0c80c105803c2c02045031300200400c275090700c5810000315005a480082e6104860603a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 632851312 1250 632850062 632850073
    0x12010605150f0d240306050f060409152a0309050d0503010e04030c15062303071413020706020a020a1101090b220515070c050a1a0a0203071212050f09 66
    0x2c00d204801070004420018400c0c00409160b02641952503604c4021802603202149505140d00d503c81250005030480e0b1180c0e18106503031300091205107083c00541e00003440051010b41015aa03801c00b103c41511200200310f144c0b009003060b070980c2c002c02c0400e01038021030304401a081001c6c0c8503032100b03008000032500568001800280724440e1000068461030601103080c034582d5848040e2801e54010a8206540003001d1f40300758245440c4804400d011001802101d2410314103c0ae01194900d6050007500001e00034076503641c0b290111280143c1c4418215a5605c4880000303450f40280441101c0a00300d45003075800541c801d40c1550103507490040e0340d9260102015100011901340d1201e40e8150040001c0014650307236415034440048a40c40303605640780031a180913158250701340c000c6841062000024080541d54440030000c2d0305010004d0343c0e682d001d249050f4036500903240000e210308450050b031319446d42e00c0011150b808032000e0f010b01c51030f1103081c044490310304115071601d141e5000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 632852562 1250 632851312 632851327
    0x906090b03071502030d090b01060806040504080d0c0e0604060f0801080706080a0203061206090c100311091011010c0c0b070516021311070501020408060c03040c0501120b12010605150f 81
    0x4020102e011050a80120b85c509006e1a031900141c80244800795031088030100100075007500320b100c0c0c99000600320f90801c80c031302d46941c0d54003a500070202e80703156460343e903a604201980500710031007045030000c001ea51199a1403900429182008a2a000107041b4000000f0816000201c41054407000c0d1140500c903910340c0c002c00025000100110303445640b0200a10082800380714450180d42c90074042c1c02d80c26038110612804484401900040601d40030b2902504900d501c10350700c610400300c0305100080c100000848001400c521441d0b100e5180820741c0c4d401076046022650710303a2041c0350502c0a0303a40c40300c0a03501c0e0300520f0041d1044400da000c94000500d019402e50540c13210000c000541d8804410a111181d000504101c40d56035001900f400800000c11616a019002041651071032070182d69007510445c60f4801d660620404030350240e103010352500042c1d10032101500c0c80d0344021840f0750041c080c03e41303882518000c51400040c2c1d035550380344008403280c2c0551801001d00e05181e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 632853812 1250 632852562 632852579
    0x14120303130206070218091213050d0512300f040638040605030c0a0b0f04090c0210140714090301022104030801080307020a03140a020402130906090b0307 68
    0x703600c40201d030f000781c0800a45005903038550b1201c00c0300341700380701074060343c5029040c643c40c000403540303901e031307505018843d02d5181c0e0350044a0805032502a07e40c113240000910300300346010100d072040844d40e00003040e14141b00d501d42d611480340d8002c0c06a051041001c445003900f402c42d09540301504401c82d0786c005800b24800e80c00020759200400341d49000c002007281e420402c04c01000d42c030007041d90483c0000d030381c42c0760034005c3c3c001800e411000b509100208100141c00600e0a10071500e03088030201340f18600701c00d00c4007aa001040303c20341c01d000300c04104100035100c0b001e0310784400400e0702c3c01e41e42001e07003189004010301c100c050f511162469951545024001d4006401030b65140d9001c1040c04c0348aa031603c82e0903103015840400c2c02040c14a49005028444160082110f40d4401e21500c009607841081140480f500010141645102086200c0c18090b1840c0041e41043c00045d1500c1c4002455100b901241e42003001080480e446201032016a03d5682d002649607101b00000d000e04030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 632855062 1250 632853812 632853841
    0x5010504060915180f091a090412030b04060605040503152a1c021b03070b060913020a08100e0c03070510022503020916020601031716060614120303 65
    0x161410103210400a00091403046945600045a03a1044030410000014980107e4a0078042e2100700e00414504034042044004000d1010308154904898060068002c0d800407070704140c041c01c01d100d200d0315904003510b203902600c1414064800d0060300010b41c0d05944081d0b02950304403908032098020485080c01d08421040c02840c0103404200c01c000d000c0a48241c0301c03030100621400358440145410240b00c0503800480c544403134000f04800b0000030303030308580340368001c6003220381d07003025118030880f0045002d40d810000d420100060b4040707041480000d030100c0c40b41d0506801c0c80000d81405483c1d44403c524005c8542542c440c560601052900b04480c1c80f0b80f038050b00c1254006200b0040b0340044080c01d6a00c04001034040f42c060043d0308000c1a80340d404418105d5207042c0d8600c01c03400a5841a051201600c015008001c0390b140d415940111032802d070181d0743c83d0211950740c0c00d0007001041305114440300600301050350850390501e0010355801001900165007584c0e680881040e000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 632856312 1250 632855062 632855099
    0x307021209060f03100306060e040507030303050c1b280b0a0504140a060b09150105070b07052709061207030618061b020d18030f020310060816050105040609 69
    0x2e00911100010104840183d4803030ba880c4d03940c902045145041c40b070122a0950000907a44011400b04404a0000240c0c0011240e1600e800100d541d10b2a05521980c000e004640c3c10284101e01032400101c3e00086900200501b08230001c0300d603405110900010010000c010310424004001407400c0d40e03035611041d40035000d00907a4110344448034555081003012541121241d0756001525100c0c1400c1c00f8455210f41009408802818014000b800c00e00505100030520700b04000003440f290301c56403e50701c2030504403491050961200c400000d0003142070314258011007105d00025024584507505546584140780034021a90650310380ba4081c1009070f501542c4040c7e80b401e640001000c41c8201000c0d42036004401e0b4855180c650001d0a14a0090880c0f00300004903226005814081824800701c1e64009000c0c890000305101080c1480c5406540c1c821003460900005459440403606c080416003500c40b00340190380f520019152030181e80600800210030400c20f0000b80d08001100144 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 632857562 1250 632856312 632856319
    0x20615091005011d18090106060302090f19150504050405160c021c050d031a0409110616060501030602030103021507030f0f02030c010908090a050d0f23030d1a010201020307021209 79
    0xd0350130040100702410814070707400003100048010048070b40000e1007040302034810b0745006d5150401c824000f82c02c0c50070300300084d442840c0d000204405403108030040d178005e00308116410820005080082e103280c04c02c2c419240600e0a060001c0c0ca6400f070303032a0884840c0100d0310f400442e28034a4090159244d545032125040000f80c540140220344e040100c192155110b80e40030944003014040405081d444600041c0607506000d44200000d00d031100030100500d00b9605c45484818040b006003000c268810041c02e849d2038140040280003c41d00258140d078000d440c0700d56900e0620700315400364403176024050002180070036030790b14091049003c070200e100188126800d08080d10201d500715800c14000721082034000500d50780b00e0510004000007018211102d8035100382e2621018104130070391b0001403c0011200540d05600640110700d124070643d40101c3c0d89031640440414020400000000d2642200c401982420f601c1402103d00c1014254060050f000b208001204141c00c0300c034160344d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 632858812 1250 632857562 632857607
    0x9060604060c241a120a14011104031b0b040e04080a120e0106030b0108210a0504030c0603090303110301081b210105040c06020d0206160c060203040302061509100501 73
    0x2055040f20300c107400c2020100200060084804092192071803060000c01c0c0907051050030800b070400081180142c064000860880005600740312500602c82030054492030180030501009010f082c04941c3d0030400b00b9003a03184c00c0da071a0b442008040c0680d00c40c050030010030400190004400e00701816171558039050414901c0e945117610400d5403c50724502129030b564040c1042032112004809005003410001f4168507003107500c260103031301c20131010005102e10008542603560301c2a0100c80085420015011101e512214020064440600d00758000b908066884461401e01e8040320b040b17410744401024072164441c4590514400c0c6810a1341c80b00015142c01303603d12108a696108443c200000075492902e0301e03012940020b5a04030408551200c0c404510083c1c0010f60240c206159a0440329030400b2600102c92024003540f00a00143c00841880105600010198000e815100c035041c940c03010b80f0103011000d00c0466005010032440e00c400c0040f03500031003001c016580310b0f402040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 632860062 1250 632858812 632858843
    0x5150705030d1e060512030a0c020f10050a030e070b0d09030306050909030705071202061209070b07081801020c09011415120105130b011e050c06010b09040b09060604060c 75
    0x10840301e01c0c20b80c000d511044910f045441812503c41c0c2d0014081c220f03594001c0c807045844150b540d008090040c01131000118510007999541401d904528900404513440d444200500070043e40107521420042070400300781c500b82a0021900000781c2c1c0d104554141801c0040004030003400136120242c003419610b41d0045460345070b8610681c03040c3c1c449401076541c2d880d1442c1941c40c10240346e22011856454070071200060362000202c51030010803081c1ca603c992150300000f4144001607004090030000011ba0204010490b005018288000480344224803d10001682c540c3c4c2c00b842c0440e03201c298000144040055500d074035810b04405840744440701c0546117844080d601a040e00381c0f1590a0030010041f600c0c01d02c0023043c0c50710090000740011403008001801100028490100c24504800c400c01c0e1107200c2c405442500700080f0032900556900c009095049c0d0010501c103004500f4001000142d06104194134020386003e0300d55071a00e4508502142c880401c0c0070b04803500166500c03801d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 632861312 1250 632860062 632860087
    0xe010e07080c04050c040b0a05040b211503120a030608011410170303040809120a03030b09010b071e14030705062d1311030a08070b010f0515070503 65
    0x2600618280001400014140001c15141c9200d1103101c41c4202d0902d410040c510054605850031180806030392a2604140301c17080c0c5a5001e41e4000b0500508003103407410b4000030440499442c2150200c819410b0740744d45201484140b140000301c0d8059200c0d151444c581080c4030000d140001d030070b14000a0305920350341860300b503401d090703ca5441c9c01d1800e014000402d40350000c807402405028000040d1214004803607071640030003000a80b00c2030020448801640f00c202e480e43c02030540e00240c0302601181c1c90040c000b04140d0400c940221052000880c0385c1a00d5811110129007190740780b01042101c01d0007003400d4075a00400c480c000642d110310300c0e055104001902d8441e100360f014041078079040f050320b411241c01d04020522001265000440800341c4040d0941090912034142003100d00d40c1007050014144000f6542c05102d01902c0b00705009024010300704c600c0c4270380c0c0904240c1c0d9a03003030030a01a004500816502040d001405441c40da5050010400b0b02c1c031510642e42000e107281320300c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 632862562 1250 632861312 632861321
    0x210219050a0f08070801020301150806150301030f05010b090601020c0405090c0406060923130c0e060406032301031a10030506070e191401110703060e0a150b030c040f0e01 75
    0x12096410341103600340440c8009001020140c40400021801e640c50048a54003a10700ad41a08090140010114440d40c40b2103140d06024941d00e4042c0317641c2d595903d80a40048100141928694030305203e0074140d150000301c882c092901680104039030343c3e25200304001072a01030f241da041c40c466040440155156409003d00503c845e803503900301c243c81d1100c41284000a40795203030061322a51203903451581d0340b2000214030720b01d1038030014805081e03003401d40f12440c5084880e64406030200340000c4459040c0c0168600c24040e0724101d61094001c1c0f5035401900c420b0100034000e054448208179103004001c0101d030b000f40c000440c02d007074554989445e800e024040e90341d02e000070252242c5038800d04054a40d01c800f0050040e4207000f0510340742148000c0c0800c828050704009018200c1100680200940c502a54004404114101003480c3c025514000d44000312854800e41e0103c03018000103126820f01140044c0c09048010340c900d0410009114800c010030324181d490f060707058044000d114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 632863812 1250 632862562 632862569
    0x19080306150d0e15010609061706040e0a0c051008011203050f25120507050d1b02130b0906120d0503040f0b0717010b040503120a050408030a08040b01210219050a 71
    0x50801c4040b0b1000c0701341c084034141c000006010800c4000c1280681c81802581c07000c140000141c259140d440014001d4441a03c4000e03003485016407080a2095904110b41102c0088842c0d007501c20303404000381c42c0242d09118001c4018103811090001c01d02174001840b21940519000d898a030700a1034071101950607001c071204100c0302d04206810032110321a910390301c2d8040c1c1091b80c2040060f0f500c05507a0340c4d0b41e0038480200521180e400e006510981c4010040590040c0414015a4070044080c000d10003501e0f4503104a11860100c0c1084c03c3c603092003030340c0e8207140e00038001c000348803182911036a10150003260081220003d010200300b1181c090b030302802e0903664103141600c0309544030741305040603003018100da43c007000104600e03600080d8181e40316925805480e1205031220042d034070343c021031f0312107046400300040100015910a0b40d15201314030a034488100c0b03980b902841d40c1d6145029611846524a10030300e04090301c0c025042c11072020101882d401c035141c648002c54041c030307816130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 632865062 1250 632863812 632863841
    0x40c050d020702281406090d060b150403030305060306060406081002030712090317100f03151d0706120504030503041b050604060e040509060f0402060f09030318010219080306150d 79
    0x4030602174074050340503a4614180c112511070034540c0c1e036400246029142e03039005000e180d44070310141d400d03201d080c40e2400c03200718210080d4031181c3c1c034100a405002c084610500c00c1c041d580c000303451464684280b00039940844001d02c0869000c8045000a52026001406100f0601d06030792489441e8040c0900f07142c40303a95000e4084400c881800007403100a49203048010340300c0024002003400700c5202e03003103942103074202c5502501d41e1108801000000041c090f01c40c10403400307480043300041c007201120080e984140a003007003118040700b269801d40d002000900300b0801b00e404030784645414410b00c8480d04402034030076907904c00141a98000c4d0f00240204402c2744034107a091030144980c560100780c5801070500341c9843c0c00348091640004000070700c640000b00f0072149001c940c0b015103091040c050200c83da1210a01400b04000d0300040000340188607012114401131203034030310007005650200c0c0541c11500e40004001c5980604461591241010700a440011400d4002e20580300f0721007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 632866312 1250 632865062 632865139
    0x705090a060c02040b0d15020a030e01051e07260403020f0106032d050a02362401140c0a050a1b1d07050306300606040c050d020702 58
    0x144103000940305da00c03456611944900500d000411200b00c440b128007404000e006903a00b55a9800f90000d101e078042c0041d0540c64a402c01601680c0442c2602d02d0360401c003029400c41e580c00c401102c1c0c3e481c82d24540c40c0916410210140000c20702d9070b9081c0c1251217030040e100c0c5465446001801c45005034001d9591811501c60740b82030f041040b04600342d6500c101034940c11058070b134032b407107960300301007400280205400106000301010812811a1448013003030744c4078402034035106281028500b501e2043c69801110503100e0079410387c0c450368040c40f81c180c4601c4490b03800c3c503800c1a40b40d000201208164005c3e1805480001c5007408601070b50b910070500d5a055410704040c2130324801e0303150403001c80480d425007032906142c00d0485c150752081441c5072040e07032070f51000d0124aa903580712600ca042e25410050318101c4007101307940c654890311050111445550340034100401d590101e403180002c200108011222101e030740c1c0050280c0c40c000303040e0b12480c4540340d40500078809290306049083c03111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 632867562 1250 632866312 632866337
    0xb100b030a1e0b09010b0f04120c0305150103030e0904290a180b04201c060e0106271103190f1a0d0303060510022103010f0303080705090a06 62
    0x807202d219a0700c90101c40811080030030002060044a06004503a02941c0c0072039a800501120403c403000f824403140c48420280c110b26043ca8580420300040310980955100d1141c4c4601890300305040b80d42650b41e090f0b007040e0100034005200000750083d82c04140103a18411041010000610b130041210004829403420b1560002240c00303c500c0f511561807810403c002240c649613816410580001c0400b5034441c80014441d1418a15007030326800000c28811303115641000120b0803d0b4600402080c854007880201d80c034220741d1580219491a8035201c02d01c0b001746014806c1210801c04c40100046c080e0048407100b00d5508200c3d500390007204e01030b0280a555a490188408a13103501d43c1c1401a0707440080381c5450502050a402d010b609188403000c103262107a00010010100034101e880c102e070700c103c0c00039203404c50551400900c031a00c8a0700040c0c8900d10007120704076602610210b10315405c680e8111a13610028003900f0800c50107001050b2a40d503110080b800601e0103440d00b1051100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 632868812 1250 632867562 632867591
    0x100e030f010219080903090a06080105040b0a0303081b3f0702070b18130209040c050403080d090218090105010e090d090b030a18051005060d0f0b100b030a 68
    0x180d00290908030703401488040c004280195003101842c540e81072101280d40c51215480c45c40c024105102c2d4000e00700a070000c1c01c2da0700810124145d50040d0f07001d10000b0005070500080d20300314440100010401c800140f01120202c105c0c820200d0b0039560320b4035007080e0b00c1542c200002110541c1c0000307211030800001221001d00603984114040c1c800a60900c1c0011011b502c071001403050750805980012400c80b00032881d4044541d40200400342c404501d9a54811030082d00005078540c003031490316900c52409070089050780c04a0f42d00c22a45441d001403e030b2400d010f0a0020000c1340c10800d00000c0480040040e01400c0c49262507900000e165071404907554031480c006000c0c01c01c0c5401003650750442d582c0c095500350541d861911260b42e240c50701c004d071000401400c070b5280f1440b04176080220070082c0c041000403488444040a20003603c0d06402c104000c003200310000c08211f5484200c00008207001012544200039807110315101d0390b100d060701c042d58011100740c0513265031840c4003003400d00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 632870062 1250 632868812 632868823
    0x50109020c100f1404060f14100317070803070906090b090a17030903070b0705151e07020705040e0703050607090e04060519020703050c060c09010c110d060908030919110d030e100e03 80
    0x3000720700c00f540074280349c0c407603920404007404003920341c0741c0e000740b511010055401111140355201200d02d07941d20300420010503148490003071100042c040c603400a5805165020b99024490003410141c0c0e541c54a00222416038406082e05110302082c071601c6840d581c01d0005200400d41d00900a5990890b481c240b804d0028642842000140c1c074000c0c0180c600f41000414011204034001030160b4a500c1c2050346029226445182d01070708040003038003043d0021135064100c0748910111912521440780a41b03203280903015100e05216008000f4002c14556000b01c1e030040c515080300c81459010034100b4051b80d01202040c1d000c02d200294200c1d280c0302c1004401e070310481030a884da06003501440000c1c100040c001002c0c00c500213942951285036a460340d0300300d00d6584a1402c11100c4ea451428a0494008a8a0b03240340e0040f0f0031901e25202a08005a0344240c0c4030b0301c0c02600c181d20700304110203080030401c00c0d81000310740f585824103615842c1010f400601c15031142408102041c00301841c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 632871312 1250 632870062 632870081
    0x608010203010b03010509071106070f030e03190f03181103060603010501080d0f2006070801062d0203070204050a06140103090503070b0c0d050c0d050109020c100f1404060f 76
    0x9a10420040041c152901c082e603055440480d10b14181382c4500d00f0072180c2c40c40c000b81007a41d500840040c070620035003012440c0884c0c103407920180701c1d514800142c29181e0081600c0008100201381141705418814003d2581e099001d040004400748241c44000d0b02d2203850004442c0b481c0030a4600c9003d240404c001075001c88128000d0000d076042c00c0c1caa80c0c68000c9403200f0003d01542c4003100b203034140140701c10301045844000c10100c0000f0888070a40e0b410381030741c00c080442c0d84440042448da101c5c581d514003441501c030b152100b81d44c00c6901c10128404900b80b480c11404107002590050343c0d02e01551740142a5a08041401d900b00a09003c0c0707403201e248941e050614144000000840100a0f2000c258000841100326517a84070801410304ca50100190040d1410003007100c42594500948030789101d9034000c021340d0b82c031501c9c401c0413449054180044c990080c1c44900d0002c8968011200780314403c200803601c241c800b1150a089141590201c48032500e4100700c1402620900c55501315 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 632872562 1250 632871312 632871329
    0x302040608061005040b03030c1506042007080d1b020703020901060e0a03061d10020703081617070e030703051b0d1205090d0f06152306130308041806 66
    0x4604019545654203400f03403003010300a80e00c03060840c6440d9400d0054030000c02c0d900d0143c4140010410110405050807104135101d2898118282d588054040d18003416400250901d4581049921401801e40000340854400f584600241c4081020340b11030641ca401c883e00206291030441c4104405440140c025504010407580159404d950341d80c440c00440e60080740009000c00020103401541a2103241c42983d4802c2d15403201104d0f07045d900411000b400f80d652000d003a181c030700c201c0386088051070064000031a40d4045040200c160404160062281d04101408003000400310341000c101c1d80c42910550000d4500351412112055008005081100e100c1a2480d9642c1c44620303a64035003070050201f11001c20070448540b1151a05001282c228548000340000781c80d00c0d50207010700096440300800480d00004854240c00402549860b00c5180411800010301c207014450b0460650054030410f80e802c000b01180866000380701030009a01c6601c290303503461a0303010640e0881d5200715107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 632873812 1250 632872562 632872573
    0x20601060305130f1b06140715020c0a0804152d0c21020615030a0f030302040b1315081512030d0204030605070f170a11071a0601180f0e18070801060302040608 70
    0x41404944080721802317a400031000d01511940180d4078002d00840307048021506c1040300f903009000c00e2a015008642000803449140000d100b0225640c02106020f6614102000c00d402039610b8080f00c51050102c0c5490401080d0010340c48468690f00340588501440c1900b48640d01c030b0581c140b082662041d107400300e00900b40f01000c0031a581d041205000f500029100d034020341010f120303404640003880401176080c0ca0742c2050540e00d1600030b10b0310400d0580150007a100141c1e902a4a01030300c42c10741180c05039250341441d400e100c803890390a07041d01c3c0c00d0300080040002d05000c0b0320207070014500450001031b041c94888000340000781c0c125000700c144400d0040034506811911040340e481501c6043c00314090000c6145410740d8040c03140e00030720700e4008000035030070780d030502442d10720070042643c031f595510300c0385500391040c840c2900541504808020080c00307100207100307880c1c0d002540140e1119a00614860040c1000c1283d0000d01c1565101c0e40100254503203401603a003d020281c01404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 632875062 1250 632873812 632873837
    0x60f0a0e100e0405071719030203250c1809050f0a0c0e01030b0a110d02180906061204081b0a060b09100b09211f0f02040303020601060305130f1b06 65
    0x15904c101c41e00c83d92071802c6c20985102ca0481c010301c04040e41401d1203041c079020320300d01e143c041e449410508044420305240004040c250700d69150500401d600503902c81c0702c0034142204a9840324804410700c009503100d195207000654100000c50481604001400c0e00991a01d04048061200d61004403141c054070014000700e41e404882507040802410001000668800d5004040c043e0724a051400c6102207441a80f0107000c4140000041041318030b03036029522001000a00c0c040d10031148058280d1000240000720040000c21001c80400f00c40c1141c481c040d10005e20b007204150080341e1003074039401980c0c1c1c6810404440b94005c20000b819030181400c00d002d001103402036006084c4107410705601d140c0010340310012a003444c4215800c0c2d80140750b2003801614a16425229604001d190400454000d00203100341e5040e80c0d4164080c10701d592a29034101e01800000d02040082403100160070005190701d1500f4038914844e03441c0b106000e02d002001c0303040341c8081d807005041c0b00c00e0317901300c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 632876312 1250 632875062 632875073
    0x6090a02091909020a06020f0d030e0d03050c0702090c04030b0603010c0503060424090b090c041406031f03120206060102070501020c191e0513091a060f0a0e100e04 72
    0x11540428900020518040d02c0c440c0704000d042c4a030006500a034040b000420345944c045882c1c2d034107082c0c3c4000c4580030105c0c008118120350006903117600c4d0741c000a840c100f256100c1e41189401000310103030385091500680001d00c04400c2a680c4100c4084001000c004208404840315481182140200496031380d801018005102c0100a5031180e56251544c2801040c4900640701000c41082e07981d003002d0301c0e0a004402000040e108a200340010000503290305116400c0710244e034003032100c3c04440152101800401d07040a8a0b503035a180c61381c1240046644010003c500450161407c02d00061010b50080c0c104800508814110740110b80107010a0340c00095180105509071070110440c2413800944c242c00c3d8030764114008240381d4000002068071601c40000590f241110920701c0d0300c4800c040314003202c40c8080700800d1071100180c1080744010007aa0b00e58060b0f0f000e040f180c203182c05600081d56815068010403880c5015800340a0365030000c61a8001402203410202041d0500c6e840b507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 632877562 1250 632876312 632876329
    0x503060d051507080601023a090801150501030b0108060d080c01020702060d060e06061305040213150903060609060308070605060307050d030503010812160311010e030403030e0306090a02 82
    0x45401286a40c40a1080200400c544160360500791030710309040c207142c2c5005120b0701d42555514010300c0307481e032108000d40451a0402a80702c41001400980280e00c04982c0c0b0000c11005080c1031112910001a59003428000d1507040c07005030f8041c0e00400e042c000050100c1341411015410054404100041c40d00d0740c40c3e501801c01d0b040341070f80380c44468800c9040d0291164140094100c400480c400d40c1c1c0d9080340d0002d4003600c456122000050b0f5a4005009581c040c5904001e401e000300d5000304880d06090b801020310080c990320446410352101d055201c070501300c6c03020000150003a40100305100d0644070701c0c8050900a10b09000107441d50700d6030a241d01400201038011640e50003ca11155801c00145000f4903001d807160803500710328200030741103803c24481c000340342c0900300d0036180c2c10600600b15841d0a800e5040010038803240d031011900c0e1081c8403030114103036588510b64a2000010030243c401544655030304003000b852981403509110000e010044258459800c0c0c0005a48140e903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 632878812 1250 632877562 632877571
    0x705060109091509020f04140108060a0c0c030e01020c09010b090301050c1e03100806040f20100f02070b04080c01030b0301091703090c06030c1206090603030a0507050c06030907170d0503 82
    0x410042c03d6030002414000e840900d4903031061600360303884606148d56031914102c0e02581e0696400b40d0303a40d200700055403d4010b50000081208200c40c000a002d101503441151040c81140e44440118010600307810b404c3e000090b816401007000140761a003401120392186400721201d0401c0804081c144603441c0056003085108404000151401130031380582000b4070030201146d460f070416040ca03502c010201306083d5400070400e00c140e07121003d001105110b00038050a030300c03201c1302412003c6038101c406484403c114040c4181c001103018220002d400a440090041c0c01c0d00e000590014040303509449849000b13905020758400481c1011113000ca070701180502160350ba03030b94200800d090103824415550f200f5000f006020b9140c014101818100c140c100411415445400800040800c203c9420340e040d0700420000450f01e108001400d0824818400c90f8400301d413220000d0700940045850940c1d642c4140b60400c2071007e07010455201054150162968841d00c00000741244001030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 632880062 1250 632878812 632878853
    0x1906120c0302090406031407120c050f120d030519060e06040b010912050703030e030303090d142802060c040b03011a07120309140705131d030a05070506010909 70
    0xa01034410303000750125095460010801c00c0450b850b440c288510b40000107100c0520312880304082520701400362100105500604403082c0c280c40c14080019120710b03c007203a90808020404050074000420034400c2c1e40015882c0440e86141911060380120305040d007c6042500304003040045404130500c29800c584103950120700e003054000140da00c14515404032021800c0355a4103410b108021403408141d038400d9507819861b04508041650342e010a40304c841e440c3d003000380e48107045806a80002d099081d030a00f142e0418400b900c0060151b4195103000040c5141c8403140759003a0741c10b008040c3d004444411150809050280788541030105000d440d084440c402e14040500071401d080d11003159001e0004071111406450040c080e01c62201c1c115032410503041402150341e0003007075100c00c1c0c460141032189041c541d03103480c0f806807844051201141d041c4400200201c58140b00404a00b031941e1503296913030460380b42441c0380c01416030080f41810300d8503901000092068031001903202259 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 632881312 1250 632880062 632880071
    0x41802040f27020d0f02031e0d030c050403080d050709080d02010f0b010306081209010c0611180321070f080a1706030d0903060e10050112030201050105040b150f0f120105190612 78
    0x51007c64038190240004404e466410048e120100900150f00c1011a201c0d03541404101100a4292614021804014041c800500c8010700e000896031190380e215a0504c0d040d1081c59036807803d24107000b526140e8100503515903030f11600300044c90180c0c0b1442402031808001062415005544508030550071041041300020300c00c20581c400c0048140f010342080040100000503084407440c0e41c00030f41c4c40680101412480e02c900d00e404100c5c1c05064100116100a60101442002c0d10f54000b91044400210382425040403402072405001c41a08903100c144401004581d58001c041008221510960190b0364403841241e0080c1d82800f00c03548403c0124641e01000c29040c2030030002c00800780c440d40b0f81400044c0a41d402100d1100e07050080d0000c10459803a8424801640c5c02c20840036041128440e02d40c04140b80840144040c06419074501e007040c8402480301303050f900c081410404810810014001d41c5001c551000406410b41e08810303010b0314004020348160f901510ba103d90386d40d103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 632882562 1250 632881312 632881343
    0x30f03070e10090e0a050c090d020105130e010f0803270d060903020d11030301050901030f08040b0304060f1802013204080616110a02041802040f27020d 67
    0xc03444180c0318000208003400c0c90b40e00d8040140700700503610601441400074004909090520312503e800b419034100d4003490588280c0501040c450205001c0307041003010058034040070f522111100c003801c40444564115490040e08101c090140d07008140349030400c1100215084041d200d114003c4a0004010107005c02000090221003171107502034449410076001c0400c15601040146e062051a281d007400c5000c0c40c808aa0360340024080e89401065140040c80841c1e500340c0340400a902c65010070b45001d0b00c81c6582c0c00b40b900252001ca03a1281c0300c020011110513a80250b4540c0b500c0c1c841620a0015641c0000b4446443d01c41c6645490a81815030260031030010700c400c116003e0350010a0395039940e04540d503902d440c03c5852401d0003007e44544e19996105480500c07114045600804800d0030507000c000081995401407840d0049100ba0400140c036180106450f0040b290307c0051980b81c0300c040702820454039640f80c005c448128608400507510300c0382c98540143c00041c4039804400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 632883812 1250 632882562 632882567
    0xc010804021f020a0b090304030b0105060f0c0f1b0609090601110c0d03020a05060711062412100b0105091c0606030816030912020a0303031812021b0d05030f0307 71
    0x2110a01a00700350652201011450f80008029084178820300c40c40076a41c3c0c644d6003d9459008034000200040210001081180303000005402d40d403015000d028504280d5515807454041030100c1c0c1c05168115520701810703040800c8900174002e8059441c1803600203040c00143e84450014009414040d145410080c5c07404100040c807644100a02650220240c41c10080d40d40e103408841201c040c411440001d41d002d101e604450318102d010380c01007a10742c64240007101300c000940c050307002d90440c051030258540c0e80c80e1201960145200051300787c1105c0c401440c0d06071850400702c2414000c1c10801d69a0300d03103910041d1100d0745070484070040c86584918200000e081e05500142420b4130103d044e403a1a5480710003030070114420f4071041725099030789480c40c6109070745000296110030b00201c10004a4001c0d0025003040080b034418849a002aa4560728021018190b03d001070b13200c060036040c6a0541d2026003ea40c504035141c94034803031640d80d02640c900ca11990300c11030040210128041d1070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 632885062 1250 632883812 632883829
    0x3070818011d2116030c050309030d0f08090f10090f17030108070801060803070f0222022a0a080f211b0304021311210601200c01080402 60
    0x5076412007080408450407103940d0341403450040e443c50381001d505140162401d0883d041c070041c0c00d500840c1016a600d09680071079202d0810381d001d0000708440e0b445540c043c4035074800e00d5100e484404054100c0c2d00020504038000301148030700d5114001111380307481c001034518005041072101080f444158a482c3c01424030070f181c000c1503c401d000070300b10400c03e00c10241d0f068891035400c40d450940d0b180070003030907900e1500c00c040a9070010000c1401085401d404070440c0ba0000c0c3c001655201406800300c0f010761071442c10148181d001ca28400301441c0d54855039a006001d82044050000c01c07a1030035100c0980220040c0070070300c00150303144001d401b9001e40f81009800c0c20741c42108140707000f4040e0040c008580a40141e041a0a00c0320b80b980548152805a0340140121007116400ca0901d4010034521500043d100d209004144d02c0e4480501c007180c1c1001d05c24443d45141c140000050b02c0003000760b98107120307e47d54103000804c0300c00004003101c8a0200b444e0455094071180042840e04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 632886312 1250 632885062 632885081
    0xc0310030c0b071e080f1612031e0b0a09020c010e120c1527010b040f150503070503030708090d0f03020a1713090e0f030a090303090503030307081801 66
    0x10007500c1d00c00114050600c001e0301d00c00e4080d0500d50043d8a80c101c100c0100b40020200400003501844100c03420000080940310b00c0500c00980b0040101c2c584406400d0703e12195810006078076000301c2c8001c0e0944000d07110684403251401d03c580d4042c400024580800f40c0120a0420360215103680004000d4010703031400503244050703540514034655101c0555110281841d454071036000d800140c5005001268850b0100b50070f03000e080c2c0213042080740030980c5028100f46941d01e4410005207561944038514003a00c80010004a0f1b10480c10f20185403903c950261380320750071152007004640c8000c011100a240e00041040e62480800002080185190806803e240200c4280c0d0f0405400003034103c540e900980c2043c022900d01c03421103409205000006010001000042040c20031075006940803081e05001c0e1880c0055072244145182c20507840800010840e0301c04100b815000403d0340c0182406a010318a180b403c980080d0120001400e001c3d0481c0081c1d00031910724100b903009400c2da = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 632887562 1250 632886312 632886323
    0x1080408071a040c060822050709110414100c1e0503030a02221a0c120d14090f03070b06190b0406020f07150302031003060c020604110103140c031003 66
    0x141c114003541c60106281200e04841c0ca441440c03000c61080d0040b02c0780d521464611447c01580389034004031301125038016070111510720030303950080791401d40c500900c201880f40d90542504c941c54180d1402c0030808442240740a52031001404e18007581c001c0718604155003001f008014aa00710175000050300c01240c0242040c0400f10910881c400d2a800409010340070704004d5800241c105503100d2271921a00c03840409061313011101e4000012100900031201e120340c16590908403402c0700d03201692100c10a151100d07501d0710040a0485044c645540152803100101444071880e1000b680e64412901d0103042d07501c4120006205c0d580b014100413100c00c0311078070000705c696204030700c40c0c5507045405950094043c03528114480d080002d0508100d803c151824081186920b0051340258000741690002c108400f0340030003c240f42e0b001d42410300c0480c3d03000386200d283c1410a111100f003040001810182496414880399004101c03440e006801104610398940302c100411401c08100d9200a00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 632888812 1250 632887562 632887583
    0x140711030d020a08040b070f0f0f1404080c090f010612090206040510021b010f090317071b0315050103020f011202130f051002150a0b010203090d0b042a050108040807 73
    0x10360f4814091130280703104401e581c9991f241c164003507030060300018118001450710901103d000c2d00c0f45041200c0e41c001400c0000901c04902c0121403030703074440c0d0410f02540e4400c2440c032106c1c2c2400c10740d0541c009454603541c03196504140b002401c1300207400070b480103d03484155990544d80c3d600c040301e006160052a00800701c44882c406510f82d140d400c0b2070146c0710000d440c1c0c0c000075400b0700d040035103c58184c0da40140d045d0a50380c03100011008a501590b1101082c0b081d080011003180805035525100035049800c40e15501e42001200c001c18403400010f41440010030050700d807900c0c80d0390302c41002d080c8684020700c2c0070882c00003401a046421a44401c5020004920f40e0300b001c000d0030391304203407004030700340a11000c240d03034401003180741150507036600d000525021407a40c0070f0780c0001c0d01403050ba4a44400380d400154581c210507810759041400300d061000700002d2640007040ca14840c0301c40110303051444040990340003203100d020f0512965000082c00c22000200302c84c0c1d4079a111340b0006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 632890062 1250 632888812 632888827
    0x10f0614091809010c03110904051f0e150316030201030207110a171c0203040e1320210c010e190305030a0f080609010302060d021306080910140711030d02 68
    0x10050b80251030054555292034407200c0150321901a2000221421140c01c3ca0328205006000003840b0082c01011128000708103183c2c003801440d4110028410302d0381001c4142005a4244941100b84008a101e0707403000200400c560240140718049a0302400c0c010b0b124622400c0031500809116092584406039500c0484e224105511454180003200200c400c07082c100d804c5030090341900442d4001503401804200321003459000b1300355004480b5126130880071620b6650f0400000040e010103044c0510941407101e90609012025004825401361615600050700c000d85815400030b0160411565024071711280d280c420171041c0440e1090f003011902541c900380561260090304264000074040d124101448ac82560030314003c51000700b011465920b507034204022a40b055000c601d5035074003404800c0c0396029411001c0001e1606844290040c9803010900381440c4000070030844035864a0045110720b0b231411103031507200c1d00c10308014202400e01521245940038107130349070307002278000030310207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 632891312 1250 632890062 632890099
    0x101208130f140114030a09030507060507031b0c022d03070801020406020d0914010804031202031512070b1804060b0705030a080f070c0f1b03050303040b0c03010f061409 74
    0x140304541d9040b004424418200e001180c035400d40700e5070451060000d10108540d1304140d0701244640d07219041c100d1a248a59032000c0a4410440740500880c0e83c1b0000c0c0103034003880c11700c4c100b51466a0310f8094101e9010380e00080c90020440c9408500c100b000e00203c4080c00d40003140c241e86036000f030490703011960b55001e081c080e500c1409003074010b002e2880520715580c080c110f03440640303088025010905244800444c2d860100070720a84c10051070040c0014001038038801036024200c0d071101d04901c00103100038048010026a07214065910018003005803900b0320041c0e400c1901420b10380d0301e802c59030900003009002e140c0c01c030302c03010340700060f1080030048000700400400d850703138442c12055604c1c0d400c0c10034120401c841c15008540e1002e030314400030b22400c45c10084c140c03013003109102e000f00c007a00402d400c00711908211a150f20003c1480103110246100e01d501040703800c0001d00c3c660400320386880e043e07864420341e03003404600300b06061020041816184c9108002e000c0240074035110006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 632892562 1250 632891312 632891339
    0x71205180f011a0607080a050d06050406170111211005150301090c03062106110d09150905150907180903030b0405010b03150a030f03020c130510120813 67
    0x20440106541140303503c49082400503110b1181e0450380300c0d801d00152110503111342d407103554101030065840c400800d681d515440b5070009032655180300301e03001032000a11401c40e071000010541e0300e80d05000e0561105864420844c00307100103c00c104003500e801010480d81102c2e07030003841e48460001c0b840421581e101020303504031200d80c1c6040c058601421010b404540607800380e5040ca060032000501e02c000303000081c40740548545000540014070301e0700e60903d60803071a10101e540e0380350a10300003072000d820a030307003092800c0c03200030004c07008150f132059a01c00324500744035070740d100000c0001c40f091414403507280204511144000700c155500038a4001300b00c80b220440129246c00054151800c2c5441401c0c16646803001d45465501c403100e44c4001c0410410429510001d603080100004002045481201d40300740c00410403800413400b0000b0518400001c01c82c0c0ba8584400c104c003101280c6031400803101c10075a001c20345041400d041c0e0300c521560b5a07000011300d4607040002d00c94014941e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 632893812 1250 632892562 632892581
    0x1b09031c081303050f0c0a14030903010c140702010f17040c030c0e0f060910080708100b06070c050405040201030906150905150108151c1b090203071205180f01 70
    0x241d02005695100114003038080d20000680041e4080c84a05460440c60b0020b107000048242280d0204802c0d0343c1e0391010001d410fa81240ca5000490425001e0409004070039048d001ea041003a01c545001d2940c9000b0f0154400280c104660b41040b08006401381a0919080190140084940c0b90500b03002c01c10031001c0c48200da581095050004407800c0e9604001d0044402300c540d0749094139000c0c01c10080c0c20024085041404084c2e0002400c4130f0100401001001d216000d007610312943c0703040400f220b140c4c94103580aa4410403552000400207a100740c10358908a400040c0d0f41ca81d400100c3c000d0010000c0104414175292554000a200d14100340481b0003400d4180015aa80da0b0441d445000601d09035021030076000c04186640340b41c1c04030741c40c6600d002d80f10304890710f07054042c0142c44c01c40450650b09031256400b80c560322400480484050324040358103600c0d50070000f00003451400d501042400d259912004100c041480d2a0740c9000303078084d078040350090070a603408140207220056 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 632895062 1250 632893812 632893817
    0x310030c0b0307020a06051f0618240324140f0f180604150e220c032004060803180901030f080c030913090201080f040b1b09031c 57
    0x1000041c1240600044070300c42c1000ba0702070680001d241d82d802c00078000150800550420342209804007400003180340c0300038004d035510305400c4102e0000d640b1000070705402044040394628440b0381c0e84000484002451046840c000a540038200241d01e83c66003011140014160334031000540c10003003050000c4000c0b01185d000009030381481c00c02c6001505801202d801c0414076143d480ca901600d600c156210b400600085680d10703498030150403504594200d519007058003001c1c003c0703c0300c81d02040c0c542e0590700c0b400b01c00703510310701d840e50124501742e0b01c0001c141425000790154802075002e1000e008140c05030042c01102d440300b04541d125005002d1035180405071144070311480c0390445a0030304a80d0424220a50b803d02911400c0542d40300f105106141d21007004002865194260310f5000c1c1481510006010b05c1d02e4400149008005010350035203100300018400441c00101e4501c1d0006402e48140400100d01d003001c40050050401050781409440e094000004c10420107601111003036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 632896312 1250 632895062 632895083
    0xb010e0103090510090f060e01090510050103030e0607110a03111c02060f09061204050c0a06020c10030209010905060409060311090705071128090509010612120c08031003 75
    0xa200440803185280b401520540c042c492440c0341045540c020240d403401001502400c0710940c94a0041d520200540c02141e90340e20181800d010090001c0761903c01046000d02c202d51450320014810f604400c003403031190b40c0009102e41004071070850b842501e00c0c0a000512415035a0400401c070880b00300c5a140500e0354124404000001117082800c61b640c0180103500b070100e40010320800e1b404c0020b042e40c00100c104140d40700072075500062407095208400501204031300d903003445501d51056100409541c880045500c1035605e000000d69505200c0c40c005841709203000040742c0c80c0c038043d400b05401c05400640403c10003803d03001007041c2c0340240c604031520b0582c8428000c142108440e15000103005000007c001800d424541c0c1031b030030f00100040002c00003030040910020703000c00c1003181144005410030000020380140b0f0350000904000308080383c41c1125540031524154070041c4070043d410507c1c403150380555030b0514859000071300c1caa100c2c608001d00d02805289800300307a03500c0303828 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 632897562 1250 632896312 632896337
    0x501030b010318060207230705040c0e100e060d02160204110c03071b1805090d030b0d06020304140a1b0f030c1202031507020705120d05030115120f0b01 67
    0xb4018400300010100440191844640344c0d03400039044044101c0c0d0b0a524040b070b6038103161980b4085103070032848801520049181100708001c64a0345900f040510142c00340c414071540d51020800c190b10070a0a0149420441d080014001e101d103e40c61401a840400c152410b8020a800641064800d4508122281540c2c0c0b841c105d900034a4bd2181e5513034410046040007a02d43d10180e018001c4002c02e1840840d2900f078410000c0c030b600131034079440d1540c80f0304101500408010342801170038142002c11815110b5000714800804441010748031540000108041209803a44900307040a5107007550441c00c103030300e07041c5c800fa001789220502d45d0a417175401144c0240710b59032440c100d0707a00c280d03212000b03864407400000241c810502030f81d05004d99400910030011b01301502e84600c4481d40500a0681403104001e0800301e1824200700a5110000742d000080d003010481e419111403592140c0c0003003210b20101c03010040841c20141d0507040000411400c0780035088208110341c02d03212131481e040c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 632898812 1250 632897562 632897567
    0xf090f0d031508070b04051908101e05061c0f020a1202030f03030c03011404140132030d05092715030313090e03090a1e1505033402070501030b01 64
    0x13600849003010310400003040720785031824010903142c10800301101c0040d0764010b03035801c0c0710741003000d0071095455110b0000340c000b0302d00c0c00c080e00a92100041000c0d00384000131601c0c0c142d03103050004007141501d40700001e02c2078295969101e00c0c0d00405000c0300130b8444503401a400c51070360b0100d020713100b01c0764200c0728494084142d91140c0d0f043c0b2400c1d400c6a20b40006000940d00450f100ba0b005641d940c4410184003407014018060700d010040301c4080f03d0345180d40c08400c0c2c80c005130b41c00c03038104410f000241c2d0b5501060416844500e03150460701c414509000600c1d415a04400f41c40c8200c0007441000c03131881412885101d51104405207441880c3e10080c15183e2042c07410200c05048801010711180d0040c1d40106040d89402088034240304150740414078449040d08024030b159440c00f264140c030800d40e5000e1002d4400c0b040c074000b00381800304000d002c40c00050301c004500740c000700d004004c8044400d00c50b90304130782c2c1403c032401041c02a1070103502d400a502402e40002e0a00718410447d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632900062 1250 632898812 632898823
    0x9060501030c050102010c050408120d0f0203090625140702040b030f0105060a050406030201171b04031b1a160204020706290603160e04110f040608010e06090f090f0d031508 76
    0x20500c4025014800c0e0411286003507038403c4000c07000cc1503807040c20a0003080e85102540c440c0c07190750f0007081c8904005030152809001480e035400324000001040384c102e0f9004c901d9015807036002c0b6000d521401684000b1340a80801801d1701d070180308003c0100d070030880540081c0d02030003064074079060039a11101030205941240c040a408503600d03080345d202600c0e49a1015900506104032855400e0702c00b25090f945502580c403d85409502c90040641c2050814000c0010072150049103108281c0d40164a245d0181c00418024462008141000e6499a80403200c4980e848841000228840325416940210701c200b420b4601440c0c6211084a04001c4122170046860200008803c50b0006080f60704d03140200d40140c0181d00c03115100e0b115545040948903080019282d151510b08041e40142105816440307601424410303000c0c041e20303455080711290405041c1308041e207a81d4542d2900c511b4031681480103c00d5208e01a0091642c0d0760550041c0b95849049054a40b8141c0d500880783d0b440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632901312 1250 632900062 632900069
    0x5091006050a03120f030f060807030b010e010f050616020406061106090615060904060e0a29010518031603060b0a050409080a0c02030f030a08060f060a080103030e0409060501030c050102010c0504 86
    0x2020404c1c4031031120380c02a640410074024a20340030580c0181100c00c5005d4800741c7d480019160b00568081c400c116100080380d0242905c0b0740b0404040d8906024a03100306124844c0ca0f000389c00c002130707000c4c41c40c0c80c002980f044507801520070302c80c1e1030340d40100604003209010300c0e29090098801140e41d0410200d421400761110500c02c0701030700f401004202d0303030b40e201c0a840703540903688400004100442d0903905100e02148003000402c0686a013003d40e58007a46210840303203c80c14188080d0300d03038008040c1c0340b01440c41140e801184003a440032a1401828030190407680c010a1800400c01610f500003e0790b8502c00d8603200c2c4841e03a00d00c14441a980c68040c0140031a509000d14400c8030b01c0341c02c1c2c060309a400141141c400000751526941554052203030035001400900c03c000c010300304003014012a14040d154245024101440140b01c0403041c04010104003a14442080d1691903410900c0c0080d041903003040311356964a04031070360000e144640f41c0175500300006000124003c1c000d0343c1c01c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632902562 1250 632901312 632901323
    0x50d0c0f020c01080c16050102030f100308220e090c120118151b030501030317070c030311190c050c060403150b060d0216050f030307020c2205091006050a03 69
    0xd00b019801075500e03400041500c19010b50a20111010200e091420302d42c1e0b41c01200010307943c1c10078035100c203403caa008040044107890641c040001075400783c11241240307800305164500401c10341100d801c080300c41d4840c0c650b99646200b0b01c00008400b24401c0c02d01642110b0020179054600d040390300361b6a4a034404401e000a40c0d0081001c00c0d40701c05c0b911401e00d00352000180c15920b042d41c00d0070028198481c10002940c5500500403d60405400c42003100b40c2c589118480c40d0014005090703015041d802410140c44456042025000500b5074801c010308600926101d440800b008141c3c04040d981502c0c6442418060052800d0040864081d660459204c0541d41074800c14400900080d07100260007010400145030b450b540c81c07010f840c094842c41549020481a801c240d8604503000c0001d16160700708005000613550001000c507455942038072044807644401c3e64540600c10300525086d021400c10f4200078082c040820612216840c0c18030401800d80c40c1c4090020001450000a11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632903812 1250 632902562 632902573
    0x10618050114090a0b0309070902040b070206180a1d010509040305041e0902030a09060c0216290a0801181e020318070e0114010302121f080706050d0c0f02 68
    0x4194070072503044241c01040c10200385450a800c000c03c107092201e901c00081d85c100031003404400c2ea81444010024040c520080d0b05160030450006881c0c490640b00901c50700c4005a030954001141041003000700c80249070010182d51240300d040311910f049c1d2013104000c0c1020000c03895280c1300d950300e400f450f09076440a0a250030042880024000b200359024202004400040c03810a20700065108000c0c1c00f80100c0e03001345a00c3e1107000c2c0c41280700d1150540d0420491021008d280c411041c04846071160a00c1902d000c0f80c0e403c0d0b501d07412140c070041c03401d040060001c2c006070300301c0d24250481c0e504900801e00e000c00259210201c9440c5080e904060a2411600805050700e401864008207501c048044500c1203101a0b4a4526503510008481c059000100310100c030708050911240c0080c20154542032503115565500d000003041c075650401640181c60000c0d084c1d00b800d0010303100180407545185c1c2c5881010708160084034520006d542000014020107115088003880c04040b50001c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632905062 1250 632903812 632903819
    0xb090a1d0a02030405101a040509062509180b03120408060c0912010c020d1b08030a02250317070c0510200f03100906060c0b04050c0d050f0105010618 66
    0x1c0c0650700250043d074251084030041c00b11030038948208030810b1052203d81164080800900c001d444004010f00000c1d00000c2c00c01c03c3e52040c50509800740c508412201d003040300406815110a40c00c0d400c050a844085031400c3d0f901c460661000588410440440d11440c1c80502c480a0a02c00e0307014420560b004280401da003c1d107940042c142102c001050360304845d03003040000342140c1c2c00145100c01a4044413240030314503005200034000b94201c11074070240f103d26807070f6207050388030181c96401a664000303251040780605030349071105c60345a80c55000321070718103080081c0010f5181e0400c5004030305820204030410700507100802026404006000400000c3e00c040340104a4880b1400d424108075280500300441140104840347c2d95000d11034503820440a848481200c3d0f0704140121440c0200611100d60450000005aa403000b00c5107500da13290b140860400f6400140c941c1c10120003070700542008408a10003411007080d00007004160f90340c06003241c151410014000e0561408601031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632906312 1250 632905062 632905081
    0x906092738060607030f05161403070c080c01020706082e06031118010e12011514030705010503010e0411180411090f151203030f0103021504061202071b0b090a1d 71
    0x30048232040625a05c0100c2a50301c440d81d8001c1d00038040c130000d8000184443c10800c1298882c2d01800f1108002d0a01c9905940041d644028130301802042c4101030340018400074511100d1103268071042d26001505c00c2c030015483c2080010f020b5100441c2c105182080b42080100584040d92095809130103c01c84075001541c2c0c40302000700a640020108000d0401c00c0d10901035003210783c192914003500f1920307040c007072030301c442c00c0b440018401d0300700080070825603078072100b613030305448500108154503111441e100c0c020b042d00b01401c54028441d8208003504039511010144502c0c003502007902c0650314802000b405643c201c0706412125079140208609800369a0108944017024002c5804041d1360140907142da0021500e10070301d180791100500131400d040c403140c2a079415070380c90141041d0030f0520180105840103401d1110341d03400b1500c0c006100365070050a400c0c044030b40e1000422a1213000d1f0880a40c402510b15020b0000c80e100050f00b09041211850341d000c0d045028440c80c1c0f5550b441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632907562 1250 632906312 632906317
    0xc030207031b0b0105040c051e041a070c03140a41060411040902060d0c0f02060c0415030605300a02060904020a02010603020907090906092738060607030f05 69
    0x7d400c00c00100380007007a45814007182c4002e00585141080e501d482c60304141220080c2100c00b5013485900a00140c4002405158006c0030380307034030484854180e03100d0b001080c0381c9080490041c01603413810400000103041564000e40c0503036514034071410780c6008002c002c00c02402c12080b10345a4060300005c0c01290074100ca00f143d5540003400421048103a03000030305140c02c10881a1215130344c3d8084c94040729040418051300c00403a002030310440c94400300c0c558076030069200e48010180802c640c103085034801c0d440742c8040c02004001c0701d0030868551910385030641e41000380032035a60882c0d000c599081c000030183e0016600800181c42c0c885500c050001a400c044080015503486010110050340d8610b0b00030b05c242416680d64400381c1ca00b07000e12065500315409888400d00d0154a0600c01d060310325000a21030704018541180401840d0958030080d204403480c1d400351845030610701c0c0d005c15248078414074258500c20403203501e40317070200704162040c0c100080226545140864419004901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632908812 1250 632907562 632907581
    0x20406030c0c0f14031e090a0503060f0a0e0a0c06020309090903040b0702061c0c05071109040c1202011e12150b0405150d02070803071209080901051c0c030207031b0b010504 76
    0x50701c2c06c0002892600e11404079001c0034003602400070505010505064003800e0003850b00301c0003001e0900300807044c03020742000a050f01c51103d4031500382ca2003842041100b01e4815500011154065a071090f000b9100e820001030320348034401d03001c0030512003140007040e9070503541260503440c40c00e130b415420086641d000341c00d800045600300e44150703441000751280a00350700994881555629551a104c4401e00004003000e00c10000c0e00d0078040441d0440107424140c8000d448020414005400141c03a4216400c0c444003289242c10f003903141081d884415154440c41c00305003070040c441c1c544040200c6e20700d640234041c0e484509002c100121320b408801d00c140d20411461103450500440000300c1a640711b01c0003900c0c5d9000c008180700049500a500c5400405c0909040203c0002a61195800e12070241e1150401c54003261a444d4403155450690f50030944600c100500740310321902902a42003514250302092010340310002e42c080d40700f4642030b4140e002c030803c1440da09150070040104084807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632910062 1250 632908812 632908853
    0x151605090a1e060f110601060f0e100306080d05030906070c0c180504110f03060703020a020c031c08070f0206040f0f120c0501060914040b04020102160603020406030c0c0f 75
    0x880011040c003041950300403803441d08144907100f4101180a04052482c050030410403621140c00c1a4110011031010306640c62441c007025580315040c800c0328407913040703031070290700c0601d00075000003040d01540150103c891400a442c591703580c418066520f40002c03140d100203908050005000d4070704c64910342d42220301c80c0c8001c5a9507616100d455600d4412904280302407943e903001e100038131132442003564080d10125120a020800440860b894100140c11482403640118050343c0036802070090f903525480207411034104c403003400c15034100000d9a03400e40010920480110348401c0c4200c001c18590405500200719a4440ba46c0c0c0403c4150520320070f49540d11401c600c07400045800403003072072402d03950351480440242410500e0031201c0e1588103051403403030016109044141c0e080e080c2d5110340c101c0c400c00f440d9501c80c001030f42000309004200c0800c114220300490f00700d40640c0680107403501030741d00300304230b0102e25000c0e07a0400082e500038220990003183c400010f02c800c0d40b4941c00940d4034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632911312 1250 632910062 632910079
    0x2070302120f06010b0a090906080307030f030f021602090f040b0f0403090e010b190206060a05090402040e03030106021e07121515090b01020f03030c030117070308070309050315160509 81
    0x440340381441d82c04e030420140c1c10000030303001b203509500642e0b400c05080b03441403c0000314078194030309580c0c1c401c0241c01000c1c0840c0100c8501d0541c0a9807180060b1101e14070150b60316500040802042001e2503000c0f40304041c4680850f030307603800e800c580501c42c50344001151640e8860312089218000c000b1f0084040040d03805001c02d1082c042c02c8030701e0084c41c0400d45c0c02d45544d0050a0102e0f80744100103030000719480502000034980e038451664080b40d03426134203501c43e42c0b580d0002c41c0c0603003a01130418019210000000510650000d02030722041d90401c6006085100369110640b503519600c103400f450a150310302c150124048000780d028441503060001203c0410042c0c00c8c02544d000d0b40f101012a41c0c0e07004112040d43c042c40030300b0f6070141003c0590b107145003800745485240018010560a20440c13022992080c1d010040f4030b000d5a00b06000607129003c40c0360040c108440f80c01024040d000b00f01100042a9a41c0c824902030308413007a03540340c0c030705044000300c8864011503d840d901190381c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632912562 1250 632911312 632911333
    0xa030c080702031501051212042603040f030308132001032013080c0607030f0c050312011a18091332030a0903021c06050a15060f0207030212 62
    0x104031401d03a450007020107481369072409040040d40c038540b0f00340862a80100f0540d0703501030382c00021141903c5610b1009088402c4445030410280c01e11503404c185448005000b00720181d1100b50308046a200f9900c000c1d0341d0751615001100c110115000600d0301310001089c4543c81110145085440c4040c580041d000c1100071083c4110200c40c606900344c0a00012102d50f81c050f003111000203800540c0040011000740d0300072542c01d21640c140541005050700e0081d4410348141e08015296801100300d9898000c956001e002e194800c0c420100903000110040c040000c003041510740381c01c50180c0f1030545110000910141c410f0007001100c070302d10090704241c000713074071482007000c00514100c616415400c0c84003a4031980d49082600700590f8004e2004108980c4d0100060003520f5040d200e004055401c4901d03843c403106c4082000700414104020050520b90343d91111010350403a103c00c121080e82c8220644000000030084001a089402c050000d81001c08919118102e4281250b012052 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632913669 1107 632912562 632912569
    0xe03031611060f0d15050406050108061908120309011526010f0509100c08010f05060c07080a05030406020105060126070e03030a0f03060b030402030a030c080702 71
    0x301c028000409034031088180c90340c0d40d00366800a600d403ca19600200604a0b0b494101c500d40f0301180001124603007070045004644043e1642d000c40c0d194641803003200540b40006804d413424500700011150310801941e800c026960004989034100360380c22a0030340b042d023402c3c440000800c0c6014448014010482402c06500c8514090b540c400f8201c220b000d8081c014110b034000d45003d0401c07650044c081009000c101c081c1404210380d11104200f503030103110a02900e400d001080308140010704060009105c0703c44650202c820b901d0759850640d1404c0b0344a2130884098002041c1040299024018281c1045003401c0c4030750303054003101c0100f5140d140602540c82031040134000c2001e241c0200c03891125050040c0507240e43d040d0081020300800c010151000000b49801000184900c51401b03030381c051680200903010205490324221604100312800b81d901741010085240140d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 632733812 632913669 := by
  have h0 := BRFrame.cov_init 632733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632733812 ≤ n) (h2 : n < 632913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
