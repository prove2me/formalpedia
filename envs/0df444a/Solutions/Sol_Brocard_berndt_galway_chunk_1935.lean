-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1935
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:13:02.916395+00:00
-- url     : https://prove2.me/submissions/57f9b9eb-b618-496d-899f-219b67b1f809

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 347841726 ≤ n < 348021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 347842976 1250 347841726 347841737
    0xf06070806150408011e0501081e01020c1c08010608070806011209051009060f02041a0a0e090103150c021c1103040306110c0715050304020f0d050a050102130501112d010c 75
    0x202c0031001041b00f041c100300c0143e10600803503050861050300e40341884011283d444c9260100001c2c460f00b03405907400b0b9100c0f0743c1151545814840c5940203483e01c1464000850340003400412100d20526440d4405e032400d0311f80c95041c0e1a0180111208021001440651030381e64004500203842804a084900459400411100c01c5030038100102c400c5141da5540340c610400c01044000e049001101d060012401420b884803005882560480c810780415680302d021000040100300e20503001c04041350440c6410440f149031140c060340d541000000c82d0f00e0b250814410384d0645803203403810f11440c9510132b0650381016030301c0d62184140c962402544495000214105142324000c20140340100002029030440003c4200c2c098027034800640042d00511103411180d209848403a02002d05960010072182da6803144d05003075000b0b401040900c10b040d19550742c001400d611a684d41c0f10000d0000d4050310094074506401c0008010085d01000800702e202c12b02e00c2801402c0c03040b07142080381520380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 347844226 1250 347842976 347842991
    0x403140d0f05180106051806010804021912060b100801030602130503010f060806060d08030a0b2805030f0c09150a0317090f04020c0c2103071a090f0607080615040801 73
    0x200350a482c0640c06c0903000b0039242047c0300140c04000702258100c1800e0800301225180e90010414281845038001c0807414040c00003c3c002d4001d4044500083c003400041140003030000401a560b1014000580040d03c3e50005001064a603801400d0340411010740d60150761303a0702c000c00d096840f034051031380c1100e94441e01045440d4007804520b601c03034021a00d90484809564a02110303020192900305429990303404c420b8075454001c14034124158402401804030070440e0490394400042c05032a00900a11140000c0705500040807800940c00403d00c504540d2780f05000c02426010103441580f00145210020108000d00801c080b0780352000c900a0b40d4442c1d00050110110302d88240c5c070300880c410000784403061404106040e50920840c0e0524415034110443d540c2d9041014018000d4040040d0b58030801403e03e606207982c03640b5001c3c036030075030742c40c2d0040c0307a25a101c907a500e08880e00103400140c511486200e807140c2c80400200109c0b1002c081c1c19078404250465040a1441d80d5070b4030a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 347845476 1250 347844226 347844271
    0x12070e0a0e0109051f060c0305040f0e1506030108030a08131a1608060d120c021504030606080d0c03080403090815060418080a030b0105091c15050403140d0f05 70
    0xb015070003140241c02c1c0c0b00e0b0040031030b241d900517561403050400308400c81c000e20302014420301c110360003461811402c3e0081901c0700f1200158020070b1302c41c0e051881402046400034200041628100c5003031101450421120305411382d4081c0700141b0460076044011083c0c00080c0300e030015504c1c07030001c01e854019039207016805540c0c60440c0f102c091003401200c00400684d030b500d407081951829808982e0f0031424110440c02d480010514900035032100724402d90b180003101d41d0300508110b0b0b004080501129076194982c070303200e80389032720300000043c0140030b600c000c02c1c002c02603d90810301c603190080709c0ca9600c010040c20310700c1c4c8090036480381c484141444203d18180c041c4000b203080030802e8000500844c0d4400200d8442c5003114400e140e112390b11403466a014000741c03011000090458000000c01003a03a0310307a5003217030703c0884110361144642d0014098900c1454400c035815184c81880154544500019400c400e2083c041c0d5912040c4455030265140292800342108502812018858a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 347846726 1250 347845476 347845481
    0x8030603250317120903130b03010b0702060703110a050610080d2007170c03060c070b040602030c0f0a0305071101090c180b060a0c030e041112070e0a0e0109 69
    0x1496030700541d0000c19040107904400722504202c075030100f0782500e000200050781d405801903410b0010052a500c04014001d000800245090b0001003218070485850b400c454190307000a00404c80303504004c1c05082c005082c520020502c04d1b0090a1050032020340c401e8007840c18000c207031b049903d9000503007402102041c00440c20050b1405030082d0030707452070301b0038020805101c2c200740c1d1112120000750b2900d000401e000c003401411034800101c0c001c0101c107400540d11124408660700a01c02e00b000a00310404c0442a10081b9a120129500b6a1500d4a40c1e10194001604928076410100000610f040d41000240245003071620040303903500e03040ca009000011740a01a0b40d003139043c62148800100c1c42d0100074169902a070003000280b42ca0711501c0020304080340c046801500000d15a0050b68000e800141c203940f0076643d00d281d8034000c009000c2690202e2000840080c400c3c401c0324031040c50300d95110b80c0041e492810301c00344100d140000700ca280356580041c2c00d4050000060100f8101c03030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 347847976 1250 347846726 347846743
    0x1110301060918060501020a0204050a180b010e0c07020d03050d140103050a02040f150515070c030b1006020118020103180605100302040e0307050d080907030606090c110c030d05090307090908030603 87
    0x900b041080745d103800b0000c1c1d1240150f40000b84503554510026221600650280e01050b00542340121405100c0c0b802074003491084c0039030081c1c650fa603000200e1020f1200c084440311070b0f01038130310003030b581c020b42d002e41c6d56401c0041c0b080e90458850341d1280844000441f058000c50096006003400c6000b4010311040301c0c04040b07030503007050401c004001040610086c00080710016156045d80d0841200c80080364015103100030100118000b0000910520505860080400c0400b0707515443d03840c1c5050b82240c14100f4084c85481c40042103202540c0a40e0003815a04c1c5201d0804c3c44181c102c1c6c0d40c0070300b160021681c1850110804c00c060003075081c05d20584800240343e0000718900010fa03252240d840c01034200140030170543d02c0014207075a00a01464005642c00482840540c0d01d4404003805000010031050015000c800102d40c43c80c00010b21107a10170028000d0b0401d410b0b1b04d00c04452981c4603040458051262080c00130746900c540c820100703014010200a6200d0070020101410301e0520b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 347849226 1250 347847976 347848019
    0x60e1003021008012702041703032d07050a0c020a0b0a0906030207050a12050f1810020313051003090b0a060504051f0605090f09040c1712071202011103010609 70
    0x11000140708a80c00a216145c540c0c50380d02a40415144580804000e4403858001c003500c442401030111020200002840c00b401110900c00e8589203456150b82186464424032001c803119800811400c40c043c40050070800c0c2c40b442c00c0a1562043c1c0c000c26a80e140c16409140c125400041d1000000d900c0001607004c0c1c002c9141c2946006100d841d041c0d901e022000000e0000d0041100d08500703907002e1001c41f0010b0000147d171075218011104d480a801545010503030140022403580410380d8804012a6441e42580c144508194104410301101803100d941e02400e0607a1110f03154040f03413007041e101d84280d040240c0410301c14282000c1c40181e0314003406808840ca249400120040648845102912001c0c500140c40c0d4900c90001049082a01d03074040e048455541131100340170070001c1100941d040c030300c24000d030a0b80e008104c558584405c00c991002d07410620802c000a04040e0706a5140300b05032002150a003aa004503000641c401e07031101d00800d05070001040400310700003400456105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 347850476 1250 347849226 347849237
    0x170607020f0c0307030b070302070f050a022e030902370902070b04060b0a09020c030a1e0c030e0d0602270103050106090e06120d030b04060f030c0612060e10030210 72
    0xb400b000c01e40c3c2d04141d0200600c1c40404c2c0b000608103078444e5054406254018a000018080c9030410036294200c40506038060802c862180d01c0c00310107220f40700d041045401004d1150040b912040b001066513500480e808150700384100c5271b0440d400d0b580781e41030054580071a5090052240019108901d901281d50a0b0040c0701410100317906035030007a0302c5600048007103041201e400006030200ca1640003288007510100f0400c4d003844000000c1d0940321203036100c020f649007200400c0c0c14840c6000c206d41d00040e803101d2815000907c151280082c08002400030241030f0000e80e0b4850a0341c0003d507071058010a0700b260440408010144004189402c0c02c08101d00e504210000300811032a00559480c1c42c0319030b0225038241c41d500c01e400991402c510648101051800b0b0041c09070503e100610310841c00c1800104003100014094002c03a036015411420503440c01070155200807040d4865112543d0f02e1a0000710200002819403140250303030540915642036104100c40766901120440801c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 347851726 1250 347850476 347850493
    0x12090f051005030106080901110f090102011802150c011118011403040c15120603060c03110906070f0203071a12180c040e0f010f05090c090708070305040606170607020f 74
    0x2c1c2c018044030b06407082072800c180345a0787d4040c0203000d401e10100c0d0700311104000407071004180001010301000c0d03400764028014510b1303102041d140b0241d08400a03600c2803050045801c080a807a006002204404d400840e00d4044640304800d40e0f040301c0080380700c00301c0d074043c4c0440640c0d10070742000f881100c0c84003032400c2d8100798a07580700319041c2e8000c20384030342d4500caa00c1c14101e00403951040180c0102605119103501c038640b101c0904090304054002c68100080c8100944600317040c0c0e403401d0302c090704090070b01034541c8840c247d296000070107070703014003a20001007400016204120482d01c2c140700c0c10355480d0744800c1118400c01000b05a005001c925400c10001c42502140030006c0748001c603001300d81c0e401d090038003e0500c903004100c007805618183c0e01c0107680c7c10a4011910039106141544d210000d4801841035039030044481c240001c41c040b002031100c40c06036001c1078006015180000d0314030746401d008501c909040c0841c8000360301c900104440c495042200c2020308050201402004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 347852976 1250 347851726 347851759
    0x60c0723121b030f03161a150405010501031404020f010302041703030142090b0d051504050106050318100207050105040b07020f0c060304050f03040f03050f070b041203030912090f05 80
    0x1e0044064104034480c081c10007005001c0c0b802041030b4a02200020b000c45400c0c11501d01e452314143e80b09040c0694108800052558000d100340003800d4101c00c540f142680c0e55500300b111001901c44c0b128181a801c1c840801c100021000c0030b0780740d00c00303100119070340e5041c00108403100000e4401903000849641c505c2d18a42d0890f07440f0350141c0c01c47d004021407002c000000383c0300e4101542040c03201e00c10105090760b0209843e003045005e03561450090791810307110003c0c441665002d014540c0403420401c04110b2480e64917802005828070441500c43d02c48007041c03600c05a03880007009882c240e4452042c03200b40030b503615040b030700f01e40980002c1c445482c0c03020301c3c00e441c0ca00454419100e003001000160a03c4400c1c0030112988003040140d03075596486400005040030280010303070312481402034551400200148010590b04594219410113203420340800c50865151030407000c1640315000340000540314104103c6c001035644403004081d0a2110500c90502150710803031103080382d07903d00d0006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 347854226 1250 347852976 347852983
    0xb120106030807200a2c0a140a060b030c0309010608010204030b07080f2a0c010606090e070305060604050f0415060504170303010308070201050c150106030218060c0723121b030f 78
    0x1102d03400c1c0001400d5243e4200221050041b0204440c10b0750b846c04100820704469a0068080c100e61254160f0035413030380801d0b07030b0488516000d2040b4003902040810f81e026007040282d94030010030000801e5150712a240709003a6003081e40111440c100e010b0610809a400c001d1182c0d00c40300c05c0e08258028580031144d80c00f003850340101016564070090750100240c191200300da00c2c6c0e00303d80c4020702005546602c02001d00c459842442c407000c94020205110300c0c032030f01849000e0034000b0506410030b8146010020032882d07401800341e0040e1b07a0071000c001400450900c3c00240000d488190f1254a01160303001c21010003014042103400070001400050b5940b820707594803030340a01e80300d07450b96510f400440c500380c8190410a4000e031100d000180e15681900140b001c101d4401c4e0074041c0d4400d420522400c1d0043c0191a00f0f243c015030014002400010034001c0c003145d0201c5403001c40c8101001044960070070741000300d0142c1140f004d0745100d0b000650710411056090700244401100c46040300e89 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 347855476 1250 347854226 347854229
    0xc02030a0e062106010302090a0f081219260a090c05031906092402210103050a060911060414041803051602010509041407110607120b120106030807200a 67
    0x12803c0c0e54001040b044d034030071380c192402c0c1180900b00c080305544802803429202007522030345800d44141100d034940c000204080c0c8618072900481d0001c44c2e0b03503d030019030350b0b10b4000c102d0b45150380f01c4141d4024040071241070350b03003d0051401c1c000341f402c3d514145841d01d8880398000a0207079020030910b1804000c4a06240c4a00f0b070041c1001070415043d00c2c050b20448000984c0003800702a031a60741040612036401041400510141d40c00906040101405030203400d00c005802a04071560400204156800c44d4503040e10030130b0b44004510345d04002a00302d0300030340c2007000386062151180441c0e05251184807078000e0f100c1400c007000000c96900030b01520864042d200d00c1880700c007950013164040c10940701440c200820a000c240841100c14503100c2d0211001000120100091042441d021030803e0140070282d440507981d080ca40d80f40009401303c040b009400050700784040c200000d00b07224000c05148154501170f910252070414224800c1c0181c80300700380012001c003441145d500e108000d030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 347856726 1250 347855476 347855527
    0x90105010b09060d060f08061008010506060409020a0e0a1401080c040506090d0f05060c1914030703021b06070302030106111c0e0d020d05030c0d141206030f010c02030a0e06 76
    0xf5a141d1058104c4406072042da0b02c2140010304441010407100008104184103c0c07100d208018400c0d43c1e40000c80c2628409d0340c2094000204000178000140581c008186210300c80c20040c10111180c0d000c10000758a40c0d0100084100f08203103130030f4660740a0b0751a030b00001c1d00301d0300e0381c201810702c00041c000c0d11a05001622600034401264100075251462954198200d070594000b4a003441403043c65034000c030a02211164502c0080019902910222500070416100c0701e09590b036421041d4002d60120b82000032598003414802905601041071603c240348564015840b94980b2034041e00740030020900740b0854211f500c0c61800204c0b01c4031111a0780300e05190804140003000086012421202c00c081e42010308200c8600c2400030010040410781e218004444c8020f00150080701c40e0b8580514849907030604200404111481c500c8e581d411030340040036149071020035900142100e90074140440943c002003041e02040360400902d4215032410399280c1d25203202034450070700c000750124451 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 347857976 1250 347856726 347856739
    0x607020c1806012d031d1507110a02090405010e010501150503060918031303030909061a0d0b0d0308041109040b04151d010e061008060f060f1017090105010b09 70
    0xc810740d051040e0381c0e800d10400702d282c0c84452103002c2d1004010341840046030b0246c1c903240380d140c0b0700640c0020380a01203110895034151161204502141da00c2c040c03168070280c0d48288258040569958031866002d44e20420001803840548807d060954005910000303079130f240d80b0f000b00e01040e0800c084a40c4030740115800b40d8150303181800c180071007400d0030f04488a48004a81c4094046442030041c0669000b9100d0070300d1140c0e104020300a45005004400c0142070410950414514040c040c0180c07a0955401003100041000820140800c401e8160700180d100f20511040c004070500c0b0840c1010195101c42c0d4911301516410b07020700c800740c0000c1080d01c1002d8150903041265001514104a0303020004c4164524098a400f070f0540f0b0404400700c0c040c41001c90083c041c001c1c02e440c211441f880c05400389517909180442041c5005045c0b075002414203048a0190355040c003448020050743d210004581a48200c106600d030005090060701c2e85007900505c80d0001030b40a46400d500c0403200d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 347859226 1250 347857976 347857997
    0x30c070e06090603150c07060c0e03010f02160f0f120c1703060f010c170a050a081f060c031b0614150109091d0109060b01020609030403320a050607020c180601 70
    0xd05c086e40305145001d050189081d480d210b082d0380c030070440c040b800000c030001c2c4010004210134034200d11400b101280071080c43c50850700010445144000c00714000c20003105202100d86844542c0400a0207140001c0c96038440e210810821040206111480010107410f525082c0081403101000040c05030501010349111410440e84d510391220414400340300310b440d9a14900080c040c1e81000c0204004503420301c0010342040f10300908a1034200d00c1060607604540b51801c16a4030b028401e10030b0303042061000e6140500c40081c4203400303d0a2040200240c904501442243c81640203864402c1644d080078115610b0380e4051081d1080d1041028005103001c902c1149688043d00050f01031002c2d402c0c003000100f403190319400842c91020030f80a1303455a54a1540068a1748107034000105102040101040001a620003101100385070742c00c3e0808101c240c2c0605d40c542541c001003200c80d9841107042085007036040c0400110610181c880800103000607071545a6104010003d60401800005c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 347860476 1250 347859226 347859241
    0x415020d050f180a180e06040218100b030112120e18090316141c05071b03150b0f0d080405040207230601030b0612031218030c070e0609060315 63
    0x1101e4007284401000c000c803c81d640ca0071250b501c29503417260700340d107840c1c4a665003050501080c401d1042c0e50080c401412844030082b0104d041c40d010f090a014102078038004148400c255004601900902200009807a1240381580a5103880180700080010400c81c0e0b000c10b880d0a0460488410302c03e80742d40d07141d511003608500c0d6018140710408441410b208207801c0c1f09c0d1001002d2810907402041d284030515000c100501030003080b0700900090b00411440303002c9403581051345614810030800c9400c0e00e65940f140c0d01d05110880644403895522811403405160061180488090640c0c0038101589184c4554106011324400c0c140142d800140340d400700103040f981c02400407181c0034070301640c15905c080c00c1c0d9120000d00044071801c0c4a0306c0442c0c460b10300b0000703084154215074011840c0100d0828001c0e00c92101405800042440c2107401d9110501803014041055101c0020254903162a08007043c940e030103402d80d0300800205003885000e45000c15407408605203460700b0040d90702c9041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 347861726 1250 347860476 347860507
    0x15090411120a06020702040b0907050a0804050a0c1d07021603020d060b0904080301090e1912020a060c05090307140105070b0c07060911040b01030c0207060e1809030415020d050f 78
    0x760580c50300840c150740082002c158041c000940c020780701000030b9034401d01400143c5505442e440c1c042101440a03641c4644a014200c3e40140f0400a9031a9490342c2e64030003100e01200d801440518000302c07103035600040038a40e559840007851000705215082030300680e00b0f00303569000c080e00411780c8034034101c2072200d06d4000000f5080c001c6d0207805646454140101c446c0c01c280145400d407410510b48400f442400a00860503181c1c1410f0102c01c00e03920b984407104881d042503890254040e000c1c403100464158807030342600d518241c90350396071080302804045c24040c031904503220956040841a040d66408403e0381c50040d40100f0032010307515041d40990f09405008401040745046c204040704000040070301e4000d00d08140c1d0305000c1801000015030a070b40c056144040160300c0a5410000c80340700c1c00c003c020f5044043c210b02c031017500765070100b1100c1d13000310b550148e164400a001c1000c1407050101c0320b030806281c80501001048107200410780d00c1048030b10304c490300002c00d00c100c6051940 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 347862976 1250 347861726 347861749
    0x90607200f0303090a150501180b220c090617010306050601050c0706170f1308030a090b01031b0609061e0e13050a05011202090a09031b050304050915090411 69
    0x411a41c80b807800707104c0140e860003080c800312024041181c41c0c2c24041140e0040307a050320f07031171841c015441c10440c43c00802402c603255120740c4551515040007941398104d1955407001c1d001103000c10b86103094180982503215540c041d6040086900004070040b00110441c1e040d0b0360301100100c0d03a03448a00041707070f1a000b8001961a00d0240b81400203d05400c032010101c5103000c00c1c4103130740c0740e520080c5500040000312215064600d0f66482100020380a9005680c0070b8903e180000b21a8650340310b00c0d0380600260030485040c82c80011503d44100345603011402444c035881d2060b0f01ca0b0038034500030903603191140310091850088641000d843e016141041501e10082c04070106c10000344450405410160b030000440741c94100003040403161240003445958028081c03105640703461656200038981c1c4103096082102c82c10000817038040104099484030f0003900155120b44c109400c00482507005404104180c3e1015080f0b40d00e0740701d4000300f941c0250030142c070084e403400c04004189050b055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 347864226 1250 347862976 347863003
    0x100e0c06030106090e010f0311010f20010b0a0e061f0909020f0306010f050c0d05130b04030f050d08010e0f060127060908010b09010b070609060615020609060720 71
    0x700020480c0390307003c0005412110f81c0800405542da07101c02e0240c0e45011400050406030702a44060203d500400000e40c40305414a801e01098400740f1424500c007201509204403a510b44a005070a85041440c8030081e01c0701441e01da229040c100002158110720250a40700103084102e07000c055030003044070030028072114002b0755036964102c141413480d030b00c210b90b4907004c6905160301001b01031046064034620071032100102818505100c00b920b4503002000d040703507a1031002b8000700f18100b550000e0300c0254415941e040040701d2070f103403e6040c10705a1103007000304140346004028280d0212141c0360010043c4806007619114840104c84406403003c040a1f0603103490515a510366440032000120390742c0303540d092030340c1d0741301e8404500740c5040c3c084443c1d01605403c014040c030302030b1740c00400711180704140000f0f05222542e01c000c180d40440e40402d011a02d07408034091481e80500035141d0291040000d00395500c1c1c28030340a00b2110740003031520035000808110400f049002c10421402480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 347865476 1250 347864226 347864239
    0x4050403030501050111070f062304030302030705070e04050706140c06101d091b0307030c08030301061e14030603071d16020708070b0a030f15090c090305100e0c 71
    0x5080c100680506000e10030f5a000401e8042e040d0288a40480c400094910b5814450041032401c07900b101c882407218819514100340203104099440c03003c0c0100021480b03a005180c6581070ba00300181841e101c0d50003500124503d004100000780b0110341081561050f09004101c41181c512015090140d200150342c10310450040c0111481c0c40601d074400c072002c2403241128040d0340c082544104c01c1c01c1d284c0d50a6903121070520000303582c01d2960905ea40d04050b085034205030360781d224107503968001d5002600c0f6410000051101e40d0748010044074401e00c51030a007901c0044980001d00d41c0811a9a4808650300800810a40e58091040300c008000350301e9a80c60018202c0b1903020700c2103007540c1488000c100440e5040c2d140f8000701e0400c0440c0e08403c01b43c00c03440e24150000320141d0058582c1313000c065031000c00200a000921510b00d034038a603240c42d006420b042c24203010444140c0c17000c04090200b040d03020400604001050090010303403040c0420005440c03284c1c2c614210b40c05015607030020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 347866726 1250 347865476 347865481
    0x207060605131e02090a050d03050918090d110a020411041707051009060f0c0c0e0114010e060310120804050a120b0a05040f030809070b180f0a050109030212010207020405 75
    0x841c80d40043c0c00c400b091281c81c4070481c03035020340d40f0100e201d160030381a000021803000b0000d9190810140800d24068184180b400009500080c038807201c80e1510b8189102d08018484001001c1002c0461000207041408081201d02030300c50303070b078284618008d210755140e1045140d5507921205440c020310070350b89460305031015415080c0e04c034070050203818010000c00b04c812003418070545082c004c4645607155844459507441045030001e41c5c0c48010303511340201040000e0500c24921410b4000d2000224885005085034001484421940b101c0c0748501c0c010f02c14880e0302307040d1030349542c1280c1020700b15400c072201c0392601d0b0350b03180a2540020360100e100400090820080b644c01c402013413203041140c4181d40c0300000711044270410754014003c03a03102038400c0d0009014542050300000703a02c04907000c185c3d444075200110340c00310580041405062641c1c1c08541030050b0b90889424040340d40380000c904040000f00004990300c8003911410040c3e10003251018294112070135550090700c14030651 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 347867976 1250 347866726 347866759
    0x608030406020c04150f060c1a040b0118060806150301111908090303040c0e190c0f090e0f0a02160503040b1207050703021e070f030b0a06050d12030207060605 70
    0x40711610695130299007044120508080040e102c0f0041da141000c6240d442c81c200310040f2403030354854500b01c8612515840a01c0c10407207070254144900d110f2950302a40350b040c0064000d10342d04120a0346800c50130030354240a544004555a540400d040410400c00d1405400003809051780441d20725000000190801c01c0000e0021012104245902ea01c00c6586900e46841d0f0349110803180a00f400565400c01d0007400400d002142c0c1001e2141007141114011410040448202058502c08101d05c140350540300d0380c00c01c1d107140092101c1c107240c070301e5440c165910a2010400500c1d2042c1181c4c00100f4443c954521704810801940001c102e035180e0303480ea412220340768030403c44800c0c2042010300180e070a5114204580141c0d030f044c0c5c060907041340108042c2c08840503440440036280180140480d40340b401415042c000c6014001030051410407154550443c1c01d203400c030f130703010710048038250010500f0700c0d03036845400c48140b60060b07954205060000040015820030740d4800d25035114507280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 347869226 1250 347867976 347867983
    0x5101a0d0501060906050105120705030c0d020a02060a0506270a1b0305011d01120b090f0f010207120905030a14011d01140601021917040b160311240604060803040602 73
    0x81c1c0302c09131000c1103480c0c0c40c1c100644c0e02c2e0103410602050070390030400080056202d035000e0740d008030565100c00d00b800700302140f0a06a8008503130400050380038504010040c0d040c1e004031a0131810a4482c0b051011824031507440700c8800c070544002c1c071840100424002005070348000c004401c4003807030b110102c2c00080300601a00080c4a180c0300c140d540300e09414416031500d01381e412a01b489020004c4002079540d03000c032610000b064000310b07014405001503e11030034880480c2440720380000607502c550b40e242c01e24000051401d01070812074840b400f400755031000180350070802d4010721008200c0300510700c9240513041d60380079814481460400c868195505400140c1c4041c000031080d010386d41c0d035400490303540840141c08074040ca4030b8141c1a011524076600c0010b0402c00c02c0c20b0510f0640c6030556060380f41c1c0f00c0300e90032140c4020030100e0420b069214030b20558040f0101d02130310118900707401000c241c0104c0c4403159041014540400c809981ea54007040c020041c1805594555541703040103500c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 347870476 1250 347869226 347869229
    0x90601030b010911091c0b090106090e0a030e1c02030a0308070f0e0a090c0201060b07080c1203010602100b04140a06171225060908090a0b030405101a0d050106 70
    0x3000200c8500114a403a91801000032248400844c10b051540b418104001c1001040c0c4c1c060182c00c0340c44100011070034240300c0c603200d0710148001040c801d10700103c1c10222a00101a94102c3d0080d0200800181e44809442c072441802c071a031540b032aa03142d54903035250500c454002d6141c407031001c00c10300b01500f01c4442032140c0e01036240d40e441e68407124415218111490f003800c1d0300122642081c4105034059000c5a00f8032903a10001801d00d4a6242c00c4015901404c0259030306580031560610080c410081100e81c1010104c289055514000c0041e5488907050b080c5021300340c0f01d80d03801e109070b1600d80c002180e91022003090010f0f81410740d034080c02014240180341c02074150111844807010009503c10070f804200300003500d804100c80d10000b80e0b5043e6650f8924544401c455400030a01c1809594015405648233035503d2440e0420002500400c0c3c0c440ca104640a104003c00325030003045018401040d00d1021800c02c031000d503214480140e901265610004178800e607001d10205610210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 347871726 1250 347870476 347870483
    0x90c010e06032a07320604081b033705030112080918060405070e030c0d051c050a08010f03260f1201051c080a050a090b040608040303050106210513020909060103 71
    0x1480085c0000c00342e510881041c0031503115601030404503000501c07100003003045d4000c1d00322490040941540040c07c41c2e1024070610510300700034000c09560503030302880103071402c803983d80380300a0f10400740068452b010504c640303000e60a03503451043c180300242c01280e070385100060440c1410103008800b410604000c0c0c4000d40940d15000c00100c10a00580c46040040320042c024044450001c2c10001c1c0c802d414502107a090203940100080c024441c007103d0003100b0300ba00c803261140b070700f014000c00c0020141e10030a414136101c00200b0100d4441e1581890500c540302a102005a11105138a418418004030a2210800040b412006e010f00411103043ea9411101c503004100c0c0a40c2c4160001d03070344a00035000080c1084084440740c0100d008200c015528103000d061035a03608168a00354005511030707408507100104201c10154548230b154050002070401c8011828401490700640304034032090140180c0d01c1c4e0102e07420240c282c56040350716038010038902091400809942e100d540a01c000c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 347872976 1250 347871726 347871773
    0x30a1e0203152b020f04050106172202120c060409020405040e070b09060a091203030c17160f0c020406150f050c0a0201031a0901090203090c010e06032a07 68
    0x10b10181c0343c0328004007812050382a1880542909450014610300d4140003241d00082e80440c0b0007007500c0d10300460f4020511525591181011000c524034035210041c200c603820b0030200517448100c51180704034070381c132a0141c034105454615081039070b19000143c000b05604c04000310300050721168540040c000d50b282a0707424410038408050296a41000b4011107082c00070a1009080c10308095001e0600680c1914040c0f070030590702d11558801036202c0030107400082d101d440e8140e071207411035800c1c1c00b4011100144203c500d4040700400304010216011020080340311100058503100d1881c0c000c0d0f645e0003d1082211607501c0380d0b04002a5801c01d02c81005c0395000c4803142400707015000f0746040004d8180034040001040d03004500a100360018140c80002809001349c0a44070850101d010b002c070518010307544c0c1801c0381c0f09440c0258104050741044100160130003644c8400c01583d800c0116250703c4100c90300c42c0070100d456400042c2c0480220301c0701103602414003400302d0440c0e170200f03c1803410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 347874226 1250 347872976 347873011
    0x13140f06101a030a0e150405060a0c080402010906050c0309041113050303120615070501090302010605090c0f342006190c080906040906080d03020304120302030a1e0203 74
    0xea0b580078110107240220500d083c000502400388030b410046040c00c500e0141c910081407003140801c40d41003500c060f140d0707900c00801c010208000b40300312403000001d07090620861800d40c0c002481a1114001e0f0401c0000c0456603c940351020015101000c4005209001d40b400d08001c501c04ca4011108007215a400c01500041d141800300880300d5800e810b04034100303030340d40f40d90030302464003412950310700302450070058500820028451180641d100f940081a46803410b8100714012501808009103000c0800554030352001c100b00b100c00311404118420500d0400d07091844038141080c181c00022150b441100c03081180402400101c45007034580262011950424400b2600948203c50706c8490040160070302030f40150081480907200d00c5000340740c0411080800d04c0c640003580a0101e091300c5003410301403a0410b02000e55040960324045040d460a07882d1000a0003407010511f040c50345c0080840c0c100c44050300718410442402d941c4842030401106000e00035070040f03078141c07034050181c1031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 347875476 1250 347874226 347874239
    0x41205030702090c1c021309141e011413090b01060801030b0f1306020304020d0c08010b150703080412110106030311011805030d0209040204120501060317030402030613140f0610 78
    0x551740a00d100d20800c580550f28804100c00941c0815400002c203103032401c0014001400703006080b0344001c0f1121011450038070318a400c4241d25a007407050f51a86074240140b05800b013244000469030801c070f46481049005d031800400406034000c024024615180003c201c42d81c000129504aa1040820030402e035681040c0403080d000c180c4000b42c2c040399180b00c00d40451071903000365400c617000030202c00241d91a07a03110f070100c0ca0301d9406040c1c965110060a0420b15100098501c0400d10364140e524002c0c0315070380281101e1000380000c01d4116001e00b1410100e00c1056841c0d284a025002005200c0d1a400c01800d4001c4e0b0080c081081d42c200008001c003181784906d8515410743c0800218103010f42d6080b110065040340441e50b0f00070341d09100005110160520b506a043c0c080c4000040d41400c1d4141b00f55031010b0b428886100c020100107210050720000b43ea150301c460100c1c03146001c80701d14502085880b2108030b052029209078200082c80f102c0104120b0300800002c458540038613031703490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 347876726 1250 347875476 347875501
    0xb070f0318030809030d0903120605010503010b070b07050408060a0501030209130c15050d110301060e09010e06010305130f120207060201060602030306040903110f01020a0e060708030414010204120503070209 91
    0x201d4401c00655008414006401075034559000080c0b00c013600c3c24a459607401e44c0445a85040030390014203035980150302031025119000280c01d0a2802030b01c0e540c100000010684501c002c0108818032840000300c0c00d51148003a50301801800041e100c0904218250401900081c0004d910515100f4041a0b0081d941d07410b11644580c010441c5002d6450300000a980006518160007401400c11180c0494a4144a00b00c0380e00b04041c1007039180d50414100420000040700301d28000c0750082d006200810038110344540c004824a0041500d644942c20403410b660840801010010a42005001c210740244103080a2010307900b11800256503440403402d850b254407411016804c03c002284590401da080146854000c5c01c01c0c940c806800b0000500e015021108010b0750796002c2020080d0b00e80c0404080081039044842c04c2c00c02d01540c407010840d00c03014200030b101024060308440c1c40803081d01070310004c0400c10b0032060800c405003403070307500ca61040300128412031403030b0005031200c032144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 347877976 1250 347876726 347876741
    0x6100806010816111501030c0b0a0203120402040b0d0f1202011505041107050f0601090606020d050a180302030d050703030f05010e060918120c211c090f0b070f03 71
    0x142c1da00700040d151140a49514401c0481c0901040380b48104090000010030000c2203200001040b01903941c50343c01c0400c0c908203280c00c01d00400000708041c0060301e0f400010b45181e00b169015920f0300d601c440c130005006240d50410603400c0040e0320900c80500030084145c919490040f0b40f65100700111000c12030803030312074014031416800c050702c0a014500f002d5100c0c01d10303a081041e445190102c19200c580c40d1200300522521039500c65401800742600b02c0c003800d0014112b5000402d8250002d24024045029005034101041030038140e0071515040306203008000c54001d0207603a00c59014070b400514540c420306054000ca0b0615469009001c0079118a904880b601282d0002d1a100d860400282c82d5000c3d0000303149040c90301e44803049500c244451604404c500706100da80e241a140c1103402c01a15071f41c607000c99203030321111401c7c1e000214110760800c0b08030808540a4040e0307000e450002c00c40c184028000c8400b08000604001e02481d502e03005103643d480c0c500011111920880688658 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 347879226 1250 347877976 347877979
    0x6020c01080f13150912020d0906090905071806050406090e010e0601050906121e06120705210105160311040803090d0606050d120f030b0604120602070209040b06100806 74
    0x1602c0041c094041c21201005880d10500b0001342d01018440d15000b0b9540300d1005517008100c44030301ca8125a0104180502c810007414542015803400c0000b80c0507035000d2240300401501d500004011307074411010b41107803c03016885050b8694071000014203c0e0460b0080300041004618081400041c000d4441d04980024149200c1d035a1000d0044440d81c10004140e80c0010302400710310010b0b2500e4420340d04c100e42c10181e00b403043d400038040401040024014138001c54620305018840d0b0b80205261003078440a940c04401c07241610601d041e500038011014080754038040a019081d8442e00703c5064030401907806008049954070304e090ba600c190f2160340400e41c002c000700006030800440a50f683d9001e0a80060003a95a0740441d0050701440400c4800c04450385070302d20055040f84c0310541001403450b00f040302a28040c003160143c07040b030051400c00d0924100510402155804941d200d0f940500110420308061030169210a400c0c2c441c0ba11503826040080400d81c451184140300e00c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 347880476 1250 347879226 347879251
    0x414270f03041401030b0a03050c010e18070311090303070305130b0405030a0f03090909050c1206100501050c0a050f0d0909050403090605090d0c0b0a080604090803010b0f0c010f020406020c0108 85
    0x5800308540103c914003410720306050326500764007503541d40c02e50144000c2d030060010748160303200c14000401454541c450300c1d2051105505000175100c4030700413280c0c0611300d0b0030002044840b42c000040d0901a0900081d0f25110000b12442010b50010142c0f00310003041c1390304041261950204003203030165010300c98165104600e1800800c5489117241b01050107400d2001a494a846d1a002514580b46041c0d80710391200c1d40034455030801e17800c00100100414003900780781c106102d500200340440d100b41c0741001000f00e00c2e404910814444c1250881d4401c00308d680c80440d907994903444100200f26880801c90901c00000d50304058001c07140b0803a03050740c903a015070381080c1042d038840d0451202c079074103d148040980009001c0d2284c02c80a40842c454982c0c0380c0e829401c0080441d0001400503004900700850340d0002400d02c01501d064640c800c00c0b250700d4100340c0b51000201d001d007280303c2010b9804c040d0030400300242640104103940341907098500201103140155111003054a074086100c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 347881726 1250 347880476 347880479
    0x40b15130510051215040207031d01030e070501110c0a080a330f0b180a1d120c030d060605070c080d020a060c03090215090429010c020414270f0304 65
    0x45640d6507036038000c084880305c990046200c00400c0417600520700840100e401002e040c1c0701c0204900c1d6240c1169004d20b01440710b401c807500c84a403034050503c12241032200c088541e9030b086805011981702c40c0c0014080514166550303d0f426a01d1680c07200039688020340384030240c071465910501c075007040b41e542c0d5810003174040250a8001000c6611000c130481c0d980b5450801e02d0f0750b9400c2001401d1502c0d00b481d04440c14112541c804032000c407644940c80c0c0103030308800b24100c100807601051030b4144038990b644401403040305a06512850300d105403031074a401b01c0410065002006008054004c0040709800380c1c41c1d900880e90ba2640d81040d1000d68007040e1050002607040e007010301d50440500d07001c00e10980f1903011422840400c148582210408505444141083e205e07980d42c064000400641081961101d448120350881100381007006c03800e40c0703505540b15500302840e01c101c0502229030a180c40e0100d80503030307003549618160f500f2902620042d8210001200e80c1403031180c40246103000e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 347882976 1250 347881726 347881747
    0x50604020d110d111303110f120f0c030706020a2a0b0301060e010f1707030608070906081005070c03030e071205033601081017030a090905130809040b1513051005 71
    0x849103241f0b020350101c0c1500c1000c078961070707851b007943c2041820300c000d04812414410090610b0040c00855000380e00080c000c10101c0e500190091260350009120102040234840222140035105c1c4410300002c121000060780380c9078040218101c03000343e902ca0700c101828200446100955410101c00500411803c00120a01c0002c05810a1a6040c00502c2c5070341c4141e02818943c1c15440381c00f145690b254100242c00c000c0c82100d90048030708604020f0342c41c0c8604003502070303818980c0103010140c0c0ca018010f4085001c01041010740308020256812003801e141c41035496001c0350300500b0f542640c14140c018200354603101e1034a9107094100420055181d00110703480c00c0000c0511820300301c0c203c0001401188074043d02c601c8a21000a1552000e10403006420311006501943c045481c040420018140e1420f40c96000350b4001313030b4142e82e52000800103015050001c0920303030005d00f005e07160b204500c4010042c41d01c0e040d0180345000c02540c0b0030401140d0800e1082c010007007441000702c2c0712701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 347884226 1250 347882976 347882993
    0x90c140706051513090c0806010e13030c081602180f07031806050403090e0f0105130902060c061807170c0d031803060518010203070e0103050604020d110d111303 71
    0x400c000071840c2c0c03c40750040d40000c1c0003c0c0c5811400b0403540c0e4498550003441840c00050740a0f00407400200450352401e60911400e11300140b02500d243d803401f82c0d66080520030344220720b400d504608941d4172805a646c00c0c100c00700d001c105c05c0388108180d510301d60b154500c02d0b54152040480107003c031490355414105030044c040314100745011288a59100300050400e2092500a034026510304090358203011410349000400381c0717241d92851b80d03140104200e5455046c40803005603011408a08000e041c404907145000e1004800c100b80603540400651800c203404000c101c0e0610401c0b0780a082d900c60078491914448800017103150444184c4002c0e40c1040700b440d641c2c02c0e1017480c006e8404403d0125544d020902500129030207500d400600203001c500f0a00a0058002d0310000c62550034204009040000c40e180040d043c1522a0000f41c455565035052f1020460f0300b034420302841c4906901c2c0032841d88a03812803041c0c24904082501a2501e25003a80e09035503050140034055400d42e20f88590 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 347885476 1250 347884226 347884231
    0x11505090a1508030702010f05030906130c03080a0201050702010605010e030606040513080a0c0c050f01020319020c040f1d01050c031b0d0f0510080d090e060604080115090c14070605 80
    0x344241ca0b0280399903040e009007200300081c140d04001c4c0d911011180700052003201d4084101003001f4040c02402219140460344d44c3c1c025189000d400f0816011340307403403041c48807194005040700001203414071031740ba01904280d210301a03c2c0e0081108544503001503a501c925401e50a4141c2c0c007001c0040c01d82c0c00c1940c440ba03040350f5648a0400d90800e196908880e40c0d2182c09680d001030142d054400800103400341400107041d0444104060300401d0000035075901445015089402440300002d00380c0c2e009105895010300098400d02600c18958078172009400c00c080101c400d486e442103030408498040c882d250041c0592101c00d451500da403010440d800546e0300c5c55502c008410401c400a0310414410000302080c0d9100c0800d0620386012280d00052080e40015803682048841c030b806154400c07201c0c003da40e60141c840d0320396141c80020900d18001d0340c1115207150328081c94a401400210700110448062940a100b8034202c0101200d91036012003071004181800c0c001500003410942200d40d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 347886726 1250 347885476 347885491
    0x405040f060504180b010905040305182407170405030717030f1216030b0609040f1821091202010302070305120406050105270403080c070f12030c0201150509 69
    0x41c001e92120b00040c1180d1644041e4a4202003040e00502003000121046004010607a0100194600781e10007401d680302e1268445541050200e5211156031502070194421809040d0504401c41c00b403030b000d180ba1300500701682d13110480883c42150300c0d9014110303001d07100094094200da81c502500f6649441050404500d02d00041c0900005000014041d11420852200400740c03401d109140607244040c0615010425090401460243d01c41100702c1d18201000e41c0c00180035000120080000c1c4a4800c0c0800c0e030300b0b4081c4090090245c103044407144580c2030004890b004003c140183c078450142e00c06d54000e88180d186d02c03000b66020b035014069944c02814014980307581c071410949076500c21101210600e82c0e0b01d0040c8000d06080c80708004008004071880000c3c07009014440941800030001000c000b00c0f10700180107103034000207072038107281d11111610400900f464006e200b2918040e850300002d01e0540d5480342684140115a81030f929203102e050703841d0400040c003901c1c0c0d50003007242c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 347887976 1250 347886726 347886731
    0x7050d030806061b030702010905041407050c01090618050601050a06020a03230c2b09030602031503121908130b06030705030304061106280b0d02130c12020a050405040f 74
    0xb004100d1000300815440c01c1c84c4070140d5a41c15180c40050090704030381d00400c0c000c1d40351041d4803040e240803102d2560040164142580c40308880c0d40f2590151540c60350062103142045008106000840c8240c00010710030420b9403038580c0c80b00e06012507242e41e4820000164407100400e00402e00030714810200000000c20183d1b400041c4241800e190300c41030103000150f1010704507040e0841c100d00360710b100c0d01540460000c080001a00200000300e0340c0405040d041d40040030a43c001150300180340622005002d503180710b01c500c039075140d6940011035020304100d1001d5503d1106440b9091591203124801103049400b2002e48070010525402402d41c1e805100f13181d40400d05a40401c0500b001307100c66aa4003505620300b00d00c1078145440900300b09035100c9043c0c001d11a031040183e2000101c2404000018401d00e0080010315074845071030060b41000242424420180c0650843d1140e820181c84480b4840182542c0008901c01e50b0644400036400f40310034070031f500d0250444200c100c00458003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 347889226 1250 347887976 347887987
    0x4030f050a05300a0203060f0613081f1a01120f060513060611030c030f072a0302040b0924030f03120f0705040605070f02060705101d07050d03080606 66
    0x415640c80312002c400c0106452160782d607a4084410909542d00c010b50320803e41c02c41c1030520100d000708d0000c11180f44221f2003c20700c80d44290780c080f01d5a00600b4104c044601c03580410204100705101e9543e00f410141c00c2c040003012164401c15065541501a500c2c010103000b0070042200809031416800c0990703448050000c3c2c0781d621002e8009031480d10890016003c0d24192000d00044920940b915440d082400b1050811401006a6803c000300c858810f90701e8005140c007640c0031102d0b0440d208462002501c3e0208030010000c1c0005480c404c0c1c40412031141c09804000c1c0076101155810400030600c2c208071140304500148080c58900603048032484014292000e00f140c0003640f000c080b460045003049a0420b0850000360420313403600f000c5203800d090180003030144c41024006440c00d503200403c01c08545808003160000303a0000c05607507a2282002c001409040c0e0301c68041c01c251040c0c00401b802c0c1c0320100d03000e011210024180001d521141d51305691800c40101802d51082d4107010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 347890476 1250 347889226 347889247
    0x6020306190b030601031a0a030f051011070b0108011a040c0203120a0f23040305090f0d0b01030c140f0909010212040c030302060f0f0711010b0607030503060a0e04030f050a05 77
    0x303141c000382c80c100380a15140c0ca01000018122500d200b040050304126082805240d1030720307180c2c142980d0304442030301c06075240380c20101d2420418100c24440c507441d1136051507006100b40044d01c1d403517100381c90040060344e030703240c520b8240c4070741164155503c00c40840121981c030f480c0d8041c0588105600660b428001c5950070340c8966081150481032040e120218004285441e11a042d03016001c0d001502e80c40040000040d503040000304010107101000400030781c1552410311460b400301c1c0c0123001c40400c80c0140742088080302c00303200449411a5100010a121100c044688610b11003d0a51070160480e007013003219100c405081882c00c2d560030000301c0382d240b0055400500c95809195106402803541c90024a0081c1c01066501c0c17062103242442078010720461016004500ca180c251402c100411034940103004443d00d903035100c18000f0b000001c07d078000000d544151011030f6495082607841c500081050001c40c0c006000400c040c0c4030a402501500103400c48456900e8101e041c484c00340c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 347891726 1250 347890476 347890519
    0x9160905040c030501090609060305060708100b1c0c03110d0902040617150105031c030b1518030f0a030807200703060603021e01021e0f011406030d020c01020a06020306 74
    0x151a0001c4c0d22000103001d619201c1c01560004e04001c08100038061450316920344a440241a050810042e08045900307824501c4030030020309200175481d9580c00d0304001101010400c912084111424940c0b4071000030300078407400084d076081e40b0005e4500082c041307180004182ca600c089078055510310300491407124030345485442c228040d0061150380c1c091400c0020400059011600c6640700000502c030890380d046440580c20504d040208200649000064880010381401c1131881d0b0302260221211070b040d002c490341c8600543c25100f0b441d8910000ca911000781c00340141c0490042c5000c180110b1003600107001c2440e400303007100d204034403409010382491a140d0050b56102d031540403d10551400d00101d4655091244107580d82da002440003070340b11801145070341d14a02c2188100850401d00744002c0b421019000020002c040850244110001e025940c550003807040d4103020b08280c0c0005000e110f2408160010f0264640302d5650502a40c03000309019080418242c0701001e13800c120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 347892976 1250 347891726 347891741
    0x10212010803042318070c0b1501090806040507210c0e0f060603042d0b040c080c030303010308041e05030f0d390303060509040f0201030c0801050916090504 69
    0x107806540e4852a00d003441242c0e40c03070303101c807145460050240b058150780c8003a90b0310440d0b42c80342403204040e651079900350380e40b00c80088003a0005c0480c40411841c4881703003400d200344060036215072081a495501c1507030744041c01c4800409643c002c07042030000d1030741c080a0519000e1000c0d52140e1018940d0f0b541c0128105503403114407800d0034441800030201c103003d10035a200700c0a880c020b00314074158403000d00c0c0c104001030303035a000b103044400a00003010100044104540158421809042615111005c0c8455109000c124003908610460501d00401260b04880c2c03c9000f0b1410542801000e030070b1044805a240c80e07006000070001020744061280b8400c0884a0004d41290340403c10094080d44242c21941410104010083e05d401400d44080540094020320041d0030420780c44c05034014107d6422503640006c0107003c10082000000c00707034210620030707a410f21281c0070303800d030503510000c00707000d0103a2044103400012880e02c803000420402106614105d103043c0c0d42c0307002240844501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 347894226 1250 347892976 347892989
    0x201200f030d0207030801121e0303021b0604050f030901120c0c0210020c030706090b160c05090c0403061a010c02131508030702041d0303010b1e041d0a0504020913030201021201 78
    0x4a004c03420f054201d100350b801080502a85204d22a040d9070f01ca50900d806408440c0c00217229042c01c003818840e50645a0741380c488101a0000d040522409a58010031a800c440502c1030582182c0300186c00f00c1551005ea4040e120945012195244a03028044111401b010031580c6102440580d9a900400846581903005001d41e480c1c0d0600f410f00344200f03070b0400403e20002c1e4108104117410a000c95030840c1303241640756901c18042c90000a0361459038000c55102841c00c0030f0110801f030507002401280d21644081040c28525400c0001c034801068001c1d01044001003440054108030b09102d098a000d000c00189181040030000c40d1a80b888e08105480da0001c2204002c43c2032034800e501c603805d41c000810f550354151103d190f40d648814003c2040e40b1a011402d000000715024420f654500d00300921502d981d00c801051820300a0fa82950410000b800b0108801048070702c19640560780103810451140d03038000742c041c01021644000c408540d820044135001182e101c1c60503029099 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 347895476 1250 347894226 347894231
    0x140f06150f09090601090f0b060c0d09060c0506010909050c0d03030c02070e0103080a1b060606030c080a020306010807180f1205152404090f110312070201200f030d 72
    0x250309001807000c0e66403060780541030a000380b08080302c0001c4d60904540541d080800c40f02c003441030000240c0030740701001d504002d0229800311541c4012400000d000c01590b5002950b0b50f03205070803200032000d40e00140807a0031100040c00420000c0d040383c00290f01840c1102c200400d40f41c0440e11017228454182c002a17524580c0750711701ea0f410300c050702c0108803603807901a0550460b1180710641c49a054100b00307020041c0c1d80c1c1541e105020030241c070400e4024104020242c1d50f0356001c1c005d41705224140c1c00040c900070000d12030650500c04c1d03a01031030341030303480e4a1156600c071410340d850b044152426074401e03500000021000020060f180150100302d07115240704510385080c07880d21854007080c1060079038503020001c8940610850745061068440749200d10300760900070034020222108043e08425010550302c0910903658010160400142c085034038070303040c0f404544041d02a00c00c00a00003440c1c0741020f0303c2e0220200328141ea4250f034000751203000c1a0f03215103526562000308125251074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 347896726 1250 347895476 347895511
    0xf080f1b0106080c0411030112020d05070801020c06100803070624060e130c080c0d1d010207030e090105030c0d08090904300f080403030f1a0901120f140f06 69
    0x600c04d10502c42d03600001d0b203052090741254201d10011b40070502a080e10090784070704c01d40a542d21a0880c8000a8000342a280103d0b1202d000728083e500c846400389884c414070001c1a00707007217a0305100c012215241d02542c106401541c860307025048020015170740b401c0100c104101541d0441030300c0001c2c80c1c5516a492450f61400900c00b00034024481035010741c2c94a1803034242c00350003001165111f2210350342665550700c21803060700188900d03048020039028a0f0b80464801105600803c040d03402500d070f8803101e000354402c10842d05003d0080e02d0b09508500340aa219080042d050004a40b00d52030242c20b05892802140b8580b2085409650718209003a001103400ca4001d111144000c01400340c410b04058804040c02e6400c1c9010034100300000540003600b07051213a03008501c0300d49024410701068040d001d50f080408100781082e0302c1640500d000181c0b2115008180c0281580302c507000795a080b0716100c10362559449040500c4038040c01d0309030204144140f0400d4450454084944c03c100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 347897976 1250 347896726 347896739
    0xa0e040615081312050d15030c082509110d091a010b03010e01050f0102012a0f11073b1902031509100f0e0106020610030f080f1b0106 59
    0x540c020b843c00d200215007114200100e80340c040840c0c1c50340c1407420441d07075404441d8a02d000900c8602150505103143c01070104c2045002c1d40004111004032003260b403600304078000c10b00c101510b02c0c0e480003511914081003111403003940140c0748000804d2401800d25018017455019600171110444021520708044d2000388a006c18460140c841c503003555080d5814400030780c103000d6041c002c05100c2d10405844030a540e10035005490240e046803445401622007054040c119401312020740049080716056810152117100390640460b41c00c00100882442c00d850b21140f035640134101503004030f04081d6030202854150414100b070389450181c0705145084588c90114044c4110301d000054010001d210070908030754924199a54102c5001403d52a0b140c0801c1c51145035a0001840f20380110b80062044070448041d03040729015000d8880c03558603e903016908181c940402440c151f41c0100c400081414030028261802410741c80915081000141080384044620885901e81d1508000d101c10b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 347899226 1250 347897976 347897987
    0x151202130504060b07050d08060f060d0b01030c020102070209010b1624110301080a02012015101205030406080406020405090a1508060105010c1b170703030e010c0312020a0e040615 79
    0x10304168040c03500f08645c42e60f5071519086064070072420051000e01168a0f076071025844000244003d100a948083c03a07402c18016202c89a00030380440e12b0050907100107030040c0202c03202c03646c1c001d0090589030308101604c1c045402070103115040005404a000c000342084210b00019803295000c0c1d89503180c201c118809070785c3c03008800340c1c0a00c02030004221a040010345c1250866090070555500304200c800001903503c1c03040140c3c410700c1000c0c1e08141500b140d200190050b180000302140642e00c1da00040e0346c2015400c001081503108120030065a88607183e040d40007032007141c016203080d80e114000381c030072074066030080041c2d956646003010903e030249080008250f0070015250940c0f61200180814203c0c81015000c040c2031000c0055000e03012000b42c010306281d0b5180e00380320406241d5203076a0406400210041102240e04006640c0114050811154565189005e0030321750180440a034000344c00901c1404452410215540d440d40200340c0605508134100841d0820414000d05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347900476 1250 347899226 347899229
    0x3003040309030c05030d09210b0112021e220b18011d010522110d0501081005010b0711010c0510050916031e020105040e0c1b0f060115120213050406 65
    0x119a01100044410381d81003200e5108580e104070307600307800703118504000400440b091802042c12540c4000401e008844880103400c09001780d403a00c1d036440182103018044ac10aa8070345a000d155140b0780300c8ed20750010b010640b110600d00c0041030b0b0242283c00300718102281c80700d5030310150310070006103c03802d070346034076034907142c1c818022201c0075454031011030884101400402003258918050450469098019403402d40301c0a0289550780c1c0c0f40340e0300000410081c0181080342c090660121005001070151038140c0c0c40c441166880c14250b030365260441d11015198505000c40b491402021440074040300481c1c00304c424001c2002c1c81d20000c50307414048407000c0c1504aa8810700e080c80030808030182c0400908400c02e00c0c0071100340600050700e0303034050f50380400703440b0340c03000c0800c1010410180641804041d90740e40074401c401c80440c06444e847c400005959980c0301c0340040214800000c0f86028811a07401e200201c0e40e5801a00c10584c3c2c001341001d414198092010022803c09105100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347901726 1250 347900476 347900479
    0x50c031216020c0a030206090a0e10030201090b030420040e0a1b06172403030409060f090b090a0b01050d1109121c08090c13090203060709083003040309030c05 70
    0x103034200c1078000510104513900029008400105014150361120740c81e00c40501500030114a0b946088404036140d04bc0138001240018910000010240b40c0791040c2d90240307601c2900c6c51000c13170f407001095650341c0c075014030964400d40310704052800130001e1007003400050051610342e14036141844680d001c0880d80d400a0200100c4070a10301c201d01c000ca01042e04104100d0040000c44020071340100c0311012528030a034113010000300000c07500348503400780c421290707248a44000d041e0f49413001c80481e000d403500140c1120149000a159418592180708800c005051035414114084d00130800c86076400c160040058000421403d9450000d00c80c1d10401081002003958250320380114541031590034188040c003880001140c042102404140481d01020300004003180b164080780002d0507417104103a000e4080c0d000418445482001d144d000d98041d0b5000b0940791210940c410166810000400c120141c0c2034a130180c0055240003d502550081c3c0c6d03030100301401d5007080c110005007644030300d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347902976 1250 347901726 347901733
    0x40212010b181825020316141e10020f0306040e0709050a060513020306030d1b12050a110105012102060417010603020109231e120d0f09051f050c03121602 68
    0x4c40d80950001c21107d03000b000300a00b401000711840d03c508111080108010103004400c146056042040000c0840f400000d04442c051500c044241040340720394a8400c82886081002404900300394205006030140d1381e0844404645d181d400c8011258242c840d080078076142c00301080300d4504445c2c0c920410900c03100031032943c01d1000001303a0b94002a0720000c248031400028403c01c08136101e48200380c0341c1081c0c41100c15000090010441c0c0c0c8145950700104030342c8821410344200c144101816204142281c15954080503c0210005c440704802c03070740a2800c01000c100680c1c00b84c11112068800030001c01c03190300f50700c009010003000303800240d2103000b241e00d51240d402801884011607001520a401c040e0603c01c5861240c0500e04201604242c640c024010050b0002642c0307011031580741d480c000710340b03001d0504880d010322078860903a02038100c4039031014018100c03031071a540c16040e0a11a1074000e002400505580003080300c9070650602d0020044182c101c15000f0304294443d102a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347904226 1250 347902976 347903041
    0x120908120c030d0e12030a1d1507050c030d09060b010f02120d0203040f0b07080402040501050f030304090509011b05030603160b0313051006080f0c040212010b1818 72
    0x12070b58070f006001010380c040d91503240d82d4130403000c144030700400c05032518003807030340c0785060004900500302d00c1c0492208504050040f081c010710104c0c0e0307011240002c0c1e62a540c152201102110650085031343c030714039070200300101c0ca80324015201d011480c6206560104490300090009030124010800340000d5402c43c1c170302c0e0210880c0039400c40740c0c40542c10000503180d031550308110703620840c5204c000300401148024810b001d500440c25a02c1140300b01d4040c840350381c03190107008510715501c48454066200380310612a29080d50445030340030402d60700000e889418001c0489120072200f1204011500000500903103081c04d0111240341c0ca003035890300800da480c00140d03085520001708001481e24081405c82c08005051100c0402e400c0808424000300381c88000194070341e40c9a01c010015032240c801c00c00b26504042c02540c111700811511024561b00c0e0507400c2c0c400740c0c8882003021036030100c95080300d41e59403914040348a43c00380d4503100c5110b28101551500c405100001000c5030f880102c007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347905476 1250 347904226 347904247
    0x3020a02030f03192607080f010b09010c030503150a15030b0607021003020c0705090a0b0315040f0b07170109020a1206210f020402040608250f050f0712090812 70
    0x740007000d4812807602c4402e50501d00003840c500c0c5d401c1c1e40e21521410240b410b0103a44c40e8001c9005005509a981c003070744590b81d400c0b072640745200b0304150f00e0100360400b80032030109024101540d44502c01d94030750030010511500088410406e43c116400208201c619001410f90511404078407030003d4580c946401a01d40010358445c603044051001c054000514031110601404804000d200250072140c25090500b095400f4003408040540248150a5954074440c0407244190243d5001029201d050b24282c56402050500802c95410b10243c1c14040c0d021284440c03445000780990100181c581c2110071000340052296076002e4003880c01d11405211207035146140010a82188008402c01d80c0d0514081d0001c1c403940f4400707584280b010400141007600144c40354800c504a070b041c1c50034a02134821440082d01c9510ac20000039040c0e0882e0308901d4002d01c014042e0041c9031a80500301440c3d41c0da0034040402690104002600802e01004042420881c80d01000c09081400d420b0400804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347906726 1250 347905476 347905507
    0x40308210106020604021011060702011a06180405221a09061e06040e011e061211100e042a141206040e0a060b01200307140304080a03020a02030f03 65
    0x3440a48541140c07c01b915009010b0344504100640a509076511031412580190080c0910344400d9100d09010351440c455141c282e08403203410300b0013070601540c01c0d070a505200c01000300400b49882c07108525202005064210034005031148544512000143c041c00d40c0c240040c40584019090b034071010500c90b640e0480040413240d1504440e003485582e55600024018001903055a0301b9946483c80c1198030101102c03640c025400360344424441266541014400c4998011014000c140903010402991401041252800d1440e2820350b003500c01e2540001c04442e044c400020040d00d401009041041954207600c6060300c040c01c04000095003450581110320800320030b031642c0b001d8140060f4440d0340d542e22003200078205008945170304c980780ca03046000341001c1038054007043c0021042d030703400a40394213900194515007006d9414254583e94a800101c1c2e0700074071070f445000034040440c0580c820020840140d000c0e80c000c20591a841c01810305003240036801d88065001000110b99100803c2c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347907976 1250 347906726 347906731
    0x10020c010c0c03390309230303040b0705210c06010506090109090e0a0507060203040608130f06051503030a03060915060f0503070302040b0406081e06010f0516080403082101060206 79
    0x20300c5000f6113045814048060303c074035541e0350620450294030384c1e014560b22080b988107840b040c0c02c1d07521498054000d403c003850901c0e0f5003690305503c20401030102c0300702813000e448898843c00031981d0804071009070402400340c415042c400c10703402249044070031101f04034050041805032502031130400301000003490b0700f90f1030141803070131501c1d2484031551100401410030542e400100b176609541d151100251294028413400340046c0140340464a100c0d5100da40f8038040c1e82c028104181e100d42035650070040c20300140560313400141d4460f410f0283e1014001043c4100784e0740e4001440f1400c0c40001801c60780c02000441c0950020001440582e42100981720000c2e5581007154036607989110440c081e10903a040803081c0d5101040c00688030350480e401ca07000b035900c0b0410003412217150300303022815001241c4160000300701c110a02c009034040c90003072140607450700c443e41079600c0644500195502903032084860840c000365500402c0c44410300d283e0004640d1052075050b5140500003076550002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347909226 1250 347907976 347908007
    0x20f010815061810030204030b09060f191d10060e0c1b030d0218130504051e0f01022106090103120e0d20011806080c071410020c010c0c03 61
    0xe582c030754000c6020070000f00800b005007070580d8007003100c1c4020080c0d04a0f11003152403214a00c0031644650010510754400d00085000da003c655402c90000d101c1e0000d4180390019680c3d45200140d41a884071034041416400c0c0020680c40fa20040440c0445000343d001d0038002040205009203503000f1001c864900917503107240d00740c12034080d0006017588601c01d00c042c0b60620025820b02c4092203c4009510404101e8444250104281c100001d41e01c3c110340080c2250041189080c0143e000e401046640703259004075603051404420082c01c81c1d2040c81c1c50214200c0f81c0044d070be0b00ea8160000c2983c0040c043c0c607a0a003651645c5d13141090540c002d0b200c103042c07101c084011112a01e902180e610085d402c43c2011040c880459006400310b03507002c100c0b600160705150038031000c40800741c000085442650747c00d0680d81c3c8441d041030712608600b000b1520582c02d48443d00c2d14403c00c2203e0311007050000401031703488441074490ba003103403048000301007840300c4450f0802c0070a42040c02e000b01e400c82d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347910476 1250 347909226 347909239
    0x3009060708071a0a091703040b0402040c05040504020403110f0f060301230a1203030f23090115080319140f090f03060702010e010605030111030402010f031e09020f010815 75
    0x4061611450907083c041082c20f0162281c000c01503407180035003100c08440e0080c081c0e00020322400384241d40c51710046802401e0841d00c1404540141020b5201d060781c40c405280c240c0c101904d40c00028241c0c3c0c450351003901d42031101ea46920300c0b4074008506861098049132110f119001620124500d80014825011a4200e80285022018892904000320f010045c8160016034490310190f101c200c0010040e400640790248501940d0203510507240104c18410682c0d805560382100c10443e000d009220041d42d540b20308a811010100358242c40c041c207102c1c1c0c0990f48440b8040c0850040d012000300d03000c200f02c400300703540381000700703c408482d0040f400491250760740d2170103008188408001021260584211410480520b41c1984040003100c6454020310400d90385104041c02d0f541c01101d01d103a890020004100158006e016290203409a8100450914250400c01001954180750003c0e20703a00c0712041000c514181c3e07a5030441a5090800100e03900f8814400b100302032040510501070314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347911726 1250 347910476 347910487
    0xb100c030518030a0605090d090e011203020f061e0903071502090303191d060c0c0f1810030309080105070206010b180303040b040e0f0103080720033009060708 70
    0x310708240842c0c9111001d01215031000071460044000c241c00c41e0000c42c41c0c0079420042c9038a9100340300d04c001b100c04c40c0040d0b0321540d0800c1394080039403d503001b0440941c45222000c04461340c092181c588610301085401d0b40780690103200c0500f2110080911545030420060640041d00e40300c021140b440f6450030042e01d03109084080780c41d502ca042c18490039480c20f28400d03000c03183d001c0440112016680d005540007030411052159074054120501c4040d0400d001d05400c5080800c159012180024442003a5001400388054175001c250b4103a420200b8a007030900501d030700502c1c00da000b005114001c00c030303900c0d00c100000d4584406003d0481c104000240c10341d0b07206040c05481040b203030700400341d90b501c580c1c42046011540c02031107562401c881001c001a40007141011090490f034000c0515450f01c80640c0d20800b84200200300b01075204482c1c45074400a482c2004000001c04100800d00c00c40c0d150032000d510540039200540041440421800b545030301e8503819121b149500c00c0907140c50340c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347912976 1250 347911726 347911747
    0x2130509041a0612030c0c030c01020f0615040b090a0e0d0807080f0402041d010506100503060109060e030111030a09061a100305190207050a032c0d0609080c07090b100c0305 76
    0x90108001128840480c5c901d04580c00400c1b15404040118202d8203a214000d0041e6203c2d0ce071900311703c540380c115a0001e409684805403e46441d00010000207009410500048401030162072001c00c086d0340c0c410800c01082d0070401c0d240a1070b81e6080451451510100c002e200541c0100f03402c0c4681c4c0e40102003811502c4540120050001d81d4210101d02880090014020304045400a21501203440102030207401001201d0088106039103207044181000020b441c010440e1040540542d07039810465500680700c40558002c0700450000301c0c111801d82407331402d036002041c0c80c410501da403585105061369124002d489004450802041a0b511900701d00c0028185441016010740001a0a01000b0340441c80700042840703911a0016100b241800b62246255044155110424500f2092080c908080c20310702c1135200311004110103403640e40b0400d15400800c0c4004c2c1c80d621207101032001c0c0000d8001c0a041c10345c240d50f00c4a1040340b4410007081007540c4c00015003031100000701e44248 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347914226 1250 347912976 347912989
    0x9240314011509140117120c070306050403030207060e01140105040c0306050d05030304050d050405090604020d02131806061103070308370612020a03060c03060f080102130509041a06 80
    0xa1504401c0d155000e00e41c2c0e0803140000e8080504c10070301c542109000800c0120000041211480306800100a070700f0340b014011901e940f03c05803d030350030b2184081c00030001d10507026561086119540243e15281c1515111058440d005015145a41045080b00e0a0201c806065045440850700480d003810805400c1d030003400250001c85d0003018400142c070922000200542c041c2e445801110000c0c08055001c0fa118000e6025095000c4000f4010860314036054025042c0c4060745040149003400510000c41c080f08141d01600c550f00c1441c908101b01041e0b8841e2500030580c80c2001c15200304110070464503441f81c60802410f005404020980c45d07640151482814448980b8019802e00c2600e01d510352403000c00b101c2003609060507004a80001401900c8107502d5019140320400c604694070740d03000e405481c00507020550341e18400100d054201a100707008041c8030000503a603031100404041812640d0300094060b4082005101c00100800c161a001d001442c0c120020740c1c0758400010517 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347915476 1250 347914226 347914241
    0x10e04020904140408030708090a0c0e04080d0c08060307050102070f091515050903010b01171305030d0c0e03060c09060403080a03060b07060b030f060912030c090d0803010924031401 80
    0x44003e14070421040040c45002940240c00d03030b8450166560b0b030015100e5a5000b94540180002203801040011603c00c40c0c6154005100301540e50810905020300c504884010b4862800145250240701c06400c0074807003030010705000c2c03014000721030401c05583c3d040c41c4c0e05c1c8100c2c0b01e055590802c44149528804442c0c0c00b41140310703812a102c000900c401859604008000d03440b951a0035500c468641c051801104145030083d0055071550399054203c1086004003800e40c2c60340020000d80d01340038141c1c03056420203601fa84a112048402c00c0900d46400401040c110804a040188003415501c4006a4080703941c010905a0b07540c01303100080b8003920700c0d0707030010f403010902040d08020030005070841c0d14480c03001c0c1c0c1281c610a085440c9a1780c2c501040e80c2e942e80350381110340310755817000c1903400440e401080341e0001c03803500341c1c4800400c4d403000c004502510f440d074003c0014030208009004442d0303a403e49010415004484421000e40c40381940700061042c050118a0051500290080f04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347916726 1250 347915476 347915501
    0x112d010b04020a02060709050a060813031112130e060a0312020c0306070306081b010f260915150307050907020c190f09180b0601022e0c0e010e04020904 67
    0x1503c4200803440656a00b2007a1402c10100b012a08041040c1c2058070f80841106c80550340c4240b5503c500c212020900040318055080019502c024149410200701404583e496034a5865540e50410350024000801c0e4001100281c3c0c010280002a80c400350705070240c0350800b000d580308041c0b4003c1a8600804144081e80500683e4200900240c1691040302103440c103c1c15103a17240103000200030030012048029010a82948000070114404c008102c20f07190111181c0c600c441e03007201300e00c06109045900c17101c85d034480584c407081180c0c04444160444403881c081c100940c60074001079124111401030758080d0f07400c0e400040041d8803c1201d0038016202400f034404001c120a541101d104890184103442e08501d0000074100c441e5205404140300704003e83c0c1c00406032961113120030000904860704520490b080c200c10070b900d11443c6400031126041c072043d8035040b80f8a100c1940d0340c00100708180907082000c0e0300307541d80101e8442c80d05181140d0050780c400081c400a00103040450004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347917976 1250 347916726 347916731
    0x50a0c0b01121a060904081605491809020d0f0c02030708030a050414030c0a0c14100f1e111603050d12020702040f050403112d010b04 59
    0xd50403000302c8500b041c0c5004004960408240760240148002c09580642d0044158400600420142d078050018444d001c144c1c8000c20072251519440c0034074501011400c0c12060003203502d50740c092010035180351421030303c0710759035506148000c058800d980340c5181070110f0f40740303080c80c2244c0c070004100c040c141d4003404644800d03507031f101003000740421192486800e2502c80e214071400e0002040d11803c0c3c0c0e0004a480c42c40d5035820010b405008003800c11102054511074203103c44005101400255140000070b10b0321100c1070804804a84450703104910844440000c0101d0341c5410350492030868081c00c3c9840c1202c9500004c81e07203a500308104001d44940070b200741000a40c0b005803003a00d070f1320365400c40b4100c0c4840000c0714031a9841d40300003099644080e43c4440d2103401003141000b865000c803c014204482c540203d41551002c0b40089403c1d81d446040004040d08040180c00318078106c0002c1100a0268501c03000c08400c200b1780c440507460032a1284400203003500809541c08014005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347919226 1250 347917976 347917979
    0x1f051005100e010801171e0c1008041704030b1f211109010b0406210912080708090c0d150c020c01111f020a03021b0705011d10050a0c0b01 61
    0x510202d02d84080c680011901000011480d01c80c008405010034034001612049001c628140c061481810b03042440e8011580304921640e02c6224095005c4c00645642049184c5403510094034140032102c0911340105000c280302007984800c005a2206040c0444403081035810000500108141e01c05505010803d1041c0c0c4002e080e0205401014441c0f514036603944c0301c0400b02321027002e0034001d0081741c0b00140400c00595202d17106900c030070725403140321120314180c0200c002c00341c0e8150901074407124080b1088801490b40148130310341c011568504000103007005c168580d00d4606d000001440340d24050541340900800c07000b00319624030548820022400349180c0a900d4040270582d4502040300d90750041061a0f010800b005c6410003048980c0704129607062410007508200b441c03404159080c08510003001d41545174414000c8107100030b0003218581800180901d50b111140b2100303a04254401d0b000391104105400c09800d03c0c1006625038249002c11141c60380780b20302c0544400080c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347920476 1250 347919226 347919259
    0x80a0212010b1b210f040b0a091503091505060301110c060f01120c091d031605010f020c1e010e0d08010f050402031501080703020c0313171f051005 65
    0xa01100d05041d03107a01e101c0c102196499281c00c040301d40c0b0311811191001303400c10740300c0650042c02d2003d0321121150500352900d403108003607080307050170303001041d0082800d0041120211190000c0c200d9443e00b03200fa0b04480d640c0c00c40810302c2120000703600752038201042d980e40c0e00703401295081c25483c001c80c0c4c8506c002c0010903680c0000f6543e20085582d424004070302c803191201001d0803a81c0010f0040c0440b498414014014134009589021012541c1d405040050702400200702111110300c11848805103402d2003821034129801d8010344030f10411500c041e4800101e082d000241c004001c1c50b20180040307010354050721600103071460740c0c090b0301d001c080e030341c0d4211440c5070682e1501d83c030141403540ca4005200c10cc0c0301c151441070340881000d5010708590b105909190380640f86250142c10b003808a940d40e0b1864010780ca00c002c280031291014070402051085000307210f2903207001800700500b0b4604411150b000380220014450b1100005600c1e01c502d6480305c4010030003d0504000300200c0c94 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347921726 1250 347920476 347920499
    0x16141906051909030c080306041401031b05010807091205030f071b0603020304021f021e01020c010b1e21030f031e15060703090306020c061801050c0a080a021201 71
    0x11a0032002e501d600005a10703031100c51140c80825503040c2c4414204008603194000c440e08010700407580551281445020041b00880a500940c400c58039034112101c01c4242c0c841344059500210b040049060800912680c08110001101c40b0050074002c551801e0401d10b003140320b0001204107694000480c44104002240f0036101003003000b001c1d032090f40c0c60310800c800345e120a03107000e54010b0b100d102d4072000d042504502205110756004807180c0180202790f014180c0e16040302960765940c04100b080103c0004e01a406030b5400484450b280c480031640d401d0081c81da034400880c0920100c41001c2207005c0300310055440c00303000808498640781d20110030056580216148179004030807071280545460540c0c0c043c0d0051130340c0140307285000c50305030500400b5088200240c0030051380030030000203d400e1388014208400d885002d031a4501d0451a440d0060800404c5500103030714001c01c01c20070f0703480d92080d580701c50303107074a0500c00645070300340c40c2d0001e0300902c042954041c611000024031900d000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347922976 1250 347921726 347921731
    0xd0f0302122a0403211e050301080708030301030f061d0115090f1806020d0b0a03050d021c0203090f060409140a0e0c06030a0e19050a06111614190605 66
    0x210300c01030803082c4024101105014610005102d00305142c0303491164507400801c40c0c810181490060740c03410408001a81c0b411100021a020550000c0140010704050000c000507150f2080103610f55403555907000f600b01c14510000d410190b171441d03800180d100301c85920314580850781c003e000e55011b01242c070140c01024403c8403e03403840e0a94650412825000c0e640a0350040c84261081912645606010307501811400d102c0680c1c40c2c1031500e03290f44201c0c010018600030740040c852100481c9029191003510101c260041e4280540c01692560000440f400e8001c1560302c0d04d03080d200e1401088140c02607030003106900e41000107074107088020020300792060444100034400c1000f0b00f144103881d0484040e01d1608540d0810010b0105a05a00f04201502e600e0044814010031440901e4810400c804116070a802041444062103aa4040c18541d0501c811210740b40155443e40341441c200c01d2840102000341d08215500c0e004014005a160010009104c0b440703000645018001480c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347924226 1250 347922976 347923021
    0x61810121503020607020d0203010f090804140d021018030605010602030c0d110a0f0c030b0705041409060a0302130906060609030c1a0f070503130e1501020604050d0f030212 76
    0x6140401c09070031046100101102d80207800a86045074a0302846490308a01e02c06907055900d0789800700c8083c06621071000c3c00f900440b0500d07166414014005007014940c0030851055502000300d001580e5484d0000d0480c2d00c042c2030a00114407400f080d00340d540b00c5940007130403103850a800082c0860300400140400c0c0340070340540b80090480031003582e00c1040204800f02660000b1b820324000b40c01d0700e8002c038807140182040950b007940c940d60f0f8030b00c1d101e04481312400100003090070803100c203102107168a10311080b6150b0300d8a02d808004030300d035256036110103485494020200c00c4480582d40c404652181c0280301400056103c0e5000b03003055011f403208403a0388900110014014480c503000a030a80410012607140012040100a107030b003144000351a9030100300300290050300d06e14080d0005214910500070540740101288100b1030950f024281036401000400002940c007194102100300c080c101884070b9003030034200710300074042e640c01103014030210814046082c40107080ca00d0303007404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347925476 1250 347924226 347924231
    0xf030a091e11030f06150120010605130504080306150712090810110406111609050708010905040209040308091905060604060803040b0304080702042301080d020a1106181012 76
    0x40c001d16a4884c4030743c1900b42e09030030900100740600484600c3d200721410514041030a500c60325038440041c9501400c58445139980c26040003941020041441c4403010b418080007a0300d0300741c60320540340c0300c002c040501c0b4001c80c003000d03207032016120192000340b81c20418035844403188090140c00001c40e07020301d15241c41340070390611701b0a00d1341c041c8050f01010070070128105480c114065510002e40030a0403020f0150900c007030001c61402c0d020380000e00d03400364041020705200402522005040c0c200003080760804c2c042201603204d0400c1c0300d8101e80c1c103240c02d02d22a500c0c41995030608010310031380242d80006841da9030a01c100041e030180500b004640030810360340c2c0d8070300c5e0f59501d10452081c100f106c0d2042c0009070109500c0000f0f05402800031b4000320b0010a0044070704a151b00c0c021490640301015001031000c2407017007240c000001440d00050100c03400c4c0e6224103224041026099108000c002041111724001c0c1220003050500949040d020084081d40603003032552201181c081c0f0391 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347926726 1250 347925476 347925503
    0x60603050612071703040815010e01050f22060801110c191e021302030f18030a0905040207060216030503070f0915050a021509030c060a02030c0f030a091e 68
    0x10b40004003600c480600c07402403805520b00040880310880810002145000c20b1100042e981024054810110051421888190b042080711046000181c0000e40510140c110000450f190f60b918200c2c4040c040f407e0220780d00340b141c026400303010325401000640d42440580052101c906c009005408240e100703540d5640800c0c01001c0da98103c0e020064002d80e500a180100c0c070540424054985002807e2000310300c04045007082a0f0b8416140d846060303c49104000310904035840412034039002401031031502c03400590003403041c1480d00441d17204590000c0c0e400304100c2d03640d0496608143d03407805210301040504001e01650400c0340c540020682d148800c9114a00c01c0408001b03580b06440b4015912200c42c0085440340c004070082c0b01548983c10310041000c0744d4080c09480b40e040d0380011650354071541c072064100003002d4800460280140240000310b01441d05586c410815512500e440f40d0768a4101380140107280b201a2540703e01e000380310b142c10749012150040038010b00910082d013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347927976 1250 347926726 347926729
    0xc010e01061707170a02030109030c3e0f0909010c090b031009020912011b02011a1c0201120f0209090603031801030b01230c0c10020307030e01090b0d0606030506 71
    0x140404400066682284505004c2c6641d00c12125444e080c611046560245184d4040b0b800c42c5c0440b0b10a40c0031580d42c1051000300804104440e50f0303115207072070003c1c40c154a03034040c0c2c00720042c1c02c102c0c1c03445a034591541d8405131100f465912404000900b030102600f09030801d40d00030515030411a0010750f00000102e00c00c041c003000c40b4068410340c131121290381d01e020354590003900510141031744040c4030014542040407d0103000700070400c210a854580000c0c803c0603003140c074009404410a0015201c04482d90749001d0500d1403004840b11984513070031507200489800c81c00701e804512203868404907200c0000c00b036010340004507054600c00340d01d440c1c030010155070b80689100001804400c41c00c0c074040e13521079048038400810604002003150b107981006d68541e00c40300c804580003240800d1000c4034000c20009500c4000342036070030b0795805c800350300000e403a8804c02c00c01409004c220010703501390380d2103040214002c1400d1016240c403034824240704805090507200d0640005c0c245008542e59 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347929226 1250 347927976 347927999
    0x6090606070812040c050d0605070201050921090105040e10051903110d08090d03020a05010c08010b03010303050a09090507022514091b210702060c04031b09020c010e0106 75
    0x10550800b90740c9003801510b0400d403401c100028402c9030b00400d540740009541d120700c1d0140108a10a5401280364a018480282114002004846240e1201c030400c000101c259150704030700d640c0c44036003070340d12440c0308010703103040c40b03140e00c00110700980c0c004004050080a00007810394000715035042c0c2c0b06c02c0441180540804500000c0c0c840303a0180d100c06814908041c0801c0000d1080c0800c1c0d00b00000d68002a40410386d10500b900544c0080410380c003040000e100d181000202410a048294100380d6554807500050200038184100010580400c5006d060480c004000703081c01480346103002070009480c0e10007020a4540020480f08039502c01c3c1d200c0200c41d054134144026111000403280400002c00c3c4040d0501005211000c0c2c0894800e241500609134200d0107003007a86841c10301344548081d000001e0a41381190010810300c82c0958801c001c41d801c42e40c20100140103420391081c45101840316500444401e0b10000c1c1c01e601101e0b044d004003541480450007040040e40c1e407640001c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347930476 1250 347929226 347929237
    0x3060921030f07030203060d080a120f021206060d0b0a0b090925050706021303060914070e04082a16081f020c10060803040510180e07020307060f0506090606 69
    0x20341e140c82d40003803940c0d031095002d141e1003040104081203140e1951280b0351258002400d620000d42d1400c0c1e003c0074560f060007a9140415100c0c0300b10f16144c0988402801d81c4006480302e480b0308000030704014943c01607000b10783c01e01c0000780032800c420390741c1c07024000503480090400d000d00d84600000d034803d011041e55459003030448460081d4007502e484100d52962010808981c0560f003407000c8400c00444000c058091845003100140e12003440c2003041d5095881c140c000d030240c0c0071a400340041100051401d421a500141480e03c51960b280140c00d0040d04a032016030f4801c0166404803103440c00901036800d441990307050052a5118101b8070384a06100b411006400d0110f21f0278804086c1035801081e0420040c41a43d401a2085550000b600c0d000d07400468503920120342400326140000c2c0c1100604018100b44030092b8641150102c150301c184210141c506090002441c4a40280100c807445c0794480c004202c00802e01e960080203100651b0114060711845002841c43e05090048a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347931726 1250 347930476 347930491
    0x3072115030b060d15020406030b060c03040501080c0403051c12090f08071e0602040f060504061b020f100804120203040501120e0a1e151104031403090306092103 71
    0x140001d0940d140c0755428107000c2c14240d00903070032002620105605a00d0078801c21241c050150b81d4030300c0c040c0010145c81c00d40e0a0648940c00c10880d10542200000845048940a083c40d841a9030303203c0d042140e500880d070001d0020301510407051603a251440c0c440c86421019103d03440c0010036010b502c000c440682e0030040085a2201c15100401d1564001e400811302c150020150704580c0c0740d0386040a920300800721030141e00070809101400e084030101001c1d02d16460400c0c02c191406070000c100c84900e48070110705104540c030701400c0d51121440c0d0048800c01030004540348000080061401008131819901807401203440007060344080100d904a90050392041048192050118000d00c0c0858000040784500e240c01400200360555420402007124080b0915103070500f01701910400244060600914140e0000780a2203180c05a40559070010100c2000c0301c4110350462952150a2000c1d606210703510030856030070b01c002234004042c074035641c841c1c0c0101001c1819075103034003043e43c021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347932976 1250 347931726 347931761
    0x2040509031606180615080609150604090c030c1436090f0d08160306030510020d090803010807030213020906190203070b0a1b0203070215130902030721 67
    0x3000403d850360020140b00c103a041c443e80e81410701e0b80d10700c070844044040c10010f54041803000c10168505010550b400b6600d40c2c00b5100c1c1900708a6003882d410300051605208550380c610b01c00074041e00000e0070b00555800981d0f102ca07151580c004140c0b00f2145586548103440300104800b5081d0028050b001000240f1481d118140e0742c0c003081444110b0003004d14609100f400ea200d003043e00304005070802d40e030321503c442c145428900000c0c044202c003a0005d00a140c10800100001a0009121120440c1c2080c0060311003078107440242c090003c0441c040d10200c40800007040b0044080f4034001220b20844881d80c00c40035250a00041c2d004000d140f60f80440180034802c948107a286101c401e0301c0d4240f054070b2511506640752008040217440c00314021f60343c5c5080f62102091618150300d052040c1c0003c0d400c003040b41c4d00052110b42031506650034140c001c0780035104024a070811402428000105548a20300f5441c02080400c102880072101c142000c583c1c940c0301c40c03138030803030f0203121194422 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347934226 1250 347932976 347933017
    0x90b03070b1b01020d0c030b03240a0b0a090f061517060402070803040b04020907020f0703060e16030305180d05100506031006120b0903030c030a050403180e040204050903 75
    0xc1c64440d8104000409800000d2201d1a41081007840141034403001c600c40040d50700704510004044490b2030300918040ea10659180e410034807500b641e800c00303911000b1117480301d9a410000d40041c10900c1c2c00346400101c0300c640480c814519802080e180400008100401ca03514000324036120f40c01080400800c2590008d1807103007015425a60388014040c001516000803907640082a070700850781038607810f00d4817060108611340450b80540010892000b0541c05499000003030711940648402401c00b56141000f0140250034030001c06171a00481941c2d001541d01d050184c03060f405400300e00c9110a0301c04004038107182c07098000c090b20780c0100c01081d0603864402c10310b00900028040c640e06108a441d43c810000b000c0c000d40700903089044244c14400b0040c81e08400740040a8424045600b007841000010070381c560984c2d81c40501040003040540769810309441304241885404864805010003217404000c10102d180220310945080100e03a03164600e05803a070086401312031031500311020307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347935476 1250 347934226 347934239
    0x607180314070312050c010e030301140418080a020609010608030301060f050a09240311030603250e0c090f0a0303021c120c0c0b07030b0307051507140102030a06090b0307 75
    0x1010250388241d0710455000e55200d44031021803c86038105140003c400050401240c0800c0c020440110100c100444c210350403c9190310141d0703040101940580d50395160805041d9083c0c40c0c2000c1607821800303072540c40d150304d000291079440464103a46103600b40343d80061000b4000013124101c0e2041e9a43c0c00f020364149400300d899503c0344c9100c03020804820000b2412600c20b030341c03a00784c5034041400c0c441010a50701c0090b043c2c1d0906611800562070500412039143c901044084284480310a85c10304044404451600d240f01c50f08081c4040072070008000503d4160001030140640c211080c1032901445400c1000c4001170380001030068000c5400303110000440406400000d03210304000107007956401c101e100f1981c00300c1d08503000801d0105000107010714102c44503040005440c0501550300c1300c0010036a05d11a5101e401e0003130029486000d40000b26805030f4840d603510030180886505202a418080e410658140404924118002030000440d02c12480780400180182041d54039260 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347936726 1250 347935476 347935493
    0xd110901090531020628050a090f0f050607020102070909030801090513020315060d06090b1515040b030c070506072a17070206070203030c010504060b0906011706010e0411040806071803 81
    0x84140c54035005503820602d004030713040d6040380021b413290385254550710800c4004000c02c007994040040c8100d85081805a10b08284980003a502d05440321907480c000c03032004034a0b281300c41d03100c090618034040759101015840101c4a04071825100184903030b403518900c8181d0002007080c000e50590025180b200c15401c0002c03440d9202d14000c0c04e060321565151a800c0c280c5490940031104a40d4010401c03900241c85803881000a42c103944813180f4034142030140300e00344550301030020141c0010000444545040f002c4a10b49030340082650214185aa406008030b035250320f0343c0b405000c0505025030105404041982c540390441c5441c0d51809854050f0b403290350000f50141e0301700604100c1140562400c0000307002d40c0c10040300001d507510b0213041600481c0c01d8150074520807000601840803070b0383e000d0008141c54a9850416540340c803030a0041c0e45290068030300039001400c200d01d00c040301c0300410241c400c46114200f0b903000c40c1d41e070001c2141c09903605804100c4080380d03504188046007804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347937976 1250 347936726 347936737
    0x61706010e0d030216060c0f080c21070b010501020105060a0614070b040507090c031407080a090506280c0c0327090605030f0a020901050d1109010905310206 69
    0x6040141c0410400d10108a88036825501507025a11440001c043e403900010082d00602062401c1c8440241c95500d401c8204464100540700800102c0c0f6010308400031710a03600030b0784c203100d07900c610b4a0040752012802d8104502c1501c424180740000284c650040c01000c0c0f2480c0001c00889a5034140001610100c4030284000c1c0d1104c01402140b0000b251241b45a010b940500000c240042c60072402c03006861255101c01c0c06c150804090043c8005c150400b00d81000580c10314507029500c00920b540100711100d0044d002e0703c501014030806102c0d08016846014100714550414015010100252806000280001078401280c640444e11481800d400004501000d0240c54254108041c6006442c2c0110003019900cac02d08100915003003000b64450244140130b440e0344000d94001407807a180512545018011410705201001800d1417030340003148000b00070320102e503142d14824001300401c5903040703019070085c04040303100032902c01420110003a90380c09240d82582d607400e02000d034119 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347939226 1250 347937976 347937979
    0x1506090915062f030a0e030f0705010c030e12120c010c03060503030403110d0503030f390d0212010b030402041d1018021c02040f0e030d0902030f03160501050a06061706 74
    0x303c2c5081c0c6149030051000340070010960ba14590029101c0040504108c1d000f000c400ca9503014510030440d40e48c0104032400031981508159842c0d00f540d13000b150844245d40d24501d040d02424501007021000c40300613000304807a14000b0012150308040070307412104c0c01c0c000d02d545507105000030000200b42c5c1c15580b00401d8040c0441c10b508400e80d540700c3c6142c00c03d42c2d03100a0001900208115100c0007a806001110b0462058080d0744100c8040480105181040ca80d80c80d030000d580725807a50710b031b0100c034040b51420300020300030741e961400c86074140c1095604074402d9080a8111441849a50711550102e4643e40503000892062181200030401c3d841100c0c1d10010005031100580d46800e682d120806007034174200070400540c410401280c0c5140c1800d45480c0c40e00700d20050150340041555503001800c10002a02030a038000a46070210001000107103100000b85040d11517803070b150b14043c0510440003441356495000c5c0b03030029510b181c042d85001030380e18040301c03440c1c000040c1d4050304910b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347940476 1250 347939226 347939297
    0x30603030906070605041a060f090c090a141201090b0f040c05040c110d02030a0c080c01021b0f010c02030405010804080918070c0c0e070804080d150609091506 70
    0x310001c18500c3c0c03ca50000c0c0e51540d40d030020002440244041d030281c510034110040400c0c03500100041d80e10850f07014407801000302c0307030004041c8041c9500726000b02400034038400607030307507250300c3d64039004640c01c0090b0017181d5a010701c0c204d11105014110700e050b48501e0100c3d06699010781b5182ca01c1c0014001d4401e5100004d00180d03a84691040c07400381520fa0341d504442e0442180450711340300601e03002ca03045600410010750307500c2c0d02c00c180c0b05070b03140d0000d0300b15501e00121400c1130281c00368100329048150802840d48040d5000902c0040c1d04607140300030f02c054010884280c0e00c0303000d1413044601081070701d0700080001d0720843c01404000b0300181106002c8400d02407820707c01c2030445501001c42c20701e50800003400f055240c440700034030710700307400b8801450400c000810451000e40010079a00000c1a103240c2040c5039044001c0a20000501c0041a070b621034000305007175401e01c21001014a8428a000c000b0883c900d10760948220343c4417812203201130740500c243d4801c2c20781e410800e0300303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347941726 1250 347940476 347940487
    0x7200a03090f030b1810020409020c0615130e03070b0a062108090f040f0507020d140c0304031e0f030e0406081b0616060510080f0703050c0915100c060c022103060303 73
    0x846d148090400340581110045c0c0790034907141054500400074000d9007003040c10714030014031650786241c0c80e011150102000700c0d01c01c60840c40d480c13560060280c002e10700d68042042109042c8564800800c07942503a525601422a04018020bc9411404040c02943c0c003080b9520050a2840c41e100080c2c9010700000303034562000340075070101e40c401e65510005070416a000310a035a880140000001c0c040702486140000040d2400d030b5901c02d520006220b1247c8100400c0744646000160004075005007011040081030701d4000c0004041942d171500c079a01e801c00100700580000340c000d40061b4100e8407a40d00050780410070019030000410b210a103240545c0741d1740001c01602074503004504255040b400b140c184502941403002c2034010b213410b60700070f40c0100301246e8006506200c0c1a0f0aa5134071a054584042c6820364120400e041500a5107030710340403c18643c0b12403616241401004c00704401001a0070498480d91035100c1100500e05075840002240074140c001d6410083c010126403400e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347942976 1250 347941726 347941753
    0x1c0f020d03090503151b090a09050606120c0d0515090402120715120b0103020901020703080304150c08041a01050a17030c06010b04030c0f1d07200a03090f030b18 71
    0x3805010301d5107510250030038441c0700c401b19007403a410303017030b0f1650480c0c1071607200c0000c51980a00e9100b4030031943e440790040b0355140c5a00341100c5041345d2040700802149400741c4008001d5014821055030740e454240004c450303030080c04102d014503500520700d1109031503a030208001d000c04004880428000c031040014040481c40740c04c5010781080c2c940760540d07030b032a8085004850365803802c44d040c03600401c0b644115030b81c082003010035aa44001001c0c1c070f989483c00d00c0181a45c2442c2c800d0301c03040c540015080c420f07400c002c03214030451052010807503042014400d02d903159420702c90300c3d81001c5595001e0200f140c1c11421040d2980c00001100e08101c40300f225640f410500b030344410200400040c0c10b0041c0405a08000013404007030060312801c80c540040a50001008441d01e20400314050114422038401d11320220f00055003280d0446144c2c000382060345513201306030300f1004144520000035403012180c0311107003140e400007d0410240c1d140c0701c3c0c9070302d441c070011840c1e80740740207009104103407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347944226 1250 347942976 347942983
    0x60f0424091d15071407050a031218150c0309020409080a0906030c0503070e030f101e0b0f0d021906050304030e041a1c08181c0f020d03090503 63
    0xc0010071000b1550180c8030b501904584074610701c0001a0300040d00f8000d032801069881508181c1e28546900b40003050540d803642805400c07401007860050811003414103600441c5080d4640004404209600ca0406046074800308040c00405d00001280304d0699500694044000f5401c98207000c1201c100d50340c0010104c80d000c0104503a01c41004c90145030441d40002c2a001a194078101040095841c00d0090000d0100a040f68104141d030a41380485880600c16184650029030485080b0302d541004403024040c03010482c505542001d6118140304040e01075440c2016001c0c0c001191403030760b07000340300c8181d000c04403e03604804c001012810b0701d00a045600001c01842c0d45060b242d09142c64010265401e03c50364910840c2080000c6825400c0d900a01c1c803007203000c803000260000722071100841810520b03406007041001043d612600b140c18000d20080203411600e240e540e400326030388000290702d1f01c10040d044408a83d11300005081210b01181214028241905241e40d50000a450b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347945476 1250 347944226 347944229
    0xb03210d05040f0b07020304080c1003020d0e0105011802041206091a04060506010906080105130e120c0703060b0a060c1b0302060a03090b060108071d0415230108060f0424 75
    0x490240f4940032509108404290b107402101c60f102540c42c140c5008a0540d507407410441d0a03214120024102c4d01c4c8600940c104c507a440d504080612048242d0186540280802d118080e541d200030450b55902a0591003198244c849661120050614980750000205160780c005c0300c000900440040100742184841c2e44294840c000109203868104001080491158800700902c40c0e40401030220340c2c0c1d828140303d8004c3c5c00141c000b4030780e080062010700d003c40034040800d60300c0c80010510110303071001c00c1003400e481c010002071002410600500a49103160f10405000400821020000901c8a030048240c11009294115056100e0300081c425a1102c8203542c0826a598800c4e01040508010aa8454000d0a01e0035242c6041034003d0300340002c800340c00200c0c607221800e1501a0351b0b56072018002c4595002044282070b1560031a24000c442c01d9040c0100e94100d46186500350321a20310307548602c0e006008a04403080b903034107002c090a0380c0240c1c0c8881c9003000076104003059142e4108070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347946726 1250 347945476 347945483
    0xf0909020f0a0822200d2415060c170309030703140706110423030606010c03111e072921040b0a140c0301050d081207170702010b03210d0504 62
    0x80b503808542440f01100d1418070171707190007082d06800d05008078900b81c140103240381100c2140c04c404030b0124120001403e13906144428070381140e1000c2000356010051302402c2d4400c40c100c0c135407052004080b05150204031132000485d0310400480300000d12800c074205540c1d0a00149a0034070856550702c04c144c81c0c3c0c0850000c0710120100c0d0030400900b10701c4520102d144408100c100340340c1c003000800d48406c00105007505110402000ca01094400d07018410203104070029600400e0588046801c6060070100040f00751050440c082919030181c1c480c001071101d4411507001c00e15058075180c03070035045440500844403100c403403079600c0d0782601c2200b40300324411030441e0000e10303140700c1c99021904015001d21001d1b080900f00f04d518400402240d054403021a07490319414020718080d050f5124180307080741030341040300504c004150000c0c001d07080d003211140b902c9810398030764004a007200c81c481d16a59043d2302080c2d03452003980d20ba404080419141803800d41c9032042c1e403032284041d00c10544044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347947976 1250 347946726 347946743
    0x4030c09090606210b06190306090302070f0602060a1a12010603051b0f060904180b0109060509040b04060b0105041706061003060f0306020306030316030f0909020f0a0822 75
    0x150402c0344510611000e80243d078901150590740c00d00070301010100c03040040c00c4d406143c5c042522a621080a55410b456404504901d10f40f6460031602510390f0a104401600c41c0010108003502c480c1c0c004001e4807941c0d4000c00c600d0795124035034006040f00045040203610f210000d03889640340c260300c5646080c5c281d000440e070070b891407a0161034109a217524000491514003007411503034407052452403441040300c285031a9142440040c008129003081c8012850b140d0342c0403000c20001e400740034102c0c0c0800b001081480d1b600d02c02e029068030308444c018810910103000400007001f50b800252040c0b0b040c58243e041075100c0b04040d500c212002e9004a46a0204040060500e48080608900d03203181c5001d000503840d00c0c00780c0c02c2c030006070300000302040d03008000100191820000e0303841d50b0400b040601088112414003074102c2027030321440c00000e040c01001207140c0c1c3c1c440c0211a20004104001031814240c91011145454050a011620042020010040c0d00d20a1303114110038082c00e0fa8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347949226 1250 347947976 347947991
    0x103030503131b2c0105010c0f0c0b04260a0f060e01200d0e0a0f0209040302030d090803070e031203150f030a050139030506061207200118020f0604030c09 68
    0x101c01c1d02030103101c00ea60544e84000300501650b6400192072107043d60000c5c0c090300078549403405068001941e00315640e01c09022038000b42e1070b208180120040011031354031003107003002e441c0380c10780b0742c1d00140002d041c00007035000d1700f0b0014038130750f20000e10813150700c000148040840c11180c0072001c55031004c001034140861304448500c4070b0310601e512440351000030080e02c0e40344c0e40d9000400c6147c2c0c1c03001e0b2181e07480c44000b5050600034400c98071200b1180b9401c001551440c9082035a81d0404d88248001642080101c0c00074100001d100d401c030b000901407541941d0b2022460b1054000780403125400080070100b1070304030f46080000c4000303140300d1000480c07180d94101c3d00c00b0607542c030041c0a0101011041891110100c05c8150502d204054940402c503907075040041003040c071954090202054515040088895001ca400e5100d03030240e089060407030407200e8015090f20032022001c1c1001e43e440c1d02c40d5006282090a27120b1480b8040c00c1d01c1c0c10580d982d00c58040800c1143d100c44030094a8040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347950476 1250 347949226 347949269
    0x10b01020706030b0f061b0708030406080a0b0906040b060408010509030c0105070c0b01090f0915150b0721030e0318030606060c03030f0a060f0902090f090103030503131b 75
    0x144042c2000f480c0810180c0403000000344880e06845a035401201c0000e003881c83c0006241c0c56511801030442140c1e0025680c4010325509d51091241400040302e030760101e8103006190168100021000341407010035290704d01004010040c9120307403a07000d00c0030480021001c40a0182c0307485101c150001d507480e40301d0104881d00b5100000d00b51010030040d0101c0f24002440400314a05651801500180380c0c4401481000281a4680b000d003c0000c0d122080d4002c1c0f2003500800241c450240c0120045a503882080683c2d015515004041c130365016280b0109008443d40d03958100d59501d00482c4900503a100c440c00c507404000c07107802d107500c4501202030a0604100094020030207403012450155804003131a00c9000180c0340040804814010801e0b6034034503040034020781109400003504550f2000100000e502003211300d8010341c50342d2950300c040c2c94a20507481c1260741640300d4510715035964043c413400c840c154604a40041d00c80c081000e00c011a44c0e0344601502c0d03a010040840c0c1340743d10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347951726 1250 347950476 347950483
    0xc100804140609190c1802031504050606040b030a150f09050609150f1f120509010b0a0b0d0204030503041d0604060f06180e0c0405011704030e01050906120702010b0102 74
    0xd4010140e03a111209200850b0030001c0c04c0b0700d607003071044441d0840d01803e2030000e1100456500c80341c1d4690862000480c170054550045003e006041e614500c480441350601c01238407811580242d10900600c0200560305002000f158060201400002e100ca680c4032032801c0121507820429001e0352001c814800502c6500c50b00390401401c0b140d50a16182c160300b0114002c601070b105a01650a5840340d4015440d10030b0404d182102003078204140910b0100028999500d40c0040d00c0b4460614010504900d8184030b0a80082d20107400390094500300041142103501c006a4484403c1d800c000000c04200700b44042d001400200a00400f1032204074001a0b050b44040c0c00350340328a01e0103c08000e0008140000801c54541c0d050103400c01490380c02d0742c1c5400d5025401040c0a940c10320030000c280e08004010000d603407090b203030380300040054002032245507811074008020600d82400246998002e601404800c180180224035085204a42c0c0c1d0302c5402c09d45450f40980c1d1542081b042a60701403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347952976 1250 347951726 347951753
    0x3160309080a0b0604020c0c090f06100e0d031b14030d050c0309070302010f050c0313170f0706081504020d0f05090c0d080d090f0305070c0b0a050d0e0c100804 70
    0x301d004180045454481c9a58140054281403049034001040300f2000410b0249120a4500074801082840c1c44492044116403c07035155100d10b551200c07a180c02c500a482840c1074007000380c003000b0038041e9a50f041d42c1a0002c5409400708600802030000000e44840521b44800240d40c00f864891044410000070f851001e4000400c40d442441041842080081d84104480e024a4100c0d454003100b041640d4911501c00b074609640030000f210711810f05500340c4074040f1f0328004007010a040441c852142c4917852010001110303049464104030161040000f2170b00a68070700c00441d8400e083c400024101e0f4841c01141c0c00c0c0d1611012564940d01786885803e43c08414800680b600c42140000107090305108c0c4001000f055020814080d880c100d940403081d2980d000a00c41da0a000714207000d400d94000341c0c01140c044045000200754000e40b0010b07a200b100c019207806042c06101030146014221021100070f2070300c2142c6035030401d0b5880b0358244080303a2982e2903402d8642071900f042003604941 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347954226 1250 347952976 347952989
    0x170a0504050a0b060f040e07080c120d11151f0501090f030f1401050f0910021207050715020d021c02030103081b0118060203060f120709020a050c03160309 68
    0x100410400416004038071001c0c0c941d4071921003582940c403400019807045d02424601e0b000380c513004135520b0f820000074030030f019901800104e414822140042001701e03148022446e406802c001c400b90580c900502c042c22031b801104050702d01c0000341004038501c1080c00c0b02c540c0c0580505a05a1030399038031801500020f03142c2071038100c0400e42405000e400074822440020100c0c1c4020340200c080c82031004081520b031500c80028040d50030020500f10341c4403c20f440e880d8040c0181400703030400306003d200322142c0900790811540030b641c4202094503150800202174994001c3c030348014005010a100828051507103607801a04e0f1325402034903a030300201c994546001144100010310110310100150f4612006100440c025105800c0c20396000d8000c040484141d0824901c00000708a4250007841c80f446041d500b0741c000401c1501005207081803107142c0c0c0900d07000f80c6000d00401e2015002064081982d003880da1600300302040140c555881801142c0c205038000200c00100b45c0e200d031455004024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347955476 1250 347954226 347954231
    0x18060a0f0b090601021f06031406010608070e15030910090b0702070e091e0708010501060509010e0303030403170c090307121a0106080115030e010f0515060f12040f0f03170a 76
    0x1c0c0f150020707603201c4000c4814008a19468025900d082d050741280002d542e2201401d10b161140c0c0c24207555404c0280680300200710070f140002c1203280f2034a1101c40641008200303402c19039845445117041e600291864040d805230411154100282d406a07244652169080059510b800603000781044030301d410940001c0d1200d02402850389002443e09145a01440811440c402000c0078529156081d40860341e20b5081100000d1065000380141c60036940a89580288103240c00806807603201c00ca90080124586590a000308003424002c03d038032840100ca07051402d808100003a14014084e40030200000c1d0300500c8500704640c1d11030501d08111180d5196001c0c2d4180100a0003480c0140a50040c402c002c10040d140a40309810500e440d0000700000c101c101800316180000e80030865201c41e021400040100c22418890115030302014101400340c1003601c04503c00a1841e0f0185c801d9885042c40d0b00d11101085040c04500c2e500d6100c0c0c3c56814145c0b01100c0c03c0304107584000c1a80a40c0351 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347956726 1250 347955476 347955481
    0x305070f05030f130c080c0f041b200102040f03060b040501030f030e01020102070b0114040c09080d12021902030c0106060c0c09050702010f11090a080318060318060a0f0b09 76
    0x250000c042e41d03004001020848032030782d920140c5030342d111030124000d04402ea4000001070b0311388011502040c00304007a110700e041c501241c0140016124141c03500d0040205040103081c0da9031141e0610311078403007140320120481c00b840310091f0076030700140c1180703461180b0600d0030010000e4500c0b4a110b0924155000e129a41c9103488410003100d207408043e003400b03449004280243e100b903048841460303020000806550f1a0120700f071030a84500111409a407412000c080c0c0c950240e2500411614060300501344c00d25042c1085034504074040119400903003d0090010900c0000c42522094200341d0083d07072102ca41c18500c6094079000e0340003a0a01207860049400b14101012070b0060301c003610004070740743e203818008030b00400051209a601510b03201c1014050103142f801080304003030032200d41c07140a480f122aaa142d1203410655034001d02c0300f05080702e0508100c005141d100881000e40702011800ca5a41410306404494a2511301d03940c900c9000c107100e55219250b040941900e10403140d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347957976 1250 347956726 347956757
    0x6030f091106030c1c09030e0103060311040b03011e05240607060e1603050304060215010f270203010906050a15020a06050a0e0304080102040f0e1608041719030507 72
    0x724024926400303010008000b440d1102014111410210f1007541e4901144062095400400c182c2c0c81c1100042c2c80010303444411747c440c0c040ea4098a403c241404c1804605070200001070440e4409640c1654a8504440341076460322118440700c55a040013190758902502140c511403800c1710301c022440c00c070f039105a5417521032a0642c0c0301d46901030000036219044800f41d624214242440e0281c07481a1040481000b10100140040321368903005c81d040f508d460881c5803060070003405403458405102800f00b00c1c68154041203001c0480035900c81a0300d042403011203050383d00981100c844692501020004c81c01e00b0100d080090410101811000544143c000d4880200841c0079001c01e4030341000c80d038580c00d1940040c80c0020b220b8120b03682d0303690f03030784000f07010390003900ca0300746604201040040c12030f20702c1416510844040c9810000e0a01c0060241d03800c02c8007500664020816070321a40e8220040c400400c9441a07001280c204084640360041c190380c00241580100465161201040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347959226 1250 347957976 347957993
    0x12040803040e0a0905030a020f010b060a020a1b150c050715080f060a1211030c040e070317090a030f0204061e0302041d01090803070318020a030b070c0c090606030f09 73
    0xb50b5100c140e66940c691105a640005000000409000303400000b03402030303055400050aa411b48070b40310003403004540100c204440741c003a1120101c05a08041540d000060b0850752424a0b144190603074000c403074680c24000c19102c44c070080c20020601d5000e85a0a0100400081e401481e07411000c680c00d0b904010020072841e8080e0040412042c10780120301c05a40300c003807000207468181014800c2d0005400d0050740c521810004501071f005000141c189810301d800b60400000102e001051414507560b2002c0204650900695404100303001c40811743d511b410003c00114040c4448020003611030041004850060b400541c4c09000c0d4860780c4446101303842c4010459804850020b11280060b02001001c5120b51a0112951800781d83c00c040000001c00303140111847da8041100302848a5151441c542c0c9910180d8070082041c2c00b040010500c41001d64818600d10301004914140d941c2c900001c1e000da003000d1030701508c0e0308e81804001c1d1305114224920225030b000740000c141980f1200c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347960476 1250 347959226 347959229
    0x10e0c1e0c010b12010b4209040518010c022805030d05100f1403031204020103090c03080a110106050d1b0b0d0c030f09020102070905100e0f07021204080304 69
    0x1000000800c4031041c421082d4807800b81580c0260542e000b000c85200070311700a1180224803481a043e840c2c1d00541134000200c1e440c403401040000c0900e001114150507103030200b80e143e0b041e090304200703c0440d00d41c841d8082c1c0b5020713180c00842001c2040c007440717145003075400c0c4d049200110b40c04503c0365514019002e80d290380100798480443c0e0700445504020381144103019a103c0c03154240b0040c0b0038aa842145c4400803681940401c503032070b940320b941180c44907040b280d0070741d4103601c00e01500d00f90000e2061341a80183c0b05040008401b0502e030b036501464095640141d40d000008036101d120260002c10900e80c00c0c090340020020b00741080000340c0d00c00c240050240c440b02100300e200321500f100440540c060040d0800307030f5864060203805da20207840302c0140390000a0070061041000c425038052035000950580180070402e0800304004018140205240104d9440c5413000030300ca80700f10700940c02980091030107070003417801210207460446083ca80003d0b9440c100010402140c2c044140c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347961726 1250 347960476 347960527
    0x7062105070e011808071205190f0b060612040f1e030516081b010f060b1606050c160606030b0612071502100e010902090601090b0909041505040506010e0c 68
    0x2c4d40318420241c900182c40258016545a104811001c42e502103001c44d14000c10b031148084444100583e100860a50000e520050241b00510300010005a0061149031700c110081d0041c0c0c00c10120900a01003000195004d8980d141840034100511a900750f40d1001116902d0f8100026042c56600905a00c80d14070700900b9941000c2c01141084040f00840d5102c80c00d540c020780b5002003013200e103402811043d102c0c18805180800019020304200145d070392405002c1c0900c0c200d02e146494060241c0700050545001190401c031110381c010407108555000350003640c000900c0c81c10b5180003550a90041c1c4488e12607826004480c80040000402c0b0081d038030700000d51900351105001c180e20300b5043c0c3c11032514450400844450000c815445401142d0003100d28002d16202c200055841030194002e0210706002000001c400b810128407180c0c100c1c0c840c500075001b02c007100070380500302c50044d10704803580d8005000401061a0380001d00740c0200001c10443e240010101004142a147c11903c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347962976 1250 347961726 347961737
    0x9020a09080c101110110301091a0604090b1201060b04140312030403050a0e030d030f050708062b060207110a090c050a0c020f0a09050106030c0512070302091207062105070e01 77
    0xd02184c2070601c244246401750300c0b024002e1050201034084150424000d01150620300031002c207400310400044004814064045440d0a00300000c02c0090201250a035410800c03506420400030003d1217050000c00100c0a12504e8600b0062441d90030050041c0d0b00d4800e62140c2ca08001c0c3d81c04178011250015814204165a80d440300c20580301a00350056044c0d042c064094000030389509a040040396510900d02004580e40d2208141c034504c009a44058000112031401c1d008001808903111829a84601280880145598510a07617000d140f080701c00081c8032504c455641441d04c44140600403508050113101c0040200170080d001e80f4035540204000010510b0543d03c079104402c07405003020307195204103510b41d5403580150400788a17041c0000d03d0443c0e9810340138402d5050341c5202c0000350b848035464917409000c4020390407400c103c0783d1000c184480d03100742c2e9808002d044010503080d250b41180c0100110840903001c039002e0586005414001040000350707104100402010003400c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347964226 1250 347962976 347962997
    0x1202060a03180515180a05071502070b04031a010e0c031603021b0105060a05060405220b060a08010603050a020918070324030c0f030302060a02071b09020a09080c10 72
    0x505500b940c2c1c003003000d030803401811300341e50b0707605a441c0b4030b988280d0180b9040040c91070045c42056491076500c40180080e00580004d04c0302c448001080484008144110f42d031541d00c44d003081d04258042e0b032003102c122005d10446000300c140984210b0041039150f90302811403a10411030b104d2880b00070000740c5610100b25404400d0380c0664156071011410101000c0380e8a250300600c0d0080c8800c1e40c0b8280305503601580000c483c504041111300350756020304600e03011041803414000541c0200074002400d40c9401c10714202d910f494002e00388501d0541c0e41c0300142d516104e00681200c07806003124944600401c0303c0441501c5040d00780c1c3c10844c00c03080c45480341e40c912108600030b020085072420854450110f085000580e00d2201051701d01803030500212540c0e03442c2d444102c004902c8001e025804c0000050310f4500d07143d019107201405a40080a010190507490b240941e9a130400190540c1c045950000c5950000c0200f014000100040c00c4030400040050142e550340d451103400c102113070f80e6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347965476 1250 347964226 347964251
    0x50708070f1109010902031e04050a170307030c03410a060603050a0218091b040b2205031011070c030302150907030b0103030c02012c04061202060a03 66
    0x4a40c11650010003200481c1402c0c90400c8102c8100c0061a02c90b800090020800c006a0700c00c403400380720a01d52501c1038802c1590108042c00008005946038050503e00d24085141404d0540b0032461540c402540d9240c0340030054125000031030301404040c85d20900188139805081080c10b0300180f90045056400c1541c5440e106030350001c003401040c00f000c001c4c0a05800c031a080f44081d03a146803001d101c1c3e1343d01c1c10000400c138022100072141408803802d52808505105500035000020402c000814510b19400b002903540180d01610150800003162075000d0b2902c041d00c40d001d02042c161a61107880d00000a503503145070a0f202c8282d60341d458980d400303001d40804403451a944084400115640da007030103503c4042c11828107400e003032020005540c480010070071406503580010245026429524120340c0d503404500c080b4144003000d205080300300740c1c2150781001201d11440c04020720034413a081c0800c0d0780140e03000e04401111441c0101c0142d8810043d82c200380410b19001945444801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347966726 1250 347965476 347965493
    0x507080711160602011a2b05071710060b030f0c0307030e0f0708010c091206020711030303180706020a0309050f181e1b070303050601200304031a0f01060507 69
    0x1c102c0802e18494640050015019088400c491100c04e4200d0f04400c07200040c465959024022120959a1480821101170403c2260b0745003e008030101c0301c080e6203424120800c010300d00240c54042d884017295040701107a0f0700a54015140d840d0b00c0905504000d1041104064003529408041c0707004000205107600c81d9000158024400382110b040c0c4c0000a201900c0c2c1546000d00d00c01542800094071429014600e40422200d0f001020340c1070000e903845104c000e4104200454900001c4006046580d0701040954044c4510344003011070440503404031482c08510f070380a20305540180c603003200466006460f800480e0070680740f4a40d40d41101001658402c156406621481c3c41e510520000e070a90044407031480388103884001c4561100c1c92410340714011540f564001d03034000c00c5250002032080e006103421040605004921440355240d0014102e00e00107800c50603403000c1010418404482801410100d10728482242d40c2003c1c190280018014010b01c02402400103c440421003e80d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347967976 1250 347966726 347966743
    0x503030a0e0f1c170a02030d02090d02040608010b131b0c050f010203070503070207050d1e030903170702032a0918120306041505010f0c0f020d0605190507080711 71
    0x20007100700c4050860400c80f41a001c0102525003200b43d410060140c030000702214000c0c00f45400840c1001d48a00c542406036000708404c40d08074555035188001a2558060b01c2d003d04440c10002c100c1c040000c080c0000000e0107000441060705000315100310303054400503a540c010710b514140421078620300340140350030210010310045620000400020300d90207009107001d400301d81d00362070707038256607108010800008640141c40c1d05803007801101e480c502240340c4558503109041030070840c1d5a0751140403401c910150000922600000c000c0300f10315040c0466030400c1d5030f00d64032568110720612103120290301340c5030f44c5000728080d0010a50010305c080d0404024080d1008550084a030240c01166a070000d6504a0049003400301405010455150b8042902c606075155141202c0700300e800c4616020742030054814054140c480030158403000345e1901210b006d198003062034280104000e20907074020b14401c80740c03441c10092000340c0d680041440c0e0050a54078101d4604c00c0501c8a90b41480301c00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347969226 1250 347967976 347967979
    0xe150d0903030b03150f0c0306090c0d09050a03050c0c0405010b090d0f121701061e0e01051c05010302010e0603040321020910080108060a0b0112021b030304031106060a0503030a0e0f 80
    0x624081035a07225000c0c2d142845a06a4208071b1099210f107070f40070380c480c04142c4206500219420009803c00703010406403482079031084020039012031030b0715014104001d42d41c0c00e0740040c90000c0c04d040d40b10003c0024215034032041d02c003000a0341c905990310065003e000c100e10301c07480c0d080100b0018052400f061706c0d034444e045041c00d518440381c41d00c05048280f21701d10600583c0d05079800000c009001c0d403011391100d1106143e82a40040740141158036111510340c0b503060040a1010280c500c0080d8408606220001c0340080c080d4110700001d8101e40b14810520702c1050204100800039078010203810200d000b2007551076210700350321101d2010b400b1307184e04940c10015041100d44c00940c00b4203454101c5d908a016110385880d06046007003515992404980496019186400d0080d025401802c0c40a041084a6030305843c451485013940d100369000d4001a2100303401c944000024000e26420040c00c8520142691800c07000c01d45a0003048000c0c001c4c000401403a640e1910f0720461320420250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347970476 1250 347969226 347969233
    0x1e020d3e0309131406060906070f031107090e0712030c11060702061215030304081f060f060c03030f02040e0a090f080d09152d0e060c0a0e150d0903030b03 68
    0x2800f10b0349002040070010391201d607200c1c1c2000c5001c606100c001c444600e000600703600e140001a459501d070341001c0c40c20071020420b80c46014440c8060a11180007e00899100401d6403846005118580341d016048140501103080400001a400844044041e6403200955581505000c00198180104000a0b401c0f01000407421750001780314100318401c100c04007910402c80581c50070b16a80c2d00542c010001d0f0340e071168900030004102c005841442c1e250b41e41d0045202a11460000d101c07281a074464000310f4a50340760001010340500441d8a00c1d2032035a001c509152401e90031450000000d0940304a13035664901c1c07403080c0020820102180790300040b40607560056040d00a00602c1c0144041d076003408003250b0301480c00d03041e0044602d6403220814403401c89070410744a1100d0f02e907081c1c0e48405250748611080890005010341307445210140c8056840c3c02403140e02803c0c4105800340e540c411800d54408420852060003a03130440c1650b000002190400e5250030f4006003410322460340d0620 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347971726 1250 347970476 347970499
    0x260106172e060e0702100510090b120d020705032e0c0c060903020607120501050d0b0702070801091209060509091b070204060909060c05120c07031e020d3e0309 70
    0xf402c8644035024400035400c641602082040c0d410072a04150380350417104100c1c0004005c0e600c070940182c902180300415040b00d034000b00c8441445e086000080402680201d8410002841c040c8407a10301514900380e4141901e0104010b018070071425a0000240c03a960350130003881c0792003408111003450b4084006c0103504514280a0344d44c05040359601c001038004100d10104d40c0007800b40342e04840c8050034940c81e60000c2c2c0d990900c00038004000d08218481d045001800304000d00810545a005603580c65004414603c018103514654100200b480b0041103d0071040e25602030403540900941600031420a00c4da18900181c80303000e2029500134180340010800f1444e590086070440d01c0341c1010000a016004e00342c600c0d0280080031048400550300003405c5a40d481c0080c0b940a2103894100d84811f00c1138800340068130f031703a01d241b03005074400d02004201e5a0852805003030140400c804910441110501100008075903c1b2403189484007142c584c1d1211007001a1035540030000d0a1074581f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347972976 1250 347971726 347971739
    0x190209151314061504030803041718010f0c0506070f02011104060302250c0608040501090c0603050405010506030609030409021c09050a0510060b030a090c260106172e06 74
    0x1e19510b010031018042c0900481c2407031070001100e1380034208480788242024a59100d0300c850703410040040c1c5040320b2885024080f1400000144820144a0240d18118500c071000400000c102102c04060240c00b00c1c401c4041480014620fa128540b132810384d19070304d04114120702502b0626941e440c180004140881c0f40303609500030740281000c401c2d1042e44d4544030035141440d0744000c04054006040000d0034020984a09140c0c0c1d0300c01e000e03000124481d90b86079100040d0850903132107800000d5840e814001000b20138081d980e0410801c0700101400e040c241040ca17101d101e640700b08611f4640c0040c8280002049184030039440c003c01c0405c01220031642401600c0b08006e620484a170301805411003801c1c0990300c1440c05030303070309a4001803c5a4540d841d1100400181e501520200308041002480d00c071888043d1443c0a11408000c0c01c3e0040040064251080d80c2c0058403034281448050120f45800501c0c1c0d01c2440c03200740200043e0040300da99101d40341e04102022031043c1402d4010520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347974226 1250 347972976 347972981
    0x61401150212030c0f0d0204080303040b010302040f0603050c0d0303060f0b030403020f1501260a08130b0711010309021c06060e070f020a1203021204050d03060501021902091513 78
    0x4914540c1c0030742d00454607003160b48209110403500920346000038062040320540c1c1c440509051014240010300d0541c40d00c3c01d091440c5c108603000c82d0f640381000e0041c411410300e405226404441108203000050444c0e4809441c2c0594954081c018103a040d1480d040c14400d4010600804040703090b0745090b40c466604210607441110706030090312074940d451051590010b030f502280c6c603001c00d89a90303503420002000d508416940d0740c0b0484041c1d40341203060044051204800143c0700d0000c0603600d0101c0201e260196409900c1541c00c00c40922010020600c1c140100002034001d185c0010f156050f03100082007004500011400c81d85948410020480158008070a40c2c030151045291543c50b00001c460744001c0c5103650300141c00400060700080d5941c040c059148c0308500340542080c142c03001c2c61030340351400ca0f0180e40c0390344983d800031003035900761207901c0140000384054518148010b816a20030704e0345410080c0280300f480002140c1440505112101c1c281c010a42e114034079241d03000ca4007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347975476 1250 347974226 347974259
    0x1b09050618220507110c090a060b030f100503010608060f090a05030c06060901050a050310050709051306090e06060108011e091b0e100c081305040204030b040302070501170a020304061401 82
    0x2000c0d454200442c0c2200d01130365850600c505c641d00244820000c40040c0702481c2005003c411781e9a46841c0041b500504d00d001844c42506030304d900e00c4040c50007010810f4840c0711a48003d00a0745405400e000d0303410302203400790740400c020b01008030507160110f540d0701c2c0803407015001e0010b000c0414050900e120224115024850454140b2402c1c0d80f1641000605d26681c420301d580b56102c49903954200d03400c2c0c4c00c4642c2c0566603003000580c060380c40e07001c1407010440c1c0286009990b034400c0c0910070f103002403240000c1c0520880042c000b524151001800451041c040c5a40f64030300d02c82000c581c042c000d10f450300941600d5409001d40e91107000041c507c1014541c85001180380585c105000d810000200085006582d851401040c500d0329084003541c0030a04e49001c4100b00345001caa1901d0324001800103520504018940b4905410024100300158002030b04018074a4296032240f00e031090070070340000c1d00020050383c035262480c3c04001404090b004040c20ba104c1000010f000000404501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347976726 1250 347975476 347975539
    0x40e01080a0c080105060108060d0309050a0b07020a0b0c0c0111010e1002030603010e0d121d0d08070210060501170901230901060501020313030609080d050a0f1b09050618 75
    0x140b000e920b40d00c3d8142a284211142d40c0019180c02c000b8107071380b0303040841c0d42c102c80c041d0824003465a1214080340a030f4100b5000380d050040b00049040460400d514003d0041000d040c115040440c0a540c1a4483da00c0b448000d04211068406014845003903010402d40804201203a81402152200d48069003049030114401d500e042012001d0902c040750703940585450b41d84881c15803605d00c003040010556082040c0c0720090450165115440410480144a50b5a00e0700c02aa03c1e140500900d000ca05440b5503e5641c100030301004280d8012007001e0484260702c1080c840e0b55143da01040c014541100b0340e51100c188907405845083c12035510502694640c0000d10038180c42c0d40040e6074a00c294019000d0000b2000c2041000c11916840229010b01c030340900791134807100405800c1943c40c00ea641d0030743c0b59518070180c0c1400340140f0510244560340300100980c3c1003d10f102030100c03021482014011003000803440005030380304c0e00011121324000c103000c41c40d0341841e0100003071041c0b41c070981 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347977976 1250 347976726 347976743
    0x130e01030c0902070201080109050c0705190605010f06050d1109130b01081003080d02090d02030f011b0c02010c060c020f01020c25050303070f050109020603010303180b0c070911040e01080a 83
    0xb0075010054000c44050617010f03100d20303001e030f443c212515004240082003c0004201440048001042030002607522900c3c41c070460659a001c5c02d01c00111001079015010140314060300f00121038021060320022040c0ca00d00140201c00300010141030301c10011016402228101c03401841d5171030307903c096500d49003a40c7d16031035a034030b018100c00c05120078000540202c1050002d01c8840007540c0080c0700152016101b42010340e030b1135000c00c0c54120031901680560f51501105444450741e0480050060341514003038031a11066000a44a020f648201600c043c4c0c691841d4075001c3c2c020003401c21000b40c0c0a008540e69400701c01c00d41d841d01051307820b000b00305002990a118442100d00c0c06c40c280c0e2401006103141c130f8019a101d200104200000b01c445548400c1e4600142e507507000598000c43c000d48840030915141d042588040d031140d000810244030602c04107401c40400030b014801c4d01c101e91400034800380f0009181c1045e014030b82c800121100e8007030010400303c40100781341d00614031543d0032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347979226 1250 347977976 347977979
    0x1306020d11011a0d0f082d0a0806100918151401021203040c0905100504050a050c03060d081207050405130e03070209070e0306070f14070c03020f06130e01030c 70
    0x501e0984840c0a200280030f12480015855403405030b001006035841407002c0c4803541d441d95602c41079900b007400070100300820501e9041507409400042c03900d4602038502e02d45400034081001d490790384042c240c0c1d805803181d1001c0c07002450240030280b000d005040e84840c074203507008070310102601d001d0031104a0380081c01f900050341c2c68100210044041c058001d020801850401c0c026640c00c014030948180c8141a400682c6c0c090324410540103110005a00311103d00382418401503803000341a00d4103888c604801c000c4855044025a500031108460f407800344042c03401c00341d0581c001c9480b01c00b2075000e48414095121342000c02002100c0c01a030301e0000d0718400e0b028500884407400c0b20a156a042000140d006107050410030354032004a041c10400400d008011030f00d01101200e44c00c0c0440c1000b1008550260440d00d0910745000690707055181070403d503140200e60025120080c007920071034440b00c615030382d440261034155002e07070301010400d642c40400044002c000c1c030080d60700042c0c080e0b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347980476 1250 347979226 347979257
    0x1503060914070c051905150c13050613031e0204150312030f061511010b06090d0b06060f030901050402010e042309010e150406112d1306020d 62
    0x1600710102041c03900c003016541da108241d440b0203114801303c9a5008000190a0502d180d40c0d100780c00c00d00403401004994038107164508045006885080d9105e024000c1d00394041042d6a00702c02e85a0548106445d24078400c5084601c0c03406400050203031107c88084601c19a00019410455001700e40503c105c1d1001130850340340013054080a07210010100620303054500a80240014440725200042d0951382c13121100fa000045c0030415000492442c1c0f038a540e01824052848140000c568082c503016489001810b0845a1000100280264400180b40d5074418013a00d51070f58900b02450380e01e20300a0803140c020101143d007240402c270308442030782060a2620484480e44910b000064a00e403400c004030001c6000101030519071343d280d411021000a0038030200701c03000c2c00c14201c1d0895042c03030301c0c00209445902412181c000824013010309078200d9945020344c0340c0709010007046011910781c1c14047c907111783c2c124031070904c5524000042580c2c1c0000c3c1d46c0401a155035414140580789403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347981726 1250 347980476 347980481
    0x30f1103091c120b0f0604060804120201050c0a030e0c1203071e02100818120d05060301270f05070b030103030e01080906061c0b0c21091f09020a15030609 68
    0x2030b05030001d00c0c004503011800889a1003042e505600801d124070781c80b4400009845988260403082c0005d40010a000400601c0c0c0d50f40c0a20a200303000a00444c0350184a8143c14001d02e1012010140c655007043c19820050104001c03880c80074100c41009103201100719580c0c1d00c024406c07100c01121512081455884811031145c0e1503009110359180f00d80580b0460303c916002c1c0808120b02c0c0d400070b044580e58420814a005900c0000b015078440d58802d440d4400c44c0c1d402032030b950113030b410021100c0c200000d00c030090021165201441d410540c80e070034916101203404400030201c0c85501c8004c2062429440034504030b034882e6840201c201169001140d0701601030b540002030b40d110760082141c40c42c0030101d41c6600320144000c008082080d855038145400b05943d04e0b07020301c0b800a042d071140ca8480400b201108000382c4070000c5418000382d13250f5a07001c032100076500d00c051110510b4881c6401d4010030980e640080607404e05075101c24102d02a818640d581901203860301000040800c141e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347982976 1250 347981726 347981773
    0x50a0f050310030f080909040b0603010b030304050a0b0f130303020c0a05040b091b160b0114011409010807110607091e0b04030b0a0e07030c08070611031603030f110309 74
    0x1e100d182c81c6030b491680d8802160054800c102c441e58014051200d0035102e810015114600540039404641080030515003186c0c0d003600100d0194000308000d01c140d0311280c44150880340020341d4243d840740b40c1000c41c0d43d1400350130400301c44801103c20000034941d000510403003520b03044603520304542ea02c41c01c12045400d071000542d040092800004c016003074942d01c003200c1c000001c20300340c41e202e20411940c0c2400000e5508a4200e106100140260040060841c402c028203003480001504007090340380e9680074040c0840c0c100659900050304041c0b042c0301c00c9214401070343c2100c050b4102040e001d01406018002c59508410030484034400c1ea150b05101800c581002c68501c0c58130f0700b1520380381c00c0907000510420b202d42c2c0715101c88007078840400100d40110f0240f514406240d0401c441e03d810715803594081400c129917080354401d030741303030100071a512403101003881c1e41c5032500343c502034001c3d00341e545c201030101c0d28141d60495042d448400031849030131240306580d40140100c0c03c848141c07100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347984226 1250 347982976 347982991
    0xc06050412060f180510050a0b0603040b0601051c0c02010e0313060c020402041e090e060717180d090614130e0405010f06150210050c0334050a0f0503 66
    0x3901c0030301c0101d503040d4003081200d100e00b58045201000204910615040301d2403c44003540000303180c0300030101c03610030136401403852401400314000040003d4014000900b000c0c1c500408400130424581c002c07001c480c001d03003800b4111000000c198060340010f0212190180155013480e40c04842c204020088945607900600c40f00040340c24400f089650891540089070480d9080001007a0010410f4081e84955208044c0300303c070070b05001c040802c2d00c1206180121a0384000b040c01140e0380c100d50760100c0752898081c0380301c0344d40d20303888c04141d0340350117040d000620300034641c0011032a1750082c1030005039034103a2a000e088020380016403a09201e8028490281d0302150414011001e03189030b00f039000f5005400201703406178680482030890302c80c1c1c1d028070100e13a1b5441350f1040842e014400c3c12801c0020190420a40c0340142d01402c3e03074803004094004100054081a9800d61007054004011041001c1c07030080c03124100000d403030340d44580b240c1004603a007045480f420174440c1013180c0c4280c0f00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347985476 1250 347984226 347984249
    0x60402010f120e010f02190305060d060b040216030306140a030c060c38090a020f01080c070b0c0304060509070602030d0b37090903200a1b030c060504 66
    0x10750500860741519001200d5031075039120aa4a060305009002d8807500d203018440c0161307280300d40001641040c411441c0c4105150400d01006941e50741c480c00442180d82140d40804c1d0804210000340c028400c500c034043c04980e61205070030502d5030550004080d5090f9102e0b4130129100d010821030920010301c001448900903000501c0302904c101d08a14000d403043c1424600c110700da184030300c0120a00446000400204542d0403180f4041c15030181d000307045a006004c4120385e5801142d0030007900b4070b03007505200140b0b000c580403450000494050070707000b04094038a801c0000c2503c80c164010340e825a52603091101040840c40d001c5218011121950015441d2000c03444140001e42122410310b6806031240240058014400120782e01c42c0300300203802c404070441d001490720026000d4000b1a96985801c4490000170740000b0b18040440c01352100040002a0105c424600b0501d1000185201142e00c2d51180e4130000a079910143c0344134070441844681c9600045070103001b940703e0203403800c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347986726 1250 347985476 347985497
    0x10b09040f020d081b010b06070b150a0503100504121106190615030207030207081207141002040305030307080a0b0a170c03120903060a02090d021302090d060204051206040201 77
    0x3558100150310051003d8a00c5449210a0711460500e40080440f070750428642c480030380e0200020f1003000b1060404903061414801030703880d02c19030060010b00c8041d125071402c40c0101517035980d090240040c04000c080760210a07500780d105000d06001d40e0300f21643e20700c4444a030740030b40c0940c8010807519655001800030ba5242c440001a00c2600f1640c500f80d0740daa902c002c141d021b40714000140c05003190300c025a9444803450001c1c41d2508039805070b000c9420002140d04421020000c480c000c5070031140a0404180c0c040046080026103240d601c2041c3c0700103000030030400c010024500c40d80c5161650801555101c001f0340c1503914045201c0c1d4031100340c00701403100092509140869100300d4046841886845c00424900010030700b8141c02c1d01c0010900040c1c034642081402d07840600f106056007400054001f0540b440c2c0000d034000e03c01c40e510504042c0180980d03064840901c80240f5038501c449039810054020350160140502640030582030005040c0b0008500e40201d9040c1e5840c882c3d80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347987976 1250 347986726 347986733
    0x150315140c03060319030c02090a0501140a0f0b1e040303020c0109140307090c03090b070e0a06031b0c0203030706050106120c0503090c060c0f0304080105070206060d05070522020313020f03010b0904 87
    0x500e104106c040c060f0221050000d42c8810698501c0743c102c1c80c10016003541000383d5021013800c051402445015425414004280000218400c44481c00422511007100707a60081d44030000c00c03402540444c010400105059002402c050707422801e032948800309403035508244c00c0707000c402e01042d015440300b07004114162081e48407038484000c81c50b001404022039903803a0480c00050303403914001a001d803946202450807014900c0200894102000006510300d11502202602075049052045584e115800e645041c011200f00d80e031320000400c55036031aa4005040050310400e00c000940c50000000d00c0540600102c0c5d000d80782e49001020250700707240c00c1283d85d034020300f402072090180007a00648554200013134000f500c4200004900d13460203c800a142c50300051200344a20401280c004c0410408680d04055550a0b80d0a488035560002c4241d6410150b0b681d0030303451440041088800140e00c070500010321b10880f00c0c09800e0082070700301800e030b44c6004011544102030780f002c117000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347989226 1250 347987976 347988013
    0x10080303240a0806150409080703031b0309020f1c0803090f010b0a0e060d060209060409050a0e0a1e03020712120206090d050f071104050421080408040306150315140c030603 76
    0x85e0001400402c242099035a00100c680158204401180c1c0364408100f04180d41d40000d51a07050a1608002c024003540000e5124034007030b40c00c2ca0188030b5842d110202041001000c0b04815000f0340150794905203440c05030350304c94402c0d600044951a02601d9801403804540d29412a880110881680d450b5007017000301c40c140c004021180c20750b003040020300f0b40d03c1d064040c000800481100060600e462003145003503800b140d00400a43d04520940800240c41c031065240d803640500d403907d0482c2d00303454240c8c0342200940000c1400c1d00c0f55800d910401c100c40e0510342c02d041d02682583d880751504144150707a81d001120b00c00229809200180506004030080d06c00e281c000c0c10010030483c034a02c0418126081a101a0f480c00c0940c4100021074802d41446031550509140a42c4035142c15103403200b642c021030100610694031211108041c4401025201c099504003800b400148098448000142021a4100e0040141c2c00c001031000030350001360f9114400284c05824a050340c600280170 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347990476 1250 347989226 347989261
    0x90506120114030c10170105060a080106080a06030c030b011d07050d02071a0114091503030a0804050a020a0b0309011107120305060102031c0915051003060510080303240a0806 77
    0x2c1520a06113440c03075580d2280203001e001455600c0340350000241084288000d103058110900940c030800080010940c02045281180c005141002c00768440080340c80103482c159202405200843d0000f10602c641540828104c480d05040c0701d44141e070000e41741d0b054007011507086000c140203101c0c80d8071304009034008106061080c0f0101505a01ea40031000b80c282003a046540424508d4142d10941d08000c500c154019540000072000403000c007000a0f0750b81b20750380e40700f400c0010100101d01002010099440c100c0c0d4010040d0401c541c44070301999460300100c80d404415800c103560340c0b81d204100001c94020079081000341c0c604c40b651120980103040080c1040e411440104502c180203441e0340004664914055170205048940c1e0030104c4000d80c01d40086443c0702d00c2e040a004040301103111388007c13242d1200c4080b90541d58040b19405028090f408890725000000c1001422510343e2100202d180d02e41c83c01e0183c041041062280d09103850040038500d03444600498480c0068840080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347991726 1250 347990476 347990479
    0x1a0717010620070803070c0b12011202040f0905060907060c050a060525090e0c0307200c0d030e030105010b070b01030803060609040914070603020c1209060c150106090506120114 78
    0x3aa4002040c2e103003407800789683e200c041c40e034101199a804001c02d0803d24001480d080c04924142180300808040070403040c42280402c4c8a801070103021501e035604038070107070101220b04104a50050811036117038001210904014003402030b000c101140180301c44401c41d604480101070b400c1c03c3e9a600381c01800041c000c907580001007641140221951819060702004503a01d02c42c0d070b03620f030060800d40010b001c1c0174a000b8000500802c0031301a0b10540c503403c40c402295500014001c03d0300c034141040c41d80441c460300144100110b800740b40e003008100e803445405400801c02a070341c504603074010b401000c070000c180285034801080070910031406076410820041a2600d00070030040001d04964400c6402c8507600b40070000105a007005101410007800070f400c05624100007690956205c0516119007181c4a0010901101c580c0758513056642401d010400c4a600b445540400440e4103424440c6000207060500d0100303241c107000043d20070030255003000640300c4c0d003410118001d88103280202c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347992976 1250 347991726 347991767
    0x80d14130302120a291f152a080f1806030115030c03092406030206030a0e2b0f0512010f05040f020c0d0f1404031a07170106 55
    0x440036039200309403d0480303184140140881e61091a00c1503084882100c100e0b01c500c8050300703000c2d842c402051402c0d8070582800810900e030031190070302411070840c0e8100301e014001c43d820020780c1c150000d04030a1440054a282902114510074910104c4000700e401045203009200280c0f4075004c92001e010155400c4000720041e005d98408568150030036442000c1210303102918142041e010310442400021501d001d110302625512032001108004812052450040a444030b50700c0e0507134441c10203142c3c010051552420034084801c05001e82d5440c0e0a0240190030403802203481071003612150240041c110742100704486402e5030b80e03403011041a0180300302007103500c660180c440c0210780038100051450312046c5c24081030104644941444112580c410004074400281c00075815158032a02c4ca4070480000d500720080741c50a101e004880c0c6142e60106011007044001301c401d8080310104c1e072890030240d0f6145000c45003a10f5025041145080900050006034450040c9050130b18120088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347994226 1250 347992976 347992979
    0x411070c140a080118061a030a2303030a09110a031106090f031c02070f0f0306050705070c03030305010612110904091b090b150708040603050712060b13080d1413 71
    0x1450175507440c0011034460f58000030072913041240c80d104520013244081074003020701c070000d400300343d9620101e040a0724016101404c0c0e90305d080300103651041002103906694403810080e4000014112107042142c0c4000e0580d101213441c20000040002c0b01e800c103c010146000342030601c0b030140d0064009542007503190701060100c0d1800c00441f2030f00101c2a10011080e25409070003400c16406030450310049a902500f04105400442e001c0d00352034010600190344c4e240c5580645031840761210040a00718180000000e260305544400c1c100c5681c0c0d204c94200c151040442c8085a04001d001c0314441d00c1407001311404d06007035220211041c03040b001d11038080c0642c5083d12011000f9442070804a413241c0c0750900504010100c461421102000b990501b4500d54401c410360103140a1107040654035400100e03524031611101404a220503000c204082d22107031105150b500035090282c02150304440040d2200002a014144156950710591621012003000311240d00c03d1848040d02c8030301040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347995476 1250 347994226 347994239
    0x703090f020616060501090b0f191d07020c2709010f0e010b01270501080403170403030b0103150602030a05090d02060c010b1206090d05220605090411070c140a 70
    0x100801d05030503c040c2c0000c1d03100d150020555105812900c01c003400c0c040704404a40300c030160180340c202d084621030590741c1040030401003081160310101b0607903050345600100c01c0074014402d0103040fa590a840c4911030380d50034400b034000400700e18220204088143c0f202e0600d8181d52070307000390200f0004240302a2000402c810b0380c0302c2c00c0020115966903541c442c041c1d81c01102e070f50203003c0546040c2d4544d00400c580d015140c4428803030b440c10300c08a040060201403142c0300301704401600042050207230509050040003885001030780342c08a032038994240c114408000d0340ea001c54681e64000d40c42c1441d01003007241c41340c001c2c08000350000700804082d001646d0b0170300604040342010000003081001d500c100305421488550741011a0402801c1c00700f011400b081001c200d0496003892540c4545068001c0d1007030404a00001940102e047c0c0420740b25402001080e007000d08a07001d10412822071040025849015030040c81c0001c0e8480030808503214140c00030319090700804181125a0356070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347996726 1250 347995476 347995489
    0x30f0a110d030209100309150c1241180f0111030921090603070c14010e060c0a0801090510030206040312090f030b07030e0309040905060a1109090703090f02 69
    0x81d41d038400700c0e0700800c194240f420900105803d280e441d150a004118080e100d10a40351003a280780708001341c0351541040781502494501c4020714003124200500042d03400361030196268280e0340c19a1b000312900c91a030007021890055154960710714a5143c2d43c560010540c0611010107035000e113400303404489034100b0820b00c40e01c44441d2200b8060384e501c0c80e0492005082c071078004901445490042c0c4a5142000f900c42680e072121000c0c4d5045913a0b071229182541c1c0c010101d18010140c0004182a050903181074210a034040503201c03c03030f80c0548a81110140d103010707100c1c0382000a040000108820307046a0040da0304001041c100800c0a500d90300824200d074480d400546410414090480a85601c50f6011006005011400d4001c03802c6039144242414003816079410940ca40000151010040c0125110190b00800030800c0302050300d050764035044200c420384011850a001820380036650412510f403180001c040c55056940d10800350000d00000310140c1c1c1e030742000302c80000184c5800707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347997976 1250 347996726 347996743
    0xf03031308060a0c1d0a0f1401020706020c0f01032007080a08011d0a021b03040807051207060c02220606090302040b010e01020c01051615150611030f0a11 68
    0x444500000a04001503985004009860043c0c00c51421303203000f80780b5500110800c5441081a5448540d807107100018541c40001d40000402100903040007400c285040c40b01c1c86007941c00e800740c41c40075a032140709907100c1000e40805500030440c0c2d02c0c42c0016600c07030b0f44881c02140d4400070b070b1035030740180b40c4a6a040c2c3e080035030708a0f00345a00083d0340a0194000c4101c500418013094142c03021403070724101016060014245101e4141c01159150700314180703010141c0751492010460b5192603841c10080d070741c1c650720b216003402200c0c00038440107071210204445068584a440d205100c0340e4541c2400201c0b0510002c804858242150718a070180c1c1c94025000100ba655407008400c03030841c01007001b240e1001400301c0c14403441a5000e10581d80110781c50746040001d003003860315401c0940840c40d550581e010000d003900c0c0c80903003480003100950300143d403902130380e08a1454940c442e001aa81200302d0049480035502c11301c03007000050a004000c160446032850901d0503003204610305881c0c00d680 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347999226 1250 347997976 347997997
    0x91502071109090604050307110402070f0c210b04080c030c0304120b071115151f090b121f080a14010c030b130b120d0809060106080919020f0303 64
    0x3076508903285401d54005800186034806401c0600b0241d840c19a2403080000c01001c2e4003440d40314902035900d03641541d28054100a407030702401040d151501c04000c8500a07215142d03103072a0800d62212140880b220702540c000070703824850f1501d8441a04540000da07901038503220400141001e01c41c244064001450140d00f001c4a0b01c0c81440e080c8003d050003849001000440f51420b4000c100028400301c04001c040401140c6807107031003c50100810601280e90008884100031110325000c00840450008941d108000b01d51615100002032156820001c041c2c145800030a07042202900504c0100c1d81030000d4040403980e0749815402c20352482020b441000c41ca44402c0c00c504828014400d070315032145010040c0c003540c200011007800c03085c0d01c000141c566607491280d507522040c12403800c40d00c15030100c807261103200c1c400600c2100121164a0f0902440c4c00016a181c0144119401044100c0183c40c42c01c25040103002000304100c13003030380d02c044a40300c95015610244000c0c90304004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348000476 1250 347999226 347999243
    0x40e0a02061b0c01050a0c0210020f070611060702010b10080709050909100f05010609030b0c0f2a0a0209191401060e19060e191a0705010f060303080a09150207 70
    0x5241d60442c24244500d030300fa814403600300700c8010b04039481050043d01d07a1341110918002c50099030f04134035040c0c3c40c0c0c040c4206803250800126026800000d02c903000003203c812501e940d0394014040b42614a607802194000600b616400c01e0b6a005107481644851a840e207070b092280d40d400081c5000c071090300c00b081d00b034110641d0a019890305006190107201420028003295240c40001400411103101c081c04019564000c11004e4a5a400300e42013000c100300782c181c031024240e1010a03250261420b2400580104041008500c008030711102140c1c1c0041c0907401540d50419078003020710083c1004a04541d40f0704036014508451910240a8105992180c01020b805010f010381c40c2e202c02403c81c5030344841d0382c04203c01d5078090451040306c0c070103540c01201c80f4441407000e41c002d02140c00c50301c41002020703d024503942904002c0c0075054041c0b802070040401a040210032282c1d40e00014000409900000d686c0261503004030070490b100c2d09004039059203001050003240c00c9160219110307007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348001726 1250 348000476 348000517
    0x9111201180219080402040b0915010509030c03010609050601081021052109011706090601112b09090b0d1b050a0e0f071b200306101e0302010e040e0a0206 68
    0x1d0a2003400307800300044d150a127250500c20b030741c01d102c00840d80041d4100480000c1010f880e460078040803042075400f800134400c80381c840c580303c0040c00d421101c450000380c00b41c0000d080c2d54030710004207084583c08071040c9070140344141c3c0c031012282d41c948140c1d814806d0380d000304110b141012095114514100c8020f0303d94034440001480d0f04010030000c0c2202c103508090140ca940e80341c01603034209109081c0340404442c0c0802640c1400204995a084043c094140d59041c1c405000c044044403003070781d20150f1250f2a50b1b0002c045848030540580c000b030010100d54005159a0442e41c43c1d000e0400003591055542c90008035500720503004104208861030501c042e502c1024403080d0843c03850b00b081c00c03089501d041e10742c00003c0060070140c41e102140e170703803030303011499a4444800d8110041d0170341d0b50760314060359a003145064078466088500e203c2081e41101c848110351020569605035587e0000000354401c01018101c44840380c8040d0103070f00300d64030040ea24900204403100020140071102d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348002976 1250 348001726 348001729
    0x6060a05030102040f1503061e0501023c031b030d150303022112070f090602010b010e04050c160302070314071802030406060801110409111201180219080402 69
    0x8164801402070b8010b01090003800e010303480300e90a031800104942c0742d286e10500110041d0515610099070400d010600f4440142e00c01d001c00300f6140b0a8088400030700700e051540b60041e1200110481c54940511404000301c04540400900b0b02e1450480f4104003404280c245501c08a0380c00c0440369000280000b1011124051360802d43d400c03941c0c00413000e10f1510069107030a0342c0400c0602031940c00401088440c41402910100f8104124108061800d1035028103103400005108000c00c00b80000000d0461050040942407241030756145c0d1015400000d2001402028008007403480c1c0070301502030310707000c030101e01103640d402a03000340003251950401622003261480082d03030b1034008a00a00c6440d07030000c5410408a00b0303201c010f0340d81c0d0381c0341040d0b0010040b581109030340794241040c130302018091102a1054440120301007100000c80103280c5154401c01032480d40c210350000c010040c44440095244045951170805480c000c00b02e15841d508000840307121010842c88418131055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348004226 1250 348002976 348002989
    0x30c19170907031112031b10060f030b06041b2f1c0906051902150708060a0603020408060601030b01210507030507030b0d080c1603140c0d201507050606 67
    0x1148050b1002c540303c1035003c5c0b41c2c1ea00e83c455101070304280c007580c48410311400c004120000e01c03d084140200819a1034a245c80074600b603503c82501c12200010100d50b80b840c1c2482401121150f5100340c01e020a2590b0080e00c1c1e03013400a1880c924140c401c0d40c504c072654482c10714910005160000340c40c201600c0c0c120220101200705002c81046800c032001c0c40354036003040484000452480c03000c07403419100c042c200e103010000f04000302040700800c1400550740c2c1010026000307040807540c2005103500e951b0200c0c200c1c080c5103c3e02689501034008904154026440200d0301103040c540380c8440c081c2d080c003140541c1c0c07010002c6942d085c0e86108000c00f444e89440742c1c40c1c120800e850240100c2420340c000a4181d034a200001e0019880044c04211804082200f8010135240201e030b07006881e5281451303440107140b441814010300a040240b4424074000540450032540700b20b08040100c6108000c20015011900c450341001c414100d41011944007005001100c0c407c0d80141401e00e0101c091218 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348005476 1250 348004226 348004253
    0x30506070921081b100b011103030402040b2b150c0c030315080a0c05041401030c0902070201022107060b0a060f0315150513050105030c1917090703 65
    0x10015218414015000300c60029001c03500e5032602c0c2da0182903903043c07091592065042080c41c10000400000ca80e003400b041c4c40744503000c1c910007041030307020840054401d50301c0850301d0001e41d00200001070051070701da40320002011015001c0c07400000445448074840407084e010f20100591030040fa03040082c24401d0184202c0d2056040c881882340f42c0c07000e05030001680000341459214401da00b00c1d4114141c030840244015130888582c3c00c60b41c20300b040c40c0c1c1500e005d5039000e203080404602444041030720090403254841440c070079442c54850648000d40101500f00c1c11801079a40c40103210461400d012403a1119440700f07903640c12607240030001c44840e003100502400416408204458001ca049404803040c1c1c200800d41d01c040304002c48044100d50418480500310601010300c1c0c643c0321002d40640b9007403815080003180c0b903030010b55007400b04540b00510328800300030b403140010f089a4049403078031050420000c8400880b1960920040480b50760546502000c0100144000d01c0c10000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348006726 1250 348005476 348005491
    0x12120f0304170a09121a10030606090506030303060d030314041a09150606220305031c02030c090d020609090c031512030414011e020318041404060b04090b10030506 72
    0x245010254031000c1c00812045c0b0035203004605a0702d03d10140020140903006900c10f18410a030360345481a40d45041c800309000a0310020b251200100711249188078107405030200400850450b80d1304002c11285504c0924202d08150329001c40e000340c240c00090b118001c0c1d2140d0080c80c0d0034a42c0b44008007080c2c400038280000c503032182c40120030752050400311079003204003564080c1c0c1c0c0d940400541c0b05d0400c0018141c4a41c1d0b80d0f01d00000080c00000b0014041d5034880b00c03011000c2c101c20b180e03148140e000070b89540d00e6a0300c0410415040d494034402d6004503601c0a040f640c10149248000f0b920000b04460030f450900001080000a45045512640f900710468403500340100300c2c840940d40340910700900c100302000d0034281006a0042c0745a2480101c010140c40b10008071101c000c0d12138000007035100c8500210030315001586040d015800c0d0305000703806c000303240d0b41d0707540c0350351303000e44199103400307401664070900d06010605005071684526a85610100b40070700d5460031a152000082004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348007976 1250 348006726 348006773
    0xe09040c05011b02030f0303042604062607020c040606051204080c010615091508010e07030507050d15050906041512020f0406080618030a0e12120f0304 67
    0x91034280568003510000c0c601503401c54207801c00f40341018000b0030040c0d0705111b6110002c54411001000314480c510030031204004c2d402003c088429801c0c3c04111b402694002d00c820300c1854410040e20b4102c071a070418116640500e06031804500105444020040c4c20203602000700e8107007401810000c114a02d032161609060603840c01c81343c0c2000d08000c144080006d120b000f0a4400d400c950702070110740007019008040c451029007235540382d12810308452103244400102c640100600c0e4105c0b5202c000641c010703500d00e030045008000040061003486000d2000d0301c0d0310388070740c4100008000c0307200b003810040303081c03008000305610008d001510981c2068885181c1000b1070104408664a510f10310182010034030000705200048041660410b150040c001105503000070700500520351084040008501010115228407500d1007d50100d190003910603160309241c4800405010804140e0b480c0c92552070410920344d0184400321810b000120078042442103581080001407a900020b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348009226 1250 348007976 348007981
    0x150b1f021e0307140a02030601180f020a12020d0e100905100213060f030f020d02040504050604052203050d0f02120108030c0604110f040501091a0a1d0c0403140c010e09 74
    0xc259503032248920040c420103003020313960a0740408003c6030000503401403c3e02c80660b11140d4221085019640303075a680e03130a0241c69040322542d4803c540340740c0d01540c0c031141c0c1300d020000184080e5001c007801a01407692540000c0321140107200024100300c2411010400701411f0805515080000300c000c0302c1c1a2041000145417403071441d400003180c7c12400c040d080401e902c5030503001032003000e1101580da40000351101c17030303944c0340d90040064680071034003000141c90310307000e01c0f084a800f00e4902409658103095202c240700c0395140c144646201c0d1600e249003981e40c0048401792000320201c0a80d1540128440411820110440c7d01600840005604102100749a0780c3d0b9a500604040d100e0400250282c00644940c103031810006000751040c4440e5a49843c0c54000308242094680a2070700300301050074902e046104013003142e13041c0c401000c4003151003014072101c140140003c04c500b0340402001001514802c440c4400000700b0b409011450340060024100d910014509840754021108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348010476 1250 348009226 348009283
    0x18171005010602010f27120207080f010209090c0319110c03130f06020607050f0a03020c2e0207051f150e0609100303050a0c03030209060d061d040503030103150b1f02 73
    0x180b070504e294101f81c0c0410300e0101001c4c240d08041c880d41281801380100e03002054154015001000b0014003600d08000603511f030042503c0b035010503106a0314440c40c42c604000f8481380b40e08000c115400bc84d6156141ca120f4032059860340d0f105150325007030144048010401d04010090b41001440031b40040c01061a04201c02482c5110704038101001a00c0490540d0b0440e1095054904855458003212405904100210706c0304201707844600512950705c428030300d104068000c1d1008550b00000810342c0c0012640548000d02c0301a1024807079954903801401c441d200301900340d008101d004500c00a03424840180b0000610003004d115000c410001c04100103a4081d003145e0700e04a4074034103405840340c00d1404030040d118403c2007030345c0804085014681d0080c5a400401150b00d2130b0746600d209000c2d0341002840b0042103a01078802c1d0002d000400c00f20703109001c0d5807200d5540500003e030200300100000c0d581c4031182c0d0064685441b080e401e442c2550100000304092204480c1e06250100198 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348011726 1250 348010476 348010541
    0xe090307020607030302071b180e010c120e150408121b04050d020d0c0f1e03030e100c0507030c06020c0a051e0301020712030203041218171005010602010f 68
    0x100002d040641c001207038000d10011035410405230740c9020103060311541d2114107200c0c00f002150400c4010b07103408503080b0300540503c140c00c400315554035845410b84c40001c00c100100754202c410001c50040b0617200344ca005900016a200310702c6080b0058407518204100001040c006140e0400d4024510108045010300002d41e030460b213044400404080072803010501c10303529020014a00b0b054001c0c007060481701e01c488034082c0e44000c8008a40c88821415010b5000c0c8188130183c00308034051030020450400149040b007100b054280780d02241555a102494030030240e000740c400c0b10741204240310321607042c403000940c00021500c054440341403200158882c1c2c2c0081e9040144401c4103107245041d2000e40586802581119960b2070341c0d0b040d076101401a6004440c112840c44410443c855240c0c003d40d0078500c10b0300e4040189031814140305006600100e030715032900d1148100421504900f60307d0041c6806441907a002046040c1d0a00644050710300c00115001c1240d400e050003413044d542d42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348012976 1250 348011726 348011737
    0x1204062001090804170a140102180901050901030b0711030409020a0306092009180a06050307050306070f08060402160f020418032c09040f021e1c0303021903060e0903070206 76
    0x440a80c01074145005c1900d4206461001008030800004160342c1480c194091314408100c8801c407000308004008004e40070720309004545d8400c5158006002080c51190820b5010445041031f000c00e545616403c1e2a54005a000441007600080c0b08580c041d8140074550040503410005d000c003030040c51182d80800c00400504c80c3d46c900110f0441030982d00c1a40c842c910000d03600070701c2d484c1e003080221040a41101d02606000e4842c1420020b00f41c1000a503103841941c080d41d40358460320341c2e907074210780002001d412554000e4013440469400d045a04c2960590343c4241140b0022a01e02e02c1403105603031032907060348800c0e0401807003240441e80005602c440c5080b01c4131240300028801c10050020741d480c000c1d00f034000706042e081000b0070104108100000e03000300e03546104880312003000741515040744040b50300b02e00c819100d01c2c40d6060410003103061a109003800360410095541d590740303189003452440000707511034004000030003822092a070411103203401b40d4540111900031030f1162113030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348014226 1250 348012976 348012989
    0x521011d030d051017070e09060906150109180c02010c0302040f1412010903120f061512060e090304030c0509040206070f051f0902010807030c0f0c051204062001090804 74
    0x3104001443da0072020080c20180c81e51a0103001102020f8028a1b9500300d98019582c6000c09400441c001a40c0003a100740300b490302d0001041d140e500e40d02d0009802165011550503ca0002c80c042070381c1d1400d01c2100da501c0f00c130580000340070005000c02802d440f464144203042c54410081031201c8c4440300c0000056504c0a807210003e80140c0d80402c60710105850580c00765480c1c40c00c508100340c0c1c01110b4405042030f49009005420b114654001181e00905c200001c9924068248404074090400b5201d66585a48001910380c2d6410390440d848a040f6041c0c003060300001000e00400c45040800c8028101c251030904480c80e190380800c10501c601240507000042c130366122820044100701000d01e81076403036590805c5502c5640703140f02620018404a000c00c1c2414000307800740c2c0c8280305800740340d0516980c90303000c0381822400b0354404000e40f030262040d02a002449000e440600020001002e4a90702d4060804404122100d104400602040d0603418aa00390001c901800c0c15642550b41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348015476 1250 348014226 348014231
    0x3020c1531021011070f050901031106160b190203040c05040209030a1403040e0a02090a05040203060303070f0f0c08030a090306021b010906050603101e0906060521011d030d 76
    0x2007888161900c51012100a601554801c12250101c1d0b000000040c44d50501040703903501601d491300981805168020a5000758103030004001140300003652007100c0502400c11032422112420080c0344112000d4152620407418041c00464240c02102900741c1003482e03011410f505207955038488242c407510840f03120b5500494104041da4050103944100fa6002c04040078804044400c16243d40080c402c00c46a482c0305400150b60b01c4690080b5a500328006211492050821003007200039000503041540511081c00407800140c280f02d042c0d203030036000780040d080000c104d241290500086401c213100c10b0f00f0038803086981540000950068a50003900961595600000d0049001184081c40705c5036090504071800d20072181d10150041405a0a072086040110f072994107a4400c0341680d1514004448031641c0b000e960341c040d4504c42e01c94000481c10f140d81d2000119200d240d040e164118050200c001038440009208007003001002c50407150f007170080d056a903501d0340916040a0380d280d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348016726 1250 348015476 348015541
    0x1060225182f07120215010f0603050106030911041104090e060108190b0f040303150b0702030c0102030f121512100c020606060d050702010e01050c07050c09100302240a03020c15 78
    0xa00030702400b82481e054801c46c50403583e403424402000450b522560011900c0c010000c60384c14030a00405a105400c21400c03c02d100030241404020101001241c61283c0244004210088140103002080440d50b0040100e94107183c011400c04820004d03100e200c0d0000c0c0d0b03414000900c6403403003c4d444004800100743c160341da420140d0160666950302080f040705048089045001c07180502a40c0740281c080314207448141005982d24420702c40c48240e11030082c1300a01580022040069103c86450f03034203035610180c5030100f648503c040032020500c6e0000c040c0507030f05c0750f05407280d0803603d10703a84010800c6082c260081116031140e500c00004803500c602c0090b560900035049000940001e00c000c10891518001d60000354222020458841c041d01c020fa8045180400c0410b0059410a0b01154440d03d550300700301c500c85007003210442040d07110040034110305070803001c1c06400c119a02d026030f462480340c900341c1c208503403d00c0e0794080203404018401da41c108000b400121072805c03002c1c2c00110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348017976 1250 348016726 348016763
    0x10909201b150115140906070204090b2701050408030c0304030c0209070206071101020306030709150b030103061506021c030c03111303061401060225182f07 69
    0x803001d0940080d4512030385041a64003100700030801e0407034001429050101e41809001c441400c801d52200d4440881407140b02250701e000002003a207148010800035006011f60345001041d001241e1a00054210800c40041e4031102e0089410050b8108020016807030a0340d02c152030f6000c007500702050080003000043c2018021003c001d80550001d00342d000501d00220002d41d41c03c0e00311140303000901c0e0451043d440d41014001e8034000d80c0000e01404030a410400e100b40201640c4092926413422420002101d03002c940066000c0c6014000110302c001181a800711a14807581c0040c0443d40051387d5002d01c020340b0f50400358000018600401c101d08604002c60262401005404d010700c800a000b00d054030500c268a03040324429041800041003d45201e064000c00744200310168208403120080440741140400034039143c10411031240e070f103455201c0a9000215014980c5540d1040c001508856551183c0c40e0a280508005041d0280d051644407501540380e0090141444201d5039449 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348019226 1250 348017976 348018007
    0x30207060819140702120405030a02060901140a0e0315042a090f0b0415030507030b040804150c0302100b0604120809060a020706030c020c0618150409060501090920 72
    0x14101002c00600006034443c0440b0010742e010b03100c003c003501c182c8100018039a0058195402c4520007000350900c3c00580c1c0922807158090008581008014503a4194034180754001c0c020006171580c2d1940030481c0c0c0c406051805441102d84814004c0314020000002c1b000e003040842407a1010b030741c2901c1031000c15807482c10000e60b007103a080c0303601303000b0305c041805125448a40c90780800c44080c80081c0d100c0000d40f841c031341127010180941c0c00909090010170012400340b604240715071001444c00b50f8a41c3c5401d1502026017401d000580a440c10350241541080643d5a01c07020040800c0205280780c00524540300303d128034190f6002804140050046180c103031103c03000050401c551b40d5030504030080d1550344502030700c1c0100745480b140d40d80844c070008980b250094003900c00e52400707040180d140710118200d01107a034800c0c00b0400c0041c0c158000c4000c1c00c010111820701041d04c5042000141016050340c0224154a01d08401a10078000d00f0801407106540007186a039170320003000c0300081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348020476 1250 348019226 348019261
    0x114070e0a05040509012412030507030203040806010f0e150604060f030603080d050115020307020303030a0b042d1a100c0804030803040b0709140307053f190302070608 74
    0x902c2440c100405c60446419000341c0701d51007a803459840310040070316004000301c0940c05850340036104042040006405480200002ca020b40112414965961483c07407400c4000d810509250b04440c90030032803203004107001078000680303a102c0ca43d50b1a049011500c0c0e806148140f1040203105007003403605038040d6200501842c1c10120b1140d80d02504d140c0e840141c01c003072041001c0741140d0400301058900c04802d030f600d1a903009000e1899600c641010101514150032803540c80350f501c043c02140d228013624140c1340103000d8400c1181e414180e00c989000c50b004103c0318403051400341c14139000c0c0e83e6000c6c9019405842c606145d0751040540c00d184419028540000300542000004c0c03105001c03105451610980d40750b5071340210b554a440100e9600d440d0b84140c1a05540b002c00d060200f4540b001c0500b80c0c0e89030800c000b401200c0c820000000744075003a0044544298a9151412046402d0000940c0b040c841d4040d04441c01840c1d8000b5a42d200f507101e0201040300c01d5000c5400700800400040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348021582 1106 348020476 348020479
    0x3010b07020a1502011a011412090114040804050411041d0414010c050910050a0206010e0c16030e01030b010918050c121608090114070e0a05 62
    0x10950000482242c0c07000350418041514510907003a0b1140903c80da0000c1080e60115841c59074a1041e04052810800c020744800d0400c5584030840303841b1254140440d480740da80d010114010040300e4a1044000141800d0005014610024205a41301203404100442c188400c5600c1071040340700705010340b80700c1030710241d1000c0f594407210380c404c0c056941411800c0c4041045421100e000c00320101085020a46001d581007049120700051643c2c00d10502e80507003200c01a42d00c0c907051040c1d080309202040001c1f0504085030603070360140380700c004607440701c41d481c0b0f0003414254610700a140005d151843c03040d40c2d1343c03103000c0c95800c690410744c0d5410303004a66444940644402801c0c540314020820406040460b01c625a80c42640040f41011181c500c981d0000d040f54400343c40d0003a560304104615140654002005401081508005170245041c2000c5001f8994a41c0490b = true := by decide +kernel

theorem cover : BRFrame.Cov 347841726 348021582 := by
  have h0 := BRFrame.cov_init 347841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 347841726 ≤ n) (h2 : n < 348021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
