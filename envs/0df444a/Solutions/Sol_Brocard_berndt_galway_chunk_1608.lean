-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1608
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:50:31.17473+00:00
-- url     : https://prove2.me/submissions/eb12d61a-5c14-4d98-8f11-13f508be01e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289028776 ≤ n < 289208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289030026 1250 289028776 289028807
    0x90402070f0803161101021e0a0507150c1209021e0d050105161103070b01030b0a020702040e070501020c010305010e010b090d1707030f020d09090b03030903030408102a 74
    0x4840460700003481000146110f400c40862201c4100f8040300010002c1c0003000c00c0a00c5c40e44104445552904568211030310344012642240d80ca0311010300443e601c0c480d1000c090241d0004003110040e41d243c507085400c50803c290340d820800348a24a00038101c4a6079000294454400304003c1c8040d000006030244094000740307001041803890303d605081d510103e803024103100e10309046440c400d81100d906c2e503441c81c03100021410000640c1d98100840e0040c000178240c0d100d960000780d44001d8940407110283d0340504144401445001c0d0780e40e845245000d01c6015000c0c06400380d400c0d511a10843d412100300d406440d4890b403801070210105d82c4201c61040d00203e4041036480400c1c41c07000b840d4105251300850654683c150f06009103007480c00c92102003103400402d030b400d1866502036441c41c1600c0481750005080942030002900d10f20589131115054000850000f56805c0301154017903091480e20410b01c4610882d640c00f54000d030001c0300d2284505110282803909170310461880511421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289031276 1250 289030026 289030043
    0x110a0e330409060611070308091201180c060314010509060613030506010f050406061e0201020c010f050f150a0e071b0f140f031c061d16020a02010509040207 69
    0x400e485041141200d00614114440d00040410050465200c0e600003440030780303001d19846000ca04499168200c1d8400600515400b00b00d00c041590340303400d245910080386000f00030515415120944001c0451020340300701f80710400000300e0034001e001d8094110103000c2001d126a0a01e42005203484010b007220360884424011010702180c030341c41390700245020390000c00c119850007605180c107a4868201c1d6008030300340881000b10503000162512410111600702640210040303007203009008844580441d90308240f80113110f448144d0000b4010190388bd60482141e4666400c0030010741c8440d5213540180d600e20041200d0b80c005152141c110302d803071404010a1080c070310072811150400c1d50030f270b4a02d0345040c0c11804124040c000320304540040700c05040b01600c028071242c1c40b8000c0c2245540c07203a50f00010300c4000200755102c01c3c0500b1140102440e8000d80100b491075590301105d1071345c00140940c180c1c50625000103040d580f455416500c4501d001c40450611001c3d40220b44100c55107075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289032526 1250 289031276 289031329
    0x906030a0303111317010501081504122f100e0a0206030a06050303280e010e0609010210020307020f120301140d05031c0f180506010501080c0d09060f110a0e 69
    0x30300e0440814005e1404560803121512203010039030840f40c041c0d000c404258081c07506076810805503100d880d4429003080c080f5981100404041c0c40441c13698280300071030701c804800c02080d11540b404a06180d901141200c01c01d01802e140c0350102c4010401315a016030103503e1100061508030010355001000581c0482c40759a20b10100c4d1841e0450442210007904240000c1881c2824000c00e0303598a0003842c01003a81c43e04240041c0000c0300b64502c035405440000f0701010140d000300915140c0e9181a1000c540d00e1802004c0207496851170f100e241080d001e4032070140d0515010f0030659043c4e40701800c40c0d00b05452000d040088c80c1e618042d003116075000c1808000d4810b04c450390200000040c0ca8004196650b6000c00c00044035500340c030009603000100340400114a000400702d040d55000e00b0154965110b41010444a018001c00031003c1818044245c04002046d0489401c0780719a100c24400c1e89600d1020300124003c492084000441804c1c410402d45024201c0003031181c0e9900d40e005446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289033776 1250 289032526 289032547
    0x80a0c080c0607030c390b0906091c1e030609290a060e0d050a0c0b0a17010b03071d15030103140c06070b04170301080f010501050906030a030311 64
    0xd8028034a620007642042080010081c0c06001d100040945854042c0c80a00c00385e00a1030701c0140240c641421196114030300100c8940044000c1a40b50094018905d51400d902056540c5008a5030b411040c01408800650a680500c20143e8050240c4480c80c0f0b6010000103840a034181d841c00108141c1c85c0d440000b0a44028070503440085030007a10070f06401040d50040c525420004407250091081e8807081000355032110490500d24003c440c5003040b00b01d141000351504500d1003010b071041c440c4580000c1d50303020820081281c0d00c1c5648600412030800a0f400c02e541c4400d1007000c49030101040065145440b440002075800c00d001034031060603050300042101c0316143c0000420078080000180144514881c0c440d01600060008108404401000c66180c3c042c40c0c00082c001101d141c0828100000b034010607140040025407180c4942c2c1d504034490b65425440f121401c07079403904002003030394140800c0c0c0f01e02c40c42e0013a00901c0300c0003242c0c4d4118028007200a802e14a00c8040c001001013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289035026 1250 289033776 289033793
    0x17070203070c08060f0c1815070210020f010c0207050f090a0f0204090603030207080a0201050a051803060415140105221103010303090501022a0f0111010f20030108030403080a0c 78
    0x9410520004c4c5418036000541065288000e000c111140405000303100b41e000c0160f550b0300c50103105a4228030304443c1e00108002c0c0d40106203000f5400710342410b0030b401040d4002004103000005800a02030080c182c0e8060f40c070b82c1d5883c0034071a04805e4841d00c155240c1051a441500302c07071624400601441d0400c082030403030704103401180c0041e884010400605904025210161400d007002d0041d42c20168000782807849203400b036109004000c03442103440c0c5801113403d0200340014080d01c03854a001e150615000d54054600341159203800340a100984808200f40e05850011b0145603400031422504a0406000221001c484e40c551011010b071040140165000714802e40f2450445420400060b092007401480480b0140c2d00d41f10300d8a02081d17188100c002030701c0c03c0e00e00480f09040c110040300d0120030310f401d0079120740c20015074445004241d4090640341301e509c2d840300020446200c481c02244000c0c0b01d500c1b078580c003c0c0b00a10108101c038000305004d40a600341950303003808030394640d4603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289036276 1250 289035026 289035029
    0xf050d03081e07031b02060c1209070806040c05090f0402030c0f030703020319020916020c01030f02090418060b03030702012a0b04050718060b0703030509070b130f090c17070203070c 80
    0x5e44881a07065124060100190019203074005058240740846919225000700009440903000d210086011001c042c8240400342002206440c454500784c1895000d1101600c0354500403603045000660b104805034599004990080c06000b41d404950100240342e00390842050389401030b411300000507602044916980700118640c1001c0060034010003007504401480307843e000030f500382c08400255003c1202d0300c1244090800165260724041003200078000c060340704c0d40182c50007ca04103208040c0a800c06d0892240c4018882281c1d40428591240110302000740401c054600700300400f1504e0202c4c1c0103880c000c0c0c0703610001222030346034078424140941e4203440c00e4004007400e000008807014183c0200f020030034203120143c50b04140b10014843d40310b02404165071940480e200190502440d0002d1a01c800c202d034031035000995a500e01c008510545540340e0094030005151800d84c0038502c100e8007152201c080a0046034105071168800800b54030450008101c1c040005980b00358440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289037526 1250 289036276 289036291
    0x6060807031127010b0703090b0301080303062103040b07051c1805040b0f0409031808030a031406061c0b130e1506130b03010207021008100f050d03081e 67
    0x9440040510601a0850295401001044142c0b0b1403c09142503000d125045645440341326030b0750011030400722454801a0002101140000000103000c0e10020103180142004c448500a040020065180f130101e10b029060a40d0030a0004108c140c070342a025250071401003003aa4400180700c603003d041c0c1c1030024540f4010510200c001508400303001c140380c001d0314060f03070300300000c4103440c00040b000121203001c0c0d4802c0f071b00d818466040612440300400350719240c4184025847d103174099651250800c1e0b0b40070000a18056089041c0030a104030b160107404080c1885260100049400d83d04c10005e100710b40d14181c44400d200200d4a80c41a051003d442601001400e0144001c11604203090041514040e610880030b00c09590b032030b07852080181e08103500006910b02d021020902901409401950050802010050183d00960f070703039200d64860821000f18640300c0d1900b200b510071502646030810b81c150348210029006400342500320052404114407545010080315030142c3c203c6860 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289038776 1250 289037526 289037543
    0x61f21060f05100905100306180b070905030d020303010e0c0c031603080105151801030f060f0305070f12030e06090a05060d0b090a0b2b0503040807051f020303070c0606080703 77
    0x200d11603e80d07002040103404501014001d9007410002e00c01c071124503000140050741e40e20413500013041c040c800c80318890350081d004009840c151130068102c400038030419003e800382c4241e0480c01c92010007228180c88000003140d0301c5864125940c0c20b07075000001d00c080c43d403000300710440031400491011510640300b540c540c5d00c03030340c1403009019220141c110908440482070250320703852904070f4140e0071105000c1c6000034510428a5130513000d080d00c4c1d407090b02c031180000004401e203c800700d000e40c20740d20b40e5a1180c61065581c0503008000706a106c0240c006002c14000b43c165107860002003101c21001403048080c1a160000030352540d0008c0c00d02da04241d5a60340c060740b40d082c0b680307801c0d0703000301148c0f020012000100c0200e819620b0200c4c15201b030000c1c5203e6442240c440388a121180b5030080c04690310307140c503458000d5482019014041c85400d4140e014190403192440da00142d144643c0a14207507282c7c0740e001c2e2507461305d095040720300c6612083c0100303c4080c1001050021402500c20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289040026 1250 289038776 289038781
    0x210705042313050903180411070f05010c020d14030421020f010e061e040203010609050c0a030608061303050901030e100c03060b030f01030201050a110a0311061f21060f05 75
    0x4002c2c02c0d07400015a1081d2600341000c124140c1000700c190742c2e606c200d500036a0090302000c40000e0040800d0343c008080d00c0720104401060001d1101c000c1381c400d00c14002000301080321310b41643d48148d0100000006440440c1114071060503c0245800038070900b08180250425034102c3c803e820030f580c22800607404001d070701c400141300340035004086110002400c9542042580301e43da0075905940f0b2508070070254049800c40d02c007513001c03000038200350004000034180008500c139260300c0742c0c02e4503000904000c00880d02042c00705032280550f00b03400c141c100d01381566a040e42c064002c240e003d414150703515111848160240034660b01d4091014002500c1d90761114054100ca0b166003100c42d5040c0180700300705100300d141655a0569809007001d68484420250403907190003e00764848103406031480400405420880650b507050081040d90340d690742e480640d81904201c1c0b2001c05401c2545801000003030340d602004080c3c12100324989894600a403514010744100507000d07880c86985004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289041276 1250 289040026 289040029
    0x5010903080f070e210c0607060209030f0c01080a05041a040302030a0f02030306281a040311030307020d0209070c0c08100507020a08030403140d0c170702032107050423 74
    0x1d040e0f600c01054141400c092090f44042404000505024502a01c6902140303c0d0080d00700a046609200100155600e2489140c03070b10180d04803090b800e000f0b00c40c1c0802c0000e065000b20385507840170410b030b44d100001c1da07544074201c0c080c2c03101900039600007000159184480001c04c21261040c0e020f81c0040d40e8542c0d00380c600400c10070300c1a504000b19001401442610ba41e0101c8030105800c2c980306114039119000c0c0b902008141035030060800511041e01c8040000303c071005042188e020300005034815414005164803441b0741e00000358418403e8aa14005160900d18103400c1b02039464511422885950f50b40c8845140341c00c00390300d0303911201c030076202c00c03078640102c1d03a0015080c40a0019008555140b0750740c0d005c05000242400018011040050304810a4a6070b80308296404c0c4009010310101801c24580203410002d4031000c080051980390000040f12818180e8021400e0040003a0030030b03c070502d402a1545042003000c0100144402049507115042d80c030b500000302100344180c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289042526 1250 289041276 289041301
    0xa08071128080d051b0c1c0b010504051909140a05060402030c0d02010207090216020a150906050f0a12020f030907060e10090501030504020307030212030d051522090501090308 77
    0x60100102e9807200c440b443d50994000b00380c50580204840d824060320b19580c54904020741341c54500d801c00085901c020700540240e110340d03d428060388190b801c2c2d98071601030005403a822240301c075014024040d5042440c08541c0300040030b078024070001025031848906181803266114003500c0303d901240500c82580307018000c0144208040712b050360070f8513207680040e40b0303a60103115640d4090790100d514078422901419000b200342d402004260000e0300c0350b02c2e00b1140c0c50050b14440000e0000c0388040782041c003d60880c0c070344c50404d2080c0b9007400c42c201021587d58441e0508060025000c3c4007400d60b1000c504003450040c240c0c4009401500d04001c00103040c0400d42d03a0852040100081d40b010040c0c1003180382d000e45800386404160750740c1e0340c000309140580d164002500f1464401030b40002c0480400545140780e02400c0510581d207070807100a0384405a0003145511001b008013540b00224290158400c1e03001d45c10011489031300d940c581c9802c507108800b00b0b5003c01c0041c010000143c0b00c0340c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289043776 1250 289042526 289042529
    0x50106091406090906220506040803040b15031002070303150b09100302030f01033009090f200a12060b040501080718050f131a030d110a08071128 64
    0x1038400601c94a4074400039680c801780540400595500710504a84030302c608158940815080822148103013000d00d003026450b8421242501c3d00f0000c0404981c0c0445d403064a03e1181000400400d241c08102496400a50240703404030b00b0306940d07207940b542100c0303c05012001010029403140e2550308580500404103140c1d410703101014410000c000e0286001c2c80d0160640342c100c0c0e84060140328040c1e510f0b001d400c0c0420740405005076030800f80aa660310900c8902640c188000522490604482500079a2003816a91075001d141011000040b40702d20f0103400d0050643c509480c0d641050b4005100303c84e9540c00401003401300203070520180d6003201003282c0140d918039091446c8040030020341c00d078940c140126442030075002c0031001655a2a12049400c0a0340b0608206d0107243c000d00d001412690380e000f80c00b0380985440c41d142c0a0152041c200c1d03c0c4003090181881d210301e965201001e44c0181000c40b07070741e4140e04800c1c000d03464103152032613000d04946003503010441640e00240401c175035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289045026 1250 289043776 289043779
    0x709020d05010b040f150c0602070b010515040e041202120c010e010b010c05060a050406020c0d020105060307090606081605040306050f0601120501081e15130b07020c0a03080a0c050106091406 84
    0xc01080011603044000d510840e1b10101505c40c480a0100e0111010b000d40b240280c072844c00410f0040600600305016030403184d04560022010fa60300e480641c1c68007542c03181c2c80f41003420310000b5020401c50300303c0b00c80c800f400d441541da44070700707024866060b60049802c190b6140e645103905070300f10100f441065440305090a02003807035a8166225035941c000102010381068441003c50f04008035501951240b01c0e840069504004036160024004c00301103400d284030344103000b00007469003418400c00b03040d9005691102c40e5a0b0780c3e01011940011140b141d1010010204000000b060003886028040c072900c0902001509112000410810102c0322440c2d041c0c1c985001001603e000280214013039522983c400c40c0030781c00740300407410302c0004000490131300158000c200d10204003a100c901c0003442a000c101440c0c6800c081243e4807140381d11180d8205803135500600100f202c45000d40640f40483ca080c40042c01c4650300e09003910095402508455260070440450911010341640d01550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289046276 1250 289045026 289045049
    0x50d080f160309020f06041203021902010c0b04030e0d0305030106021e0c040b0f130203090d02030a0806010c02032d071a0904020c12040b0a0807020604030206070315080709020d0501 80
    0x5100c2040003248050125940600d542d8440d140f0841d00d030350f01070f44140038000702201c0c0c485985040f400d0011103054011401405a895403182c0302340b500008040594040c2d454200302e94240c2c0c0c4081e03440c28050710580038842c81c0c0c01c008481e540c0e1400d00308a0180700780c0e100c646a5241090292401201000c410140e6040070141428a140051958441d890459000c90b0011601c1c02040e41c582e900800690802c0904035040a120402e80080d80189009401c035403801e900d080003240c80e4040c0b07a0f81400001c144401050040d0710880001c40300b5400102560000745050080e032880e9194491603404402d194006150305c00350a00c1504000e142d0300c4062503000f885c50315540040c4c800e5140c07042c416507010a00d004055020050322090707109086c03103a544d458030f03114644050740000c00c1000008440740001007086201041d41c50243c1d80c160005c0c01d09845042c800c0c1c004d01500c00584020b0003154100044030b51041001c0c80040000e50b4005070780b01c6c110f202020585d076050b040074000c0c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289047526 1250 289046276 289046281
    0x10030b0f0402010206150105041d010f050603010b042c07030905060606040e060d05010912051e0405061b03092806180603020702040209130212072f070b0304050d080f 73
    0xd03004200c85e548500b40c0015a8400101c090060b070300e5010315000310461156003404612190042400d00d41030741c40c42d038180d001e840d43c0c810422144d44404d006005e9140801c1c00700300b00807001802c0a0f4066009490f074000e40c0358001070340443d007000031141000041d03150000752042c410184261501311005a0b00b8910341380c00c02540350100b85000d80054000c0007002d00344403c0c4407080d88411041c5501070307222103c000042c0c00042440d04031141d44068602d400100c581c00c0c1e0b03e91421201180c0c0060700c9142800812007008080200c0407081003685d01003000711030203075030740d4400b81c9900b20f0507a008910552520385481611180640000e17082c40032885056111031003840c148411140c00340740241e0b445002e440403a019000300c82d00701e0342104980c80075000101c0d554028280303588881190107243d58500d6421101039070381d109010602d5240b03810764026002901d9919003c4901e00048812050703403450131080340d600841e01a941500080b0800d8511940700312603542028151081200301e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289048776 1250 289047526 289047529
    0xb07021902120a0c03031101151404091a190e0a020108040209090a1e0203010b31020f03040303090c06031a120f07080d1412040b061810030b0f0402 65
    0x31502840041e119401400e800b4802c49000c020906960780d1119060715515901d10b405012a41c0206d181010781d400c06e1101000344004101c1d07202115000c0074240100c82100f41800002c0489a90643e8055200c0360790f00c000c005c425940702e0061040d490106510110300315501c5c122503040c5203d6085030030003480306000d0303030b40100669045601111184159120b003c0042d1420100503401800100c2c0821200c040b6111203032003152850095009000c2da9880808010084150303103100800c905191a1121903989024002d01d159518a8001464030034824500e8402d5081103400301e00107034948894200f001001c640c4000280010704090140d661500b08010101c1c225408840c05000924101046004100004407403201c10070152207a6a4940401e151142d100c010820081000c8681e400c071205641d02c00c41e081d10b040b04070003115589540c3e481100d542000fa20341507010b100d00f800807181180d48010f003800748460030200446a4070318070f82802500c0d070003090340041c1c8031720340700b0003025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289050026 1250 289048776 289048813
    0xb01080603120f1314100f02100f0b030a1203060803070c1802071202060702010c0207060504090b03030405100509090a060303170402190303030917090607060b03010f0207050a0b0702 80
    0x1550844142c00341c840004429062140c000d6044507010791141000004481d84214800603000030b0941c0c103010324404444007903628603280d42001005034800304441041800d141d0007061070341c0f4000c41c0454255001d01c0080c0c5009660007090310540b459a00444590303401d440740c2c000400000020314101003036a10391a241e5103052148030044e4040d400e00d800481d03002d82c101e070000f40e407241d901031004490140003940c404013280d881000d90320708070010400c240001a01011204e484c2e998600c0d00b8203008007400949203010f209505444180300106496490380d00c0030300c201509540f059120307603183d8108091844082e1441c08118139240040c00800d501c07241c2d07858800c560800741d400039200d03403012504490a480c1480e81c091b500480220400d0f515422290180e030060310f448880c2c8440443c02000c5204003040e80b540450100041000a4215001110030600c02400042d80d040741040060980e07010410071515a0807401c081006c1200c20501180c222841e44004c1a941d003030003c90110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289051276 1250 289050026 289050043
    0x60e070507030905040e01050703150f0308162103061d0f060d06020a0e03010b0301050f07140405060a050a02011a060d1505060d090c08210a05130f0503010b01080603 73
    0x4100001984a007418043c0c2c60034001003201800c10400621540b28680c02000140c0d03540c030003e81000742e000059201c090b90740f41a0b800b01c1c0055100305107186c5d503d12044c1d1103c0b011480030b503011581c03c1c000c41c42020504003811011000c1f815511581e14000382110410740080340b010080c1d1142d14950b20f0244000b680c011040ca0400751551608000100e00041e07a4200610140c0001405a030042d80400e40e04144801640203201e145416406c160070b0302c400321484a440060360000403596841130141e1440c20b020071480324542625080032400030703070203c0c0060000c1140040e0303c20050790b0921540d10445009104042603030380d00340005455108484031490015200c0d4150524140d20711400c03802440000c080582d1340300101842d42c00307445401400d907842d1380000380001e07013082c00bc035129a01d4069920492625800c041503108282c100d071030114100b01c1c00340170080180034600405000340180d043e00f5880b4910b0301007017500751440040d40d9810003540e402808015200029104c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289052526 1250 289051276 289051291
    0x703020a081c050a051e1b060615030c1308071802120105060c0705180f01080318060d0b090403020a2102030403060b011710080c060705191401020a05041503060e 71
    0x1940d640d100c2d14204c17928000c0f5159003d0b8880e03401c0c03070f807002c50540c600241401c071205070b1407c080341042c1908546070305045482541140d4011220031005ca040802581d0100f1160105070815051810702e03c102a0f182c0c2184009501c500400c0c00140d1449040311811025050190f181c600c900c210034181440621407503000d804003096103031100d50309124000203094013900010351412101424010208143c407007450f4003203658000710b9200320100c01c4070104508080189414421801482040e0b8000032005a1340c50b134a84801030b482c0d494281c0d0783d0240b03020398024110303108075042c8000609960f0f040c0040e04410803425150058021083d20101d03030300b103140020b2030300c10803006035030802d0b20542c0c3d0302100d0b948004011a050545801d803080d1410f1074104c8111000c15000c5c0540d5215405000e800c0fa481020b4015442a0348070b940003916128080c50321403034540717140d89400c1e600700000304d102041c0e020400780021b04588a03115800301892078140201440c003042d40b4604000a800c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289053776 1250 289052526 289052537
    0x3050111210403030e1f060f0305030406110705090a02030906070e0a0306020d0e070b0c060c0f09120129090f07092607090b090f0c030112050a08030103050703020a081c 74
    0x1c007498013030b912880909070101c0c16100f0a03120400500c02c0c07580c5903000c44012525265004c2845540780c60f060042d264028001c600c0c050401d60103941030024644031950720300c10b14034085903a440340c1721400d0041c100e9000c003507102e09040f4580c2e802e04000601c007204000084070f030308066a0b5030300165011030b40c0001006a031a04140750000260030326502c0c0441501c11007000040c00640300000389112002d10701550740a4403840952a085d10410130002340b0144107000310196440d203815540c0000c0c10030400021000b0110f001211001502030704005504071280c9251450300f0203c000c60390004521012070040d240101c4080c200750300030300514012008101d07824094484000ca00c851f2015414200d0713084541d19082d070b2029045800d440741c041c40c1640e000c903400030b00780b0003005c0c000c0b8905020982140c0c00c0050415080304d8611095516108248e01c2d00080f03070520f401580a503010f100a000c0b054110300500c040d46501e9404142654401c0c001d0304803a000f04850462200141d1508 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289055026 1250 289053776 289053781
    0xf09060409050a05010501060203220602031e0d061e0501030e06070e03070b13060905040e0a1b030b040b15151e0d1d07080d0909090206040b0a03060305011121 70
    0x1545490741c0e050008041798a0030b400854401c3e00000a004080006a84e81c12030a15004855401d20f015204038000340e40140100c40801c0140c1c00c03010b1045465062060501c400c05900009582c51980300c0403050000d11008401d0003035489002e00501820700b002d104402410b41c4403070b540c800007401e0204010443c14080e003585e90a0044a0081c8600300c082500d81e140698072203000b0606104280100e01030300400211401c043c0101101c40d01107401501e0b044046403508201401c144c07804400c50340c162100030000a280e10100e6000d5405224402200d00e000400341c203030f100c11062414400d81018402044111203d41264954100944148900c000084e05481180a4032240c4c00f101c508180101e444001d01c8000350101107500c1e012a8880d075510101c1d251603101d9410648006503503448180700030300d00c58111418051016000794903141e5903a4a203c2c2e640c1081c210880003070b4031100d080040c014240a00c0c0c21180200e2100303807504da0385840714050a400c1c4025031001d015074000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289056276 1250 289055026 289055033
    0x30a0b06030a020d030305090c041b0818030a02070e090601050a1404020403060c0c170913020f040503070609060f1704030e010c080313140d050322060c030f0b0f09060409 75
    0x1001c582c20760301924031152201c0b01d02c0d02178003400301200c03140d4144c45904203c1c0907078502030103030301400c1180c648008442500b1200072200d202000304055500210f44645207400b06080004281c42a410b6000d1300d1403604244103409010350191a00100303500000c0188800e035a003e001d00c080790185038031615542d0710480868042e0141d94000382c5560f150401241003960000c066220031803042c65980942130300000040e1990088a14031608406410b012422800050780288003040002030b10703034242655000007910707214954010304006043d152040007142e800c070b035503242190400d04119000c1080e0b0303000090724610003400641003000214070440242d0250500d020855042800261350303141c00d8494042c25a81c01b40115070711100d000030410006400b0900384181200b569501e45551600c042a08e1105021a22186400c003114240c90000b483c80c803441844031125100800c103c080980950101c0d007070001c500b409425400d00e40340182e0b4a2800c02544001c0485000441119904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289057526 1250 289056276 289056283
    0x30b100608071d030714031912110f060a021b07051005031906080c210d031d01060311090a140105060f041205030403020f0607050d0c020d05011a041802030a0b0603 72
    0x45a8581600a0600125120a000041081b000303420303822102912003007a1080c00c01c5842d074001402c0680d02a44030504030344034124602c00c0c80300510071600d0311035554074000c0c149079082c1da28002070b43e03001900301ca01005245c40240010701d808003604420f0b190102007010504600000003c01c100040052001500300700044008d00002e0000c020841c6c0307521031584c0d00c441d0380502503c501200710440c0424107004c0a80307036020f0841c0c07001c2c00290b0130984e0188d004e007010100c01d0004c81501800c0d11030040d000d00c6000b009501940c1d8901400c910a03044c070040410242168010074248100c0035070318600d01d9503840c1120070a840099440c00346508040c0c060003250004680d41d0b00c1c810404040c0007001000c0c00070f89000b141c0b120042e0f50309108021007440f540d40c0040c00e40c0c0280904240c11401100843d07005800684140d494140654031a421644000320014800000304000840e509061041324481000c02c0c104210707403000ca4002a42e10b003038408006148401c4000051520748050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289058776 1250 289057526 289057577
    0x6150d06180c05120d20030408030f03100e040b151c1a010509060a030602071104020a0206040b07021609110f0a120f090c0302040504050124030b10060807 68
    0x594200d100715180c28550100d891003401c3c4101030400300352145200108400608005984880889040c91603420a1610a82c0d683c88424002444001400e420034001071540003824103d0035624503003c0b0003000c003842c66802211808076140100000103a04502082d040707680d4034039000903a450741c000540c407080544c0c113011030b441001d549201085516580d0010f210a040c415201680e00c49040c400c002108907a000d50000c0590310800104000e94020900d041c01800180e000a9140d40810242e81c041801200180d000340100001e00c03034220140d0f0f030400d100e4406003100305041200036210381030b1406002010b65807021800f000364a07800403500d20040310b8000989030310b000c0034041c04800c0740c00d4060b00102d0a081c480d0440c18050712801017075581c0528404055415a002e003c01000024000c9584d5980c94156840c00310740c00c0c6c60100400d50540c2542000c81c2549007100c0800006400c1e0078080104c001c01b4040c1680042001e94440d4075407900f0410340030f48211112070881d51 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289060026 1250 289058776 289058801
    0xc0304110a0f081506040506030a0308090a0c0e060f010c0c05040b030307060e013216030b131a010e09040f170a020102090a06080610081305070e0601020c0306150d06 73
    0x5580c00040d0f4a00302240c408810030440c4800e41280c0d0f545428030081c0c50080322490386c5500280741110000740035045440c7c01c038400e80100c0b10002e21698492505d48116001101034842c008104840d514000001038102c5400b86003000560380c00e580ea503121011719000740b6102d070b92135902c11010707500c040080c0d409031030300504103200c0d4243d62002d5900815101200800c7d8a00d00c2c03071080280708445200c840c0c41c0e01c1c0710b03000450703955500704091031a1003080603440406444884510700e036070b40c203166a8600c1103604000248980daa0026264140f01941214140301090b012040c16a4035031464607030081d00b19011410440c6140f0301314611803145080703448030724400315251303510b81d0341513019000081d0142c40c3d10382c0c1c00f6150b010542c0e549004403030455100c040c40c0b0900f00c0c1180b01c0c140041d00034101047d0340c0c00d866103959904c1d08041c401c0c0c00c100b580110300b00802c2140d680c1041802c81c00c0100780c024043c02c0c1407145080e89001c1c90940818050100c5000344810010a5400401c10002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289061276 1250 289060026 289060049
    0x11150708031e060a060f140c1006080c0f03071503150f05010905010908030a12110d020915031902032502030a1205060f040f150b0c0d080c0304110a 65
    0x1812100345249005406030042e900030701200080d40b0381040001002555016116880000740c14030f0102c80a10b850000301c40c01204c01c0c01100001c110803c03403141440b0b01201c0110b401401c02000038588114141c0311446010619445c0d0303810344000c1562001c1e107184c1e01605e0b4220300144001d9010f090600046007600751440710000d051545602c0d205e00346c2e0026a965007440d580c0d81d00440d400e01d03450140c00b016800400881e03071024000d440e4605010307a180e1004c0f03803003065042c1c4004160030416010005c21340001e020195443e168100b01144549100d915007182041190b100d030040d034954140f0801c545c0000410300492059000143c01c0c0141c0120504a12210710001d40300c5d0042143c40010500f4079003030718000421406102e100702d80242a0940161003082007001914007034992490304c0d42c0d40d18000f00c1d03800110007804090003580d00302d20b60350154501c24a1500c035800650904004d01c00041c00307110004102102e400a40003190712603000540000540301a000c1d42c0501c041d0311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289062526 1250 289061276 289061281
    0xa0b0604170106060c0201051909030b010801020d0e16051302040f030c06030506010305070f0f030e0f060412090f1214070905160e03071203020f0604060f0b06071115070803 76
    0x204081110580c226a08000f80507156643c002940c910b2066080240803075070900c6227201c1c080a40245400251581c85c041200036640d440d4000091403e0f0004041d603500040c40b82c004071054003480131011700c400010069100001001c0c800701d500d83c081c042c800e00054401c40000000c58040d40c015180f07003159080c801d55246400b40b2403801074481c8074042070503c0c00144103980603100705449002a44c440c00701d0042c40510480d5440c045030156000d15603202020705070175130104802c1158407240e50040030a410142802d1170201c40305900541042034080080c4030305180c02d04d41108076001c1d108a52400030039440c015003124040b02103041c0ba03211706040040c800f10aa007003603010302580b44070b41242e601d81d1002101c5504991412031b0b09540030f000100300d2140b01d080c401240a029206840d04040907106841c00c051065600340c83c2d02e9160f40051111050611a9819a001c2100e01034601540d9941e07140c041e0004505042c41080c4004204505244280c101c480065118401d1a9a407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289063776 1250 289062526 289062539
    0x8041a04031506151e0e011205131e0c0605030c07020415030611040503060402060d0e0a0803091b010c060b0a09110301180603051009110d060e0d020105100605030a0b0604 75
    0x100f641d84035040480011200f94446503000c4c1c4031103000c2c000d0200c2031005940c2c000200b6102c103886d41400c075040100014085240c108588206400781c440344800000000281c00d2030a80d09036144449656a0f07010140c1c4000920150280811243e890a005480f551041c4185005004010f0003035005400c00b0700c200000c100b00781d80d440235240b0a580402088200200740300e0b07680681d0240c1e03501340e07000401180c05850302201805409982241c04514911841c4409091050030102120019070100078041340100034021036140c0d4174100c1000216201090000301886821200908101d039200d10800146d1200303641c0e4000303403403040010702403400640604602c545c003d00c15491103e403501991110b00744c1074064241102d030020018111003c8c0c01218100030b10581000300c031094607028001c0c6854a0b011403030320940d40107010000c0d0300301501a6050501c0e6055501c17404691400040141c40703042c1c007a403201546e5080c035160b6100c3c1e964454100040c007030100101d034000c1d000704000800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289065026 1250 289063776 289063781
    0x10201151202220b0a0b091305151906120b0a03080307090806070216050411030106050d020903101b02010504150c090906080120040e0103150f0504030504080c0d08041a040315 77
    0x104103803000005295a106034828500079160040d9201c444089408d1400c0540d030081e541280d110046d14400c0c2c903000000414040c10b00602d20402d00c16414100203d58028034400068180c1d00c0b810701500d0541000259050744c1404003c0c4082004404585c1c420300c81d040c42c00103042c030201207c802d410444e101230f65840c1100741000001100042c08070b100c1c00d203802101641400c01c000f039400c2d039080c04420341742d41d0000d5001443c0326500b4030044036a40c2d410028410b0001c01e00500240d1003100c5820303518160440034404055a05000030700c00040d803041d0b00b0110200c11103100180980c04a101200c060010742c1c00741800609102e00480c14060652011301c00b10550030700d0130b624507a003107c011541d000314490720b0b51007078103100100301040b954100c1e02c01a082828000419848076600c00c02180d80030342c0c0640000314046420f1100390020001c00e8140d03441181c44155406255440020b58400d5020300c541da1034a581140d20b03591903034020348002c1c1da0300400204d064121510110300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289066276 1250 289065026 289065041
    0x9030c0a0b060a0801090c0521030f090901050306130605070c05070305030c010c090b092202070f0b070201200c010605130911040506010f0e030718020408070501020115120222 77
    0x325262a01e400078420005106c0c03107502070303032004410000c0342c81d00c2c1c01c1000c8802e8544107800b0303030340c0310001486070780f44240018080e80000d035803450b407141254410300c403441c13005030842030185d48140240010f001d4407000340201154000d8000c40c1036611030300e007103905115400d001000c174803403160013004200011003c1c003802c4402c0d000800040e803195108440c0b001c03583c82009980b8404201c14a55414481d80c8200382c0302002918000f0000c3c00b00c51441280c2c04068155200f481d02c1d0b40020030000400f0b8840d400003042c1c4001c0c02030612600303000200d940f807401803041e81100007510071502182900410012303c002002d590b815a440d1440da0040c00540000f15488108110142d40d01d19042c400d060142c881030399880c000125881055030042e1140d86a660300d0301c075082c800240f0b40c101070400c40c0704000b1360001503210b0f4680324405243c01c1550700014150b904004402c40c4003042203000208540000c202c6503d082d0150000c83c01045015140c035501003602e660301200010103070002d80c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289067526 1250 289066276 289066279
    0x102403030801080c06160f0204021312020102010f022a2b17040c05060c100c090e01120803270a0c06110604020102100e1606180b070503030f09030c0a0b06 68
    0x45240d211300007040700501c10b90b5401030b92907544d0b9181001258400d02506240ca1015100528010395071181f881460b6203540b2060300381384052060011540d0a014401c80c0302c00c101d9040d410078503900d02d03502c460f680b101d403403030014080c00344605a0305004101c07110220700c2d20300024039a0f060380c0b403c1c000e0500e00050a000440d07086030041c2150368003c11918402c903000100480c4181c100010003400f82d000340b0301e0f4141c0e8882d02440080d03504080c82080d17005c071480d03200c54004a140c0295913101000580c0400051105100e610001c2406501165440000061403420000402c03862142240d00700250030388500c5481404020802c3c200d4810040d42c0c1aa19031031402600104c4290380c8e10303c100c900900580180c000c1d0343c0da91425070440c03202d0081300e105076043c3c03c00c454011040112558440344c00542041461580741d01c0036007142c0050701c1000c090520f4000c01c1e0711959660302c8050441d60340c01c41601c00040365100c081c000d0380c204000c014191b89901c00030381445281010241c1b59035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289068776 1250 289067526 289067533
    0x904050f011a0c0601091802030607091802130605070302070b0d0f0501080f0a060c031e050f0f10060c020d060f0509061f0e0903040f03050609010510030510240303080108 75
    0x102110803044207589064400f1070040100340c4c00c1002c80b138050100d0111503004001900000750050754103000c0d4502c20000f070b541d04010185080c05002007001a55041c000d050b1040050680310a02070790344034190fa40c43c1c10300341d03650f074071070b15080346014210390051910078404140181490311340d801c0301e80000f03440707a018800760b41ca4004944d103a50340c1d5800500c0540c4080012800a0b05d140c1201503c03030740900300060083d02005c01440c85c1e41103258000da0301035550041021070b451125407a50002100143d02100b4a8100005183c009450142c0014440c0070042c0408650b180d081078503006a00842c144041803a125688000d0a020b580b83c414601070200001c00c903410380400c2a000407080c2c55075424080ca00001c08003c4040905554114001044086409064413040c0d900940c81031000b00b26a2812210080c2124006040e659440700d520b0410804180001411504401d585400152101c00c44454288441c0c1d6803d94280364500200700006164001025a040341d01403000e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289070026 1250 289068776 289068809
    0x6041b21020f060a080a0906060807060201050603060a0501030f03051e070812160e06030604020c152410031a03120a08360a06090c1701050f01090e030904050f01 71
    0x3c000080c0900b20300311000034182800140c5880907504280c0e801401050002446030b03c4070156801c21000d90450000f5030b4503242482910b0404001c7c07158006080103040081e54110307a9940101d00c0703040005000c000000c40c00c0310507000382c4d41c405540009204800303a0f884c4000d28221902d40c0042c508028401c09410000780c12401940c80d8010341901c03030341e818001d4005481000100e1700064900c0d07412a80c24494400101c50400c00f02c01d60320340f90094902945011549402c00440c002c3c1d2170001103414402018840d10b51544600700c00b0080d0401256049141d220082ca107400c1880c1160b05203e017000600e04086100e00410082c007103652111810390700d6110510320001d802c070140010440103420036640354941c001400395a5444000da03922010300e80c0724281a5200c0d0201640e070721607006420410010040b02000c414400c030320003400a4600281501c0303166005118003507040c0c0e00c0c0d03001000151824400c640400e90018010001818502000d0005420034003e44841032141004c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289071276 1250 289070026 289070029
    0x91b06030a29121f0e1c0c0c0b07020d03050a0c17031b0c03070813090905010203060103050a1a01080912070c050102010c09030f12090b0307020f06160206041b21020f 73
    0x2403c40c8107154904504d20380602010410006084c01c021070080f41c050078107002220004607102e00c821002d296140d03550100581060503040029503c401a100c008005000c0180c4420650441050b050304007035031a11380945083c0c0b2000039280b80201131025004200d0281c49001d4007460103202503904403052008182000d92441c45a41e003200000d601c280b024000140207203005290514110321003125003a41d48000c002134a5023a941201d13071781d4001c0200030702960306d07114650f48080041d03024000c00b80c0702c0060391519141c01d05460304001940300080c9103d441007002e0300120200b0040700d80c2c0c8458074240307100f804c81c0500826005500300750504a090b8400ea55080941e50010380e000d04900540e580d00016810701c0c028003081c090403280014108a511000d144261700e260098502100207154840c2030500040c094000d64610b403180c04120b0342e0010380142d001c3e0b4410515040d01202120491100d8001d900520b80c0141c507a40300403642d80e04140c000350320341c130a54007100482001030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289072526 1250 289071276 289071283
    0x351f0504060b221701020c010c0e0d020d030e0618090609012d0b16060b01080903120a09020a031a0702061501030f0b0901060f08091b06030a2912 64
    0xc1a140b0540c0c050080300e0712182001e10355440103c05040f0440500d94034041d5010713204515103103220036540800c0007458500d0030300402d02c01410b0b6107800c03480c2c076030f00c800022201c4131414000303170040c00c607003400c1c0041501560282217000001854292221076141c01d4080c0c00c0031240d0f80ca4000c01201b000300c0c1f05800e109240b1410b88051501a0003400000240c0040302452800d400780c0d005100710000580c1c180000c005d25400c080e600c8051000a414209001941c9043c419581000045410806140030120035184c04071443d04c5400303402e403503403107195000c1c5c08241c102a6010078172100010421099121160340180c50621644030303540c8030002030307844440844507030404640724003c0380000c0d071195228102c0e0fa07569100001c2e1010509021a040010980081c2c0200c2d407182c0b079818403e0b070821200c503800b003881c030002d01b40c4456851050b8020004070034041d01409d8040041640040d050700039600803c101011b408444004962842c074001c01042c03150b008400350341b90f0214130803011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289073776 1250 289072526 289072529
    0x30e19150b030a03051815071b031722090c0f0201050c1603110706050315030a020315130609030e0f01080402010e120f2b020a03351f050406 62
    0x4001e48403034103540d10184c070311b80c1c040300d007800c04400c1c02c15a0300324664586426091542d00c2e510026103604c1f2a181c203402c4114440410052007401e03070344c10000a104103012000040b01039030a40d46541c03200614082d000c6222a07041b000d88a560004a00d1120320740c400d500202031a900c1103191115000e09031700701d40701138500c0d00100404100140e0109101d404120000744030b4540360601a2a00600a080c0a4150446030000b0000004d0147d00d120109072800b03644012405410717054181e034006556030a281c0c1504200311400400118841c4071290840e0a25800000c117100791103103460001d1103001c0b180c5409103d42003075108000c480d4840e2245034840d60707040e1511408e5107509410490451004050945203204801d0700c048040403d22003001480350085003208880c4241c4da01440440d10a500101150301112551006c40c0c0c0c0503140b995540c0c9000300103901a107407009a19400d55026000d0710200c80c510b401d0003170584040c075540e807200700e0520f10448040c0d291400c120507600c49 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289075026 1250 289073776 289073779
    0x1c0201062309011505120601050d05040b090c0a08150a020708040801140f010302210c130509121e03070903140303040b09060709060e0301060e07020a05011a011e030e19150b 76
    0x20f02500c0c8119a410b12247d0f04000d050600b5030074000e200c0c81d00d03000c0d20003c43e0211005441101842405d43e070402c0007080301b034000c80d0f89030716007428040c10307503620000380680e41c01700100c4501107024900b0581c112703150b554110f20500c4c1c0e52501c40c80180d01034108135460b918844a010700003052480d400584605881d4000c0c81035080035032191805604291000d403501590151100d00c0d4283c2d5181c2c1d14041c3d0180d02258081000d180c0420301e1030418128032854a80c513582005101010480c040c845020549400c003025126140c90b0b004581109054100904c08200190340c1d414110001000c2d40c4158414104001c082c1c0c1c074520340b02d850706400e80700003001c40d081e0482403024a000e02510070340e000303028000050341540c40c19080009031080c6c0d00200034ae0807244c600810b00000380681814450180606607505411000003840c120107140108049014041100c12003032207500040701280c04001200d07036180640c4126140207010a03012140001c1c080050b8005480e01d00514402040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289076276 1250 289075026 289075037
    0x906020a02010f0f030f02030a06050a08010c0207030f0c050306070809060a0e03092b0f05061311130e0111040906050307290c070608040606090e1c02010623090115 72
    0x6001e03c0595000b184080d1500c2810b40b1004a0840f1607110310203184160350020700824118030700018070403091155000005540d0401d11a29035054000410404176075200d246e0202401c2d4a00740513071081c86a801070780d450300400c0180403040e9800380e01203020302520f00c190381c51a210411504111000c0904590454106002000c0c2ca89800310180c51410b0403112011011400c1d09500c070326904100c2c008035a401740c0b200f814410b1010030001035501aa0903001a640140280c58010249140303145403440b5001c00d60080030a4206600051091604c031802400500d1a1002010841e005401080b10b080d1601c84002803a01d00001c40b0740881c2c49055200b1000007951300d006000115061001001107410010035101c080c0800125000300403542e02c0c5d6078181402d1600000340c8417540d1001c0f51140c1815694040240c0104101d11000306c042c121685078103c01074141e000d824160b114004010015a112709d40d4034540101244e507400c201d90301d00040e070300c0d600d42882d42c070641070100c0c00180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289077526 1250 289076276 289076297
    0x209070c0506150105070f0803041208190c0509060703030b0312040b03150402040e09010b0405130b0f090c10050909010605030c04120602090d060f0c110309012d08070906020a0201 79
    0x4001c011a0000f01c074042c50710700e00d0264181c40e10220100314030012a07890000004010030700110081c0c0c0d44e042012844c1c030751720030b060203038100c0e040c07001c24000700e2001503a600b80e8081d214040c0c0c4c00c445040c88050000350301c4620f1410b001c0e00400d14506107a00a0084074501c10007080d07070000b00c400b0380e40c0c150030050443d182c1c4004201c581500185050b0050350821001c62101d58011040b13104d0400038001003810b0b1517190920041d0fa102070650b01003a11440e01010004001e2601190300ca08112403880043e501e601100e8540514083c20540240401c0b201c200c40c00d5101c0e0042c00c10322801c0d2a9108503036600d0000720b880c0e00c0100c43c0c458034200c00344018068058005c0e1848505801050058103047c5180005041c1c030500720421500141e40b40030310100c01d80603024400c070700d12040c00d00c01c4d101030700f01c003c094072842440441070402901000c0100e60008038402002a00e501e80d29802101c2198080940343c11070656000020510002c8001082840062040600c030b6040c1d41d03110106 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289078776 1250 289077526 289077541
    0x601080c0412050c0d080408010605030c01140304150c110f0a030f20190510050105010806190b0a080402033304241e0207020d0b0613020d05040209070c0506 69
    0x7440b0444202d4281c02040c0a014880c3e9900404038151401919115619407030146110300319070325030380142d0007908000f204612a03030308030851081c0c0c1100000903e40c1c0759160b18141488185d20314201100da484d2040c07134401c0a074010b8540c4200001038088890030300c10382c28000c1d603c8c1d0a004008002501c3c0c2c80126850034882e00700702c1128204c2a0700b024090701d0101d01d203414001100380c039800b40c2c8031184403542405001c006c4c4101c8050861070800855040c040002d0039500000e041c0740c040d44040783c0b840350000c03851811900810008440b9502c821000c1d00091040c8010b440c168842d03c1400070a014010042455088504002323641c1401d04910b003208004a0400078810743d0001040004160361380142840d840545009003000680008441c031085108021191310b142450300c10b01c0160010385404c44124100c0c7d801200080d041d03620000010702440b00612502c4d80c1500100d42d0810300c904c50b410245c0501c1c42110b03d1030840e41e03038080440e007951b803414000e41036600240108060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289080026 1250 289078776 289078799
    0x10f02040e070f110106060810050103200f04030503043803010515190c1b06020c0d02040603050a0b06030d210c0e19290714011404050a0303050601080c04 68
    0x2c000c101d08210009952140c180c0f801c64140c1c2d401f003408900e102d4100894407004503d400007030032003403c0401100008480c10388150b880550104c2c0c2e50040080c10403000c0f004c51003a030300290352100032641d40e15240c88115a21507601304484001c07031480201111001241700d000e20710403403052582419030b03103800c0c104040b0402e00b038015031210320104021070900800401c085000280c0d41c4481d41340b50868980032180c0c07501c0c0003c10203100101e0707009100c90b03a4041602d40442108654485080165000190007080d1981c00100684210741301c85040000d901c1405110b10307070490544861400e040e01c01d40380300150301070241e031000942d404058101d0b07070350340040d03031804482c41d0044940e6621400315130582c803500307420054440036100030042c650884008824a14001c0710030515290b2002c0700c08458065960010300714502c041011440f0402544003194a1580c04d140d03010500b05400d1090b2140800d1000307400081c14040012043c0d409004414018851003030964a85480c10045184 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289081276 1250 289080026 289080047
    0x20114060d020603240a0305011d19020609063f04020112051b04120c0918031103090a0f08010c1d060a030609022a0d021b0f04110309010f02040e07 65
    0x19442d102e1117034a00354440310b203a0005144580b0001070710aa00524428204000e40c0304014994003a03548899031030301d801e241e0401c0c1c0e9070584086854000e1200090401c0c00b0708109410074900d504c201800480c1c0b064054218085100d264103091111003090404014003203601901050303014a091441510941c01242d014001c645050800100f10010304410f92080e03004540a0740c040d0031801c184271400350070900410590f07408000c80b40c0808011105885450030140502084c0481d0300200b41043c411140074540090180a200d030301d540d006030700d0321054050005150700e013200300902b05004011810722004a03400ca01600f04600701041180d81c00005400b0070142c40f1100094604014000380c010012411107101c84a114440746110260f02c1002e002c281d03a220804903400b030340c1c011406041c1c0612001890003400410400706417118101c500007a0414602096042010f406030007850140783c00c1c070002e100340011251902c05034040c034010002070400e40700c042042c0b40c0c01006003c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289082526 1250 289081276 289081321
    0xb030604150e10051f030506010203040905040807060608030309100b0303090901090203010312021f0c1b0f03030e010b0f040c0309210f030c080a0c050c0a03020114060d020603 77
    0x141c1e003010008607400046150b200c62a0380c640101070103820000c540c0c002c4003400b002c0d01e000c501e40120302d0b20708100d1000710508030281079030741011680c5a44248200d8010b440400d10501180c20b1034503040d82281e115070320603a41545012000704180d10003000302c81c02244840000d01c82d5641d2140140f004100445800358148030401c01402c3e15214590202d009017030098005071298914104030754642008101d00307046401c492100c448812460500d08490f441d210360006a6816a600036030b0b011100504c240c02080d0321403c20000c200c0080c400da50400d109030b509120212500316000d00780c58034144c1307842d480b0044050112090815610406c0d20007010319012a0100f220785a000030302820800400c2c615420f00d5003084441d401554485442d01586010450410308540082241602805100b80b45440d04e40d400043c501c25401d5841c00c80248007554030358501d48c0b4001c0d000b4000b81840604010310b00c400529585000410220000c0c7c019001501e99503480340b5040c148102d04507104e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289083776 1250 289082526 289082531
    0x1e04020d0219080712020f06070308070c06060b030c07060c090b09090a0f11041406120a021308100204080601170717193905040c02120d0b090f100b030604 68
    0x64a030030401500000380880b6800280d17014075801449101c4d400b40480d83d0081404101030000a0713071151460343e00940a103041043d2146501c0c0030000380101d40c0c04002440d10220503c218980c80400038140340d48900d030b0401c01400e03216401d0b140000e10384100e41d02c8500601c441d040d02e003443e4407030651000c00303404d000030346503003084d1640c0444408000010316107170040750500000c000700b0a424070070081210700a0400380c0311040c007444018010040c200643c1c000c902d000c0c4e0400c22051f401c0c09010050140c4816401060000009421520070840c15202e0f4000004040040c940b034030004013003060141036890b09201454061466101407028280f0500b21142c1c46020010a2150b040b480380f904030904207030034405c1481036000c10700207042c004180901500d0304122035482c501150001c3d0340201c2e02c419030250031381c100809400c41808644000843d1100400d03d0703481034a5030901101c680c05180c6400c0d400360b0000800319202c11002c8120001030000e034124030081d6904c00c0009001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289085026 1250 289083776 289083779
    0x1f12200723031c0b0f010c0f0f0b060f041a010f0c0b04080a09051f0f0903081303020a1d340f0306120308011206110703081e04020d0219 60
    0x3010840c541c0c400040d4499040455000a40c0c2102c21040d0000d440301c070001e0040344600c0c00003032401d2002850040c14403010320386107410003840d200b045070310f290044c0018031162290304042c0c842000840f111882000072040c441107034a0184140004403024a00960342d80b401701006580800c140d4400405201c0c100a84100290401c50700a114500c0303800300588800c5118009400c1203042e0700400d200c0c1c1c9500070415400d0360f518410807901c20f100c3c5009501c0289081c030030781d10300c182a00050001140000c010b8211200651403d080740e209880d8444282d580c0d40359010904000120701c0c1132070901402150380181d01c2c40c0b1015800d6911080b9410254480b140428100c507219107082c04507a26406640c50140c00d803152070014212591303041648140c1350750080002c10140100039075440082c2e54602407182039406180802510b01e400c076912885400d015100550032120041602e5003540481060345490002c00d000d07a07800380007071044c03c0d680e40c00c018a998404040d180e51040d520720 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289086276 1250 289085026 289085063
    0x120912140a050a030309020901050a06120c0516111804171e07060b0102070e01050303040e091014090615090a0203090a051903080604020301062c1f122007 68
    0x241c00d080f50311035100010701c0c0085105201003004142e01c450302c2142054010000b0703d0b000b0b500721900341c03201c15002404020011059615008160260710090928404201082620510038880d80b004403210f100c081c10512014181c01d00884008107070a20300005040d28442c0d090151895000004603c42d60000701c40d2015420b03001542d040e55681c3d11503182503171658050025001030242407107909003660418001c03030781c0c0e07100740e02c04e0400c3e20b4840300c002030700c01506011418401440785402d1000038440c8149100c820301c00d9a001ca654080c50010031401c2c150030102c03d10060015003511019616004d00340025040108583c803903000c2c100706040080c0c0c1c103110003030b01c01c0345940d035151140c0c1c40390600505000d4001c1c02c2600840c410001404800d8214645805a0401c0040c0d403110246418400c2620500d0720543c0341c01545126480c403d8040c40300051035540101e50342c80c12001004200802030366150b43d40141d100010204151850142030024460180203091a40d40d1100c200c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289087526 1250 289086276 289086283
    0xa0f17040b0a1401050916090503060a0204060906030501061b050a14030a0905060c0a140a05012c030703080415021e04090c090e01060807030e0118120912140a05 71
    0x1a82240c0c1e2441450030030100a1051058030f82d121246001c0507040d40c100b1020604100c0060705040c0d10000c0c200c3c880c8070540c8243c009102071301000e01919054208000080041d40050103141e0100c1c10743c04001c18128820303c1018122035480c0c1d01d0781c0807420720a03006c1c0b80361080404107440700d00500d002180424403501d41c060800710113030700541e9507249028005080c0e1b001500401e204910400c602c1501140000d0042c00b06038100f4018546100c4012266240410011000b8015424403c2000b60746508140c0408000704115840345204840b035106920b901c40c0e0300c0c00a02040d0f003140420003007044810100e002c5090620700515101c1c402207403070101e4885624401841900081c103003c00e034114060403038a041a4104800220300b03200b500e400001c4140261403c0181e0704000a00e202d00c40d420404044640d03000811951544214000e03c1e591010b00030b5a070b20744500403240c6900c0c0b1959068049604d1a02581c60200d040e0362110002c0a00080d4084580300341c4842e4804101b060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289088776 1250 289087526 289087531
    0x1080d1b03030e190201032f1b0d080402090709082e110910090308031503030f12040b0108070b0406120207020a080a060605040207080406050c07092c01020306060a0f17 74
    0x21046004d0700c10051000405513107822074600ca02150414081036580807240e90810000038040100d529003400070481001036154030004125403068000c10740b0456000840e080c0554001e80303610800c0da0751010103030b400040c00d1081c22115840f0405820741c0c1c0e4543e44100c60150100c603050060280c001813000d050711103065046007078290009030803449103000080d11002202c681051404103245484003011400020054a07074144d14040440c03495405108440c3c0d910784113101c1a44a4291884032280544212411900c40c1301110000c1080b1700d0015043d401c441c000b004a40c034040c100078045850910075018440201d8003808840f00503516a604840175280d600010704109a15041020a44d00150b00040c00740b031041201c8408103d40c68201c800761205410000d50b90a8014500c2d131800e182a800340101c0341c60480d10035040d003140316100b0448900d9881c800c04811080e441c40c2d080380b10540340b1030340c000c504110106000d80140e211152901c142c1c01c10984150882111646100c004c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289090026 1250 289088776 289088803
    0x608060d1a0a021c05090729282a02030708031909091401050405070c0b07110d02011503030c020102030c010e06010f06020a1a151e0901080d1b03030e 66
    0x21489003c442c4040016450b0200304c1c003801e0181d8201045034945400050080004e98112501107112002c1880e51a48450420307103401607032100581115004002000310401c1e075603010100e03402c40c40d84240c51915804010f03c0c5160002c10101a1141001c440a402282c050041200000b11310905002400040b501864a81103804900300010000380c1e23590441c09036a417078186411207006211000c141900c1c01524009400c1d141c20900f9683e6920886004203481800703010883e00c0c6500007c45480c1c0344420301204c45180e00f040080c0e007030b111409800b96803004a100e0400100f44144041c803d01401801607074605440c4214450a4a03c1e100c5d098111740c0c0080d00401103400c5c00c03240000142940d2014046000e4182d8480c510308880d403140c0301a41809002140700c003070460300182151000141800c404038401c0d9854207010400d00c0780d083c8910381c034100001f003040001c20b01c21591001503071425068031a4a90a04002010f048241c08050351444d0b507981140013048807412103540d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289091276 1250 289090026 289090031
    0x2070b07021c080408090f0319060b12061b0f0304051c050406050d050901061502070e060609030d0f0302070b040b0402040c050418092613050402040608060d1a0a 71
    0x148000040c0c038000340c540702c0000e805503003210b1050103a880f00103160440e601c0107280340e0700c500c08030020b1400070901c0e00d02545409840301c071318519240001c010101034407525040c070148410303200300240b0f035400070003503203042d0040c0c000240c1c0c80d44140e4584030501d0b845480203003000d2036608400090f420459040702c0a610081e0014031b08061400c101080040d1494803a00d480d040038002880c5004000141c011030351030fa40420080c54081d0451406403180031100318035000103090084d6110118842c80c5415880d010105969041c04011a82800c0000d4020300401d132189070301329903d10541c00c031301080560030720101000640350781300c950103140104002000c6040c5401000100d41d2103120308000d10070100410400310350602001a0a5090311000150621003401c1c209580071135860641c2c154841c0c18454110a8042009401125218108031941d00d4a8805010480c03140d4007031403000c100078200145940c40d00000d500170a03441904d810884414403030f611286420142c5903c82000d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289092526 1250 289091276 289091281
    0x11070b090f0c0613060c030e060d0b0a08070b071b0317070203010b011106010b130b04090917040303140c1603121818020307050f04061d0108070e0402090102010b0402070b 75
    0x4070100200e42900070200c1c1c00c0752074401d40781e4900200e1000c52041c0340a00402500c1501818040c1102045030700024003c1561000344501c441d00078807032003020a100e03016004001c1188540010b0270401e4a4004601c10300c2c1210721785500082e42e6003000613580c010380c0d07480b0120000300305000103007000407c2141e8544485113031040500351884010391604105900080b40944c100014205046074121958640e86401c240388881b13114004d500103411700d0400040008540f841507011044160140c1f4442c0442604001c01d54600d01c224440540010ad80c5040c2d00e000b120a40014030745008000112101c0c504040381030741c5d07446801d50042c0d443c00002101c400d8501d81205811441c45068581e01c03034018100325100000c20941d0311981080c550100025504501400c103c542000000040d80e80780c0d036603900010411212000c0703000444641c4c1c1e08101b0749502a00440d4000d803119104c0411002d00030007840002c0d0420494141150348905003a41942c4070751008007802401611f4403403040c0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289093776 1250 289092526 289092553
    0x303010603360309090510050f010e030f1b0d05100b2d01030b0f060304080702030703021207050109361e0603050105060f0d03080402030c0603010902030f061905010311070b09 77
    0x13240130703510040000b814682040030b40401c03862a08140c500c122010780b2800c0d9403070012190400d0300e1a00326050300c00c0b454000c00141c000550401d0212102c5004415409200c06102c118070f68140c0c0140307140d008160301210032441e900724034507401000d0400c00043c26120710003100c0c02c0d10000b0440c00b0f802000b0600805580c54000c3e0358145905507050303110b07000d4100100301036200050010709103400100b8403d04559042c0080402560001c0c4441c003420510302a550b00c4600b03a02c03542d4045404003000240e0010f1650390b84030a1100485070603055403441c880440d02070061040900a150783c1c100e40c240101e0660301030598201c0b14400054103604510f003041c2111000f9022b14480c0903c503641d84032036658040240f202640c140f0780402c0a07121407012900d002041c0104981c00350300400007049107003659000e10b105030b940462010403a11103800340726420080c0552800e0b8902c2150003400f0550181d0000d50030100f4605425180072503d80300c411095005480001d51504400b0030302008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289095026 1250 289093776 289093787
    0x120c12060906050a030305090604031406010602010e0a02012a211407112209060f0b090412050c07150f080c09010804140102160c0f06050c03030106033603 68
    0x1411004004001c0103061100084011303807544402420004001040c0d0b00c5501d03400d054a000390b134001c075520300004c924a070650710b0b00340074040d00e40150310b0aa01941d0000b40061303801c11003074040e1070700c0c5c1019028611070f1301e80c04494446d944550720803d80040c00507036207045000210500702140104081c1c00f81008180050484003007a66460a0241802040d04e0f60000403114008403890051041040909849404c03450100c224203850540c4034028031140d50012070965950303142c1003104c2081e0900700a191402901e0150084100c0c42e0031400b0240644024a01140c440080310001131b42c0e102800048200b101d5179400042240c0a37031252150464005508007050a408030308042c200000240200c500410182003000d01040c14103607403600b90f049a0a1482c030114604c11448141411040001c00b84030342d205a0031486030001c0c0e41e501c030348140d0700e2060041c4080c1d442c40c0d01e4014120081c0000540ac1a0b180e00091a40d19103020019043c4102c28980b0f518070360b5010141c1805040b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289096276 1250 289095026 289095029
    0x21005030402040b090709061b110409031211040611150f06010e030f031e0a020c040b0105040806040f0203061803070605041b120b06010c0f0204050712090605010305071406041401120c1206 83
    0x8070027440c8240000800006810310010406d40d4000b414400310b08084861130110450006041c0c5041b45001010035484001c1c17007a01c820b5114047c0200c020900d141c0d94814084207080401e02d8000880c00c90540b00500541061052424640300d281c0380c0300007800c1000302c10014540d9440015840b03420300c14040310030700c10400161007a00305590114088d48820f40315284620880d035583c021080b03a1b0040041e50003810720300049500510701032a16818640900b442a84613116540005000c00c29803ca0600303000118009141849440d0f40d80d00c0281c0000b42c42112002e50300300c040b20108042001841c01400c2e2680709151180c00c43c1002482401c01802e024104444043e11a000c076140101241c4840d5054500158940e981c5004940300200310100c52403050610150f81e0500c14240c220a0690740103d094402199a40b1072000c0c10036000320801d504010140800c016407414220180701554060400c404c0d030b21001034151045500a21000c8085220148410f00d80c030b989201e241c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289097526 1250 289096276 289096307
    0xc031303021507020a06260a0e15150108223503370605010201060803030105091902090612010608090f120c0f12070302060703020403021005030402040b09070906 71
    0x3d14040690700401d81c0201a8099101032004c40480b06022501d00a22080c444104000c130044d00c0c1420448032028000b00c80142041d8841d80c603003d100d006c02500028050030503400380d50b143c1082e610066a4400000301754142e140c0340140a04400c41484800c0001c60748079614104640000b00c40c1e071741c01071300c184040c2c00441144203002c0c1008080d500071660082c1c59018804404101640c003da0105901e00011114035840484500001440c0d04241c0c01e44109800038840c03280c69504d81960b038042446240d034000e203250701280100c0200c5924000f815000a400b41c074001c40d8101080380b90b4440c4044000c40c0b0b10003401000243c2e4402c400c1034002201d50050a20300544032034080d41c40c15408407158a00e040000c906660b000e041003e141c8086134501618031200d62001030390901d4005105c00d40140c011280001e14182c8607108582c1929401030860220303106a98007110150401403080360000e555900400b100d665059040f441440d00c0d98403003904508161004004010420000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289098776 1250 289097526 289097569
    0x6132a090806010b0d091401060b0309070e13031115071701240503130b0108010c0e0a0803160c050414150402070503030a09080f04081c110606040b01050c03130302 72
    0x148116610402110326081c0c1c0c200b030200d030383d05440c00c25551661f40344084400e03a41c6440d400003640030ba5440514407980300102501c2030541d8a2828501c011000c46041c0c0c0e00040b81146d0400080c010411001da40920f0822907081d0859201d080030250000c5d40c0c02000300d44800005d144c1d0f01104400135000d002d40c3e042407018524110090888040081c403047d060000120014003003100c5201104d0503107810464000503541d4a480b414020542c6085e0040001c41c860360700c44c11410040940760841c3d1100006620303010984004109030348201c1400c43d081c43d0380e0741000629a41da070141600c0400b005c01c462070142803c40c40104d60000d0703103a10501683c01444000082000401501e0303001058540100b2904080d02c0c02401e04e02c1680c060f0a86104046408039103100005054983c0c20a06105045002a4040155508011540c025060b58000b00c0040c007141030542280110703100c103050070780c1000c14040000d411030b007000c1c00b40c46003106420410815850000d090b135804100d040d240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289100026 1250 289098776 289098779
    0x131407180b0a020d0e131404110109060207151205071d1504170c030109050d02010506010c08040902181e0315060d0f050a0209180c041406132a09080601 67
    0x29441d400055013000034025101d0f1218400e441c1d244090300d2080342d0318400c1115203030b200c00d440740c500d805a400756441010b0800c032124950240103460b043d101d0303640060201c01c0c6401c0030b91800c4040ca64040c4100114a800701d1b0085809004041c01540b140d140c0c040b000100420325841c55407ca0032051142d8403104000094035035880484003a2000400400c21407484c0c1d94601e40360070041514280c15600c0c0c030400f00c09018010032840204452640240090385940c4011950b078507403100c0c041d04210080008212401d001c1e801040d09161b000c0c186100e000c000c40004004000d054408110070900c0d04120701d9524041c4001c0d0500140f51402c01414100380d4080380b0360280610005103104020030481d010f000042108440c0b4590080c031440561500310241e5480c84022071100c1102e10441c031045400703190601440000da0030300b44001c11165a1a020001940c9852185403003031a91030703d29404850540000c0c1080f00c544580000381065009001001850f030f1b540300e076210781c000500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 289101276 1250 289100026 289100047
    0x3005040b090d0f0e04090503090607060203190b0102031803010b1918060803070609051009110907081501140c121201051f0513050306090604020405060f01020c131407180b 75
    0xd00ca05101c4c050b540081c00400601c0c1c002e00d14401c40080d5540024080380c540c0400030300341c004501c601544c034140d844402c10459040241d866030f01c001c9016130002e200e42103800c8000340c802000e40c100107002254485501003c1001e002c030070070100400c496850300620001411003481208076a90302c4003000b04914107034009032a40039040c00184140c3e02d030800002800b00410403c000d04201c45c60403c441e04052409001845044031042e00031001400041c40d003030300500c6280c3c42010012a9030b800c42281000460722981f10313900120341180140100221007504101c0484106903104c52280c0d02c203c0ba00e010b940c01e580581c0007512924681b0300b4428180400080d45511541a04115464000d0f00b03c10045070a001e400c143d4047c8a9002007105a190000e891801b45009850401042d01e4620a2098040c0c0d184c0006015a02c08803415610341070581d0032141024401c0400078820411010074a002d11041e6200c1d0300003080403424924000300c405418000b000c0b0031f44d036a440c1802842 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 289102526 1250 289101276 289101287
    0x71104050106110604080c2107020102060601030b06030f0714070501060f140d080d060b0a020d12051e04140f0a030908030301031a06150f040f05030309013005040b090d0f 75
    0x5c02c0108545d2000c203915540e04402c0200c0701c540003822032611000c011110040c1c05a803c6944182e005124040c08a00c007075000b07128500320b100c800380070355195903100b4030041003175000a0a018104541070165910341c2a44402a0207aa03110354004035a02c2e1401106011401c0981c0200151000c8510b14240755510320310718800c0c0036448220b085d240e03080e41254030003c5c42c8642c4003c0c0301030800500f81a0056000c0b034488081c3d801c0c1d450304480c0c0d140f5600d504c003c8071003ca4000415035070210004a00c0d25400c99130f164454400c0f900090041c1d518240c0a0400c500c803128901d00780d0000b0394a808054026800c4030280120307100450543d13145880340035900b48991165000040d1aa0124405468011401c410b1225408609685100b500d040c81c40c0c1e64000e1003100c44101250300e0200c0c07240b03408006c840d00d248050351103525036260020494401c800a403080422003000c4440c03a0bd40d0603071401600d01c6240540044852860007207a2142080e84860074401000300c4120400040c68102c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 289103776 1250 289102526 289102531
    0x709050705071e0206030106081e04240b040e010c020f16060c02010e0306042018011e180506150a0f080601050d06080a0302010c11030304150605060711040501061106 73
    0x1603c5442c0003000411204400820a01c0030390060800000400e0310764008600300d0050284480b03e000240000b00100d40d0b424043e14018408030181c003034120103903170000b808900744044050010b85408480000317822500312401c20300b6940d44032024140d6180e0144485079005c44030700d015143e11800030310588100070081c0200428400b2040d860b00640e44610404d0750040000341c00c0b1aa68100303400c0c610b143c1c0d0a03242400a00c40f910400c00c8006040c0b041c04611018450002c8808036401e00e61802c107030000c0040c454600c01411440000d04000103175451640400d54000045c0b9400e00d20240003500741480c9420341c020304208890010f1540c86001c68510b6082032401e0403042c3ca0762001201c652007288496130502c1d0078800c01080300b020100f1650f24186c80b0740c00801c648600745070b090300c2042c4120581003140c0c10a200150200d0001c1041e100d00d941c40c580001172507920381303001030060f40056030280d521101c2220b00450606151151501416190405996050391441c0d80d66407203600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 289105026 1250 289103776 289103783
    0x30c010c080f0d0204050603070e1e0619020f03160c09111902120406111915050c0904050a050a0f0b06070f020a0302041b080a15031b0e0a0905070905070507 69
    0x10f0481d00c41c140075415100a400001c001503540c1c102604018901c40c090300702144101040820b0702c0b0a100381803185002c142d070180c0300908008017a82600d882042da008804158050040420031041050000b04224000655209030074061410000c0d03208145c2d400c2960050301d881c410800c140d00c01020b452042111110654604c0381c403100072401d28100c0c50b10310745010030100b0081010303908010440b43c40c448440440d440c1050783d0008d450329030150b40c409070400040c0f85504c2500e8400340c10160b0301801e400c0c001c42c600001c000c00700b8111041110207001540e0744a043c00281189801110841d620305401800b603440c480c0005a203a102d00074008104031402c1c0c00401c2151035540007500151740051080001140c80702000c0c07200700300100300030700041030000000d001c3c00302c510030000007422602070840502d0650740c0e00340d031005508a000c08000d41c54203001510504039121144156941e000101d01c050ba54501a458440740e5044014420f0a00d410405072940c40825075112541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 289106276 1250 289105026 289105057
    0x5010b01030c090b0309101a01121401150912060204080c030a0519030909060b1e0a0c0b0619080106050301060f0509060d140604080a0f020a0b01030b07090e090c030c010c08 76
    0x701c141d41d9902e009603a07c4030308a03403030902c0c4a600e50705800d403521820f800c80c2a2a010b8480e61110080000c94203000c440800c03484000006211020300c01000703c40784500380c00e040c1e503819125840072700c13503e00460f070803140d040c0c0000e02844466014407001c2c003420400d50050496815030769403151900180c1700383c88100c440640c1c00c0e03014944a121140010b040c09142000960b403036090300d20b050742c0852240055010042c0a94200b92114030803509510503550304c40d84a0000c81c0d07116000c18402411203a0b1002880c001c8062407215031001c54014448039000103441c61a003000e060030744440398403040040040743d404201c1920b441e400103500035011220000300082910700032948128048640d40b0610516041004000c01e98008102507821070301da031682c4251005040741c3c0c90009031402030026045600400002c5c0e40825071a07006016420000030540c0c8450080440c40e04c11640519103500c038508403c0706080511a0000815080c42c3c04414a603141d100c000091294058150000c3c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 289107526 1250 289106276 289106281
    0x52701030314071401090636020f1305160315141c050102180a0303020a02010f20030304060e030901080408090109030c1701050a0c0e06090a031b0305010b01030c090b03 74
    0xb252803049608031a804105460340528000c2d12034000d2060200031101a8503000318001400080c1500021000e400301ca0400607180d03e2001402c003004030041260009000380c160360003a41c414220288442c030b00c1324002001e1902510308a042a01e0308400414036241549010300114610b81c0d00040e90920842c548144d040e000c00300351000c1040c119010710401c0003100104020040d0010181c49161000e2040c10603030200400040080b2444004c0250b0302031f0340040011f5016150f004446030700343c10100300d0440c080c1001514410b07490143c0703645410002c100010800c1c1446240c41c082c00d00030086042000034030020300f03a0080075101a080700008180d0840340c0c0c1c89410224083c0d54002580c1c4a46c9036101e0324030800802540000f04a5401e09000804881c030700d100e00001d40116584581c075600c040001d005081d80018500e0f5000030105801102040d8400401c106046013000d51000039455421302c1802c40347d8190709a81018240b1075803607000351b40a25880255220031000c0c0340d40780c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 289108776 1250 289107526 289107557
    0x302010606030209033a050409151805130c06091a0306180c0c1203011805090c01050c01020906041502150c0702150d0c0207050a060203040308071205041206060527010303 75
    0x301070100114032a14043c6c086004203e038010003500031183c3c00041881a039510103c40d66032050140a090280c401d6400700d0080103a2540059802c40306441d0740b4180901c06844241c107085040c0c0142d004036070b2000040000c07120095a0709207030500811000d0840c1000c00000c0c2c5004217107401d0300f1170310034500041400c0c04980c000325100204400122851002a06030140d0303950000d12039402c1c032000040c41c18034140390a001e613030700c204c4014015000d50000c000055409030000b034402c803060740d0f080c000d20516840b208020400f07410040b0f1b00203070300e050700c1d1030081c0750404003a402010b0822241c103003c041c02064050780c042c250b040f01c070f000400c034030413110344011301a0300c0f0724092190030203070041920341d00464120191ba4090310309000e103544a240980c0c2d0b034812031000910b900b404003c000c0c00300b02d01003000321421649140c07242c5080c0d5601c55902e180c150712036054541c0c40e0741d5a020440e601d8026480719251014184005010301c5004103002101c005100140a00c07060741c0512505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 289110026 1250 289108776 289108843
    0x5151206060703111617011a041a04020409020d0509070f050906042702010f0e0f060a02010e0d050d0b0a14010c02031f02130b030603070b0c1f0207030201060603020903 74
    0x2180d4400311140b40600170400c000801d0188100ca08204000a13407000c40d81041c0540014401c00b10310080c03034600742ca02800000c04c103036812907e00e1b003540e40c040b0f2080c2da107500050008001000c40544ca402417070280808585000e86050340c10361000302c0400a1441c02c82120045401c11a1508166a101e030045030141850105400040001d500e403040c1c483c0d1461030608411703000307a0703541d4418005c1e44010399502070180d0700c2d030307038001e88180c00615245007140c0100041f400e00d10012541c030550b070326020b1030995804007900201d980860310b1009141c0601c0307078500300081104c4140135545021096140040b0118040d81000f00c5104402c2c155142000084103011000c0b41240303030009940c00c030300c00940240e100018101070b1003600003091884502940d008090003400343c04071a20b042c2d07412100b0f17806062910100d004000c40c0d910300c0109180f1030000900554405a96206a880c0007421240140c00c0038081c144180716400880e2000251107610040344800030240210550343c2959 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 289111276 1250 289110026 289110047
    0x60c15110702060730020a3c0510051303050d0603200f03010c051b010e010c17160e040c030f05071119030f030203060118090605151206060703 63
    0x1080000003410310f040080c07014a41480e81160174104100c2c414084001e204d803540a6540b00069101c0c0749400007048082c2e0b4902034400440e41014100d56000d18403005036141d041c0140488800d003030303c400510000707101c2544000100c0d8010801450031407411800f50142502c0901004008030b4510211101540030034055030b00314251940c0c0e14a98001840c04d074013040c0c1668000c0c12010444641414140100002105591141800d195074034030020f03004041d20409403400c1d9218001809010740a20130300b0240916980d8400d4000d0802200c444c80312000b07400704241480045620000c40d5224901c0399440e01d0440e008500044021011400f60240640010500b407070003003845805604121221410038401c0c0584442c07030721042c0c1900c0d0f025103012003d004900030003441c884061090b0b0045a1080c01418550100075100300c459004400c16044108151343e074034014081417400218440506e10388034940d0b458611500d064070701010000c0c10fa180502c00c04074080003094080c0e040c024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 289112526 1250 289111276 289111279
    0xc0c1715042312270a09051009230705131401090e060f04020a02070905010f08060f040803040f0303111c06050f0a090b210706030f0b01021506150a090807060c15110702 74
    0x18816203810519006040644000100401ca4080066100a180912207085000e050300c0e020394920210003400c0100003d00be1810007c04120a420006450103002c01038903440c83c101c0c0b240003409001604c0b01c4115040034803055444070070001e850b0307100c10b41c0c10314164080d20302603110301d12020300f6840c00005402c40d15805040000109076192008030400031550310714210ba41503110701d000c58481483c141c03000303058542c0800014005c81d04103410480c0480c031a00e0b00107040000040d025540380c10a200300f00034500c0201804600c0b0009008020180c4001c843c2e80e1620024240003803418600f62080450345a100d5864051075a5108409031514002c0c070003090744da01140c941291a44520f0180c4d4000c0381c83c040c01c01c10300300e82074482c2406d4904181c00510450300d41404980c0740361001881d540d400604440c0c110ba4861074480030381a0985952580031526040c02c41103401c100541d0000001c016500e1114004140154042415100e029200180302400c003401c02040e071080e0500a0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 289113776 1250 289112526 289112539
    0x2150f04030c0c0b0f1c0501030b150303070b15041a13090606050a0321023c0d03060e01080a020102060423030f0903010b010c0c171504231227 63
    0x18082800040040c551b41c0d0140722200c0205441816550485e4402e00000d0902203000c000034085d0141e1210b00c0c40c2080c001001c0b00d0a06141c0e07911034148803000c54614a803138042104205141c100f6026542805c2002d041d0b00d1001120440030030114411901a400060b4544442c80b082c009998400c1000e0301d00544601441c0d922410568801340c80d0380001803481002500180c1c0947c1f0118511991080040851a20324140c003010141031002414181c1c0b2107503201c100d0f180c041c9080111035460b62442d100852001c1c505040b03201542816400b18050703070414110000140ea01003070301d5074070590241000c8000300c4e9090000c084140b01460300c101718800010340403124075101c4040e014140e009c50092042004203001150750801d044801006030001c07802c02e00c40c80041880803402d4044a0b021512185004035014030400c806a034280d40c0b0480c98030800420382840f400c880c40c0c00541784010503040408040449882c410070a40344100003250565014800d244100c00075032180003001c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 289115026 1250 289113776 289113787
    0xd2d0e1902010c0b0f07170609150103021201140f0402090d1220071a091e010c020a030803010303030501080f0a0605191b180e0412051b01060602150f04030c0c0b 71
    0x5e2070170001038a00c2030109950104060001042001e118070466000d0040d04c59612841c9054450180c2a00894185a000e00c6000d4400207030043c0d260003090002d0141050114400034043c2c0074450080d0b07240581e004000c0c524950310b80016520760103511054403100c5c00c0c3c102e041203501c281c4050002214925180006804031000039014003543e0007841c8024800f242000c04110300d00c01c003c0c082d07030044840f4509442c1d280c15904150000c0d030781030415110001c031660005911310800d81003282c0581020006100745a818480c00780580300410003445070303034807900d01e40c1d03918588600000c040a07180c00005103a401e41004681004020340000c1c807025500c48003c2d04090400c20080000801c0c8a01d180d101c00b51f104201030845001900f81314941d01c2d5503c5801502081200078403d115040100da6145030600f0070300f43c031469004000242d01810548000e0034240030040712010410300a003031044907004002c045420a41c1400c0102e684c41d442d140282090200d03a010103862034010a8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 289116276 1250 289115026 289115041
    0xe0a2909060c071d010e1e0a0609020a0215010501030c0c0809060910051905030601050409050c220e070c02150901020a05030c0a11030d080105060c01020d2d0e1902010c0b 75
    0xba01c2540c0d1a0001040c4d00c140c0c3c8408052030386e000c0460f1400365106042034944011446002055004075141c075012510985440740c0e00140d91000b540781c001a07110000f9011158001000a805800246418071600b03862100041510300360803005440742d503002030200c501e5070f07608049400902006d0b011801c420398644002d08180c00c95502031007000841101445458450b808032445204140c4600e410903081400520040100038985152484c08001e030300e1049012014440711584d10507801c141c841d0074a11003018078840600441c060141500085005a1303c003495a020174a5210100351280541e03070040349040107012000e0450300000401c801900008146030103c40d0140c50340c01380f080100c8081c1995002e80c9005000042c20f080014006460103000400816024200141c14103104c1000366044520031154250b80c11941100000c0c0c4080f03684202046101c9040b08120400601c4102d0b510f0302010400381000802840300716007168001c00d591400d040d0442d9400781c06151902 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 289117526 1250 289116276 289116299
    0x60a0e030a14010b04090206030a02070c030f050105100b18010c03051c0b01020f03070804030311070e071e0c02030705011209050303150118060c0314070b070e0a2909060c07 76
    0x582240565081c21644c03052400c050103600022a40548110f14556440c410032000b07402c50074040700e5009e90003030000041001c100450007003074094800000c417400c0800e45141141699801030b44071030404d01c1140b10070300615000c00303c03001d028244a441500a480c00305c0391791044c080482074036160315003024040c00f895031000700404002e80032190103607011140766949000b03180000344880c00030002400001e105046c0c50a0b03500140d8115001c040c1c4400a9034a51201101d030140014140400f03064030074030841101c42114414100403090080d660082903d0b080c0c40d008070382c1407001c0003043d40400101a8030020101e0342201c01c2c1c07070312810b1402c6034000d4954030072503440c006000024a640c0c031402032112502211816207416412158958040c0e40f014100142c1d040c0365078046c06403001042892400903c1040c0381d039250141d41c000d00302003041d0248290403040c6150704880c008035034035040c0d550b103032010407044c4c0c90fa5486071030700c41c00550f40d03100304c01c0d0284440c090200009003114ad404e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 289118776 1250 289117526 289117553
    0xa0f062d0605070803040f0203071a0306011404080d11030d0f0e0c120304120305070c140306010b0c0304061d0402070c0e0901090c0902070c050306010807080610050a05060a0e030a 79
    0x20344039100318956551088030b0600030050042d00740103040010500281c0d070413642d04240c4c3d102a00361002c1c0ba984045074941088440c904000c2c1c007200208000325982d100603008003000e40003052500b0142800e110a03516144841c804042c0140c0c8501c12055502c2082581c494001d01241171000f41c6070001000301404d140500c0810300d102d419890155460722410b141e0503c00480011030810303152086455080004950030f41c24002c0800c001c0f0f0125401401003409084408070a10400754420203051500f801607110fa026010144086a005900842150708956132460072441020b418034040c080f401d502c0c0b44c0103074817034400181c0b0070412120329680c20469240c0028460b8560340d030074480e07007600d00c1000b00514010881c4402d001e401c08990140281c20702808041d8032640d1510b002c2460620281c00441003030348101803c1003218010400c0f1988140c1804010a12609e40000705800303180d40c1c021ba5108a0001c1242c030040f62182d4217490380390a008040340d003400c0e100d060010714071018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 289120026 1250 289118776 289118849
    0x6020f06010b0a270b03040b0f0a0504030519021f0e1b180720011a0f03070b0a0c051204090609200d090204020f0a030606170a0f06 58
    0x3480000a040100748041e1103181c402904c1d4000c108000c032014040e00600f0108034101c01d0200701c008154030248101031881580b08544465003400c201100074907a41f00280007480c400d05100400000a0f44081582e03002d820b03141c0504464070452605904160304c07001814690000542c007060003030620340251814401c070000391010841e9011821468089000c3d43d580c01200000c007003010000c1081a0742d41c032182c50b2400c00c000401c10140200b0300f500f1101c131140c40d80c4d10b03003085050945c0a9540307070300c01078030455009801000c60008203881e58118402c1e0020100045a21904e02e40a100018102c96110301510720f50707241240c28104a42082c0503058829141c070301e01007422911803207483c0900c1c0819200300c071032002e810408013060307218407a010070f02d684a100000c0140c5690001c3d200d0b1203136042c10a91100c1c900480201244c41c160302c40c0c0c0c01c2044207212101c9280c40f13164aaa0072020040000c180118a2403065010303003910340c4032030907114220a144905841004d4401d180014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 289121276 1250 289120026 289120033
    0x4080304030306050303040614030a020903030a02280b0402040209030c03030403060c09060c03120902130e0307110f01050403141504050a140106050a0b1b01110c06090a0809130908030106020f 84
    0xc680c400c5c140e5174080e134000c0740046509000d94100c0c82180b100610f030f01640320400949844040c0c1e011a045070003003201d14015a00603a0342c0c100840004c803c0a0b036120013030b901c8071034182868442000324900600040d024550002c1d03070100d6034409000c4071940420107421240c1e034507920b00c0d01c90020304264600750001001c00c1800305003684070386100752220b9015a6018250084080998028115600c04aa009920000e520003421032030103154441a0b8400c080c40c1c96518900303001469201002c1d070980b00b002c080c00c3c51412130381c020087d1000e8a4102040f850800c540c800700c0781c54400d025141d12440c440300010813041000000d9044074040c1700305050348200003d1310010342030b61914066a0f5002415203800d014040c2d003031028240d026150b030503005804030513a03190750844119081102c21400001000355030b04a041001c181c1000402c0c2c014904541691220117080c024144d21030b1103988c640505590511181c2c11511100e50407503629956541d4402c8040d41e20702801e54186503501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 289122526 1250 289121276 289121279
    0x4030803160804120e031c110c030a02010915050409020d06061101151715010b073503130c06030b0301200d05041419020f1e0f0609030604080304030306 67
    0x18401c50342c69002d00d5000070800e043d25103d940603200d40d03001344042d0760540b04002524407400000c5d0340801c0c8a040f291a03520740c0280341d1031000d00f0102c011100038000c0d0302c03040402d030060342c0c000c60340c03c200c070111044031166058003481141c1c20301c81c1c1c0e07024440326030001c0344082c0c0000080c0c0c00401280c0d042e40301d649042d82060407d90983e070101e0400110030340f0343c44081048401e440c08000c09440c0603015140345000308010f00c04580400c3c0c105a072040c00100c0d0140c10048125000d248100010340f080301d07070603d2841308540341401d0141c012544280400801c2d081d100c44801d40c0c5000e03030b100982071a030a0f20f60100038010041400507a20a42c00c2c601c02d1483c0b028a070003214910040b89440354540781d0680b01a2019010161088582e501c80c03d00203000c3d94000c8c040400359440d010030084280407640104840c050920a0591094601d280136560f018204024030010000c00e4440b04d031041c01388030008400c0d020320701100d5054003c550030001001109401984907230706c80d450410655 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 289123776 1250 289122526 289122571
    0x1508010e012120060304050721080a030c050d02070b22050a0f03180803090a09050f0a0f0e1b1302030103080307050c07151808030a0507020405040507050604030803 72
    0x3089000d240c188869100061021882c0c104a200d142850389060440307906080011581917402114240c915800034881802008800307855400203007035040311240c5400d080d03290104580302d081e00c040181507541207201074090080c41035800000854100715141d454505181000a42c2251241c0c21890080e8a000c1c918078010010314643e6040002000600e02d10b03030350719540c0c40c1700082c154180210074a441c2543c018550414018051060266845024480a010400342280c020a007014100010040e40c1200d40380c48545c070044400020400741020364507a07008084944c1030320601e0040c50200020085100ee0f600d0203254180c64001c0401e440500c0802240800e0200501c0d2146c10804500c0182c465406000703100040d2060740d110559a551109025460380200310201c1ca649001c603030034807084281e080080841da005140b60407214103000b00140f14000000384960358850204040c441c0411101010741006028641c0d80c42e20f9050103804c1c1c0c2c000711144e081551400c102104803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 289125026 1250 289123776 289123799
    0x50a0603140903041d19110d0e06040f0b0a0f1109130c080c0c0c030a03030905060901140106031a0907050c060912031902090405070305010501020f07230a1508010e01 73
    0x1700d80c00340b442c000510300401c40010555401a204021003520001804018191842201c0164400d521283c0c0c2e12104490b80009a031b4400501c0c200380d401c52010800840c03407001d59040c0040d030041849445d0b55940071142e0092054008200820749480405005e000519004101d4101c0440700c400c2100741200c010010b4880f810303043e00c0000d144002040080e18104080c009980400040c1c40b501d0580a01092400d0042c41d01035001a48840c103500c1403002c02c0c850160042d03c01030080c4807213404503001080039003041c401d007005c1603507428441301e80420350404603585400c01406039441382401c001c0200560080100081c5c540290b801007007603404000b48110000803400354581c1180c0c1d845500204101c1550b0403010701c9a02013082d0800c65480303100d06031140c211034030002025410720b4002403801070160060003542d8001c0c0c030b003802074084030342c0840300620f0425080f00c202c200440110f0040c07642035004150b60300e030110f1100c0d038060300600281d050300c8841d4044500f0741e1ba990000401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 289126276 1250 289125026 289125029
    0xa0c0632040510090c0e0f010603050606070309170102040519080d020d0c02010c14060f0f01080c030c0402030a1d0304090c0527010302040f0320150d0510050a060314090304 76
    0x2540d030003d0360895545811390001c4008900610241e0009a900d8100d00d0300303a801103c001500300003034801403140d25014407a03c0c1c1c10030030550b05a07003040119903014100101e140510744500c800040d184003140025011207000c1c00e800317040250f021144000514540c902070113044224002d030b91010508910005010014881d20303a911a408031690b001910001035801081c0c80361861243c2c1170301010001c20400d40034075452282503a1615016001e66003012042e00200310541101e001d09646950006680c0b844400844006940703444614092000300007121040180e02c00045100040d200040044c02c101c0f040d00c1d40c1071200c10108c68085070f01348a100d41c481240a203200912183e03603400250644800018100145003d4446c800c034501e8460660049038842c10002c01203001e00c2c64980d200c9007002d0143c45480c00084039200748a0140601034a000105a44100160040742e08003a41002804040c203100c4201d40c86140003400b0304101080c0040540058021401c0039100004550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 289127526 1250 289126276 289126283
    0x405060d0c140303070b090a14060702100f06050a060503040c050f060304140c04053408010b131a25080301180207060e01061e0503060c0a0c063204 65
    0x203520904021000c2c001060610007070b0b405100521101001551350025035014543c0c2c0c20007007101d41100e142c00103085d021250791002c10781200c0184410543c00148050b40d200110f4004110b010010703c0600040c0802c0d440302da406802107400061341500880190700a41c050540c0341d80c40b680321001d000f10705a6058074550030240400020303000c5001000c3d01c0c00141c00e0801aa04040d11640c000740030f44505650001d40810044480805200c8802e8250a000d03c0340c1007808500488500280581e00144075800c01e1240c00214180940c90160f83c02c809400c000764040f840d0070080c544041c83d1781102c000804c240311601d07000303441a0002080c0064266000341c1042c9507a080000d64140d24218884c00c1881070380134050b540028005000f19007030b00180000000d9002c0c0341115002e84101e00501070548a0602c6800380400c0d00d01090781c5600c440303451f00c1c0d540d50320340690017100c21891415000d0306241c41c001407a01740d9144040310300044410300c0c600900d9441000c604171070074001506d005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 289128776 1250 289127526 289127543
    0x21302070b01120204180305090117090a08130e0a02040510022b0c05060a020c06060a060f03020313020d050601080c01050a0905090c0c0d030506091012020f1507030e0405060d 77
    0x10000d484040c210814020304c003030404201520480d140c000c1d80c00d035a110440204002041307020a55900088070b00c010303420110882c049080c00c0c101d0545075020f91101400509002036003560255120703203160018503850202981500e05008810000c0d0800d00510b4451681c40003540c645510000700c40c0c21303c184000544a400e0b4110340412001c1070100c0c041c800b440f029200c01d4020540500849200d01c3c1030038405030341c1c1d83d52078054500744000100b03054810341520109104490780003c43d40c001840c0c50030f00503966120301e2040c0c0040c0d07210764002944100135401c1c8000308440803a049048405403011078610b182d01c030005540c40d018211440380060710803d0200541e2a140c0040303600940f894410502d131180f0b88065038100f60348000c141002c00d031100c09001a50a14000e1940d120070588240c1006a0034036001d04002c0c070000102038440d5002c100780441d65030320b0440020443c0900d42d201d03580d441c0305241c00781100e4034081445104070f1402c0002003090601a14690900b603004884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 289130026 1250 289128776 289128779
    0x18020c1506331b0f0619050415020313031404050105071112011d0c030d2106170a0203070911030121050102040303030603020933030115060309021302070b01 69
    0x20318a442180141c01850014248085071184000078000c1c0f034200244280e00707082142c2d82103141d241c8030002c41d80f600c0036030100d0104440c100540d80300000e900703290707000810140c5440c20004a0413a212480986c0e0034030020520408020410b1800c0d40d85100e91103041c0c03c4600c42010b04a980544d115250104404010389800125000300c2e071503100100504460365003060751081c1e421150510840b039001400550040f6541c001008003040007041203004081c0188030f104005c000c1d660700d510860380402c000700e81c1c2160324003d0304804060711041301800c05600700342508582e11001070209034001d024070200451010854010380070346840c404401442d591070000c2801901e01c40b021480c2800c1c0c801c1c041c2c4c20025a00b80014801540260b44c04a801800c2d401001034000c005019899040f0782c03400e0740b50f06c0c002c065a5654244002d00b02000803503155402007405098820800042c40076038a00205400b0b415030f0080c00c040340241e07000cac2c201c40786000b131701e0080b8860302201a0103148007100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 289131276 1250 289130026 289130059
    0xc0b0c0d020d020607030e120d1d0304080a030302210c032226040317030f0f100509130503070507060f05120408030613090b04030e040b0a0b030402010918020c1506 72
    0x280032400d00c47c00c03c0b90158000d8205290030b542107810f003c81001d4a4404852264101c0c615000445288a028600d040d01d4008071542c0c41161000003402c0c180c01003080c00800444000240042c402d00300010050315008030841d002e44e004a8000c1c0045608002a0222080b83c00684044540c029120350389c0d6440d02d01e0b0402d8442a2000030a1045020000440003d0084510101c079245c904070300c40d01c5e130074452085910124024000c125103a00d2004004294503168480b1301198029100c2039016141d00c0011020081c0014014299200018207403040280003e401400c5400c5e40d075405142c4011380f00211124804c5440c5446039808680105000ca20108000c60300715400604058104a4401c1c01c10151400308005550001100042005164100c0388044040004076020044c282c0c041000911406450241c900c4981e804400507045901484110014048820340030040d8598445000003960003e0100f04241c0182d000913200b00c800103e031140240700040130803030700303004180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 289132526 1250 289131276 289131281
    0x5070f200304050d0309050108060d1e03120c0503060a060c0201020d030f021c0e0c19060e15070b091603030e04020c0c1c0b10080307080c03070c0b0c0d020d02060703 73
    0xe00c080640010000000c1076566003050a06452281d15003070801c624040000d080d0f207400070071090045480c2d50350074001480300040034402840c400207903005070a00e4201254915240c3c1400090586800068240d02e500310021318400c4404803041c444a98031943c003100c1d15003440f80000d000d030344040803120040380203030403200c4201f031001c00042c285544044e1501d0a0001c0840091b4416034510110b07e02c0c80d4280011010301d4070a42d4040704103c002200a0035019075403042c2e9007001455412281c150352002052900c1040f44000a9203603070603403c1001c60500c3c1079991324424402d244200e5001081e1040760740071a6056261481c548500c4011b000296008200480c07075402040b00d648050b075103400d240d00c02103407a0b0301f241c803541d607903441c0c02003400b0406401c3c8290081e407800108901f5400004035882540d000e814192140c07000c1d8241c51841c0541d640c02000d0082d0210003040c84500807000d024040964000c442a00070000c501380e071a41c1e0b151100b1350050300007800081201f8000d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 289133776 1250 289132526 289132577
    0x40209040609020a03061b080402100c0807081207081806150609030a050d030f02090907030213090e1b0105131707031b03020f12030306010323091005070f 68
    0x640703020030788240c960b00140c0c00c20110340040790343c155144056000d501d000d001c2460b240c005420500d42a06140d000584e01400c402005020442c0e40010882007203040c105545a0640c040c0789a9124040040508444503044420354000340064000032031014401510b000b04010150240c61541c8500300989100c0041100b1641c0041e020025000b5070380701046451180380c0244058240b2041c428001000d071440001c21101050042c00100015910f00141580125841c180141d58052500a1524030a02a404010710038900156206681344c040b4085014ac0d40c000394681c84080000c00640303060141480039000390108000601c00343d00ca0a03403003854107284c032040314100c0b5680d94030600003005000da42440841403010410450401c164000711401d8101c81e0b01c4021481d84c0503e0f41c1d24000107100504158444443d014000001e0140300c000400c20f0501581514200d20090b81e14104000300108481c030341350018110320300c90818680e0800c00c595942105099905440c030260188 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 289135026 1250 289133776 289133783
    0xc0313050f1012180203060a05090d170a020310031202100609020705060a0507050d2d060315051f230609060f071a040311010f0203010f030305130e1e0a0e030304020904 74
    0x81513690000340c1e804002d00781c0314031188200800c10f13180074419542008021180c00c4c080c42588103903800890004034180b0340c00304850000627165510392001011041003940042e0081c0030742d003003d01185034042005201c8a201100c1849201d6407000040200d205209014041d908003078040343e551f410303641220b9003041317803031500b1800d00c00174000d010112011aa4901d24000540c407840260308c003484900c43ca11160344400700407603465510340d200c0001e9008000d00d015680c1d0f100103210807007144411214070b007200b002060103035100c460607107801034560742c0d0302c05003e0002441c807441d00d17000084401d03100000c0d003d28107200c4403003074082090f0001d0390200e44031100460b84601100c0110000361140c2d000b695241d07002404030401e20300b100e040e200c0e003035a03040c01000103010303005038250520202c0741c0c10700d0426a1001c1000a9003236007155900480c0b16402c1203428000216a020140760000300c800d00000b0b099200c0d422910201d425800c50b491240d0014030004001d4640280082c1d4403502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 289136276 1250 289135026 289135061
    0x1302010f1710080609191e120f080a1a0f0105090d0303240f0620010c02010605030115140d0f0605010b0d1815020c01020c0313050f1012 60
    0x40704040020282089403030140c00c014240080003c8201004800c0d0030490810207010008804030000c001046a001c016003040070600801310070903000d5070142d00c41074104580d208103058540380141040402c200c5070001914010100300301d003c05200e501d580c11281c1142c43c40d4403040505100c000b245030100320707041c0281449951096150900e000380682d00c40c0e580000c144402c0c1e0380c074030350140f42e1040303003070100107000d070300b8491040035480007420345106040c200d00360102c0a01d411740f0601000c0040c24a542001d0303078038402e2901500000d0548104030000e003c100c413007000d160340004a0740724101029100070781146030b500300300905480590040b41c0702c06841c41542c69610544200303a020003c02140014000c2101c50203100d01c2c65102e590a00c2d2030000b4009889034812150b5040faaa05800e80c001110780190500354119001861284162504c90341940441000d0496621445000c1d052460310340031545814040c2885170000c9444204551034040010401046250482e01c40501c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 289137526 1250 289136276 289136297
    0x101803021203090a0b07110f0f0409050604020a1e050904060603050f0a17040602030a030b2404051009060c0f0501020d060b13050303040513090c0521151302010f 71
    0x3100e150003001d24200c1a030065903207440900034000701d0610f0343d200c82107030b15040c02103800080c0d18034480c1c183c41c0c0040b41c2000c0c1200b800300c0000c000070150034505a220f894414042c04100c0040b42039481140202c9119400f555900a8600c01c142440120780e0b1805410606010626107a102190094041d000010390789441c0c2d0703100c61034100080e81c840460351104c510081080a800c02200505995180d0103040c5031820360007039a60301504800b001419101d0b035944c5a00c1d01c074481d881c0301891202041041c0d810111503080800c6e03000c1d00421303004904041c05403100c00c0c000c86585c0d048640720703622004180400c1e12a60100010139000b00c0f03040d5020040b0048080c00c0b030040202501600c03102980e030b8041100400032000d4a503014500036001440b0400c0640e0720034201513014414028041821045450802022001d940201d58400200410351510001d44940881082d00d0202291401c2241301800c4440301c03000c40344607001d034a42c08449070055114514030a8030343d4040c20708a1040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289138776 1250 289137526 289137529
    0x280f080403081b070f0e010b16060615021005010e130512030106090501020d09030c090b060d09060203040b010f0312050c2d0d050711060a140c0606041a10180302 71
    0x1a804099010000c00d2620191841c0443c10303c4800d0050a05020380e030401d0386070106030034110300c0505c40d0481d04800807800d40701d403031807101400d242640d112004000264171188948032061040d00303900300502c501c1150fa010345145110340c5040e19610542e100403960b40c107280046203206420200c5060007a2040c012820302220051070203081c007506e0305400e0504000c002841e090313025000b941001114003041001c240088110016908038141c0420300c0724018022503594820089200602807411081200b8061154003a50150388680702240c82c9984c0c1d49402c2c5c8480c856808042c0034480b22141000da840e00950081101043ca0000c0e15041c90011103045401128052204844c00c403500079848030003014000030034004507a050040c21710440d500d409a001d070780c0b107042c180100400a0705a80d039900844c0c900000c5000310070011b540b803118460058aa10081c0e480c14022400d142400718680381c5c0280000b0034007009000f180000c02003020803148080f0320084585100107035613020025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 289140026 1250 289138776 289138793
    0x30d0b120a0f2a0e240108090a0804030503040515031905060409050a05070602010c0201023c0403080409050f04080702190b160c0b030106090e0402040f1409280f080403 74
    0x11282e110601d0f4461314000c10401c58420003007855000e0604c0014404461004403e00701105000f840c0a0300c076640c94244440c0750130000c240c043d1800300d0200d800810040000002c0007a02c0e010744000e1101c1c0d402c90740c1aa80303408141c0d6402c0d2543c4c144817813864500314592010364031603002000803130740a243c1c2e1903160600c040ea40060381d060300165000d0111035024041d00071001803034402189801d00c1c400c0c00c4000900d00d1030135004500c2e882000307070360108007258182c9075100c00c50480650381c035502d18098103ea4410f04c10100b0603428900064800c0144545040c07041e034114580300d15090780c81e400c11001651155901844c0079075000d001c40d00303c9040015003c0144a040000c01d141c285040c0b11078080180e60000d940c0800810041c84403d038881d58900444460310072076408c0c0d84031803000030042c0c42081c000b000c40c2460880e0020b001003100300070300d01404c02203054070003561080d00420300c0380310010380c4d03a850598040c20307200002d00e951603040880c50242c0e040c582030607140d030754030f101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 289141276 1250 289140026 289140083
    0xa0315030c03060506181303050d140702030705070605160f0204060305030c030c15010f05091e040807031b0209061003060b030a060f0e09060c1b0f030d0b120a0f 71
    0x8481e03680300c04100310750516446c01841000116a0b8100504c0c0c07141050390619051100102040340104418040b4640364019280394031406091003054a00030710000e58a40001e24141d8182c42252800920f41e4010380c211141c1122400010340320042356240ea524041b80000200d810969810002011506c140041c0078a034030408051903a407050700b048507240c10b0b05c010a030300c1c0b2400c04100400000568201d000708543d01a652034145a895403405100300b107441c6010703185600c0d020300300410000e508000340602407103903c0d505203207420141410844559420020340018411011030124030301031421045502151030b001ca52207132640510402c54105645107580e90f43c843c60140000302107c1079a1000c1c00071141070000f24a8104c0f0641d5690710040c0c00d82c42c0107038002540484881c41c07070341456441442c00044034907045000741d11a0b6a50300c4074207085c04407480c02c81c16645a1814100070500761040340700405821580b600c4000901000c05000c4a5015002e0b07201d030000c103010300d0881c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 289142526 1250 289141276 289141283
    0x1030c150c200a0e150103090201050d0c2d0f051b070b090f060f090d0218070c03020708030903100c0309150b0112050402090f06030c130b030c010e060a0315030c03 72
    0x440900c01c0350b050108181160304601c905800d8807041000e2921130710320040500c9424a00811400c40e1070005845a02c10001b01c11400341c101400155081c0c0c201316416003c0350300c00c084144400e6110b0b44003424800e00c04800002540070100020030510a4010380b86201c2004c000755250400200b003240303000c101e5030040b0120300020520760103a241004183c525118103945481c0380001413050740d40148100c4040601c40c600b01c1c014203055480d0450091213200c2c004005ca5403d007060130000c1c00c0494040002c40062266500c00b080700305000c0180e85d510140500100004580012114058006400110101341d55085001e002c039100a140da41c0608900c00002428003d000004241c140801030789052242071106000042e100c40c3d1030954850310001c3d009c0012380341c090010b411f03c0c03151a2a5036002d405412080201503056100480802c0110116074151104100550b50140c00500c00340d80b204042c0110780d003141c02500058201440003441c0d681c803d40f603a4400f405000103800c240c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 289143776 1250 289142526 289142573
    0xb040915080d0c140a060c0809160b07080309012007050d08070507060b010c08031008010605100807230d05070e0405040203030d090212010203011203140301030c150c 73
    0x1103a0340099011600050701d00d44014181e500484000648079208030311004040d000031041c011400310040c0401702c0c2a0340d0014003400310140c0602c00602c4000107a030701000b40e010798440041c1890744030b040c080480e90b24030b5110b420096a0f4403807a28682009103541c0316952114050582c11080d41400400c02156590300380e11170034142001032802c030310307611110140400001400001c50b00242330345e0780d4561280700410b14804250049441403d00310008200755404005d02903d10404030780002582d180c8002045443e03500c8003044070f040d00c8814400081017049000c03030402823041824514040b11400000f0b842d000c04c540c1c0d409d880e40501d105240c90ba03500c005100006601c03050b90103828204640612103420942c00003500ca125a1181c8054180d41b00041d03000c5480c0c043c0c803152443e070300c64000c40d140c4d030b0344a4441c50b00300c4003540c04600140040205481f40c86420054034140c9800a0741103844504040c3c1c0345481c52100c204181c20b202c94102c1d0900007400c0c8006d1101390a000300c41c1d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 289145026 1250 289143776 289143791
    0x30708060f0f18030409020702130c110d020c090601081f03060f050601080403020c06030a14010902030402010e03150f041502210a060e040b10030c2409032a0b0409 72
    0x10000300c0702d0080d10741d032074150700403d100c01d402c035000065034181c4400307140040e0380e00d20300e200003030741c82e144034800c2110141030000c0f46110542219401140c00000001d0700c10080d80404202c2c0c031010440036044c0d10004403030205042e540315150300c9610848540d0f041c0303100d4400c50012140d9800c19401110010740b030340c089103480c0340c0902901c0d0b0411000c0c03e00c1c450743d06241e5800707074880500312161801a800400000c215480b60740015060b46e459541e2000e01d5611030910901a50046070203074085038a0b206010139034280010382c4500b032401001c201c1900c2d100d00070b91582390035026005a80e166000800100b203015a03100a0010404170503148d001d02d680007243c0c50b400e90340184a07484642c41e0100400c241c3c5010134410794099030010b006602d6039245005003141286070340016009121002c000b04100c0c1c01008000c182d0402a100c03a0740c40e03410240101c503a42d13014040108600707801d080540103901e602002c1103134000c00c0100d076004031740c81d00ca492500d0f4019034031048005844804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 289146276 1250 289145026 289145041
    0x4050a14010315050d0b0712020706020c071a040b070c18021305010f0504031e0c030503030f0f100b09030109060e010b0f0d26040909110108090a020f0f030708060f 72
    0xb000402c000d0700700c2d025400d03441c10f00054810558000060403c1c40c11b800083c00c014480d0030911200c5040440854644000382009030003502701030001e0550384034500f8042000d84120342103803101c041c0c3c40d0b442032402d8109400021503810120b0300f280e800b4100c007404642100302800011b20300e04441d03801038039a0505150104c80c02219405541440040313041690416403000c2100c00ba290031164004141c90003040c484600d4031112006411190603030750110802101000460045000300564005502ca1210440f641c08007914100c658072100201000032041320701c00342c02410001400028481066201d5209035210070205070956595030480d401140340004a40d6042441901e0308820040e490380e944068220040c8581e0702030080004420801c0140821107000d01b401120500180565160520780701207001a074a012910150002d103001030006154103806400030003003c21050385005202528082144240e0980070700180031455039010008240555503082031107130245020740 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 289147526 1250 289146276 289146281
    0x50f2b0f020f010801140d23010212090304080c040c02030d0906021306031422080c0c090106030b0a0e07090e130308070c050606131e0507090605090109030f0804050a140103 76
    0x640303040c07012103030050108214010304420310086c10758102c124018142001645815028445101b03a4090b90100d450848190054550744140707008540054072540016900d07401140550402a84145d41000031403030a908400ca07040b01600591745006112013112044c0c90003440c00f42c030619000542e6080648078031861031700a0610745400c010b61041080c454070f0070341028205c410102d85070a0103400301f9040c09018801c40354081c040725602d0300c030441440d40392002c800c2601d2040b10034100001d03083d8028086d40b110800020011094241001c4410900b0b80300a0000030410480390b40100342c02c0071461016005601d1403241c01810231542ca002008400f004003040c04000004458200040d800900150040822203203400c0d0307110004504002442d10f660701156044000740c40d45254540b070350005001d032855560712407801d40ca500741503419101d01c24000340000d881500c00c1000c940701001d10042c2034401c040c514940355a44001030036280f03094006503140009081e114003a0b68251 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 289148776 1250 289147526 289147549
    0xf0a0315050d2f0d0507091a010503040b07140a02031c0b030303220c1e050321031905040b1905070e01080901090b01080c030115050f2b0f02 62
    0x46800384002c00d1940c0e25410320943c010514298000079005205914540c6021821180c030003801040c11110345040c0160748007813a108410f61a46800d6000b00609014480110b01c0c1c00c040c0c5501d890340e00d40307a40b0210801801004034082024500310005000131020003804446080e90045841c3c0810108821428500500c05281c1c0d61034030481d0300d1a03031004001d0b25480740d80e0500035448039060000b0300c280c40008900013032041051400c04507041d4981c425495241c2c58101d10f026000e5242c4060540d00d0780c000b841d21406410b40d031300201c03200c40403000459011040300704440031a038201d49018142d4005403800c0701d8106101080040080801640461b6203441d60018001410b1030b10300a09080707d0518664104540034001601510003500415030b0640d220400c03654640c3d5800402d92107a000310340b480d11035401e04140c803001c0d00c1c01c204440c0940f0001000c001810440800f0000a000503841026020001c001c0350b8541601c0003418003002e070302540c100794024900d403042140c0034200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 289150026 1250 289148776 289148779
    0xd0809151c060f03170a030f0203010f030614070207091d1608100612060504020118030501020a020d0207080705120a0b0c07060b03030a08180a0b0a02131a09040f020f0a031505 77
    0x40c424101301280c406400da8207404802001c0716035a2075190812009400c5541840c0049400000001064088406070350102c070f02403041004044402d0301c9401040030f09032030140041e80480c8040c0240071040d808081d82901884100d2150f003031161480d0300702122602c1c0c1d5000401d9101d0100032888080c0901c1c40306032071006040120a0500c1c80e545112400700e6005403603240e682c000074046900603e0411558070003060342c002e003280d6070306d0005d0203903004660346801800f42405031950070340002000300035145035201610080d4100400d00214040f07003d4107501c5072060420800109000d0303800e250281040a0b000d43e1340ea40203080a9041c0c460703240c66140254400c104403042954456491504403603d26102c0800f0b007001c120440c9451100c44001c0c05200d181030502a15020f107074000c050b441050084640f4407a5208c1d0b00c0049400702c600320099040007005415411f1526038400301803c2c0c03403110018108a409c00d0284081d4120750281c101084e500d045031320a0190700480900107000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 289151276 1250 289150026 289150049
    0x1308010914190b0a020901050c010e06040c05120a080d0b130c170403020d0e01020304090c020601090f020301050306190f06270b2124040c05010309020d0809151c06 72
    0x20b0740c80c0c040c1141c006003003404070350307020454051b968881c03000c9403c0b2101c480024000d01c00103281aa483e0141610708545034190113030300003501d06090303200c82d02191020000e411450341d44e4031135001c558401c4e8043c042c480d58500c4000c44e59900d4072040c1d0082c83d050180001d040b103080381c025255a070032420383c00d181c0f03120400b08000654002206800f02040d4600084000c920000607451070013240c204660450401c000005003541c001441412211041000e01c0b542888101c03003401c92100f8020160541c1148001a01d45400c4040a82c544a102c00c0c0001d44070660582035070840e0499000103100554481c0c0390b51840e8552220403040321900070042020214803c00128009001d5078a42204138000c1d1329400303030103070a000c001031845a02c241c80b00c0941140e01c2014000804541c112a0301c070501e9030201c0c41e03511078800d0200c401e82c05800c1079035004031780d1200c000503000b815005a01c07072082102e6040c0008800c010b05030411202141801d074000d20052070081c0c414a42080c01c01c80c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 289152526 1250 289151276 289151323
    0xe031206060f040915030c090b0f0d0809010c0f02031506041506021e070b0d1b0c030203030103110d02040c0816030504081905040e0103050a030e030105040b0105061308010914 77
    0x180c90b01c12101124841e43d400a0603858051000e10150019840035015455100b40000c444105810249004070111a0794443d2181003042051403001c4a0001e805640d042c00350501c1540a02600050140151041c800c2400194000317803803d5040343c074101c12801c00700d040c040d4600f410300922054080d03c00000c0015810040c00941d034103020f120061307020084008103c49242d0901c0b010002d41040c031011903a510b0f6582000340a030440101e01014031031011074003503400c0d01c50740001100035415400b951442c0d2850319030040c200c07003401c5840d5204040c0030ba20380051341c903441403010300074417030f201c2035080d141900c0c80d100b0447c2c0359141c81040c0f60130700b8100400180c1c41c0382120b451400050419591101c000c40131034030b90081e42c101d52103d290b15000401448000140b40003018429944c20400d035101c002418280e80040c0d030018031001803071006020324a400c401806042d142c080c1600c09d064ce41d41011401e560420301d040e98000c00582c62034141c88424044011040c10001c110075040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 289153776 1250 289152526 289152547
    0x2010f0c05070f08210109060503060f091c0e0d05010605041b0909050a1b32030a09020102030c0703030305010e13030f0507020d0c27050601021005190e03120606 71
    0x24031188001d104010004017aa540400b90400102803040c100102a82d0b43c3c6500594008001c14080c0c0351181c8a480f00190003603200a0302c00e4850340f9044007034030204041d1080060603100a04128092113003d404c1810780f5128a8410302015000380c001003040ca191405201c221919541c01240b90200d100440d20811303001350030081260648032001416503600d05024005281d407010003903208507441c120024a40d4004041d0b40044800e106c02c2d02320f4401d01640183c1d00084500c1380f02c89010034400141040d08652007645894010b00540e442c100c5844a110b0800080b90401c50120390350f10018400340144a0781703240d01c440ca901e8515403800c000d03140601454601941c25080000000e0700108644a200740300c185191f004025400841d00c402c1060f030380328502c2d1600440c440700101c120514864500a450181006030090050340c02030303496882c00b400008040c4280943c0003060b208101e5020722402d490441104061354480a08212942d0030950140205100e0303403062201c00d911 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 289155026 1250 289153776 289153793
    0x17010c031d07062d05070501050604060e060d02010314010807061205040c0b0f09040c0305090105090703020a180e0604061506050913051302090403020d0e0a150f0207080a0302010f0c0507 82
    0x43e2101414a5120002415a4018101080b407501150b20208003042e0950380c1d0043d02600c00385208000901155036580180b008841151003280b00c41807109022480398140a25000b060314010300d4041580e0700150f0207403100380030a902901055210390070400c05568481d041d0300b4072404100052207030781455100c0341501c0d4480d00070502e44171000110700380d4900092003140c90105d006081440300100027070000d40100000c2318045901c0d42031000288900002080a0068950044c40c10310b400d0300705000458041c4200000e08c840359510b108072036054104000c650300c524070502d004a585120707045c0c4c0d115001d64542c810414410184000c0031103a5400280d008060300d407c8000401d030b52a10000c50f59071680600203034000303180304180000d0680c045000b0300e52031000e4850407144000a0240f04004800e0701c03950302440b801e061805038007445030b000d030000c1006920407240d01c40e448801d03c50a2640c0703407030211f0151390740b800500660070150081c0035000301141011414442c1a45a0103c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 289156276 1250 289155026 289155029
    0x212030708090a06060b030a18150230010602071d06100903080a080405010b0d02060d0b041d060f150d030c24051e22080417010c031d07 60
    0x140000c14000030200c80302000a181c03004e0300240280416940ca003d40c00c525070042c2d034141d4106040c4030400c4115058400c006810366440b0414840903800c1011000007900314402424295603c0714445200c0410240841c030207240f080c000164039490b01c3c4010b80380c44080d81c441d0883c00d01400c60600b40400e0400c003903a00c0710b010f45418120620280046400b002d440d0001080c400340469506419035001c15440d00c1076101e42c00030410f000c0c00314200b01440b215220300a5000c8410004070120340b070702d50030104181401030404503c0fa4046180070307950005596140e10140d101400300110400e9640303403650488404500c10310b8502c4a280414403c1d821800042c007030086400ca95020040c3e0907660028600705071280499150b521014100a0f20090380e80042c41141c40300b60046202040a003207000705e0010f8084501c82c0403803034a64000306091601582c010f81c0600002840312001d442c0307404499010000014502c000301c401408880980204d00c81d66500340648405042e40044d4420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 289157526 1250 289156276 289156291
    0xd030506012102250309060513050607080d0501060c12090f0603020307270e010e1e09030904021b06091f0e120711130e06060108090f06070f0e01021203 67
    0x1d0300702ca408030030b0310080e1255076869940360609602d028002c11200c4031220580d4803e6807a003140035502d1401711a280512503401c504018600410071082c40c24038001e01e03c0c6440350043e0b50502c6a205021070440700243e021030b0229507a84584c10400801c00c2d0781450704a420f0034143d000b64140300600c0d1648a8500804090503030010100741034501925000d2040040800080000740c0325071085105040e4a103d81043d00d10b61b00004910088410000c41c4030341011b1400010020100086840541d03000d050000d950100f04110032440d01d5900040c0300701e069155a0403202c5041e03d0707000e840e016006009a015070041c40003a51a5a0399000212041c0314200002c1140019822814145580d02000c0c1c0000800012840f0401a004c8000c0700032400456280e03031481c0405400c02c0680d84c0c5402814076641001c000641c4079070080310704640100c40b12049400880d8030442e00d078a0b140d81540e801d03001c11160310007031400961060252270308070001e20240c4030b4040200c00b0030015010180040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 289158776 1250 289157526 289157567
    0xa0906060e130207050601030305040501030f0501081903090906060503010e0c07211115010311010c050d031503020613090501050409020a1a12070302090a1208090108060a090903030e0d03050601 85
    0x12510b20b075501654401d680001c15a03805517034038038010340140c3c054070035a0302090900d00045100402403041e14101c0315150080c10070f0b03180011100c0045002101e04605015280c2c10101e40c8445621901d8050815a00c3e5550b4a504050400f182c88400400d411045001041180c002a42d0507581601044140345809038020358054180d480c08601b030301c1400b080c41400341412000366030604a504903402003002400700e0240e0f400444900d0008240076080c2ea0103408400c409034800d074005902074041e0351044114a4607640080c0c007030b40c0004000500606615020310020758544217543c018102241c041140a100703a0100303210b03480c0d43c401e40c20403110000e24180e8610f0101c0031540001044400c1490303134030b04494007400a411420f1201d000c0c8034a400007081d421032040860114540000b031150616600700011140104000c10b0590810101c0c1000684030f031980c020914007038481d0b01d01240c0b62865a12461811070703a03000080406050506201c01660041d1b03002c1c2c002e90301000f0382d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 289160026 1250 289158776 289158799
    0x702100b130c0201050619060507170f030c0706050109022b0609050403090311030d0503040b060a080729040b071e0203030a0e190b0313050f19020a0906060e 69
    0x38405a4030344204040c41402c08144400c003940c19071006110305800c4a403045541e0035200341102244841c06141d0205004008039004a54502010009444500405031510303115084c1c52401d604240c03400c2204c40008031f2000c0400165019050141035850000c504080800000480c85800c6070f80c88c10380260b4014050084800039081207002d44000c65050115050601e00140002c41512080d6480151100303c0d07107440c540403d416040a00c0c5070b66490864440fa25104928440036084907480070f240c1c440002c1d01c590501118004003441b0100c00c400c1141807032481408151140c0003c4540403c00061269407802030a5402d0726400615010296480e00040d02101440540113503051001080740608642e00107498030340d4200c1550121078164200c585020034244502604014206c00d00004500c0f003007c420500115016500712008490f40101403800d100e20f04422000d0344030b48050b0341c0c05604140808400400c0d440b03901f000058603003c1c0050401d504134152903c2012000c03007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 289161276 1250 289160026 289160029
    0xf080c061b0d02211e0a0b010f03020a0c0221073507030f080414011b121418040506120703030c032006190b150a020f030a020601030c05090702100b 65
    0x1d010440d071181c3c02200e071617801c02c80b0049002c03c000d541840c0036460b12600240c0ca68030140120f58034100c040e152904c082c407407900180c0103500024084010054984004400f50390382c120311000c015100901e041c00a031702222064104210380d08030000d580f081302e0020303c82688281c002c12060740a0710000d02d0b004000340c502c900707241e080e41c000362450fa6154012000d000807500200200c4030061f44201d01c06000e4001550b05150450158149010140035400490344549040805880714a00303055050703c0c0c0741422019130440d000207010400148000013640c10b082c40f41580241c41110b01c00c1c800301424003405e03035034411360100034200310310846114100b5011781071004010030003e1619059000c14100e5036a181d82c2181d10000c04034058040345060b1643d0700c581d859540d8042c0c6103041201d40d03440705030040e60001c100c4074114801c0d40d204420160050014114803990365014298035491410030b004100b00d00e8205512500550003440081c58000806000b540c200c6080800c80950180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 289162526 1250 289161276 289161307
    0x405060418140f07060507140c15090907080402010c0b04060f14040212120f181206060301060b0315040917190809030315040b040e060109020a0315030804050d06090f080c061b0d02 79
    0xb40d10740ac49034840c241c3d17090b401c984c400b40038001d10584040440b55038042c4210b801c1407054802a0104125a003010f01158007485000c0e4824007502c804901004030418141c100e03108610440160341e810002e00085241c80c0400902c0704040e01c0040c07490110510240d01e5a21a81c80b2946240400080000c201c0100381204000800001d201c40c8a80c0d9640004c20f440b0300d012911144a94071701040410391000c0841940e000783c02c00304480b80100414001d110091161810603103c00440c4101105d04810110041800c07140c040403182c0c2040d1108005046600f003d81100002d400900070405500008081d4440041e0126008140488031801080c02007a0b80449a103030750092000119055682d03070014480c0304461754040244481d1150030071102c034800d01008000703a504010400142c036140040d542e1180c0038603c00500c030750482d82e170101343c20000e2800b02c4920001050850b01908140b020540c0b0001d804520204161840f640c1e40d2984681c4002c80e18441d404118085407c4091 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 289163776 1250 289162526 289162543
    0x170c01060810020c010b01020a030207060f09030c080109021c0f031d1206011e0e0105010e0a080307031d09071e020106030816020f060a0206060405060418140f0706050714 75
    0x6800740e07120a882e12001da00039500074440001ea540c02c110324071845520015102d41120f8050303028016042c14000100e41d9119005007801c200039844002002103404c40440a00524aa000010301080c0603c1441050b00011941d828a0a0302500303080c049180380c49541001e07545803814030680c42c458840a6410b00c000c018864000d403202504c400354400002c1c10a044c2d03a044510041e13048080340c00d0b00b1101e81c00d8020440550041e400400a9500411605091001c01482168869140c0700c1d014995004000e00350000b4051001d5403030b400382c0c5040c00c15400340007920048440d180540c806416000808040e041120361520a442d11500c00c0d8040000703954044c1c05280d03502d000d0b0010700c01403641d042060313219071490100c043c000e10b01700080700c0b00d129041e0042c1c191503840e6020000200360003000250000c1c2c8130030601c1d624010300d000340522188140d0303c0c03200129032a1842e81c40c00e03030b030707402d2101d1035600c01501406000d8010064590303040d440341404100f00c2d802038003503042c000c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 289165026 1250 289163776 289163789
    0x212060708040b0903040803120c04030f0503070b010e012418030b0f07020303040c060507050703020904030302070b0f0c16020a0f0f24080403050d0b1c0203010b0d170c0106 76
    0x2044240400980e00002140c000c03070040d0b0b40801d207901c460310015201d114038404c0e41100c0e44104510820030000300c07480d80d88012030000c080e04065407030300c40509040b85000d040391070f60000030303460042080c581c3c101409014940300907179840d030400020380401072803d440c0000810800e0008228248505184c1000c3c1010500e20b00303410b581d0346004034440c082030302c20b10f940c0c51a4100048502d8400002e903031003103800ca01140a9585032070015030381a480300340d065078603024044011025803101d14160b07005078031955005945801e64140002c014101030041201d112500050000e0400f0080988035040318a0782c807150803141510005154140551141c074a41c0241f48000407103802c13155848040390341d1800d8181610900c03508028011300203600f80c001003580000403a0200c2d02c0f6002501c42c0c0720008800042c4460001c8c0000c0081e20703460003003007001d48403051120450030300307000c2d88840c000240c07044030320704e200b035a181400540e4503580085002c8000c540708008070400d40008000b00013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 289166276 1250 289165026 289165033
    0x1e020306040b190f08010207082b0204150216030203031c0f0c02030403030212091f360605030411190b0319050633041701140c0301031e0212 62
    0x22002c281c103d40010900c19506a044241400640032006008a0701040d600006040c42d0000d24003a860845031451500b16403c02c0c003802c0c51600e01d03c1440280302a000400f01e56841c0822400000c1c902400c2c08910610306200420410041c1c40001c04e0b83c90701c8440c5290503043c2e00704000e142004010400708600b14905208035100c000e0340102c028003e40c1e002c0d50903034500001201c21201c49105400c40b0a402605c074198000c2101c1e8008244100c0b202075181229500c44400c0c1e42070340d41035082001089103080c008180c00c042003074004074030080c5010f00f441c0b400c5182c15122180d586a03480c1007140203000880311108032415080000700984001a081c0ba1241004d142c801c00401301c0e022a00c00003850a004902589000e070700001d420840b50341100708400100d0810500c02180c07001c011040242444040760304c0300701550780c02420180d00b00002e0780440d078100c2c250111a000d00804035503081000144040340092514610480c2810b0400d00d402c00c00e840407030240403035855510780360700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 289167526 1250 289166276 289166299
    0xa150207050115032f04050a020d0c1d0307030b01140f0a140f061801030e19050c1306060f2703030c05070906060203180a0b040b04090c031e020306040b 67
    0x100c40070700301c3d0549015901071100e40070403002e4100120841407804440700d0341410f0038001d0340390a4204580c40706841c40058244012a01001c0c10782e03508140440c04074040c000d0301044130009509070030100008070000d00003545580c40d072201c2d00d0018003c04200c460100c103101120b440c0d040f4034828201010b13261034006581c800740e2540424070509031034414803001002c02811b10303000b003e4620b2443c202d1046a4030505240040d0001e2101003041c462a000342101c002c480901120ba0f00c3c3c14a00640103088052010020410551200d1031000c20b607900e000700c2401241d50044c901e481d4052241031400308039044035081d8170215050121400c2400200a0120800d5404012407440c07074854000c6a040c50745540240c0203032071560103240c0040e4418402c5031161400d001c044500880003030721135548503481e060003000650040e04040c0c0c1d00d1500040c00c2080060510500745c07190711900c0c0410608c2040382641b8160300c22820601d50094001c000f041180c0d0f01d9522071184103400400c14a11305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 289168776 1250 289167526 289167551
    0x5090f0a0302061c18030f030b01110105070302040611060f0f07052512110d0e0406050a0608040c0603090503070308040302010b190f0801090f260706091e02030a1502070501 76
    0x300e40140d500b0400f18103000e9017110802d080d038100400954151101410010800c20440041c80c4400a143c100014091003025141c400e2080c9401001e01ea41d02503550350408201401700820800d2200042d40142c04200d0070140f5800310a40240400b200000682c94070f5900b05e455005e07c1810448803015200b21541e03039960980130000246c0b003405401c098904901c01940d807252079104080150f041890745210041c4030b1030760138012110081000690507100d1012501c2401c5541040010812050070f20003403000c00d150541c010412881e091204500c103546031038581c024114010140130074031b4081400c160003034101e5100f80390098151200b80c507003101c00a92040076442010f0700c1c24002440813840c001c06020300310030345410191420b0009201d944140440c88807400c0c0c1500d070042e410064109280c843c0050401701d002e541d01007506101c60400003c041c0c22a6028101880140e0241e001070b00c000c10030b540f030190812100c0c03041352074072a2128003912401100400a505e400b0b00042ea1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 289170026 1250 289168776 289168807
    0xb0709030c0905040c090b06040e0a0204060305090a210c02040c0c060c050414060a14280e09060d03021e0303090c040204030807060506010e131d0d05090f0a030206 72
    0xc5a009205a04010b80c0e2054014122141a80c0c05012586158018000400160001d0807404030181c22945802e03500c44c039001964401f81c4066a4035600043d08010059041c00707105c0c0c000d200500501a0b45609136034280907650700070030b0b1206028010f04a40100340c01045c04034104ca801610901403007004a0b03005103000c1c105041161101d18110001701142d20a4080d40c0c20f446580c41d40307074410620041003003100e070030400031681040071031003066a400210001a02d00e2100303600030004038002806510342e8801c1a00410780400421100c03031b48050b0780303002c051a00100203407102e04106005080403418162003421440074544218007503181a50000021842101d1400c10b4030030505503042000142c0c03081d44005010a00c040c0b00c0c07500461403035030040350130030710506040091000000100300b1b95007002d800104039503a0761484c42001110100800740c40020700028241c0d02c0e1400130003620307500603820410b0007019409082d06980e12080040030146030001d00217a240c04549508070303070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 289171276 1250 289170026 289170029
    0x31e160f0302011401150c050307050106060809010b03160b070c03050102190314100303050307090e0c04030506062d0a171606020c0117280204051e1005160b0709 71
    0x40d80b80140d1401d0340c000700c4c9001e82c140da0590742d1100f800c084084080310081000402039995002c20092900000c00c00d04c140c0b0010034058070354504d207142032410903084072072111005000390002c8144001620b1900d1040741a02c04480c42c258032080b060501c09001c008036080280700e507100054007038111a15400c40d0006403610f5405014194545222440424007600c6095681c0c142003020320000c0e00030000785502510302d00c0c0040e2960b540c0d200310090000155030000000e00700040600610006000701ca520400070f880546ca4018000c2100c0d03075440c02480d00e41c880c110143c03400d111079900c44403142d0041004210b54400c0c0d01001e28500c0c0c5441c05891095100700c880c0c07400151a50000c80e0700b0030081016111200e030121f00000e44400614020452040b0201c9520010f84013800e0030f40044402500c1140180c0721420071081c400c0400c1c0c415a9149428050400e00f00720b0b560b03500c2e001025030300e289000c54440140e42036814500b100401e0050100704414108129140d001a8240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 289172526 1250 289171276 289171283
    0x180b1312031a181503070305120a11120a2a02040b0a0308030a060815040809010503040f082106241e030108010b04050601080402010e0f0a08010614090c0c031e160f 72
    0x5040b135800c00d0303540e00d40d03840300a1082c0c0100c940020741c2900d04001c0d0140700c015061154262914045607403c1000f89071000512400c0491020b082c954006881c0202195007210300001000c0d16403003072440b00445070000d100c0d589644c000107980e1100ea0038100107541c0a0782103620f90600d81c54440c007030516070052860510030b0700f00c0f041c0001010011180550b40000046140100c04801140c0a0380020400d480301c118407613402002510b01802496003038410f01910010f500c200303a011107041c4e0080c1c03500e0700c1a0300e88050035482100720200100c0c0f01d0b180b80425503440d2861540403e017000701c3d1480e5000d102001c400018004010f4000c807d800300708a8040113250341c0c141c0159105403050b41c0290004043d401d058800741010070b51207440240c0145405540365a41e0f03211400d6039815042205c180c001040c141c3c075181007888596030803540c8081c48600303005000a9841da24050340e080804030310426030007001031585207000c039000c500c0c1d10312402e00c8211032420081105658003074200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 289173776 1250 289172526 289172551
    0x30203150102281b06110601150512041b0b0a0f090b040506070f0209130507120201051905070f0c03120e0906061c180b1312031a18 58
    0xc02066101003003d201501000721441203480c00304005160010905404440c0c00c1c600c265407202c0b813546100300c0001803440e42d546ea56801d8011800d03d040c04070603840081c1c3c60003840311604559801005584c04211030040706000c942c3c3c0c0b800e0120103502034031503818078010403400100d407420444000300000e04443e180c900700d41d5140f090032a6494164170405140346014030062104d46400c40003007400f139020f001d00c4580c100050300000c0013044280ca0066146407494004400c02a05000d01b00080c114401d05400c1d607125030700041c28a02c41c0034442105001c2c5e051000f4015401501a51442a0000c95414224450349028408010240005d4a48405150b1403080880c403c0c441880d03841000351102c500d9498840c01e21640f9080520700d242c03442c1020b969200901424454400000815424225840c089040030b07040d80001a02d0075000210f41d02189010072146d41d002803241c2c4181c030340040c4c54900421502000540f080c1a15172210354800c0c00c85240c0c8074110300e24020700303581084 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 289175026 1250 289173776 289173811
    0x1051507060903180e0603030901030e010b092a0403050c0906030a17040303082a0d111c050c03070f0c0206091e011202090a0b03151309030e10081611010c030203 71
    0x500c5d131401040b108a40e05500c03c01c0280220b510a42050b1812070440c400410b03606540720008501220407241c1595010403900082c1504403061880d40d0071444941e0303800e00d050f0840d110301351105078190009000b40304410204429880401c41020519042502c40340004542c28260045600c68031060f000241802d01040c44041c3d040134003c6001c0c1002e081c04d903240c0c22600510784940040c0200300c01e0550b241c511942c25141e1100814100500301c0300d91846c80c109002d52802c1300c1c80906040f0000400340304128059402000382c20080c802810310100c02605440054201d01c1864481d6810602001d501d15080c0c0d4614100b10100c4000d80702c54416402c0d2042c075000300e001e0307002d403558400c007090020022100144011604148810441c0080da400d18007c00c806035250000c000c005c03591040076406040e88503c1c2c50700b484904950105d4102c4081c40c00174210703a409001780fa855030664807030009080c0140300c012186540c0e44024031440d000440060001d41045501694041d542480b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 289176276 1250 289175026 289175039
    0x917160b01091a090405010204080709061502060601050d0e0307061d011413110a0801020a0210050a02030103110105031509090703030e06030f010b031012060606110a0b0105150706090318 82
    0x30b140943e03001c0d6509400740050401007280703142014209a955550801002c903c254081c000c01003d007900200104126160408009403880c15421300001c540206d4140f00d0145c2e0f010081f1103103601c008001141010a40442c50300310300c02c0c2c6000a2042d4a0a0107092540700910007001c2140b0488008000b4946081d491004403007003110003104054400c80349070001007101e261505000c03805000c0380ea1841d02d07074080c00e0880e407103105044050381c005004590b40b00128011250b01c440282c0f82036045524656505042451815181e41446404000583c4e440c000c440a49041007000b040640c0d603041c00032000e038a40c0024042600019100440c040c0b4034141901103d020b03007929405410b1236880c0011050103a00040c1518100ba00e5440000800176049a4024189070044000080451a00c68060401c1c0380103420381501c0d8204031540c1d00071070392800b07800341118810341c0c8610f0000c01c51a000c1001d0700c0703800001084a4500340010727082c0343d404807004692040d908107060009850300d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 289177526 1250 289176276 289176281
    0x916030206030604021321051912051c060915090209060304021012060306020910033602060d0903020606060720060d0c02010c030b040c050306040917160b0109 70
    0x69007001c03041002c56410309181d40180780b0010922200741c01d80340c4030510f50703441c0f514814514204c2e0080807a80740900c4018401d4103c1c480d0000364551003000603a07203180c0035101001d0428248038021803645c9043c2021000c96040f540d0101c1d04020300e64891400e00000c0880141e541400a0518000708440d85240b00700c480300c0000410590540d03031142d00b04800b080340101030b0010006c0348a401501c0307a000e0701800d4040e5124510160303d8813000382c24840c0e1411000003140405040030500070350303d01c00c4220710b85c01001c0705501c4074001500b036504107040002e48400070340000c000034a200142441da400300c8420313882607007a117070661500d004012983c0034900c03000d0104c5803040501c0c002440c6210465154690103810b06081410fa442024201c41800300f807040580d4507003418059040d414441d0100d0100d088400700a401d074800401003503408001c0100d40204d9581c400101440082014820101510f40e003a540d2410503070b6010708454940d400407109942c01c10000701c0c211130f090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 289178776 1250 289177526 289177529
    0x120f2610151106151806060f03070f030506010503040f060f24050f010c050d05070219060c0203070905070906050c12070507060905180403051b0610050324130c0e01030b0916 76
    0x44c60301702c4500b440e803000583c805c0c024195917400801002144401c0c104040618482c3c003594031210070501000002a00307694008040c507040081c100708010010b800030324403104940d00b095000603000c190110201c0207001908031091404801e0400c81c04490000102c0c0e41036030300940300041c005800c100155444280341c0c00040064002c1c1d6855010030344518050800c86000a00b03041150322058086025501107400100000b45e8004d149800c1d4141001010000c10104408000d1450b0000b4001c2141c1c0d1540a0f07041000b200041450207107030100000681c4251590900350382d036440b45001e5944011910505011030300c0c5d580c00103918600705e58003201c0681081144142650340d0303038084505901040104a581c0442400c05499010801507140314800546401501505180406140001e5101a007030440c0d5039a00d036509078401260719640041155503041c010003207628249410400795048102101503400001052012613105c03030340111608000d0701c2416000c4098105403002c1c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289180026 1250 289178776 289178779
    0x3130906090e0d080403030603170712020631020301020c151303090b09040e060f19060503071a07050607050d0b090906011809050a120f261015110615 66
    0x6104010005805013580c194014030074600040d03120b881c1ea440d84030003250b0705860320b10424041010b9040000c450402c040424103030004080e1485c0406c428110f800a40c01d40c200e22088281500b03115001c03000541045a6004009640342e081126042d59501340c122210070400704180d0100c2d03403003c10b20800340c020580583c0d031881000d08000f080c01c49a404645a80d41196480c10050f041c2501400030741d00070043c0f11070b4410304d410047c2005505000800b54021010702d06481080155000100a02251103041c000128644180b1208071240104d41028009000301c0c4108041603510500620348241d1200c02040444180c8003880715070b40e0226841182a4442801171240e03030442c4884415811081e4808074041406035122401c00a00b0b52040301c0341000c043e43c4005040d0040719083c444204e905d0030740c41e1030900345d8010700303554110f00003804e82e2255078001c03d18800380070031510060241c000d50450304091844c00103182d0010480515254040c10f004101c0302c40c00c401000b84000c80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289181276 1250 289180026 289180033
    0x21c11030f070908250513050a051026030c0307030801030209010909050318120a0804050a050924012610060203090102070303121803050d05060a050d08070c0803130906090e 76
    0x1e00c3c0b9250401c5c4500c880010410703407107000c005500c0e66000918010750b02c2c51030380801c0a060640c160070039680c001d00000c059070168801408202e0b800c0368101e061164404203071541e00c019803421400c40c450710150182c40e0000117070300014540c200340030a04992094800101c20703a640d680c24011110054001804ca8100b00282004035440c03a082c4415910002c01c00f08089840c080407500c2c128100ca170482c1d9254000c00c080155280c0482c3c030b02d00425042d926401c80d45003405582050f4000000e105040b0310184e2071121007a440707003000c0400d80b01502c04e05c00e282c1a641c0080b80704a00112903000030f181715400f01080b02c84c808410359040b180181c008040160540c3c0d0705607071803045101c030b0450f11940c40fa94505075904011301101c03214003946580d99110441c0c0c03c12004d40711300808a6001d82c0d412401041a5114100c1c9800310b550801c1a8648a20700b0345032803200d0310125807020100b8880892001907100420070480c00300c8060700300c00c02080eaa50041305041e41e500000c10f4403240c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289182526 1250 289181276 289181293
    0xa0e09131b0b0a030b090c2511030303010303050903010b19290a03050103020114070c090e01140411010201061409012612070611030415021c11030f070908 68
    0x402207403441095551400e481801c1507150002480d040c1c00c0b07030340c0d003a000903200c01e507590042c18440c2c03120380c1040a088480e4a4038291030ba482c0f806403d140f0003d888a0031b040c11031001d11040618910f68800c000382629a603580d41d0070002e10b240c1081095911a503e000d6500c0c10620301100061008828041c0c155103503442d00c01c1240c0b03c1b030186244107007440b44014505a1644100c40180000c854640300001e855066000041c210792041e02407030303e015400c00c5000d0100e0459490901119034406001c103402c80d114000e00e02505600c10030384c0b403091300002840200645c0144002001001303a000f00700c603035034465582d411505660754250308140140018014000c007130503414010b4030b4900000301c0d0042501d05e02032401090301078400303110f64089070400800c0240c0c00f84864100400c420941107080540700c001e203545401440210725a03000510035021803030b82e202c40d5600c00102000704800300c4200d140302c419500444181e20826180d10000d00000e0080785c1000030744280d8402445c41c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289183776 1250 289182526 289182533
    0x207033c0b0f061903150212090105090f030703050904050a0f0218040b0406030201080604020304030203070203070f0303030c0f0516020301110d050a0c0503130b041703040609050610080a0602032a0a0e0913 90
    0x2041070f40c5071b442401340c08000a442d020040c48149005a01e6034000040c03034940094410b0400325030301c9600d00560400c10800c400300368000d0070b65010410440d4001a942c0b40d200e100802085414800480c803400429000c05030500303400e2004c02c9040c196803c1c03103415080010441143c20500009007c0351822001c19482e040039800303540d000d4440d0040307a14211181d0002031074801346600110340e25250100500030154540039401100ca002d0034100c018600c42113025100d409270380005000d0f410b1400c0346070259a0300350045205030551a007040d40e140280000b841c09090115031481c0c0460409403004001840f41d811a4421494203036000c2d084401680c4003113540313401030025148070300310070118000d0425140007580502e200f0500001c6c3e07041549070071400c0a600510304250740d00d840808000718000890070711500c1d54400401030742c1e59110400d54a04100a225101812079440c011111154003080202241da03801c0e22074200034208007081295a2404450821a48854002c2103000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289185026 1250 289183776 289183793
    0x30d0e07061215031b1e030201080c0304020a1e050f0f0a17120a03020901110c01050d0e07080703030306081b0a0b0705032809060207033c0b0f061903 66
    0x1030600612500007180e49440310069443c1603100c001740d02500d2042000b604503000d1600341980d41441c880003001c1d2458001074403802c0c00230403154190034000b001800715512841440b0280c040700201404440d1005110000000e15000311b5020b130220703002072140ea15004189007194240200102c028605054485010380380309a0301c3c0301d071486050328400e1500c10200203004208070a079001a00c0340302c1100010505c00e075891901c001d982014808200599205044880032001c13424003041120014045502d00b0f050341d88000a6800b6003d00801050383c9908041c044a801e030081310054900c900c800130a50550001c4e09522403030383d000030402d01d1a0702001d04202c44c050f0f01078070b09040c4994071560b20403521010070761001d038244100070115070b00304543d00d0207460544010481a415642e560501d0030030181203004901d0950940b00d03003101c3c4100c155004040e6400008011602490090075419064800001c13030301c2c416000400754200311182540401c00c0070b014101440c51a202c1412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289186276 1250 289185026 289185041
    0x10903150902060f0a05090411030702071502190b060102070e07050304020409020103020f130f080a05030d0f0b0315070206011202010210090204020d060b07020f04091208100f08030d0e070612 84
    0x8100005000408130300203100c004d07000841e49501c9090303030307505100100b10445100c01d00d01400c00d1014024032800eaa8006844010b4038210700c002c07960480c8980c010b0b071a240d154030342100507490243c140c0d41000f1080401500440c003e80031213503900d4541110340440181240c00c40b00041c01440040c01501d01a0406545e0360b00606006280c005200304000312607000c0c03060b030821a45030400030002c022403200380c070009102e00405008160269690513403240b0590740c0e84c902d003d842d00506e20400d030560703010707202e0040010115080f00040002d0713003400b8102203a051001d40604000006c0a8410204906155a059018250101d00040032400030684184284e810503800e1140100b4400c062180101800c0801d1a468442000c1e20411001e840c8580d8503c2c000c80c240320147c00010310034580070f441040035007001e904645d60000040840d2400350b0040c1d0841c2180a000909540b020004004440221905000c580389410000350340d04010705c501d06c002a50a00581c4070075241d6400281d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289187526 1250 289186276 289186279
    0x3010c0c0515061801150e0418060b180106020a1e03120905011407180b090927100222060f05090112020c0d08011e030204110903010c0f020705010903150902 69
    0x81015000c8110007042ca40c01340c000710803c0886070311141a06e034004001e114034002c100c40500a8260341a031524000b180c0084c003c00c00c5444420b44103a990b034840511821640014500c0c11030b40c0c0d41c1c1c100030360710710050350152011145084803c0e4110340130020b1020003030309a19007001a100713455200c0001c1111450584d100c2d541d0300c0d00b4440030300321414407038060440c1d50b403200d4407105034101c40c468904582d070242807a84020010300c10705440b0010121340c00303280319400034507081c908070b80c104c145910403001a82078020381c2c00c90b1840700040d40c003820307000d6a0689180b40402480840d40164203403401030750081460711090350510751283e00207210946040c5020741c1400c2d0700c02c001d5010703a00105044481d07034219080510015500001d41801080700760201b020b0b150b45110740d101036140c640400b1b4001c90b00c504803a0700c1840f240c011107080d104054001c01c00c140d8580300040240300c0b40c402d6100140180c000000e020b612951522081c0c0f40c02044810240003142d100000900045808a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289188776 1250 289187526 289187539
    0x203070305041a011d270c18090703060b06070b04061a0405040f0605100f0b19050f0f09181302010219110d0c0e070503060f0409030e09040602040812040503010c0c051506 75
    0x4207101b2420711400426001004024a42c015040c0d04010118845241242c81c40900c1c03404c1120a000c0003918070122074005000194a000200c013042c0240302d61a4040c145051410620042118a034411545c1c944a4090322125101c1c210030001a01c605846c06000e00301c3d00540003001c5000c0d80d11642c3c00501d9810b024544030f503038007940c1c5074400c625132000b1a20a00071840080c0342f00d03203008007460a00c80b454a180381090085600c009070180c00134450f044107000c10045041d0700d6071000e01e92034400345401499586004000f851901c48150001ca005000b09600c00080c0e200c0540100151b66000042d207290796860030034480340b0000520260307103a240040300090740103410498035020b1603450b0b81e065a203141460030300c101040c5204c0c0d103901461402d1080c60100307a00142600d4480000c4804002940796030500002a0050380c00c080901d0150110150020082c4c02c01001240d000b43c000f07126010310248199103540765010701401c1604007182c12001004204030180d07105c503005201c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289190026 1250 289188776 289188811
    0xc0709061d2703030402090112020310020a0207090501140f0102010c120203040602090603040c031a0c04090b03070305071d060f1c060216030f1701270f0203070305041a011d 76
    0x80c11100100c448003070400c0c2c00c000140006d60604211250150404010001905403281e002caa62400e6081002640c00c2d40410150400744c03007400041c000348540c41041c801540c480c90b85100282c0c0c42006248260030100c0c115545500601400544041d04c1e01e071900c405040c41c0600e0040d600c001c1c011512584d0821a180d00382e500c84000d50302890040607411035142c15864100441c003404007504020501306e40c20068441314080458003034070000c00020807a5180c21020925125036500018a5402522401300b4440030301d13884c1010400180c4031fa8500c079241d82044c0078800c03142e502000d4001c18a01c070000c114952a103a01c4121078810380c001072078951400d210030b003180481c81c1d04800003020003514004041d448100f50520411110640b0065494841c1802207072820f4000d612080e4000c07000055240d52581c000c402078a5403060956603844c08440c01401060115070850b250000056407400003c1180660303070588051b600304005040c001d10030f000300544010445209400030020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289191276 1250 289190026 289190071
    0x302010b10051b03090f0609011b14010b0a0f09151e06120203060102151306050414010c0207032004020706140106030c0215011e0f0b0c0709061d 64
    0x41c098007450703040d907070203480d07000500d01035104040226000006034418401c802c102d903140307800c07290301d550201c1e0015a20b6507070100607140602c1e100000c000400300c0180030428044072010990440400f0b0008000000b410303010464510303171602441c480f444418400b842030550b2540807180d00f950010000d04c2c0f02c1e0740c031000c41c104200c120005051994445000300030003a04843d9600f580804541e05500350700e841310000b56541c0319203124910500940d03011030303044401c2284045840e9000360081c405d034234060034020541031042d160304205600e0009400e640303d1011410724181c0c2d81c004002c4440741541691035107001020b1034030581c816420488640018194031445000f0710801024001c6ca61501c0300250442d0400191142550484864142a2080600c109066850481d01c803018a1030f000501c81d002c0e0041e81008144044104000c503a541880002d020044001400c8030006032b01c40a503c400ea90b0b280c8604005103081b10340f45215405040c0300564008003011400c01298107405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289192526 1250 289191276 289191289
    0x10020c090405010605090a0b01210612030801140916030203090715023d05040501091b18110a08180115050f03070f0509090c0306181006051005070302010b 68
    0x10740445581c3e40d550360400050401700c01c4158050421503080183c003e040001a000e0100300c00e13841004038030180d901c012021a580590003410070030011415002c900d00d00981241000e005907589101d2851300b0041518004091500c92200c1d008250081200390009901030f4001401d00c410501805401081028000101c6103590109a0042116020610411800c0100c0b0414941c0d2a07a040602030b101e1034850000010700c01000000040503070302c504016005010f840c41c0104405c22222a2000100b00c041910080e9001c1c0c4807004441c46403642e10004031003401c625125101424407000f14218003070410340d40e0000f80400000343d12219007021030300b19070701d40c001ca01503020200400c2c0480e040001030704441c2a0141c005120403400c0291900036603819101d042c2c4102100d100054410324103000500100c000541187c030076007894034550098142c080c075280e402c1e02c41c4490110700800c042c0220400c5910141a00c0d80d890b5a0034421030b040c1d8803242e800e070150b640f0f4014503407481c0c4075403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289193776 1250 289192526 289192531
    0x220608030f07110108090705010f031805030304290a0b010507050609030d1a060d020f1b0a02120a12110a08040e090f0d090509060411071b081501030210020c09 70
    0x807907045544511501d400d405020550034040d04020a60081000b40341d400034035034040d14401d0920280750025280100e005c0d05000314111b802d80b095040140810400101031405540f00388105607000d61000309010100c00008001041d484a0501041200c0d4a96228031141241803400c5494089183c81e8140f820034140d07103280d1940c0c0001605c0e0400b0b406c61051290040e1800011040084848001081801466070205119900244250340f440489045402403c0075041c25411600c03619011384d1611007582e4141d0164161a4030040041008941c1c490010703070060b01c954941c0c00c0840d0032224840701c401c003070840c0c3c4603106039000031842c2200038200504441d4117038480380c680324a56074200807804c071451005a0050b0300401c8207640040b21602994002d032808900e5a580100050150504000b1640300100000e140b07018080500000c1c18000c19100c141c4c01525507803001d132030344d54003001c0070b0b45040d1039140f0041c801454024003201e8184540d10460b900024464002a03010700103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289195026 1250 289193776 289193797
    0x706170c040e0a0603061a031c0504140301091502090103050f01050916020118210f05040b0d061212090519060302030406022203030f080f0403180f0915120222060803 73
    0x72a0300c00324a000c1000151503031581c009274086561811014005006038041c00359400b40f600c41d0981284c80c02d50101d0551500f0040103c0180040c00c07500000358015076006002030f04000028241c2c0507904401c5041b9000540742441d0343d51000c0309009042c41c0054201c046540720b1009080030620054025400e0b40500b440d0006000b200c4030900300580c40309222070500c02d0310f07a6817240042d00324065400300d44c7c2004920390b0381c24201140100402081e001710b511050f001700c046050001c4000491885021a200d40641c580c8840400c0a09049050a030110b86000501031000620036000340d500144503200c090700384040345261420510400e0f80c07442040902180030001d0551000303a01c650f0f404d040c20302d0000c1d070508444444207404014005418004401c2891400b840740d07003103060080c9004c0000c0f454503a29250504050400d48264030fa00040a48004c80c01d0299400143d1145900074104005051000040c3d0201d40084000d131207031700d547d034400050624040c8000d203000c841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289196276 1250 289195026 289195061
    0xd02040503010b030c0d120e0a1815031e0f0204060305010203160c03020a020f030322090b01030b0d020108090a060903030914010b0a0e090313080706170c040e0a060306 74
    0x10310003410b0031507144002c0c8510035481440081c071240c03552a0b01146442e0030240b01d5100400c21a026a104408070303240da501700c142d900d4000384502034403155612000340003e0a010300580d00d0b010921013a41e502028090903a01d241c8003112803000c60004889074490300d170b503602c100140d40002e0304031003003688140d650307075000420070000449080169003c950141401c0041c860a910001e585040e5054020300449942e803044041c0d42c1c080058605000500901c54aa0600490110181000c03032003680201400c0c08040d070750942c001d010b0b00600d85c602808602030250f640e001111034400c09041c0c160745000326047d04010400d1030180705640c601a40340071034200761915112210100301d540300d01c40c903454810440da0b9a50382001c100c044401800301c40310203480304040c45040d841065100e50200341c03003003800204000c0101c0d02c282110116150124105803055030320041d650100d8213604001010070050080340403030a4a582c1148031400c0014803161a903071803900301c8540108040c0d0a82 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289197526 1250 289196276 289196279
    0x120102071b060c0b042306091501060507200402040509070201020a09090b0d111306030c0f0812070f0c030b070c050c060a0c02010c050c0901060804060b010309030f05130b0d0204 78
    0x4111a00300000c2c810751074100c1c440c12080e1540c0ca03c18001610040166404814621401c0c2d000811090300c24000000d0340c1103800c080700c40030b565000d0705669402c0c403140e4400008116004009468103d60416010070a03070450241e048a56a891181c0700d0780181d0030710000c01c803034903078920a501c100c0403134000507a140180c0c1c50162074460b09030700a00d90981455500c0a40e03898000c11840510341c0300000c950041020070016140000071f04000000c03920302407000042c40245081c5104903208900707004a01c42e10f1300c107215210740c1c2c101d5500d9443d1000700500d00c00162141501d0f81d0583c01180c01e0080c042e26961405c0f413400040d501c2a0002d01510303240c00612005029445c034407071040781c1103803804207109005403008a4213100039040c801c00e101c0b42000c0c842e050102c03650881e4002d001c09015a114407010b040c40500351400d8817520b10741144040305500a12a201078603400d03490f02103191a4000c2c0840766984241200100c1c00e40b803101c0007442c1d410301000740101c215a00340158a4a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289198776 1250 289197526 289197563
    0x7030803101e142431030f140a08311401120e0102070614010f050303030a1a1207080f01090b0109020c030c0312040311060405150612010207 62
    0x400300721410006001c0d521104100b9124508110507180a003514940c41c2d4200c01e000c0140c400d003a040b4100c162075130010f1503000d00240045040c8800ba0b111a04652110b4014805070840041e808010b045441d0181c1010200700d031142c01801211076401101c010403400c0d922007000c0d40100d8400c0c0383d04003050b44980140e034020b00307145c08074610047c08031015529281d02003ca003011142e2441c184072949010a600c00801e4000c101641d10f085d000707668a0105150030001012030301c0703403603000d404820004114002c031a00c1110071034074010001e60454403040a0310000381840300142c1025400c80d00c1094260710307801818201000c101c400b601156280c03546103401e05003107004103032441e45001020000609080241815104855001030722000d000d00014034511482c030441c2650700c00850780b01d880d21002030521707214511990740c0b0701060940c0c0c0310441c0c1d110000d0780c005000c1d41150312104904000e10311000c1c0e0210008080c042c20712000c2c07d1741c40c00c982c0610f1096581402104228992 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289200026 1250 289198776 289198799
    0x207020d1e02090a200901181e0e040b041509241b120e07030c090912261f060203030405010e06040302071404060b030f0610020102160b090703080310 66
    0x50301c0380c106003c45d1000801c25481e441e8aa030072002c041ca400705040e4481d9100701d80030540d174080040608000c9032100240d40805030315901881907032403000d41c08900c081c000051240140d520441d03440b801d0311179685508481c46141014100603590383c50443c0410b080d807000e240b070380707814104005010110210b1541a5004420b000780070442405030040b80c070783e0250140f2092101c1c50400500104403034a900c4c182141a0701c09410134614040104a82915a000c603070098072a000164900c003076908180d030304c89010001d5806003914003800201150902c1c0119510054034012210050080c28010021500c42c0d001000141c1c000700070001080070901c44d10012400b8000200742903d800e0b94000e6a45d05107000300100703602403c0c1c0c54401c03031322540c1111006c2d0102c221826201d20704030b0184d80c200d58080794a40d00c10001240c580102c03c0c010b108440040d401c801c0942019445501c0700c03c40280007401005080c441c0c21000000b15402c034020b14007800b00513413100081172908106081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289201276 1250 289200026 289200031
    0x11090a0204080c0d0f0b0f07030e120a0c02030718090c050306040b0103030c0c050303030c070b1b032404090507230102100515030a05011b08060307090207020d1e0209 73
    0x802031041209110340a0000f0740e400500e5404c0310303000703001400d07442d219070f0202c1840001041c2c02c24000c01e0013002003c111a071441100550350401c041c01c510034146503103a445480d45246104100030583e034140c820807807180c03214005802c42d01460b81d1420310070301070f498401084404982d5640b000081040d0b06503600d009040803130007840c050400303803258100c109041c40b00505200701007139408100450004c0060040500030250b980701d180c034003046010b0360300082003192503206c0d80300061502c0030b410400300d01c070340425804030b41941e40e040c01140071101414240c0c20842c45920031511a0380d580d0190014852141000d8501d05141c006003000c240d600740ca410440c044511052007031030340c0c001070244045144440108850f01d40c3d01c08440045003070200c07250075010b140c1d00d80081c084150409114030900c1c3d4042040f080301054219a4140103035405503140d00402001c00c43d510041d0043c01c0c0150004000240c154130540d140c441200c001d0b0b0030b42c2a4900000105000e41c07030301322346182c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289202526 1250 289201276 289201291
    0xb0c0a0b0708061c021f090317130e130213090b04060218180403030504140d11060c0a020a1214030114041b0c0209040309090603140706020d08010b07030c0b041109 72
    0x1d1340c81d8403503400a034901c0e804191980140319000c50060329184030b4143c0c0030003150404079000d1691200c00303c140190744003940b40c2c0928803003003d0000c2e07071103041510b0b580704000c01f10588600040640c00c0000c04240c0c0303600e02490030340383c0034140d000c02ca0f0444c099000718411100107036141080000c0c00340209014490380e00c142c2096620241e600001003902da441603042c9000901c0b0354892a00703846140038070080490b1441000605000315070442d00c08940d8000b40e0003114003076556072040440758495103c0e0200160401d10201c030004420205c18208072203141018241c2034075040c940112500700364095003480b8006805641281080d1003042000c030b4400da02092664126540680652075628009001c0e000d41c0e00014181881550800003801050b4420702c00383d6030307a003482c040811050010581074020500000340311800090044220503031500c03070301c0042c0e1806140d502d0503080340e8030a800780b0480508a00001f900c09025900c6248900380a07031200c4030010600c0303a2035400800b01c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289203776 1250 289202526 289202569
    0x82d0105040b0102030f03010b0f0d060303110609120703110c04051603050c0901080412030b1906090b04030c0303120b0a060519081005120a02040e0105010303021203040b010b0c0a0b070806 83
    0x100305c6d065116045a040d039081c280303840d60300c03007581c0d528003164443d1400031468030346403580200405901c0a2042c8804880c60f040710300503103d884803d500c91109041020640c0342c02c12400c40000d00880003800c004082d0000e0b68004e200b0500406c1c1990300444400480d140c100d204d15003c1509489690f4000b400030246508010b644c500103440000040e00c068181408501080c90491007904541001403020740030003107050180080040ca1150750142602061490304040b4402d4900801c2c1c8003241d8025080f03054852454505032409404090708516181d12401c0d00030158882544010040c0610f607162591501142480c210f02c00d4540c07160010070080d882448005a0700d020110242c4504450f001c00400204031000d18240500c2c500070b402ca07003002c035500340b03580042d48082e048034000e801b41c40d0340360105144020544405c480003400c0d40044001030240710f0f10580904500c80141c0200c03044030140b5150b00703040c110308039810000038410a007000020b0900d59088000c005014030503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289205026 1250 289203776 289203787
    0x6063c0501080106030e0a2312070203030702060c120301031506090b03100c051308010f0b0102160e1e0a0506030c030c0a051c0b010602010609050610020d082d0105040b010203 77
    0x3003882c0018400c000c201034072200d1101c003a0805200c070300902641719564028400e0f0420310880c0006010500412500401c44140c0f803020081d01110380c190350080c09146018280d40c204036407a0446040c0d18454404d4602c0d940784458220015806540121038030300503040001d0084043d107099810116105041c035011502c540c034005002c00ba0582d030031001013102c0102c1d24044501707000700b140f000c42c2c40403409030024000d10194485501d8014404060000c00784600c016030f40d51640103541654121014010000070000800f60754100c04603400503015090316518491700001d06035200743c3d04640d01c1050000c1c51600b00140200d4a40c280c0142550000180c00614940103500c074050040d41850086800345482269030491140d1000d11640349507180c0740000e0080036a4001c041109281c0b81c00301e202d51416018509554180d680241551255070070100d600c0e0502800040c88881d05080006803511121014000e0000486101640d036151404000c1541c4400d0103803419504100103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289206276 1250 289205026 289205029
    0x1002071e080c06070327061b0c02040501140a1a0f191d06040b1b01090506010810090b0106030f0f021b16140d030c0c0909060509070b030a0906063c05 66
    0x1101e180d049204c009403642086c5802d01c003018101c9480c044540c0105e0121042c031941d0800c4881c005d4a0080c4c5e0100826a02c4101c08180f45640b00ba0b0b541d40701241007000c1020098101c80c00c013500c09c8544020f800d00c00d000c00c2000042d001b06181d8811344080d180078181043d0703c021742e044c2000900031001500800800401d0451256005001135030400245e0b620100c3c0120700352054494405000b00000e10290410079183c032020b000700c6c5514010f550f00e1080085150084628450f000b07483d1142591030070741c05900825580f56181c804c0c0d43c4513444100040b55501c0030301440c02030103080050401550101e1130070010000107000c6000c0200105029040a80c1c0c50b00701000015514034922506604090b11031403041030006000700340109001c1101440c640210305010f10444052120791506900305840d21130341d02900003540c0c002e0001902c0d540c02c0c3d0300003082680c007030748000564584401c601d01d618860b01c5403007180304980030090700d906229103e041d82040701080560851a042c0700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289207526 1250 289206276 289206311
    0x9050c04051902090a120c0611060c0d05060d06050412030c080c07170c0d0e0a1d07030506040b06030903041a031b070204060b0c0703050d02010e1002071e080c060703 73
    0x15102c402003075020605454a40b01d04014001038401480880106d00c101e240444024020f40900d9000510b980300a248900c00024443d001d882018112814041002c609000906004195981c40144040c55101042041c4281d5002d6802440c950140450450002e410351310003101c178104001c0c0e150200001c60ba12001652181d90780901449102041805c5400c1d04e405104a10780c901d000c4c1a40d0b075450150454180750030040306850700700c41d150303689003a4407500e2188c0c2c42c0780480c01c030010300080300c491003540030a500a00040000500040c1140440e07010b810488800049500028051042c02034100c00f00d4008da9811042e14a5490600d62a017264500340385030f82004003010605030119507994001e103011700b03483c0ca441601d41e0b4105955540c1c4065a21050307415015601d00111214418000e0400302c1e0303400300083c000c01c40c20b240040001d501141003070f142104030303035000c03107104104850001ca0389005e0848039407500d0700d00b0308140c1000005807881041c94038007000c848a040410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289208633 1107 289207526 289207561
    0x5030d0b011403061f200a111c0605090c120d0e12030405191a13051f210e030a02100608060c0c07030501090609050c0405 54
    0x1640424501c0242c44a580000308160f50030002817801c8404c000a91180c5401509200414801041a00403001e080b6494005003072240a008aa640f00c101a203000c840c6103800310301240c921484071190003001068151a000001d40304182030101c400a4000a42103c08901c00c403404c081c1c8078040b04d814040403841e1004400454180302000da1008a60700004520b02424101084250b440c11403258503080440c62010582c3e04150140d003c05100040149495085e0040d440b40f40c16600c4c0c00c45401400082540818404100042e89002c0c08a00704082207507a0400c502d0021007140c1c0800703a000741012104543c4a4000006003241100b56003681d401c101c0300c1d540354058688610032024143e1003003010401d1040303542c00504008032010201c0341400e81d65a2000d0960760740d0b1500b6a983da6448000700b01340002170202012030300e01254204103d1902c07031a8015800c422 = true := by decide +kernel

theorem cover : BRFrame.Cov 289028776 289208633 := by
  have h0 := BRFrame.cov_init 289028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289028776 ≤ n) (h2 : n < 289208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
