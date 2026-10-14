-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:33.729088+00:00
-- url     : https://prove2.me/submissions/2144427e-8f4c-4cd1-a5c0-5229f8a333dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614748201 ≤ n < 614928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614749451 1250 614748201 614748241
    0x307020a0b03040605100f050409050703020301110c06060306010e040b0901180f050d09080d030908160602271e0105091e04180b0c070305040b040b030402040f0e07030b 74
    0x140050095031210307140d0456000301d604858907800d0202013058003000403203042c01e6819a01003003600c0c03400c00302130000030151380070143c80900c01c90000002688081c895541d681c0c45844480d952144595049803500402804040c080e41c0102c0041200c101011415904035a000018100c1500c0d10003807580034180e41c1840c081c0100380e889080003000315078590040494420000d440807800c6248081c4c0343c3c01028861054540c10440350050b5240c4240c2c0039502d100e1045041a09240b0f0302c012000e241e25020600700e80f0154005010321040c185900001c1040720b00120320024054444042120084041c03026400100450440c11081c0c0c09401900c00301900a0001002c2c501544d141c061600d01841a40703010b070b89080848143c0c07080f1289090955504070654040b0358071750341c94409195000260980c01c001d030601002c2034501c24a0000c02c02050010390150310703401c0500410085800300d6030080b400f545041c94a540c000c07070100f00f03c81120f03000140c2e00741030f0352002c1c0000080c40034111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614750701 1250 614749451 614749459
    0x90d08030106020a0b01050108040209040206132606220f0218070e0a0b0405092202060403050318060309061501050f0a02070f06030c02060a110909160809030405180603030702 77
    0x200341d07103a0000c0c0e050042c90185185d030055036654001920052401e1306d010750000c0d20b4400141c003504040c001410000614909400841d035221044548070444141c0e48444500f980503089500004000c131541001119070304800c80c01000506103800d0351680401000203070f0030107103541555528281e242c0c40c607410a01505032482d16203001805021007180c405e100307000048001c10481c03164401c1da402d0350b1000c0d00450003034503018401480d0003103010300301d001c4070641000040140c50b2100507000940c0f00c0c4004649403030001c0b8079410401100d4900a009081c1031040241c101400121503401014000c1c0080300054600b0040702d40748114048142c08503000260342d641070350f00251140c116a440c0381c0c10319180752906800c030f082d2108141d9003070050b4803140114641000f00d50007890025898601d462520b000d20002c154000411503003c4c040d506900080c07410b20342c06c500d0f03003540070403068040c40c80d090800c400240750743c50050656030074040d01800942e60752420070844413440d400030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614751951 1250 614750701 614750707
    0x130c0918020304020301051812031506160515070c03082e18020a050403020120100e01051003030921140f0d02070e060d020409150c0e010c0503030a02090d08 69
    0x1009000c0a50301c266004c80c000e600e030100088045041c014000e000780c06490241122030880d803d101c026402c040e104016070b400c04003510001b590340500500300c1c52048070b4042030080e01801c10606200b58111030355400d4040c6002c0211599002d2828a8500c6e4181440c00b107685440c1500040316400c13078080004e22540401c5030025985801045d0211881541e84810182c0b0148181c001c1e40036103c1c06601003941031000b40300640c011041d81d00380d40a040103420354a0038056001c0e2800741c900d014031401581d03416803141400d0080c0a107aa20040c5007169601981c41d564000704821381a201d00810410a0205506101c003200e10b441a915045018080c0811603002c40d561131349a596031082080c0b0031558243d400c540041038040032510a0f080121613641d54a040c04404030840c40d0480e8400d655511500c00280c003144081d049211038500042c1c031900d005005055043c3c0e0255881c1440b44882813a800141c00004895004503034010144c1c40c2d181d1000401c003000c0c109440206512408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614753201 1250 614751951 614751989
    0xc050c011118030106050d02060705030c031917040c06050c010209062107090f03170702030102071b050409210e120d080604020903100504111002150f06130c09 70
    0x5010b000800140081400070074642c07010942254141e100b4a50025000e0107100d0140c0741c60005020014000c5c0c045d03d280040e602112401c5078008454500c003500300001200c0096886020311340b0500b4164094103407820b29444440783d01340d8510546041020005084202280030f40698400707150180c42151030f9034030003000d010200f07581981500b10624143c001010644184d440204031228800781d2440f260440e2070350241d02042002c806184c810400c409170040e20248024104180210250404e001000c3d2201010340e81e03552126119600f06520700d00851040c84032001a031056500c05442e201c01141d040e10404004200c861f400b804680c0740a90b80b08010414012050007584c03410703000e03034448080200f00e004000780c507900340d804003202021402031a030101d60400d00402001c01003400c8030000484104a03848007000507081a0001d490754148032201ca40c004400e10300e824aa481d0040c0030401e1700c0112022548003a40b14074201201038011200000a41108061482c1c483c1d99 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614754451 1250 614753201 614753231
    0x60e240408010f0b1c060c0c080d0b0111061608060d0c060203042c04060207020103060b040902040501030e061302091e0a0504050d0f1d04061206090c170d030c050c01 73
    0x50203090700e40a44c101000c1c15601e29080c2e42220b0501d41080c0d0150b0f2202c0300d91102c500418800a0310307414861046481e0002ca04800058104440411004038501419000040416141c190707e40d4040e404070b4140004500c9426a0241a200784e15111440c0c0e5100d0001800046003114060b0822042c0e450118080f64048014810b90b20601e40c408010500c9628000100c0f41090708801c403108082e000c1400124640c0040a402d801403502003611070b143c051102c516846580008403a5a000908000c0c0e56014002c4400035003162018103414034040000c0000507001d1407000b40306400860000754140c160014030351a9509d0101c008000b49401c0020340010001500e01f5100381c031503c2c510340e00081c801c25900d00d080046640c0d0740350440c281e021514034009050b13080ba92080e210500440d07a042e49a42070103490380039080200d0340c0d020b581028040b602c01600401000d1403c0c1000b4405c84500046130400d0103101d240c001559144030b0070031222401882c1004401d5401d0211078080d0540f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614755701 1250 614754451 614754461
    0x114070605010f0b0f0703050307031e0b150903070e07020313080105010314060907090c0212070b0403030605030d0f0c0c051801050109090e100b0a031208040b0a0204060e24040801 79
    0x180a85603e80165201c1058020301e025030154204002c004115440000f231142c009150003404901380455114103d0026103806085902054143c640d84e101425a0303142040034644400c0c045200760f450528420007282d02c8041a0150000d007500400200c0c1400b84200202e69240f5100d0418000d09901c64020034060042840180d40c1d9100071450300140e528040764860103440e00c400100340c018940300c001f4000c0c007501d8800c9030550090750003910080c4556402480c2551140c42c2c02d2101780740c103180180c1110856007000d400b070741c00405c0074162190044000c64100000381091000740321180340c80041e141e40c0f50010340d041102a8412810007045910103410382c5c0d400d0320740c10350340c945440c0034504440101d12a0403080e44a4264800744400540c0400003c05018120401664494840b4420148945006030015508004000074885c1d440012034210701c00d0070056160624009005040b4061090382034849d04901307091403505605c0106800e010f030408001907440e50740e03855031103000701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614756951 1250 614755701 614755709
    0x80607021b100c05030f13090e030703050a080c3016020c01230307090305070509100611010617030c10060e0f04060f1805010b031203010b09011407060501 68
    0x4441d0039001c0240c080c0046040080c1c0101030310000c0c4091001004075010007212409540c0c3c0d0204219011703d5940240003010f40c0400144103034296880e0000c82402c489030011501d4684d0014840e1000095109013155000000707454207a559854003608003540d8400e8101c80455215071000003070034030b0088942c58240004041e8200125a1030801c0c8000c040860001140180c07c1000461071941c05928441c1c1440001268840013850f0311f1440780301036005865840c04942020400c0080240400400f005018103847c004e009040c803640401ca80c1c0f00c01d01074041800724107081300d28815025880704004161030350704070180c001388410300e94032503106801180440c0034650103001c0030207140c05802c0480300002d00c031100659441607502c42500000c5c1084441d0b81d1100f07401c5090001e00c0c02508404801c003404021417040c246010b40c21078541103201406a007100d809011102c0205080d2411111300600c0d159032290040012600140c1c844180c10700b451001c40c6642c18401c01d5401581a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614758201 1250 614756951 614756953
    0x131e060819090308072d0c1a0f0f011703090f0103021201060f170609010e0c0d0903020309040606031a060a09050310020d06060c080906090d0b040f15020403080906030408040b0408060702 82
    0x115100300b452001c04a90101b203540e0b01e0391403098030360841c0c443e8502d468040d0050404204030804109503180902c7d090b039440104000c1c900034000c0d020704c044621401050506031110304c0b41d100d40c5015490b4040c2d074403820300c01c0007514011003140e4043d0f011503901d450310f0481c0c11040c2d030315000054072810b4141c2caa0380014218900000304912110113150240d03900501c0d03545181e207008013100a0400c001c00d05454844c00340b110032a940b04601a141d070f10382c8030b41c001d140c80e0303082d080910080720002c0d4025400c050501707032080980128042c90b0001d0003c2a0740705691808100015500d007201540f007281c040c1b00340924190035030b031258040c06134030454030010f015540d035448046a824480b000c0252800b14104820b001d14a02400100031f94800501519205902070721890042542181e054031801c03c65902c5400304010076082c4924410b521208508013415600c9641c4507001d6204101e0241c18000041020701510b2025940140740100d155036807a030310b070301c649030f02c0318001e540001c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614759451 1250 614758201 614758217
    0x4060f051605180409120903050c0f0f010806030708070b040f140102120903011404060f0c11120309011b1706030105070c080a110d020102131e06081909030807 70
    0x9002000c5100c02000e0480396211030620000079004548519000c01c0039604c940ea5048000008044100d9515160b00c280ca41e41c001c189107007030082c20415140d140318401d0300720710910742d00c5550b8048080d101c12002c2c45e0840190741d0304004a4680000c0ea0800c004500c1820000550116510010030070740782d4407142c140c4000d90710560180d01c9113128047c40d01503004030008551a1940704090900c4010041c00070508000c01401c80483c840c0c280c1c3c042d5006512071369585660784003400317480b00200d07041c6010201d240e11040044e85070389055030075078030440e0b000012440c621025080f1030608070100401840b40c040090b030150103400da950409014041e54000140f440c41c041c4111407107918a516012030004c0c00795030b480d40c142c2c84260ba0350144001500440075141d41044818000c04440e00010398460b000718464814100350360081c595610700015504030300080b01152411200c2c581800c01d2161540c5811992544d0485000d0904915210b00d1100341984100018020540ea4a076401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614760701 1250 614759451 614759461
    0x12140303070e15070606030f1b0806130303020408150f0901050108030d090203030d05010f0f0503010908090f032811040504030e0f0a030204050f1e1603050c0c010504060f05 76
    0x6268042110000082140154040a58101902c2080420240d10720f4507103080c800399503075070454010341c00503038035840c51401483c00c00020004400482c0a403054441441e0726004800d41e40c0c110050070358082044111071441098020b405460151880000303891061200302d8071054803a1044412082c010503803000308003070500611540341170301d0302500176625010603c45050054500c00a08a030180f200300117074680401d0038442d190191030401c00364102a450020f000c4500850703500044e120b07900d8031000034002a00242207440142083e43d108a80083c110006820000c13802507500d0380300994403200e0306004212140e45030451040079100481c050756401d2000b160001c0f50001c01090002201e12024600902c50b56a605401414101c015441b0740c041800e41e001a10040c030503822000600c4400d0b1004084001100810b81e0100035500d420280304c01c1c2711a10041030000d040e03440300820745440aa0f01103e100f985810300a0200e81040d203480d500a00c0a28003c0480c2850040465 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614761951 1250 614760701 614760703
    0x91c0807170a020d05070c180605040e0102090102190f0b1503102d0e1002070b0112230106030f030509090714040e060f100512070329030a06061214 65
    0x140300b0340345503000380004045840700740e41c15800700e90242c0b410402101d00181c582d04807110030740091841440418418584024407050703950070018200c540e401072195803c80c0e41c0c005642440303180282400e05031903010341403054024000325009003940f040e0004102c0d00d54011813481030000800e404454000140c1e1002d0000c69280418a02201300c8071007040310007289074180383c014201d010f03000080b40e05601c03003468680791000c0c001085403a00411a441404541c580ad1801484401686040303044141d41d80c40300a001007413041c00100c0b00d01285003007000d0075400b9601540c1c0c8180c149d10040744908018015801c03902501e4460114031380082c40b454131540388100030341c44d100782040c01c150820000301044034009003441d810161100104100750384d01d02c04450000c0c981e03140d083c4d40d502804002c0f070721124000c0903d41854104901c81120124861600b80c034501b8020340c00740d004109100080c01d1000080c1c014002d1410300001254042c00e0010340328010384118180c0ca24060994509 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614763201 1250 614761951 614761957
    0x403091d1005060a02070509090c120303010806010b0d0e031303110f10050a0c0c030c0608070903030509040902040b0a0e09010e1c0807050c06100923010605091c080717 74
    0x5521031204070001c102d1410200301800b55a8003500540c0c0c0242d0704c44d000305020020448181a140c0e00010840700b8506100710615440d28540000d585558100000960f0340c0d0810f01c1284840040001c0b1415524015400b22409840201c142c80d0350380c801030284505030303845000694000000002080700c070300d040c0200300807034003025103011170543c41c103501641c0b80c1d001500300409000c0c1c3c2c0c54010000410841c40a03020354800e0000b11001c2c0c0c103002000301424402404913051061106c82400800d400c041581c1d20070380c04807804a250310840c80890080c0c040101030303541082040030007094a807141c1d1000b91003181400000c001c40040d140364030f5900d502108040c07821a505408041d049442158141c1d40f0000c04d09000340b0707080e09061810315000d41250340d41c208c0d6040540a102c002c4080c09485169401401c0c5101c3d810905030246255040600c80c08050090000351141140c8950300b505079001000010f084047c1d259082141350307580410307002c03242c03290031411015581c1c19050507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614764451 1250 614763201 614763211
    0x50601020706080a1104030b180a0804090f1e0c1e080c0d1415011e08070809071706011e030804090c0c060e0114070203040602031204020a050301050403091d 69
    0x42280ca86000302c156040c24000d40f00e1000b80b503c4901c2680c014884070b0013400118802c1e09101c15610340703000c1c8510004204035201409810240388800442c40107005d80b0107a0f2800c030400203d140702d1050fa00d0003020741403916445c1c800076124240b8841095031020002c1441c0d0303101e00348141c0940d00443c0c50303501060803000104824001042e00a02c600d03026241c0702100ba60001900130307050301c5019840703104a07241038008601545604195038040c074554820620b8044144004406240241094000800c1802008142d030009420520100400c90081070380282c601c02941d40703801200d4542d07009004010741c0801c0341a20b40da00c80a4030b070485048030341001e43c19042904020650f0050100ca42c00714081082d01150301c40402c043e0b201c1c100c40caa400d01c000180e24070800c0c00b194001c0030001d1108007507401c01e10040081d503401100300c855500b40e4000c48000c07aa00c510010b0006c3c55250441605586084204801c154110b228001a90094940d0b5880907c1003d159129100e044030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614765701 1250 614764451 614764453
    0xd0606080a0f36080f03010807060c120e0a031704140f030705130f061409070e0603060415090f02041e060c02010813061a040b0d0b1602100203160f0305060102 70
    0x300d040e403040760f24030a24082006444a10303030740b0816074480440da034101005540041e41d0010040042a41c10051000108440d0425000402c0700303441d41d514a022202c2c00005101d4400d84106483d5681d00d112000346074000b0f100e5801100904c5005010340180c01001c2000c40386200303014180c50413000800d40c2201c010024481e0034104814480c1c520b00140c03200e071007aa15039040c2d00c2000c0150044001030102e04400c00f1400d0f03541b408000346500702500340310500c0781501300c04c0c1e1251a04d504417a8882000c0d01c0218500d026142c00458182c010351003103803514500119101980d10750340003441111140c11180c1c1544a910a80700380c064010b00c142d0700401c044d001400010b501404449501580010002c0c07900c9095840d070600340c40b0748400d076640e16000c030b0700030080300e140071b10400c1c2c00441d0594013800540c1156440d6152040080c1c151004401298160b00703055208011403003640c02c0c2c0d18402d64490604030750401c1079003451075084000c01d024000031040140302e0710400d40b080704168 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614766951 1250 614765701 614765741
    0x924060a060c0c0801050406020a08010b03040c1401140c070501020705030708060f1506120105012709090215460c020a05061204110907091a0d0606080a0f 68
    0x701050b03400c2850810201c945144401c0009103030507003840348900c40c90164002595070f50540000900740601600440d80c031550a106100208601c52601c0c82900d811b824101e0b001c120b007400503a00045890751004c4401000120310030085070104202d0100d54080e022a44aa5210403c0503243c0c940713801000020350089000801c2e85860000494101010908141e80300c42170b517011170600c0e445200d5a01030607090f00d00410142d6804240c0c8903640c0301c0410321a8240d0311042c0c824501c1e0f03401d4410303000b0f40354580c5009010b40d81c400e4465610000004003070742c0d0300c440d070058aa848805c4008004040e404510710303c48503e03a1b51a481d49851100c2c0390a01540d0b48406c0300307540ca5004150142c1c2c2040581074041000d849031002022000446001540c81d07207850715007059249a44200d0900a40c080401c0c4800d0540281040341030782e40421030103040360a02e80e2500d1050040720542c00f022828008000764554100a01074056840c0c03040601c03800302036030741600642e01600c00b24081c08441c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614768201 1250 614766951 614766959
    0x1e170105180703050a09021f0906020106211b17011103040f1e02120f0705030a0206090907111903020105070201091e0609140102130f050108040201050702030f060924060a 75
    0x2940002d42c045c01242e000101c1070942d0300810500035038654980f04034800044640b07022500040340384020700c8588000d200003400c003e01d200202c1d4402501401d8100070f26006003c12004000404080c0b4502e4603030028139544000d20090750700041c001640c01e52030300000e0f4480300c400c2c400b1248556009500600d03000c0090361407000c800034003641080315149056801740143c0c0c03814000c0d054040000010301e0002003160b40740d4107245c40741e4410362096110084510050f00d8920656000da4002c8420070080d5840b410144c4a03042268412426402005544200e4155400448400c070780664020000c0b50346889080c1d003200d58131140a080c8441d03480602c3c8210441c80d600e041120b200d003101045004a030b5843c1001c01001c0c00c514411a500031952103118508442442c0040a822183c440480c0c41e0600180c8429000b500190402800140d0700056403010000043c000b017601d4216a020310700002c03a16104c0c081014a00a04ea4a488040c8200a0b0319042d06024400087c9011410341c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614769451 1250 614768201 614768207
    0x1201050907031e020c2b0e0111070b12061c0b071206030f110105070b0c071109090d110a0c05100c051b0a0e070c03030c1e1701051807 59
    0x100070440d20402d6242c10895039003094414142d186180366030009070300e80070f0304409a41050a28002e0541900c0069605008125822002401e0131418107000a51100e8440100c0d49518030300700c000514490081c0c00100134035880002e1280e024058000100f9840342c40400c1800d403c5a107a02c003d060030240b0341d10100b041d00401c6034105207103042261909440003101020b84020354400d176010790401030140240500d00480d1a07039501c0074030382141f6055403665441c16117600500030170840301c40446c2030400c100315800542011800100b4802c2549018258995602d840c840c10400140e060840034507150400582031100f43c0d80000c000002c00e04100900010b000050011010883c41080303c601043d814031000110206484410009004032401e1000000485d4410701d030388295a42080421035000c80c1c14030f1490303454a808156500da007407080380c1e07078188400030b8034503106082d0a03400025009090743c4c1000311061116041680ea860070450391080c44e410070b02111b00702000040250f44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614770701 1250 614769451 614769469
    0x9010309022e1e0f0210230a05040c1502030f0f09101b0f02040b04090f0623010b07051204060201060801110708040501051c090b0f060d02060d0c110f0703021203120105 74
    0xd5280704555110082d00c1c03510b825504039801e40d00c24072403906408500585c800c7c15180e803241c1c01070300900841c10166601541c04101c3c4c4500388030b60b660410842c00040c0300340200c49e1101484007685886a1900c080d0781d0031603000c82960352041c400201900c00e414000d100c00c2441c00c050502805015503607840b4001800b241d020100c3c1d2290b6950400c5809592364400c01c40b109011f880100c424007190324184003150101058590302401084d0344041d4204144180c42c1928000b00c01e140d02c0307140f13514015140c40658800840742060210300800c5107030781544a54115500c0c0802804005000542c00c0010720401401405d140d0041100780072650241c2c005203201e84c2210100e030500303030307000e01c1610071034440d00d10803194143c582042c06080c04150405d0340e00a04101c409501d40c0c456070740007038580d02c40ca45040388196101d4000d6104c03540100c141c5840e2180507820b1b19200c1c501d04904e6904c0c0c54082c001288102c0d03e90029048014000003030390440700d440c1c90001100e07424102000075541c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614771951 1250 614770701 614770727
    0x30803070302090f12070302090703020c07170309040914070611030426010204060c02040b03010213031e02030105011806060809030d0f06030f031d060a120209010309022e1e 76
    0xb905200d84d601c580e0700e0701d10000d064199079801800c407690075031040000b1140c010700101708050051000c09003050b40852100d0172500401041402030000340344041c01d501038007041c00d6019207000301520500001e803081400b64000720054a0100d41c03204400d039480742000c50a44003540c401e00040c4607400d0599141440d50341b00c04228842078602d040002d00760381c05a00b0070300015100c80503010031800c2c0390042e102059402c0300258100039a01c80200c5c81c0c0300c002c1c4000740140341d18205120f0005501a180324115401400a00c00d075030b154030100e40c0104040300c0551240b031901d030001988a115030002806141040003441c83c1c0a4130528500c0a401d01c2c20150041c1551104000700090110703400c9020a4800d4075924944004a29014000c000e54650030307010700001c218042074140d112014486540103400010380301c0c05100012002044186c8000f5003020641200d084505180703481c0c6529521030119504054820344021075a8041c60100703c040b001e841c10310001180c8c05092040e91007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614773201 1250 614771951 614771959
    0x11030f1b070f0618120f060c1806031e0b011b0204021b0c03070b0313061a0301050f0f0702070620010b1f12060509060907051917090703080307030209 66
    0x381e40b03420715800580c21962141020503000c0b840c8043d032400700a0208010000a050f910500100380c803055442614140700500e100d40d0f520300052424041c00440081414400d01e172100c0c00d4031110098020040c6510350f2540c002008561084243c0764010302d85507404c180c1d00d03a29001e89403a4030412000d038800f001c0383d01c00d4003441500b6501800c208440703180d154020080500100031820f05080a000f0342016290400400820160426041c01d05000c1c03a40840001040c0c0300d90101c1d0400c0440d000649076265081c00c0501284040c0e11908038020b000308270000c101ca4880d06810f0b07036150300758401c41002c90039043c05401401c40b40180c01c0c0304482048000b040042c0040300145c0c800b4504285040b4120601c2140405150301504d2544072402113442000441e0601c8001582090b0050009100705240d074006420580708105032062540c2952104601c255280f501501c40b920715841541d80d80040350006102090009030541229048100c480ca19101d5440840c0a980088685508 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614774451 1250 614773201 614773213
    0x110702210309040f0b18040302250305010203070807120207030804060504080c1e0709060e0402151e1801021903120608030301080609010e030c07050f040b06070b0711030f1b 76
    0x1030f21036018202000f0440d00c0001801c0c1142c6040003124040780c2401c0c1814520001003100080d00025003610300711000400400c846018407a2240e0b03512540c2000300954004000d01c00c079280c2004036a40507640d162541900240800e180100300d00902c800540003402d07400109020400b2648520740003802101080d28064841411525041c000450004006001c0a1025619800344414000f50090403018031007140b52101658030028040e00c0079102e03000c24040f460b02107000400720348448003400038100070000301604c0e203803282e080f180e880c070760607620340d0801c040940c40400e00000349d0000d20b2038a840081261401c8456044641c451802c5c5540c0320310100341e410081002d54000d1034440d006000b5440c0c1840502e0958212402103c0207600901015411403400b0504a040d58003c0e280101254a8540020302400c03104107020b4100100048402c28025040b000900c200d070a52180e500924440d42815900c0c815600c41d40e03840e400521070038294000c11503841d50a01c0000c421980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614775701 1250 614774451 614774467
    0x51c0c0b0f0105030c010c0507030809030708070f08010c08091902220e0f070b0f0706111611030303010612021b060702060106020106060c17030709030c06121107022103 74
    0x8003031a800c0d98140d030030305091401001145070801404050300d100381390400c1c0c0d50f00180d507001d030b85000301d0000402c04440410002602d071410808000180260000c4030005652880c101c80060f03014000d0500d0f65003801c90310803481c0e0203400300d2405480507100801685040c3c242600d01480681030482e40116070032030f02030118908418001009520400014015032141001c2d8036000d5400104c1d5920382060f803040010040701d0044e204608001440c45079991690314002e0000c0c0265607140b1001d0b04080380300c0c10070320001500c1c9000c0301d100381c807514001e501e96410182c0e82d0000340701d5403001568203a0507803171144144e00607080d40542d1f4030110030032001180c616410b064040b10200010707400039004100c500d03424029680145518208080d2380b00c003544520341154803541540300c8000000011910042c4502e40c80c400464001c0411881d2684038900281551a019820131245080003208201200980c00b1118041c4d402001c1030320005248012034001510103503080704a000c00d00241c0c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614776951 1250 614775701 614775713
    0xc12060f0f040c0f0909091721150423070c02030a020a091e0203150904050a0203121306110304060c050312010e310b090a0f060203160c051c0c 63
    0x2e00400301c01d46451440250400004100c00c4181e44640b0300c1c0c0e400d00000d00c020a85502c8a200074180200c00c2d550b40343c4000278a1041c040c2e419107106503100c4114108880810240000d12200340b0445062212140309402c94040d6030034814000f07400c8001d60041244c40303000b166500e9041e1f1028007035808a00140c1c000407517021483d80040899500d5961410080e208a01ca00d105003102030011030450800011401010381802142e034010504030011a080c4a0100550506a0390040031120003000c990050240c503080f07072010403403540c2c0c0401d02243c0b43d4000c40303406102071000c800071414245410070442d0444034150054a00e07000400030141c2c021002d0307100034083d06000b001104142000b020380000d08511103803085682c824036200c14500401c0801d03444080740c014099648035224202c000e800d04040100c01803440001c50307000b070200306035a0007542c81070600c0d01d141c1c0e024804080040e12180030302000246140c02c21283d90710500700c2c0440040458403940f91411089145544003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614778201 1250 614776951 614776961
    0x3010b18070c0b1003060b09010602150c310f0602030d02210709030308070e06030a0c110102071a0106020705030a120c0212032218050c070b01060f080c12060f0f04 72
    0x10003041600c101c07085c010301c120b902900340c820406440c000740c0d542c500342000351a003031048030310889070007004003041d40c030091074013940d0074801c2b0800c00c03544003000c6c40501d100e0340c044c9242c4031090480380c00002440c0b5030021041c204030b400c81e80241d8600f5034100c1140000b0340c42084100703400d040b0000500c2861040c080018803903401030f212036894600794240903002c3d23000140034104000000848100355103a04059a4124054203030100740403103400010344010700002c000c0001980b0118052007031058031110801c40038120103840445981707130303c0308986605050040300d0301980241213400004450604ca0400c1f00e83c3e42c500f000382c410040c1e0002b0070135040100f09000c240d102060044c0844d240880d80060340702484034101c201840c002c03081c0c1c12524079060000c9220343c1e400002c2c01020411044612480c3d208814a109607150f8602030242d81900801000082c420400a022540303c5d4088500c00c1240400b2485195901010081c02c00011180c1c030b900208000e8000784140c0b954051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614779451 1250 614778201 614778211
    0x9040216140a03030e0c01200a120302041403070303140a090f03060608010c031e020702130e0102030106090e060303121e0c09040f0b0f06070321021803010b18070c0b 73
    0x75000d00702d02800c0042c00c1e03c480da0b9012510f134000100c0364150340c0e00a05a92500f240c1c03070046c101c1100950381010704004d00e82c0009401100d0000001440f1a072660041058843c10581182003100c0c4009040d683da0440c000240411040c10141e9032750040c0d40c1c00f8008050036864848401529400f043c0d105c0b0181754822a68a91039440a00500d0000e001e06020884103107401c10020201011a44c0c0c0c06501646034148594001421819500c2d0034090809810025209000042600280324000c0d4000d11410000841180b0045105503500984074054a0014000d505141c7c0b108040b040852000d0a03203d407007980300f907002c01c07074400d08522644641c241c042015204d9030780c00c052000350b4140c0c0b081c0414061900c401800550343d820740c11801070704140e5070315441da07802c4d260503141b410494000000d620032440b03804101e10010b400400d0034400e5484401107510070b2405042c02d841140e030b0155402004425016024401180710310b030702c1802483c26450491041c0c5030318906c1d0800b511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614780701 1250 614779451 614779453
    0x3060a17151e040b0c1e04060f081302090c1204050c1e090c0315060d050403030b0f0f01080405030f0a0903050c03060108071a04030b0702010b09060f01050904021614 73
    0x50078459081d95845219440703050840401c15404101c14807074010180148018400c032950004958055142402d440c5104003800c0300100b0403201d070001d503010750845e00c02e200018003100041000d00e4465049140203c001c43c19140340080d69030b00300604880c0003082c02c0d81c0c0b40c6c000e22030728401c11443c500303041c002c0e8040c0014101c010760010901025092030300306090806429481c02074541c40d0f021046502c1102c46640720703220b0711082e0032011078859401e02e4551186000c20200306841c0c480c1e00090146100f6242085803104031401d104010300304500355548452280c40060442d4040c030f40c81c07079102c0e00c120140d03498882d08007003842d4603421015036100080c1d1203500510411108114840c01e41008034014042580340c503100d9a0b8443ca14080c00301044444030082304d4800d032010956010f10b41c81100c1110038685800b0080c001e0010410780780c846e0303c06070302090460405400715800305034180e451504e002e01500500c000ba500003400d41360706151003018400402d80c070750301d5031680641d01c038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614781951 1250 614780701 614780713
    0x11062104060b101413051f02010605030c0f040b01030b0a0b1b0f030702010c260a02010b01031a0d020f100309021516030f030f0c030605031002190503060a17 69
    0x3040c51411107000e1000d96008054007014210207640004d05a50755042c031220720340e074404130410300030b017070313517410780c44141c00144014000310425145402e00c40b161040368020020542e0720001c01d56101071301084150060314080c0c407091b035800c0a800017942c000c4181800302d8405008408252054215805030450b4040401d9a012012880c50000e0389070035410300400075040d501071039980724800d150009051101d9a084181003185144d480030180070a22705600c03002003048000400da52140310400c0c015442c1a02c0710900d580203102e000143c8140c10500703030a0320310385024801c01c0d9040307010903031380011103480012099450780e4100c1115982030f900420144028030600000c402d07807108103940e004c4240b21451160b00030840949540f501454607001201105800798010300d0a92061030700d80341007142000d92076801d900210100d613000c3d01120700f030000005000040380039a018225403001c048420050f2244504091500140f004083c1070f03019555198035115107100c0c3d581c02205030055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614783201 1250 614781951 614781953
    0x1203270608040837020604020604092a0c120203120a0b01020a060f14072a03120203040506060a060903080f07080c07030c06090e01030308040b091014040209100b0711062104 76
    0x1300c501102410340d00050145043c0b5030300244030f030f00030f6000350111103903141c201d601000300c040500d080625001c20551542c00c0b251030000c0400c0300125050314001c03184920196240e01c0001103840c40402010300085a440b03a05208000c1c0483c0310f0154114496002d080000c02d800b071241d640c410708072904c0059030700c65088400e42c5200006010a003445110078804204842c0d202c55542003060165800d12020603502e0f056481e410400c0200f82984e10100400080107400107005005080403100c609502d0799609044841c002c40e4000240f2050040c0100185240210050b04c440d45c4030300015410305091407241450302d505c0d9031059502c80c45145003082526000751502c800780540c02c030f1040c410b604540303004d09080b4001d080104014801400910030b03040c140a0b000a0121985042c4a103801400c0806402c420680c0c00780d2080b4542004580300d10a010355803002c131141040554180205038a80120b000400c03984160003080030008000c8940c0030f5404c01e2810007100900d6500c0e0300b06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614784451 1250 614783201 614783287
    0x15120b010501020d05070b0c12130309080c1e120d05030a0b0d02010516060f02040807050102010b0607050d26010609090e01050114040b0a08030412032706080408 71
    0x1041c0d00090540d0840207004854540c4041154155900050b43c59565190440a0703d01445031180702c0c440700c0701c01428040885241c2c2c1c640a0a07034085c4c0e640c092590380320340301580c9400040c80615800300040c12210403080380c00c40c0624452400600703441c0c0c44446090814180022100c02e200047c1d000400c01900620351b10481c1c0c2014400e9981c1da8206001d43d00281551040a10880c01b28100080501c100140d42e0000e500c80494551705546680c0c5d40c9046590780c12050041074059401c000725812681072903025940c419400c00f0080050408c1a0701c1039412080c3c6001d90400301000020158000d80380d049424002e04243d90b59003111031600c1c02010440d03a12030342003207180c0d040400400a154094501e5003940404803400035592160900050400100307a100c09491300001c600040c1149110307540c46001d41c003e40f290a0070151240c84108034202540d030424001c0070740c0b00705014035482904000c2d4424440c04120303203441c030355000040c00414102c0c00c1d0510883c1b00403540761403840f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614785701 1250 614784451 614784473
    0x8012316022a1807050d02030c09030706030c091710020304080705030301030f02090601030c0807050a02031309020a110a0803010b0703051b0708071703091201111b010c0e060702010e041512 83
    0x943c1015100c000c2c20241c00061040c813071444050345107600840414541d1b41c440c0111031600130000c04840003a603490502a016103045c038090008119288000910010820002040a0b008a0140650a45000900b00250030240050f00c800b4003d003c02c4002600c2000114061401003020170315014061041018099008100c141014100f0b40c607902d406411201454000380301d070804585072000803030128034501a2081c02d4400f481c040f83c0020b001c0076264000d14907121942d9030400b4090100401c0b507590031481c00b0045c900d180401c01040711820a03405014051b10a14003a854121098651000e1285060b40c5801d543c2014608000c040030810810b0024103020009504e28142c88040300d4490203940d030418083c0480c0c11900300c3c0b5520030b503c05403400c3c6034403070000e454203410803030071900903c031401d400710f65840c0817140e2003258014000e01d42c400100406251900780164011519480300314a42a0026110495400071501d407030103e1000c9c0580700d00858034182c0c10b0078000c0c0008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614786951 1250 614785701 614785729
    0x20a080304030204061a0a1d03150604110405010807080604110705060601020c030106060903141c0518030105010e0a0213030c061d0a150c03171008012316022a 70
    0xc1c000c0c6d09014034500c0310f0960704d100541e0704114070003054020b459015401d0700000740e41d06000c1c4610184c1c0c0a04100200c1c1d0168070191340400c04460303031640c1c96665109602526001c102102e00089604d442a0f85da80d80c8440003070000b0461159242c0b403248203401244013207803a41c021004020300b40d40e04110800c1c3c414030482c003c0c0036507450b0034000f4000c02c65a0102034040c4140070f0322500c0900040045225a0a10700080e001e8489030480041840e0071800401042c036044e088208010300d014040e4a060f5603010000c4c0744251540102c01009500003440d446e65800308a8000002c9211140c4a4009000541b078054170140084130f903401d411503100d201845920603481c140410b2800c649016180611400c0242c06034102e810151481c4a4400310711988071440b10402036400607030701c0298119190540284005007060040f28880f109003803001c4e0500000300d00044200034895a000c604841c5030054407008045046d98005240c0d070140b9520280c0c1c40e51610300a607003480014403d0310 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614788201 1250 614786951 614786969
    0x15180f0a06060326030606070f05070609030b0106080f0f270601090605090f1b0c0d17091c050d020f13080c0d0506070c0611030a0606020f07060525020a08030403020406 74
    0x51340c2c44c06040700c0e207000213080240036501c00728481003044000e03165403501d941c003c0c00712182d0b603a580c0802030084da21400201d80030302940d0000070300c450196a0003030143c1d45004a1003c41d80c0d421095071901c260041c46040200d40f40b0300c1c100441a2851054610001030308050030a41d0f04080c1d072034080c0d5400f58081801010780340308200300241d107028283c0e00300c903d100c507841c40d07601e000040701024003641c14060710718010b8400900001c2d030880400d9107a4807001030413640b1981c0e8824440e03250344643c1d00c500850022040301d090345a105000820300e07280390300e4005007040c1c880d150844458002c035004802043d010641440032110400802c14000c0c003c6601d000100100d5840e9511400042c6c2503c0c2031103d295407c00c100310181c1c0100c0d00f60808050303055101d1401c095560090001c03446804050700407154401540702c80032903880c040d5146611810b203042d00c1075018000c442c2c5902140701002d6030740c100c5040141e032103c06c2c0100800ca0500215140c41c01c0d401000129040e660002100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614789451 1250 614788201 614788253
    0x603051005090c030411030724050a0225090e0313290c0c15120a0b0d140c190f06051305100c0203010e070303030e15180f0a060603 58
    0x7041e80d80006143d80300321081c6196403a0388680c58450441c4071400f0009506014500c804245801e6001044d911000c800f0300c1169200003012041d1013611500c1c100100580000c0c0e1105140c081c400030783c0340c00641c0d41e030108401c40d68558840003100e001d00600c008070f0f04006410380c0c11201c3c0301c003410003078000255440018a65802c0d40d0342c078100d009050010803072001c0f8100e150750b0024440c2648454010306141100005800b112029521101040704010480e10100e021147e640c07050300d8420341c02900f210701504003030300c5602001c050b0001c1881e01e80b0a00b070008141e0744443e100c02d00008840d044400b1541e0900d0071400c0d0741c1d0f90340d400640401c5000e0000c40340c600216040c01c0704880b8180c0d00300d50f004081200c2202c807014241c0780070350150b091600103c1b00c1d0600142607001c882c060b54003000b07904c40590016807a004111010000b6104200100d194020406611201c1500c180d0031515881901c9102e54185844840203880c507076036070300c0c04105003c006008000000018071608031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614790701 1250 614789451 614789459
    0x72105090a03171006080702030f1201031505070509040e161d15030604020618100513090b03104a0a020d1103030f040f030c0b0304051b0f04090c06030510 68
    0x400141e62141c0c1702080030790301c080341d070300d600034001c80d10288200240e9903035031803070840415100320080c4011115040b015042c070308003005905ca414001c01240d41c03191301d01640f050801014000354084480980544410500d0800600309820020440e2a20303690040c100d481041241c040c005103c00d10314007018a0b55030440d81c020881d154071542c1110501e48941d00070855580311909040c204e50031003100d4030720050540c0c0110281c80400040482070354240d88030180c1c2400d03158488095034040e445003800d01e14080c0550024081050340b05100a12003081c14800542d07500480910b200040144007412494410712030380c2c1420403906da00820844115034007040c0b0700203841c20b02420501c400c0e408000300c0d54007481180c0900c0129681c0c640caa54480c2a03404035410b01d4481151040740c0b0f402c00080604001301981e104907008406000040c0803550300c0400c003c04120115400780b41d00c1041d410b01e50301d0b44696800e8078001c0c0100c180b80b03414100068100d60019040400c15603403200100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614791951 1250 614790701 614790721
    0xe040516120b0a020706050a0e01290603180703032106081e03041707090509150103110109052107270f020f0403200a0509072105090a0317 61
    0x900c00d5106940c0035007960b0f0704000800a00500100904040c146402d216040c00541c000030100c600180081015203020741204a0341d00780300c513915a041d0258000c035201d41c0b402c28055a031100300c0c800402c003400c100c0d6170344a08046094104501140880700b2517509040b069000d100c00700d0032000300b005441e040601c502d07a03c1e04651040100565001da095124040a0058070024002e01400150010101e41c105071144050b0080203101840c200008849080005480c40711011666a8410a074203646031000c00b0b500c014081414003649400009003a12078010802402c100c0e840115240d40c103105060703007460910340c02111280d41e20000d581c0003100302c10410f40c0e44100300d100000c11004179030721480a0302588620301c4045074007040c00000e10003030102c0c84412a5000c40c444102e09129020805c00148500a03990007010031400503030018003503868412136844812a076030500000130464401d80b2002c4484000f9a002080752000b09a00005001105450300050304450f00d0000100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614793201 1250 614791951 614791979
    0x60303080f1003050708150f0106050304020607030905090f150306040b0a020d0603080d061a040602100e01090f150b0f060706200c2805071401050d0203010e040516 72
    0x904100d0301e80e000450725080141000e28000c581c04415540400c1c5d40d403c03c25110030852904c1800c010501c800182d61100c5100030038140c800640b5900e0454030ba076000c3c803419400c5410220140b001c26040480c203562100e001e980b00706040210100f1b64540040b48036030708000c1c180300501131b030f001109210000e4010b03d025540b007401840016100c0500b541000302401c034580c0060a01c403000a281d541d03c0e4034641004080c2c903941c41c0c214030340c95075840040ca2907100b9407207a200107800c03117003400d030414520b07412482c0c00500600005c9070a180540f02e22503c0e0107a68411965003025801c01c820000581c001d0005441040340c1040407026800c1c0410300610844400400d02d0307542e04140147d0080d07003541150201e1580a100d6114040d007900d0075502d1810f9200d502d944465800d00c7e00c561344403050318002065128010b409004e242c04c0c8400b000c4064403a100741402400e11009295000d0361015500174003100e03000001604282c10064103203800039080d0f00300d8911901c01804010600106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614794451 1250 614793201 614793211
    0x1006140c072706090e07050d0308040803070509040f1b2a02011e03090b0f0115030f02091504090c03110a0e150c01090203151005120a0611071506030308 67
    0x540c0840c01090b400c1d01a210b1030000308070302114a01140840c40b02e03080c0d800030022050040880700100e446904002c4114940b08009001454050000b00000c41c107070302564001c9028101642030008500004060341d90400d40102159901c840c100000840044d4420b0a00c40f0307424900b10038000044440d1a401c4198010358032010142414411640705120318202100201c040401413500164020003609101c80e007541c034903031844046401e00441100ca00d04035001c1041e0f0f0403d840d02004203801601030b403545540482d5080c00001800c1c1c550b40f400300100803120301c59540d600d08007090f01081310321141c14401014504102c0724695015002202c0d50707a10103003005600c0a05810001e601c0180a566144201d03201180010750010f05400c2507919501c03c40544105a00c00544186110001c0b07401d0740e07031000722003c10070841c00d0a51404841c0b504c020240c85000740103807214019034500303890044903600c00058800030300174a01c0030402c0040050000b4019240b5688000740460780181c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614795701 1250 614794451 614794469
    0x3050a1503031d0301140a0b060a0c020f0d02130c110303041113020405060f0d0c111c0c0203030c06090f0f1c030b0d061a0613030305031008061006140c07 68
    0x441c0088002c100c08404550038000d0090015a82c1c801b894645c62101303840280480c1d0802c035170000103242020130f8520045c0e16580c1c20001d104280c080040d11000b80c840e0300d030080c0700b1034503500244c0c0b00c1404e004c03144030300d002c00815001907440c4d0042903003082c08079616540d042070041c0030000300e440420001d0528202e44108880348601038000082c4190390080f42c0c030000005005084846c0da6003d0446552102c6040110240b54075098540d4040c0300052600d0740c12400030840490120800080054001d04c3d00040d04011603011034a558003107030780ca0303225900040801c021103000b005400d400c2e0000e0005800c02001090703210340c0d00c459011283e052182100c04030b1580512a43c05a5102c00004281307241000c49410503030020031100c0940f00704c0316031010207002c450031f01c0c00032609001410901030740e18070710755101150709800c040c0680d00c0e142c40400d80004c246404000b141c0c05015561883c19500e4642000034080d01c680c0c0c3c00c80e0070b4036a01808030085903d0003040710700490341c0c0c02c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614796951 1250 614795701 614795717
    0x70906031107060e0f01020c0c100e180a06050d0804080712030503011514070b06040b0a08100f0905070305010c020c010903230102041703030a05130b0c090d021f03050a150303 77
    0x401c4c1e15003412400301108405610109081d0160480000c40a03800503080c1c680d008030465170b420440e62144001000f035000700381e81111b1050b07011403100c0c032603001003140c3c4000780003a15a40025500c0082c500309903500348d4003103014003003003000b0f020726401404811000040741107143ea000c0c009002c144640c49403181e42c030000c040514010440c0401042441400980c0c0380c000d032900000c1e140c000d5844074012850014041c6550a0084c982000d444126008001c140c0d40c403004040038010344030b00c1d240032035140c80d280b0000030010400c0e00e014600c5040003150b0100c00c3c20303009103400583c5c01e04d941006651681000400c0540c01c010341d40c40d074801d10722508041e61503011400383c03049038851031582d100004051170100b0080080c1d4091702115a090100c0d40310080b40140300c0300c6801d400b50002e040600800c0703c8101305401004002000f5210011000f0742e60001000414050304101804102040010005074140705540d40114059410086d66201c4103000030070503400d00000301840105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614798201 1250 614796951 614796971
    0x60a0302010c1101021903030203041a0105181509100303030b04110a030903110d0e01090b1207180f1d070c05190807060203160906020705031f09060606050307090603110706 76
    0x31b0000c40c44242076a09002181c50031841c008000b58011030701911002041943c0700c18078881c41c81114100c0300c0040c880d40c22590240c0c1590403010340980540c4940704407183c4c0310890f441e955400c0e4404c507103c00500e8201c46c82c5040c062f0030f4500a0340054806c074606203004018800030425140ca50b9a2440d000503841c00600d410741c3c020b8840d2800c0e48291117240c0c960500c031030784644a00264034080e17031103104260f0b032420085a0b901514540820f0110f2803070006070760601c95100096600b40c440b50035082607a0301d14a4102d5042c1c035801c0843d038210244000da05200d40c400030301b0f41040c0980307403070450f440d071903150541c403650140009221911600012000d000107001590b90300e0360004000c654a041130481c1d1182d5003034071840e03400481c0700d51a000480e41e0010400c202107070300140262085d20046044103900805000a4200300d55a80e40200080b82c1c01e0310400020700360640b40c40740c0d06d00700640040c040d01390b150710007000c250410341c1031030f01da00710301040d6001190700000100741c8a10f8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614799451 1250 614798201 614798203
    0x30c06140d0c1205040627020306010618170102040303140903060109050a09140105060117010e0112151b0e040e100f062d0b180f040f02130509060a0302010c110102 72
    0x41500f481c040707030b42018184070500000307a0190014080c030840d00900314142e0728400080107000c4c10083d625821400040100b2406010385100d1036155070344c482426a103075000101d881021b0a039094803690701040c14400c0503003140401600c0e10301d50104900b08440381c00000da0320704050068400854a40c00401c000512039003002110541c0310101c0c014048510440600a1008596450000300d02030104811040c00d41c0c64541a2402d28511120aa080000e549420010310130b085a08140050040016030348510890030b907030301c0391a840f8030b50118590340140103201c0340c1051449245440f5101899010000701412010741f071050205d02c10300c00c460480001d04540e84162400c0c904241034110b012000c182117003030400c0e1030385214011503d95019814501802400705c8040e00000710441032481d203603500011030f0b00024030202d4020340e188035180980c0c10010003181010303202c0d07400348400c3c5010220304ea0300a00603296101e6880ca5900000e00768600c0480160950114241184090b48 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614800701 1250 614799451 614799467
    0x31502030106140711130f1d07090b180c09040609050604050c0a12050c0f0a170702060f06011808030c0307230303040b0c1608030405011404080a14190207030c06140d0c 74
    0x1f115103010480c002d40c030788051407408a02c040d140194000e8690108484400f80300b842001c1a0213080740da12000d80c64a00c100f0b000d009040030164100074841c1512540d50b0b13018100107010018400f18050901006000c01e50b400906120540c85052100408043d440070103c03030000030202012400f80c8415202c10500d1092444a000c041c1c000200300030f240350040f8521800c41c04969030407034280d0b2060012a11458141d8134a40804045030204201c2c0d03100f100f044041d40044102a8609a501c60840e4a190702078804400c1c9074001091040500c040d416212028480e40c0f1580c54960708800c0c0075a440b8800144000e22442c0e1000215000c40d0b000801da42c803440550b10000541c8020b400c201541c0d41044400b21600d608160310395481d2120150403030b00803680000c0d11030030306414110581c0e0a94050510f184001c009008000080d800c12041101d03011254020349501d40c1541050840c03000c0fa03070044000d110004007030080307800d54501100e51556444a0000300e0200820781220441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614801951 1250 614800701 614800721
    0x91c0e010c0206040e01030302190c05060c100905161707210602030405031c150603020d090204090c0e072c060702040c030b0405100b12060a03150203010614071113 72
    0x70101340450388511405031141a60b000340c0071a44000789440200f49050409040281801d442410030019402d000010b81140c0030503005540a007440320744048202c9100840130f407550b40c000a80091503000d41c80b8500098901a1584403005c4900c40419503505034510883d600841c1142c400125910b04840322034201e6441481599241080d081c031503a02e4000441e0041c0485c5070b5001c140780215244150002e1100d01d9040900c003a1400106074001d4008591800800752076403183c40060ba101e10032100004e10480c4004c3d101e50902c41d5181d0402c00003064402400a081d0400315605200e98907a0890240020419104110200419064041e02c00000d40203420044070540098260b00203a0386d031300058030104119a03652604d114060f4140c843c401c0410300400c00d2098401d01c090526500401c00380005501c2aa0396a804101800c00c8510540c903650200c010700111f030b444210248500c0075580c1c03640c2411580e031074111000440b031016600c07a040030040307081c0240040c0c010100d28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614803201 1250 614801951 614801959
    0x91903050f030a090f06020a1704050414011d0105220f0f050405010f060f0909050703081204111504050d1704080309040b030105010e0c070804051c0308091c0e010c02 73
    0x40d01c8804810341e894102d18902c0000c240b030344401250b08014451824101c8001d40c1c001c0075100d116803580b1441c88584072110110302c504108c0828103031514091075041c5000714011803125032500501c900045100c12141100503500d10040003e0b94818552441226450141040c81344242e0f81d81c0c4003c20510729101c0440e4282103401c620315425901c035a12440c0207600330300070200d085c041da80481e01a40600030142603802c0c000e100d136070900e0703208a081900c550200c981c115240d842e40300030780e0400503102110301010400c10040001030812845041300076039031b114041040801d02d010034043c502449005d032370200070300810321151000407070741441e050091907030307403511001215100d9101421950085050802225090905214503030403236226803d0100780f5211155903850039400303000c098900180600000c18142c0c0c030441c04a001d40411000b816940d2030914028080050042101c0c92603080b04840790300e020040001410b44040c031380340210101240000581c0e441200b40030103904 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614804451 1250 614803201 614803213
    0x1120603020f13140a0902090912030712021209010c0909060b040504020c0a060c0206062b02011b06140a0e24060d08030112050c0316090b0612040f230309190305 71
    0x100c45c80b03540154004e034000d484a4481d0381d5503820441da16111152070721003560081000a014074821400d10441c40c207854005442c00b50040100744221030251100c000596495590601e8a604201850000c14081030140701c581d00c0e00030004114060351044ea8051a00040c625603495420320062622039444403040114442580340255680c40454050780602488482c10711503080d070560b24030303090461910b1081030142c00d03030045444407178080222020341a0b90a850300081c10034002c41092801e0b103120443e00b031910b54028400d803003031520f03142003980140301d6a01d0342d284080680d407080100c0701c0c1c003180191180d0010a40700403c560b8080c01d4008040001b00c0c05040c07003008180c225004508883e4021a46000c25807201c1c80380008080d040c048280c10020149942c2109044010060009040c62644610901c070080c0481e8201c414541c000b50090401c22420b503090200701082c071b01d01d0358002119501c941d82c2e100340c80b80305100312110182603c891001044401c007466024040d07540d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614805701 1250 614804451 614804461
    0xe040312060510021b010c0c03080901030e03040902070218090a061526010b031501090903031b0509041103010b0d02030c0f1215010c0803040b0603100c020c01120603020f1314 77
    0x2480342e03080041540700700140c42078002c5e10340c800d103030800e8865040f4400f89481c80c17450340e4400141d03001c00001414540c03200e8000c6049242400900010705420b6805039950b03649104010003500815803107580300080c3e03000d10004007400908510000c0e404400080d00a90400d2241d250498a038030840100b0f48600507001d180c410440061912504103009101024000e4101a19442552015040d1285903c0104000361070b5400c480c000703500a00b030008402081a03001000225110801d02c042140040c3e011503c4c18035100d11104811418401400c55040c468880024800d101c002e028103600031010454258240342203d011801c02c0c901c0c41e654522040c903111555004484d040c820401c10344084605501502100102c658007420b424030f9540d866079000c0107000d01400641e0107200704984050440410300c0345511003600e82e0011300441c0c0b190350004000e80d80000b800c86555003080c50800c0182c031020480d102805040b1105040c1461b8900f0200041c010088104030403146e0106000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614806951 1250 614805701 614805703
    0x30b0705090118060f120605030111090315060906010c0314070b040c0f0506070210030b0a0b13061b2409060b040c020f1b030a0507080102041e0e04031206051002 71
    0x20076110700c283c0f103140100040d0714107001c2c160403520070100861205c48012064030302c503411081078101c8508000502c01c2d2910082400c5441608a40030310480000720000c00745010081e40c40b088101808507001840d107a00880e8281d8405803e00741030180240344041014000c894490800c0c80000f8510349807050f9090150342c240301a1005c0e07c8240d06040042040007900015206540004e41400d140c10519800e01850703011300306411003090740d91986103e0994400741240014403400c1202500c4400402400062440c0b070b43c46501400900e054810411030070708000002603410001d02e851440150107000e4014a58806581e804c0f481c03e0a44001c005407944694440101943c00f0401d10b25090802c1c1d980340d544c0c102c0581d4a41c01410614082c40e21246c00203440c2c50040c05844c190b10843e50354030f29080f5250001c0d281030350082402e1286051080000310210180c0010402c61303403400c20b288883d090040c0001e01000740020820100d425682c001c0402010301800000b022003800d4002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614808201 1250 614806951 614806957
    0xc1c0203160203190507170d150807030b0f070516050d0216030807022b0303141f140301150e06041a0f0f030f070e1005030303040b01120606030b0705 66
    0xc40e4244007514004208a02c0007050300c00814034801c40340b280c021340c00c01c00e41d01c0d608940c208892407104046241c80e030f4414003000d001e440c3c00a003400301d0b04040c03040c00300110309029084010241c1c0480b0041004c54241d407240c1703400c400079600b03240e0103849101c01102c85201c0e0320100d070016140070007820200000094947d40c01d011582c01d542c000886a0041c5040c90090700c0060091001806001c1c00f5141954652100038801f403003141c440801042d1070540e00207039240170350103c4d507598143c0b070302070f00025003440d4400100b200c4000c2d480c21110a650108015006503002900095407401c03030364809600042d4009142c10706001490f503151005882603030102e0f0a10300460814162400803591404803007108031000701000c0d00008070b5001d120307002d40d800d0344055041c0b00d42c524100065400f400004090401000400d03a1407800342c480341c05409650780319501a80c003c00c2008042100c80812906413482c04560ba4014202414160042d08060b04044d024181d0ba505201c110b980140007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614809451 1250 614808201 614808211
    0xb2a09060d060b0a030f150306020a02150a09050609010c140c010b0d060c030c020d1b05031201080d080f04050a0b0c09120d09050303210c0c0a060504060f0c02150c1c0203 75
    0x1c01c0c030a090030006d40c00b003900c00c81041c180200e08114403c0c4001561307600908202c0000380304980ba19074003401c003d0030000701601e0b0003c50f60f0b0303180140018440d0074800560f0281d0440000d01c00f0141c2e0041c0181052103040d180380500d100451800344141c0290810700d2410002010074000c0c3c0094107201e0700911141c2c3c50440480e142466a190140c008641810354442e00c0d198802c01407050000300421130b0b03058004a5483c0420051813401049000900c0e028140840003081c1c030b007440540107401003501a001c003803070000701c10400000480000c1d400760f0459001c10142c0c1a51180c0c21000401c1c042c0d50307050350340f10154103543d00304e1075800241e80b4040d28007596940b245941ea2018035441c0c0c810840e001014612080d51582241074095040b81c11020408030103107012401c01d000341c10301041800c100c031030784d417654284800c1c40090f008078400403260703100802c001c000c0c0380406992802e1816001e443d9091440020f800c2051401c151080b140e6181c0c10142c3d071160f1640050000e60045a07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614810701 1250 614809451 614809457
    0x21801030f0507091e1e0906051519030f0c181413051018060e0a0513030c021306061713030f140904020c03070b2a09060d060b0a 57
    0x700c0d0104240280c0035180c0160301607140c4405440c10917961402c031110011020700c20404015000a806c2525042c20f51586001e40740c0405260805075602c09070340300b0f584034a10030a030108404209488071000c40340e81070b00c0d060418a8050a001d0240c0180220a00951100d07203450400041c59803c028205e04280c3c440c1c08251909894400024843c1540219541c015002088102c01c583e01c40d4441900101083c03400000b941d40e8a0603031303880700b194071001c8030207a80315002000070741503020000f60049041103007840b1038a4219058261081d200d400039041121486011041d5162020001d0554180010511603242c0700c4502070074145030151401d4020000030005015040c69109224007641d1564401c00502e030103400480f104031411001d000202010441b812003540c461000300341d4102c441000d103464800c070741840700403800c3c010310030b180315423000e2440000340300150450881143c03540398858583c07450340049001d500074582e441e40018034180c80491510b002c3d60103000580410740d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614811951 1250 614810701 614810711
    0x603010b0a0309080418050604061404020c070302090c040305100204060f05031e01080a1e230f06010e070e0a0305071e1206020301031e0507060e0402070c090e010606020c030d0c0c080102180103 85
    0x20003800200c0c0c2c003d210717102c444002001480d034be42c0342a400070000c0030349aa085640701526500054290038040e0303a51200010f00090400402a040c00030301c4001504c0d0500b14201b070325051000d00b0421f0b4100c1007000f0000c00000003090510111058442190140b91000e001d41e101c00100e641c0d040401c43c196450b901700400f1500c034456801e40c06d100d0030783c01a001120708400751000c01a4010b482000100c5024180c03800807031a13800c0051a000340950000200242003280001d0a12800050550b000e440c211406002041001912004030340d1900300412042c454102000f00311903035600305100319440e4407a480300b40001a0003441c141d03801580034156005824204103000582a9401084d58100440030011a400350048403103142002d040503151000c142c2d0750048001a40d0490307112a50b0b03d40120301000360910070140a070603640010418503403e60002965002c0c0b03084501c0030400c21800900c03c010158609800501440c0b0080d9250420600d170282010301d034200d4640004e20342 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614813201 1250 614811951 614811961
    0x20c030c1305040302150c070c150801150c050307050706020d1d01080618071e023c0d0c02090606091c1e0c03050708030301050603010b0a030908041805 67
    0x890300305010a0001d142800011003686590080d14005100380c081d4092503203202036508249000341e03c540425100780b5950b2290303180642c2a82d0040d0094079401c100880d03008800707500150050706540e48032141c0c9542e08001c1c4011601d0100004004005003c04607905041100003c1c14005a0f4610340a13203924603042da00c21104000340350350300e04543c4c080c12101c07403d950068601c2078001501810124413450240c0030072641c58025105600041d422080b8103032030704903104035400e4803500341c80580000034011904c0e101e283c0f420a6504415100c1030a500000d080075110000c07181034680984024400d903070f80151000e00408000d90217555002d001130b11070b140640440f4030791325004040741e12100d07800d00101e5109080c070f401260007035a40c10140ca141041302e00d0108055104408501ca80d60451410038104941544404101c0c2e01c14801844695100001d403415900d41148040c3c85840407003003203000d040d0303459001e04107000018001c9541d0081d10030307000c4071002d1504140403075120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614814451 1250 614813201 614813203
    0x60503100603020c250506040b130b2d090301090b091603021003020315120a05010f02090306130c0918031b03050301050f040b030f0303161b0320010516020c03 70
    0x919000c118030750172000070080214800241e512410904508009225071507402281e010381c4103406c5607114030b81c00715a0b4030b0300c00707226284003000c2c1c150b0384082410818a405540150300080f098404100c0701300030211002d40c140b6040c1d40c0c2c1e0180c024000e0016042074103084201c0c04080d42d84850314000e200110b0b01e0a01c036070900104036035002c4e1049506440d41c050403002034002801e151080342c401003c141c1c5603556082405c1d400e41000c4081c03c40201d09190080c211004080c803108000d00601c01c09034a641c0c08991264081162002020740341802d00e0029810102500826425450107000c004800d0040ca006507400344241c90381140c034421005605881c644010005001800400050115040180c018180c0c00005040170a000105100003400c22250410580c502e600100c00c10103a0120f01001c026892060300306014140d070b0701910f0307000b04c1c11942c002a080c00030112b81580d0b000c0750002c004440001c12402007001e4100080e50410000303405450f00014890400702c0a400d00d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614815701 1250 614814451 614814457
    0x506011e0c0809030f120408190f08031807030b06010e034303060c0e060406020a120525020109060f02300a05130b0906090910080706050310060302 65
    0x24a40780c51488900303554540819a00018080e0b030140921200c07204101002c01000e01c1180101c1c000301d8a6500f482d82840c0740c130700b10080703181c0f00f213408540c0b074400701700441d03450070103c1e800c205400d03500d40c3c174403242107a0a03d500e404079401d0310a8242c0003040c0011a40300c1400390400740da540803c40050010956509186038503a00c0c40c04020f4800000c00c0138005403048800d0316102078104840c02c0c0c074503401802c40c0c10340c0180e0748652695503c40096901c101001c104050468030300e801c06042503002980d951114000a205a1042100440d040d00075000c2d92999001c4038607100e00c0011104580c00b0090350740500328003003820503d02056441c0503c440c84000b00c420750080c22580b002c071500f03041600c001c291080d03000701010700c1880551003150042010480e2034690a80e00d101040e124284203c0603400414000c909202a0b0000e5645404803603003207a00310f402820381d40350325076410a075040c0341e40501c030a4803c140e00011352513000000b9601c9003100c1c0101c1a4144d40d1000d040e0300380c0c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614816951 1250 614815701 614815757
    0x21070c030c0e0f0606091305060a08010c0915140d05040f020607030f0807022e021902070f05010503041203020c010e030d0c02010f05090712030905032d150c180402030a050601 77
    0x200300c0556a100c5040c0d03623072109510000050005547c076940d0140c00e401c4411200304440060543c90052016101d1030120320a05680c82c9007820454206644810650140e019610901916400883e084c0031712041d02e842059001031126584420a00d000780440e402444800c2c0410a100005034a1a00110b204030b21155131030482201d01940d0a124075008045003482e40c400b0360f00340140b00d40c0c1d001d850000706100020342c000300b01301c90600307000c000301880701c1d0300403030400c441081048000303007003403403411203d60701802c016031200308032001c0501500d0140000202131002040111002c03146800c42c40302504c0c10340003080043c420448400584204503600b41140d80015004c000351450340715070310300490082c640240401d0b00c131030019041c540c01403c8040384403101900e2681c0c82403044092841c1842c0c100c000d0500700640d001804065000601245580101282d00c00c10210800301c4140c5006000340110750302d1620030501d400030141a110140000e070072500c980c0c100c01c0c08029001000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614818201 1250 614816951 614816959
    0x1e02213106050d0f09060501180e03120603101a0a090203040818060c1204031208060f13020d06180c0f050d0b0a08191421070c030c0e0f060609 63
    0x4608100c0141c5503a4040c4a8407460f041d43e030388030b03041c5590040c0305a40f2100e00c0ba580100b190751500d24071603c034010081140071882d10700081ea03080118000b084440d0340c0c10012981c44103507203c0c0002802e01c1944960344803124188086001c050381020385e5981032680403102825030350349031043d500c103d0204480c0104003000411038811850f003056840348000100400c0b9030700d8217452441044c18084034540300e0031620310206d0b042c0208441078440d00c6000c0c46c58a40b10500b45000f0000035245080c00f82d480b4054030000d0043c0103661a140c048420414240000348000f41d46c0c0c01541e0b519041141c0300b41e030880d14011100d00c80521130385a04860541e640d907802e003084850034080c070040c0305505010703912544401d0f001540744402d0120040c0f03102c12880140b98660142042030a104e444c1d44100d00d07c2d001081040000340c110100324031440c01c0511130a456504529180d00900016040580704001c0c43c0e0001070300442540185100e903031002001c40d8162104018002c59001d408007003540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614819451 1250 614818201 614818297
    0x50709050d0803060402090612060f04090f12090b13031a010f09050c0409090807060f050c2709180d0f05030c09040906230906071e0221 60
    0x115882d040990307002440104014607084030b0744005200750313000d24203c130589140036080124500d0600001410180c0580b424041c0501030764401c00c084050080043c4400605204c03544030512070300468002e040c00c4100c4990f02e070107014130038817000c0c00b52108840008010f0198818014180b40c070604a80d010340c4214502c0e07003405200000f0b010f0003024031112074024080041c80c1d404a009642c4d4407409843c20594928843c24010113850401e0003802d03200781454180410300088004448001400c1208824107030200003110482e035005200c0d40364452050703c14415800030360014541450410404c0b5914280448825110000381c0300ca43c801140d000c1c4001b84030420071600030054004010800902d18490340d65801c102c3d800c2451100701c51481026540314030020300b41903904a900003006100078644148010020144208404880001908114107481c000c1201703125480118011506410750300120f0020303034001c841d001e84c080d44000100c9041c0900c149060080d8208103225581e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 614820701 1250 614819451 614819453
    0x1401090e0c130222030b060901150e030a020312030708070e032112040303020c0d0801051509030f060106022a0d030e0319061506080c1806040b0c060a050709050d 71
    0x2d03280c40d2020040540640070003070061804040702c4444e68a1310014100c03800c80d400c5040208101c00014510f500500041d001440140001c03542407500c48540c0c5007503130904202c440428200319119030001d41500ca035403418026181c440700035501c07960155681100c40d641c0d5403000c44003000c0c180c00c0303c1d40541100901912986800300780c0c07250001c11440c42490180a606c50200b0400b042310181c0c0042e60110320041d44034030a0000744645295880c0200c1c0fa03504240c0040c480080d1011202c50070f0000088600b2540c50901008140c401e286040c1ea070345680d0b0f910087e4840203d00c1c00100014803006020050300215956040700490252011024022a650540d0f100c2c42c220010b81c0d0511510074410301d200c00401203900d8051203100c012030360f40c1c1ca1078071050481206400c28802d00c020b44040294118012003a00c07610314808008604000044010610b1071099401504400b80c3c001004c0c201042d0024205014000206042105d65a01d08045405264a001d0f10380d0080c0030340e49500c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 614821951 1250 614820701 614820709
    0x4050c010f08010e040f0503181906080112140a06020309150c030423100e10051e06040227010e060a091a04081e061b16061104091401090e0c 62
    0x261702500c9011003400d4400d031a2601446c541200c00c480501c1e90a003075400c0030b00d08007002030781481c80c480722290186904000d00076000d80c805010b0b600f001c2e126070340c2020621062804420466541c036003598500209070500a000e0f5000b100c2d1070b1b07071601c0389800c4850148880215248180c41a030001800c5480325030b160102412946a0811081c2c2d1407510f0480c000701c00e004a000d051105500044d0038600780040030b080c050301540050084c1c2c0707041c0800c50150365085000e8181c10f20100600f11580ea4140010000c0c01030042c006a040c002c00c0c900207040039100000d002c00202621034420000b10541005554071444418a000900042c004c21041605200c0c0700210000020bd0b00d003070030707103580d000381c50181544a14030080510b5400030114540500055800030303a116406903a12070f2110b05107483d071158604000e09001001c0c1944288801075000c414501401c02c0380c030741d4603960f03044d00d0800b602810040c0ba071064080c40c000a000452482100e904428020190180c900498108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614823201 1250 614821951 614821979
    0x9061606150f0306050403021e030a02070e01060906050f22140907050901030c031d06010614070c03120c0f050319021b120703080408010c1d030c04020a05160b04050c010f0801 77
    0x307c081d8804c45500e00c0c24000e902000e5041d403080100216201c82070340c50004c0c40e03c2d071031350b1105000c0081d007001484803a40c0120090183c2c1e13070300c1c18401e80d20f00300800111054420f508400850800f00d0740501c0c801442c1c2000c1000f1a11401084405890504100b1a484c0800d0303404401080042000c89019406078202140c640c9803070400281c00d0800c162500e80d098800400c420b465000b01006122072030f048031100703c00c01c91a103280c500f040c11551700c0c4120500f80d40800380007207030f1403001004000c1c840c1040b508419484000940280c4807403800710741c0ca82003000d10f208202e20749505250340310720008541e25103041e150b01c980d1006502c0700600100c15111402001039006080001c000b080390003000304020186d2100000c0c0d1040c10000043c0305001d04031202403194150010400995000903207101402c00480d401a40d0750401607040e5241d2143c110311850144103000d800090216020354a440703140a9000d498414403801c004480305295a41d80360041039010006210380c24149040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 614824451 1250 614823201 614823203
    0xf100e010e0102030a15170619020405060a02071526070c12020a030207050108060904060b0f0d050307060507140a080604270c0522020d0209061606150f03060504 71
    0x78074100e415609030aa0780308440358540306440d420054a070415109588000303041c240d44050b800041d4a0809440b60800b501d07142c1032940608010340032046940c1200e00400009090030f031769030003284010752034010920520440c000da034480e0200c038a0203000b240c00a00ca08104a0780d40554032102300382980000360046040101c103141040000340191500b0304124095002802418a907141c000c0ca00343c52504a02e04008003041404040e40b81d800003e60010360002c00810021a564003081d0850782913040254001403c00d40b82e828401d0103c0103004950107484180030070342c2d45000c15a00340c000040305029201042003410360316403041d404103400200c020804200405108030a0500c40c8001e182070003c500c50183d428100642200726100030001a25444085034540d035414820410843d01c9105040d000609800101c2d2150f048411040c4000c19054880051400305c813100120790304201c4040d440d000c10301c800381c225000410201d406840800041c6411a5103c1028001c0640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 614825701 1250 614824451 614824453
    0x1030e070b031008060109110702010804030c0506072c0604030b040305090901030b16020109020f010e010e0d060b0316030f1709030a061b09050306010605030c0421020a080f100e 78
    0x1404982201103500440c007a101d00154000f503a42000b00346410040c06901c1041d005142520400040b88000b05882c0c000da02400c040f8040d13031303c07030601740c070070444101c00102903009107000c200b68a1780045c0400e62165407400080c04d04440803a100c121104000c3d100fa9220b034041c001003001642250140750b10601c2860002d00b002c40e911302040200500780c000b00da80e000580100318603404070b41c1e510a40d41205100034000e080468000c20f50745c0110751210790412050705002c2400d640101c00072000140c0240520301c90801c0d43c20120002c00003203060760721034055a90161100d110525043c4207994018011003991286030340c902480c20343c4245100100c200600c80809142e5090200400190142102042039030030445420200351203824004144010000d0900c85e913200050701c3c9043d14107a0030302d203503261160314420010740203640c0031011a40680b180700070105002c0c11001c010394070030389024034155143c682541d260200c2c4640c2d201640e00c20104e081055510341c10560300004504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 614826951 1250 614825701 614825713
    0x140c040504091b0303030903140315040f0605060711040506010f0f030c0c1a060306130b1302030a02030a1b0f0e0703091b0f21080a03021804140a0f060501050901030e 73
    0x403c0044059500560102c0e98601c2d00005041d041103604180c908116220b502c3c0d440c00040d0030036400b4004400034042c548d03552803000c0e0200c440d0b104c940900380007803d0b80c1e10744038540303490901d0207a000740da640210b0502c00400d40550248400d06000071158440058910480208400a101c00404031040007040080000481e08149902c000b015200c1d0340c400c603500c4d0110034903181c1000640141010140200d4036008154991502600a503031405003501042841c0002880d2030030026000c0d60501074210f0240401c016414154035040007001c000594603650254030311841b4462240003445000030300017400c0e9510a83c40140310718070a03034000001d80110100800500001d402c074042c4514040d405024000e0412403203c0d1200c02e8a801d1105130440340e4070122107000e4445201c06154020917860b0001c0d80010b0f28805001d005801000544a00448900c0380c40f41030b2171010803507252010f035140180c2540528403e07034034103840700340c6000c10b04001100101035170318074440a801a6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 614828201 1250 614826951 614826983
    0xf0e070b09151c0225080304121407030c0f02090906010e0f06091f09020301091505031204050907050c030307030204090b041b0509060c0f010c0f030b2d0a0306050a140c04050409 78
    0x245840400311b40904003064aa10b0130717282610508408130380350820700002d400054a08000725007100c607819898600407180c0419840c00c100000703110400258803d041b601080380b081d8000803414106c60420310307003a4041d144c000a601c01080103850250b080022a000100f51880307541035541141104e85443d04265940c050307840403a0400e1304400490b0f511b900800703c03901d0030035903c540a860205c0103008100495540c103a158456481064025414480024a458024425210b442d507100d426030380d40741340500d0018000d510a000f500c80c0580740c00300815540c00c041c4525491650520424180082c091401307a40680100d508164022400c005011001c001407062400c0000035000119102c20b0b80a006001800101a08820180381010608580d036840c404401c244240b00344090002d0a40016110702c400286003054210400410002c100542c5500c1f451080301d44034010092410301290b03d503460002a90401c00103602440184103d01d0246d2060340c006205104421000c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 614829451 1250 614828201 614828257
    0xc04050f180f06120309060304060518010204030b06100309020306010905090c0414150105031501050306011b03091e0e040809030a020d030e090a1e0f0e070b09151c02 73
    0x81294071801003142c04003844440c0c2020680141aa040c000145041c08580c1c004134801d400000c00141c8600c0c0c0b41c7e0702084921503000c02c42140e0b404000025565246c4034141440b03d0349050f41c3c0c89020b842c06c0070186603140d00c24410440410341c0200034085903460711708500003605000d07118003814040c00e000c0d0075941d5110300ca4140340c40c840c026060304501d049074172110302405401505051040420800851048a44030b0240611090a1498480c0c45500040311000084402c52014407140300c103032018507802c2107408007101d000c02e413509410040340706070581c000042c0c4038140c81d49030b2801c0402e000845800c0a0040490b001d41111042000e980014070520303410b06041e0085404610007004500300007a41c1940101d120009101030141c0120120380003585025070008196904441c0740e20302810f4211040603034108080b00e048540f90b080301c815aa00c40e01400340318101e6102001c07440702502041d62442200c0500c0e10f140740d0807105685010790b00c9000c0c0d00048091100e00740440c141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 614830701 1250 614829451 614829499
    0x5070f0c030225030507060309080714100c1205070e130209040e0d080f070504030309120f1b1403060f0705030414010c050a0e03120301091d06040311060f0c04050f 72
    0x7030364201c3c0000203451410201d0400403540c011000705401c00102c007000c250014100c0710241c0e400076117140300e400015881420260038954144c4070b0f60a01040d0460351764022111608541c4181c41000940c0719040c040d81c42e2514160941e070811510042c1c0090301c00c070355002e0803204030040c1c00402c02d80d80100d5540e043c6070b070f40307000c50010400380307014044c08000c04508541d014403d420a94605825500c002d069003040d441480303500d11202d580c0c9010030031303218040300b4110b52086c8604401c440900008051400e14001c0c10f160710320b0354802c00824a40022040e00500311402d44a450307845442080341c103507200520070303500355481d40c0801e411200c0911481700d0312540750380c0b540d460b0483c5e0500100390b1070f20810003610136803081c010b0701d8080d98400e00300c030f0444030b42280000d1000496074614a00b00c1080355098014080c2074100420300d60010759040d002d81d500b0040d11019921100c080b10004d0003920b035000d00351800e000038040c3e403d1034642c2101207600240041280012103851a50a013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 614831951 1250 614830701 614830753
    0x150c0801081f0b060408031309090b06220920060f0912121303021206161803020423070206010609091505091807060203070510020310120501060807050405070f0c0302 73
    0x40d0000496208c0110354450702400380840c14420300c034a00040e103035170070761101c090318a5124071403c003407481c2c600c06039800e4165824400d07075050080c5203441c10100c180c5068408041218541e840841400e86021300c11160801e0022018a081c1030019007804210b0450086d094500d02c5030b5030200107103881c80000740180c02c1c00c1007940c0b4240d030b0079881030002e000c03841c18001d4840e43c4030000b440140722160400c0754940f42c151804410401803020b5503e4071a601e540042e411600d03141d03100100200205007564001e803170550f00090750b29240412640d908c0c0074800e4100052058006214014881d08007007444072115040d000b50589820018050310000d5500b0346d040b0303083c030f0f4205a5044040c40130740020090b81c0050750900020703844040d210b0036081c010062032a40000003980b01c6c00c2d2038068001409400051420013152440d060380208840c0c024681e0b640f04040e00000ca03860300717003d8140f081003031b0f5403404034680c1068400e5a401a0b40c0c6011000d50044090039080c56000c5103402d0f0f010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 614833201 1250 614831951 614831953
    0x9080d05151e031009030f080604021b0a06050709050109030b060d080a050702030708120d0207050a140f060105090403050a0f11030c0d030609051e090c030a150c0801081f0b060408 79
    0x25001e44080500e42800c140321138451508001d400e201003900100e00c140100840e0800058070b40e980000603000380304200258264501a001414404d5400285081d50510503603080100e9181d1000903150040c4a12a050000d21a50010b0000a603201d45440c0c200c00c015000f04d10b0340c05196a108883d41010741c6103000030f0408203100003580380412041009007182c8002d0006d0280021940d06c1a12580c401a0b1040341c0001d130082c02c102c82000140305407a08a00b0701c80c620503d0001d420744400c1c2110041c64507200755400411385d4900303000070310700480c0d00d07407111490310320106001e59661504c1d117806428810340c00100c01403107506000500d1020000000340140c0380c400d01019048842540012608601c2c040402c08825035107503444201c0c495030f0078041100e0b5030702c01c8440c1c07500d0f0820403102d03018041d2440c00701c00c000c60307010b42c107924040c051805e00c6100e6000e101103804c0c0000340301c0c0819581c00802c1c895040f41100d06c000102d0f241c8003a002c00e105491070042413603075011b54010402c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 614834451 1250 614833201 614833249
    0xa1e0e031c081807030f050c1e0a0303080406020c06040b010602010c0206011a131805010f050f030a02060d230103050105090d17070306051206060405090109080d0515 73
    0x124039050040e4901035010104100d000c03034030391400400146005018100015100705042901c09081100b0002181c0c40110603100350158508a1303140c8042c11a214010128541800d050500c295803550186038094850182d0500e1610b08881000e809401580d96903030801134406100c1c0288080c510482c02080b014003503502d4564000c0c2115080c294a40c11508230000510008140a01c0c40640d141c1d8900c00a8540091070343d01500b080c6242d00c203040b500c0f00006001450445900180d0495030315110f003988042e91101805044201070781402c0e40b607084406044014030704280a0900c045002d180040c0ca070b05014040801d00d07006460900c584061003004000300310007401025484410b100241c445489031300c0e0b0141009040480800c2700e000400000b9070298840d43c001c200030300f002807803e0300712440da051702902c801d0190f4400c0c0c0100e041000003145484140601f1100c0d591009403130b4540007003128000700031305010f020781c070054100660f45045a5603a80280703120400c00825058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 614835701 1250 614834451 614834477
    0x70e04062c070306140613080303010609050f0a0308120c04120b15010c0512030702210a032405131b080907060f0504031202010f0f0902041404020f060a1e 68
    0x10445000070301c2c8404050600d90180030b09580e2010004030240240c403059180c03142c41c140b4421038500d6400883c040c4c8004400000c1159101071080d0131076500b0323100070480110580c10b000100540e400090851107040080c45e0b01601228003113035100742c010050504060b12406544080c19120380195801c00400c03082c0000510b507080b80401c80e410900b04000c108005a1740c05455900c0b449403120a69000710000b210f960003444054a80071024a1854440090a00c9100e135600100d51107400a8900103c0d28010074050284003807298104000300b00c6140780200b0001d84440c8041207408094070303085a000c50304203082800d1102c42c1c40391a050300d0f0b490300602907441c08605901440801515002074440d683c0c02c4000ca8082c1c1c1e821200701428009031100c1a4003606009080c0b183c01c510b040054070248056030320400c9007a01c226018801c030010100131490f501c1068401a5008030060b42404180c503140e4004c24030301806090686501088101500c032482001001c04081612100815 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 614836951 1250 614835701 614835779
    0x4030b060609010908240c03040c062001150303020607090e19060b04090608061311012007030308100501031a010f140409020d050609090703030f05070204020f040e010f0806070e0406 80
    0x2d0341f15403241c00c0d1504514050301c60059401e464440c41042c800c60129150841e0115a195500a070052009009010b01c054814210540703070720090b8014052440460186441442e1440444040b5a40c0460640f18107130300c14104204220412441c07640d9460001e140310b5914003a00082040c588005a414681342d03085040400080c10281000c02c41414000021352050b07041d04528403e00e006800501c0c0e0711182078120010000070591803054003000801c06610070b0045203d0303c000300d0095000303035440005400352041003c5141011380e840c01600800e5114141030790041050f0f192110707100402c0d00c011003540d1f0141e00581c08084c0c00090308094028103004847c5c000d403040c3d40e910340a1801c144010380300d49803404000c00b00280250343c421018454070a81b101690018421540e502c40c0d9014000c460b400340c070a018044441e40300004000c0707021603655040f18403590241241795204682100ca49520350007403035126554590200f18500144041d104008a8881112003298551809 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 614838201 1250 614836951 614837023
    0x1a07020703060e03040618181d190303060f0b030414030f0309070501080c0a0806041a03151008060c0409200a02010b15040f0612020f0c160b04030b060609010908 71
    0x101f0349103032100c0c0040042403140c15142a40390200f01c0c002400509610641c01c801d00c9000701d401c40340c80303822458448143c40c02e089600305d41c800e850800000c0e54544c0e1002c404c0d006441282c094002c2480002c001c201d03400440910040d451090b80d10f04113500c89100ea041d04280c98148031036220b11028401560858012600080700303490090078460744000080032048000c1c4014052900e519015802820300707049981c1d010350040030755044800c200e1000c1c600083c201d40d20506000207e400003040800440e950307001e2210885040e1425050403c2c4401400c00c4e00c0d17030349402404000700c80c800d100c10706014140c80c0c1025400030520070f01c4481000151103040c0f40020304e80c00d00304000c1021119043e410001c5034450b0a084503a81181040c0350024000c00c8449420300324006005e00e80404041803d0341c00120f102c20005046890b004481c00034015800014001d069001c04216a450900044c04c2c4d0084145000300882d6100c0c0280e0341002c4900c0000300840750600b001e81c1c04552001d0075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 614839451 1250 614838201 614838227
    0xa140f0d02070f1710060603090218040206031f030f0807110108060609010315050a030b0103020102120a050307031e090c090b01050f0304060c110105010b0a1205041a07020703060e030406 82
    0xb84461030402c010b41000920910030040400000c42180001c080140308000b0001404401003101c1507440c10081d01500c06013004034801c03012400050300d1030112011280c002c039009081541550b5980400c010380303c190501c00303514515402000170010702401070400b01d8034450742800340c81d01030701e1a1080c0a141e803101d186041c0080102000103580702c070402e80d081c0c141c0034a004120650742e00b800a42020042d0040747d04018a01800300c148075031a05894100c074402c2c3d00310b030504400103ea041c40c9003d0f0340c10600001d8010404602c00d14400d400140352104008001d03400828220500c50072142c2c510340840305141c0c1c0800c2008181210700c00e0711104030003801c0042c9841499100c10000d4400140001d1600d82d0b16812110380c640b0510015a880541c40c0003000380b07584030928000943c103c1c42c805800180c1001e0a00c00f01c54040c0540e0703006030360007403108035140b004881c0804e00c00c800401d100c0452041d11400000b1031528026144248144805950343d60308150001b04201c5054134 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 614840701 1250 614839451 614839453
    0x50f0d0e03091e092802180909060c030105090c0d050a0c08100b0301030611040f0e01030c0b040b18030f010c090f06090e160201020403080a08190e03090d02030a140f0d02 75
    0xd9207020349410130071551201e902010044c0e58859030728100c42c1c00509030302e8413050700d1002c103a11401ca000b1500c070070750280d800c44207841d140d82d40f4940c191380c03040121081100d1100900041016041c00d0709074a411135500d100541c01d010440c2e206c48100da070115000c0d1183d503100c0d00301506550700100d14903002202d14060301c0300c0c60700346000348030325210610000f00300c6681c072000315075607005007415140545400d08605d04029541d1b0031071200d070b1f4400c3c0002d8420000c1450001080c1102104440c101c4101601690400074940481191515103d808540501428000d00c14861080c400c4d54521000d64840404441c24030188812180140d0410710600c00040c00a220109400c102e2550050910070001c892501195040b4068012540300414001000c50060300c2c1540140c15188240000065401c10002450100d42699001d020040040c0c0080208045038148030184481c0140060100c4070240035517604c044007031208071651241074018071070344840d28200b42700d20102600248 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 614841951 1250 614840701 614840749
    0x50f031905060a06440109060806010f060e01090f0f060e0907050313080c030307030e0f0a21030603020d24020405010914040e1e0f03030f07050f0d0e0309 68
    0x5031014124a0142c4520250498405585a0300c1c80c01241d0000e00d50b451017030700074041290301c1c070103e40e80102030058247c4113041c0040819038040c001a102d0496910400c64602e03185000420394800503200b0340d450400100100c0403032900a101c8000b40142100d40c2d0a450705c030b1414100902c0101b03605012485400b0b400280708009601c2025039400c000d0f039801d1a084446a880c2ca03e1040c070426401e8012800044201b060709a0903501001150b42c0788810b844c910801c80080c40d88524a0130001403007107030001403c500d104000044080907241d141000154661a41c00080000d428901c0c202d6030b084038901400708900113000341021080c0782140550030326003420000f0b44001071500995107010b030010080105640c0e540c0011b0001b040040950700c2c02850007890720140443c500080d14030344100100140f8002c030010407248503881c691034080b500d07102d00c1d000310740c950711101c5814400d1105106548124845201c0e504144d02840000d41d640c180a40c248103d01a50800c00c042e0301c13a0300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 614843201 1250 614841951 614841959
    0x91401050d0209060120070f120203060712060302041d0c0a180f090210020a02011e050904020a03020c03040605030a050105090720160e0118060609030f03050f031905060a 75
    0x6000041c07a0154120744003000755665000481c5d10780c0a8420741080224546004800c80c6004201d5030162103828022044190b11303200c8955804c0c800a00094159024100068186202d450b940303107440c540510105016903260000f500b035544085021010301e03092154500c0042d001c10080e1142c04054a986404501c8c11900f00c1c5500300540c04010040e440701080380d0542656402000455030080407104910f4010340001d54030b40e0919412800314558101843c01e200c0d00c025400780070002661460710300340501c01480003075000f2074048424140c00b40801c600305001403014101400300c2d80c1d25107480e0b242000c0c4d01800d888041c0e001a009819003810b0000556118400d01c1415900340c24140902a00c031038001e20300300e01e07041d0180b450140035101280e1007030074410840c103c48070040181c816002e2254000101d030058480c3c40c011401c8a4002c0002400c003001980c4080c0c024201281094a880803401031a0701c1142c0402400b400c1242c0d1704c0701c1c04000d20606800c9502078424140c01030030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 614844451 1250 614843201 614843209
    0x60801030507031103031e03060108010b090a121719030b0d080403020405100302121b0901210c0308030106080405010f1401061101061a07050f06061011010f05010f09140105 76
    0x700f804050004c2115644c4611203403400c00c2110b50402000c0c0309040841400b007590b082c0c1d900f055802d0760024801c0310002400700145000c1e640c0c80350b401003402c4511881d03c4059603018071038aa04030f90503551401d100a102064002601245480070803039084804030304401400c4802c0c071102c241c0300360f240007003903008542600260383c2540d60540e400900c82d01e65141c7d0040c5000c441e800258801c01000555251060100d000b6075071000064129607400745031020880040310074011210741c040e40010f0b1180c0b5102005049124a000d402d00d2000d590300c82c0c40714034881d80241c2104010072400d50601042240902c115802084054030400203100f901d8100901c4082c10f10032a820451401c003540d002c00401e6100c00d00410b01c0440303d52a40f841011440d00e41e0300311440544850240c00a101399464001c1030440c032035200180050607a24a4030001d89a400031103c02020966072030743c0320390030f2031070394416180a1304035481c80b410380a280c4144c0c501925190264242c0c2d038a030000040000d521 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 614845701 1250 614844451 614844463
    0xf0102072109270c0906020d030e032d03130210032a1404031218060203030106050d0207120e150901080105040207021503010b04051014091207080a060f060608010305 73
    0x41601d00240c10650755036403402403256240410700c90340350144c800e0086411040c0e250407075089400341d560900400c5015004ca4240ca00c120309a07802c104924180f2055074400c08003840c88012181000740e03042010300034603400c1240c00d01301e010001c400e80003e500e801042c41032440701a150500406800000a0b45540c4800d4145a000b4a6150364001050b005070812035000e11440d060030b440303590364100410a00031240c042004100704a55a80c40507410355810401d54105030015840c5900c3d00c46c4c119001d5014400c0e059120b6808c1c000e400000311816003400c0c8408456031800300706d12200003088000c01c0d0082d600a8908010422503a081e40c0040c51141116011180181c80d403001c0d0010550801c000b107081240e502001001103082d4801c0d1000d08182c400076104e0154030a01c03444142c030001e811500d05649110140401040c91503c13060500d00f070204030090712000c035030710b500d4941707401381c40c400440358140c591f8140f00c0d440907284140402040f0619140445500d10345800341c03901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 614846951 1250 614845701 614845709
    0x504051b0f090423060109150b04060822030f180501091214061603110901050711120708031b0703030f1d0a060c0308060411030c09030703050f0102072109 68
    0xb0000d24009030038008105440c041c0f22420710620300b034800701c00c41078075242c60003402025241c92414455282c802d107003581110917100e948004928003814802c0944807a00c0c020701c041e007003140400e108100301c1c9403050394030a03092081d203070f051f100030400c1c00243c50f101e24041141d02c07240f48a00c040015070713400103541c0102c50380038051080d0416141803076505117800c0c003040040303403280c0b07014081c0c00e400e00d80706140f4138001550b00300000083c0c03602da44014840c89403198001403041c010000415103070480d201c00302000a1440800311081002c1a0070146607a006030059000032079503007200907681a91004c081c040e0f8010703140c52030440d68040c04c0b000801d207116003005103009446c88209003650380c102645c08020b140b11425913403207200134910001280110700280703059011a01c40d0a0500071111450581c3e8941800c5942d00c242011103a08409102035240c4a0000c001012400034407440301c440705000000350342d926260a10580e6140e40c2d000540c24000c449004071510341c2d00008003402d80e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 614848201 1250 614846951 614846959
    0xb0906030d0507050c030a0c08060f010311010e01020102090406140a0906150c1b080c041d060403110307020a0306050a1415010320030f0a0c05090d1401020f0d0504051b0f 75
    0x3071122030900038580340c50021780c5505031040048503c2444040400c440031180e1030130444e031882d0f4070900d144116000a11000f4602e03440b000c000c40c00c960080904801c0210103100045c180036088000405581c29507119420105d0340d41c05202c00307400d09900c18400360000c0c18061081307602e1310303840003000c0c400e0010300003c2000c0503043c1c2d0100041c04210001c10046043c004411685400c012034a0b48101d00456204600c1c0414808040083d01c65070500880e816000d044a5a120b4030306030b410080c100b6130604140002c00040c030050b501c1c00038039400b5601904e000a5245011030410301280c0009288181501c502d10030802c080c41074034003980d0440020f10300401c4045030410138a00d00b050091000085210202c20842c00801c0540f0003440303000300701c109210f481c0207240c081e01c10f440b030f42130180d4100d00460f00351004201280c00100c4500745107400181343c20110b031101c0700d0300c0c3c02c0350840c0c0a003a92a14103000074070504203c050388032078102c0a240c4402c0c05440002d07000c41d500126803802 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 614849451 1250 614848201 614848207
    0x60507020105030a150e040b06041413021201020d021c15150309050c040c0224060f040213050406030f0c0e0c120402031e010b041b050318030c01140a0b0906030d05 72
    0x10302e070140680e040050440c18051b040314100341c40d01d489a07280445200c0d0065107080310b005080c1070b62801c228014120a01050403075856602032203c410040c0d100d0400c0c40d0b400300450721801090344024068110b00809200403481c00c41b045c1c8040e5410001f28842e5070044131400e12040d51500e07140103030313180d4070300b000280d0708a103280c01e5040208030303a10b80780c0c4185020680c81095402140c2d445800c0803000048006491000740502001010340d00d65130010341068595810b03003000c5d03005100c0c0d054084501940155180000740c1a40c09a4004540b5211480c0000e0f04200d4090702410142238802807500451034048511206401540540e072100d00400300030030300790b480501207003c05880c81c500d003103c0c46641206560292070314542c264011032612409002411107100d941c0d802c25120b41d00d080c81d545640e8505e03c6083c180c000320f040d040c00100400344040e0000d07c1115517000d040b0310b010000780341c402c9200c001c64a894007401e01810f20f40b8108011079030701050001c60500c9904140c1d031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 614850701 1250 614849451 614849471
    0x6031026060619080a06060620060112080c0105010816090e0a0213090218190e060711070b03040f030807052d040b0711040605060a0e2b0318060507020105030a 70
    0x443da801580200458040c4110b00c01c00d200c855000f20050303d00d030b61107510050b15089030341004d81701100c1c004031031038101c200103000000d1240b60601d4200d0240c070b1444c0c10003000c1d944442c00c4440170ba001e070215038880c08445c8101031041c0c04040052803008001c0054110f8000c3d03445c0c4840d100c5100921034169aa8039200e0103506501080201ea0090310700c034079031110703a403424000c1d03041580c1c160800c402c500c03605c1a507003c050203404850b04240d8040c0c6095145d03401e0981f1050078061458a090184040101d00350101d80c02840c0f14a0103a284020000343c0c034140607002e040702911103010002304000900e071300e03c01000d6048841101d0354044045000011030503003e409590008c41150900080700002c0c0420320300018605101280e007041256620010002c062042e40703240c801250000c0070f01589403070f0400318501a281d1b82051503440c043d20702194600024102800c80c045548107043c0c0307203105d0401c002c0d03a02600c41418005c1c81c242407a0006841400001c0074911020b8171048414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 614851951 1250 614850701 614850739
    0x11030a11061c0c031a03011107020d082503081014090406021b0102040e01080606010903060b06090d03021b0603091005090a0f03020303010e0f06090105010c02040b060310260606 78
    0x2e050b504032a4000c100c00320341081c00030040e10000b1250103100c100b44541c440180341c103108000d05102c000d1401c914040a0b6800e100b00b840b103034070040e40d840405000d03c80c3c02c40a070120460017005800f45000d9040c41610f0060464071002d4044120030031406400d2040c2e6200148850b5201803c4039100034941e60f0b0702d8850042d20881041d910100c040760305117044802d054014205495075408902d031076130307210404079a40b01411a06540042d41521040000c600c4662201150082c090084e626218080c00401d14008912100f00d0044e80802e010388081401c407000c94210407000c4510602d5801c00d044030a694011000004100c43e960380c001c40ca040d07908010350401e180d40441070750044240303824003039144d400900c100e441c40002c0030001042c43c905209190300c10308000340310103403990030302004407503c2522000498000769030392000001a40d861002c0d62159186625644106e03041c021680e400c186005000301030200096070450035200040303a100d0380400240d541c900600320903561a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 614853201 1250 614851951 614851987
    0x5100e0441010b1305092d0f0c0108060d38090c0609040c030b09180709021603030906020714010b01020d020102070804090507020a0b04031808030a0c060c0908071211030a1106 77
    0xb050030411800403403c04884120031f40f083c50001c2030140c07900e0ba91841600784d1030308040b1103c9800280040005540b601e080c904071000c003801000007500100c2c1508204003484070141e0a20110401c0c1002543c1030600c6241195020210101034541c3c0ca40b0080800d80ca0b00900840c684140d440b0261840650f11130780c040f80d41c506008052100c5030518010080943c558400303140d2560154820114600b900c5000701c030000d45c044464800c0038405620b00b18001e00003040100d6425408005202c00700c0c14007003017034031141c146800006a0000c001e0000e403619002c42c40a40544e40103125500102c0d1181c0260740441d4003000d0b01066a075900c0c41c0407070030308174202001440b0405a6040c803042c5039200042202201c072400030381e01c82c641c4403030115649005141c01500082e900540400000d081c83e0840400c1c18001d0500c141c03603644610705c090034900250060384803140358041e64024003504410400b8541016400343c004c450f00d686400c03103141c1d40c00e114180105c8000681c110209028058 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 614854451 1250 614853201 614853223
    0x111041511060f0c0f12071119061116050d0206070f08040f050307150504020406051c060c050d0c0503060306010b0c030f07020102100f0c020c010305100e0441010b130509 75
    0xd601e6403245d495201e0380c86d604040d0b0700c0200107102040300f144203800020705c80d5000c07001d5801d128140d9420741d403044003601151350740030102035050200070310b011a45001c98074802d00c24000b605600c40740d540028500740c001801c40c0200103a800c2044c070340541140445400c04e4004041c0d80310004542011427841c8114075008044803940c5480342c4041245602c1280101c1c0700300e4081c403e0035074a40c01c002070f10400080d0041c0000808900a0000302c03603520200480480d41041030405030781c41394000c110ba9200220740e02194000040203520710707082c0035042c05850306481c41400c22210b0000250b490007402c00740070340c0c50000a030344015607008214041180c622200140441542c0300c1254019108410301c15000d031180c00c8282060390b0081c001c0030b110303060340341e400c40301180b501d07003140c04610740039100740c80242c00b400b01002542e0b0903c403d0000100e0081200600460840f1000070030486004512141e034905081140b503a0384a245000c2c11070040710006c10700d40c65200700d0700c1c10724840b818 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 614855701 1250 614854451 614854477
    0x8160e0a0e0f04050c0301271106130e0f01080d0f0909090c09050f06010e0d170a091712072a06030617070e01050607050a050111041511060f0c 63
    0x304000c2c0c1e000030780300b81501c1070b803043c8141c62030b4070350703d900f45030903100b04441e0651036400201e070a50000f50503580e80c10480c0d0051a401c0c1c10001024003003101c0740c1c00a59a8007804110303020501a4600043c0d115800c0007262003680001d61401d07030345644500d110001803040102807440000000e1244404102514000900b00300300000f034603061001d48810300c60390a00c01e0406002852541007003080b2071240d801a10b500c0107036944001000355850151004546003024801b213402811040c602421100e80203803142d0307441600b01004083c240c08051001462f40e4407203c008071003000c2400c155940e095000c10401c0201c100068046100145550701200c0165501c100240709079060f0082c90481c0e80c4028600884030030b0310803160700c550840c0551a0241c810f4001006503042c000020300c0d41e28003034010f49a0080c1203954582c01e503520940e007410541804a003e0268240c0450b164601e0801801c008882c0703003405100c980c03100d00080254000b518180001501d0110100c100c81c00a40485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 614856951 1250 614855701 614855729
    0xc050712080c2a0d020108010b1c02030906010611061e0a02040305160501121107140102090a063506010305220606030b0a090f06090303020d1107060c08160e0a 70
    0x74000160402840c0180e180640c0201c040f8014282200c00c0e40071107030107070f40304c650b96802c1c0092001280d001d0b80024490784a03494940e80b0300f8210b8400b450240281c0c0c000f4040030751411200825100008243e004540c1011041c8040d0f44058462460802c441003c3c0c012540d5800110f50024041d5a10285c002d0045100c44501c1a02200c03668065910980300d5140c2d2061a000b03000850703c44450b0038400840130040000441c500c0ba0489022040090003d1b2030600b030600810f001b0540c1d5030024000c901d425001c00301c41d441c1c840c86d0320b00ca010170840d42c00001000b4003000c0c03400400503000a05241d502e60220341c0309806140c2c4426100d0b0144049030301c0014926249009080500c400e440d0510002c0c0401c0d106010385c050100140d8010002c1d031504503060715501c004003118003044040c95401c002244040046000e40001c01000b0a105034443c00142003050a5510141b10a0200400e400402203a042204480712038036899290080840380c1c4c3c0004101e0040c0e150f0402d918a590034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 614858201 1250 614856951 614856973
    0xa030c0603020a030c080910020d022802010501080c011d031c02030c0606100e010f1b0305030a0506010809071202270615040b07020d050c09010305010203160c050712080c 75
    0x1d078000b0b01c11840369580400070500940003c80b075040301514080e280750400d41d2403801c241c20079009440e0b00e000c1410b00500d0482900742ca401071070142151030204a010020100300f0a07028803601e4010100e02024090107a81000000d10326100d01e24407082e0b95803240002080d94904008030040d500300704403100270100500b03401035500c2d00101c0f00c2e003100703102e00c0002880da410b01d10104d0341c0c0d400d00740d01c2e4070460345540401519081e08182550040080710102c0d441c812682c0641451a20700903203d1640d07905059916030255400104014103200680c0240400420001008002c43c2c000c00e401401c420340c24400109080b2802c810380c2003420115840482011112071014000c0380100c0b00701214031103003095082c060145210380d01d8181ca042c4200c1005d030404103441c07001e10348510240c440000020300040c00041c170a800c00c0d10160350210421107082d0718406043e802c2c0b40b06003003807000036402d60798850340e828850144002801018212804105100082e030321494524816178600f040c3c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 614859451 1250 614858201 614858207
    0x8092b170c090f010212040603020309190b0417031303081e010e27030a030c030f050a0603060608070f0302062109060906010f0605031512151f0815060a030c06 70
    0xc4901564414582c68000d40d51070745c00010386400e010b080b5100c580c00c140c64004194001c0d00020031525003800f42d80c003c886900021080e0390001072040c500c4111074101802c1209952117110141d1785080d40030030034000c3c103402041c02c0740b2203182d2510700040b441d074501c41c8010700e180c2040e490b5503079202c2000c0042560a9000d6a0901c610008002d02030035554058070040301190b100c40809458000700040050140720790060f440c036107007508020038800f072500002c508aa4080310061200c9a5406003802008441c0c002c0c0700040c1346040061204a003441810098041240b00007032084800240c03440c070015003001c03c0407070242214032003800d40c030307085d00c04a80b64041100c814060f40549000400e02100c5c003500a415544241e40d16401c642d1074070083c041e2162540a95070340001c0426100b040944100303d0b4012544500080d020f02d03050001050031804502038060101503a207907414800305400094166900c0206007130006185c8928004c1080030501e90030143c50b48541a50106000fa0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 614860701 1250 614859451 614859457
    0xf0308030906060910090515060406120f02090a21141b041802010c050f070b04090b030f1f0b03060106110f280c090c030b0108092b170c 60
    0x1030746816140b40c0d0380c41c02c0800000c050220b4400c1106401540c080c80180c482e079101e0380d84070b44403c52002c01890072200007003180d0800e600c488000faa25002900c100982c0307018005403250882010350401740342c0340c0084c44d141914010f00f01c00251520a5411028201c048980e880c1e4020031910701c10000b2511042d05d4464403022401940e050550401242c103083c0b0500240ca4000c100300d4607600d60f945d00454442d001a43d0a071118800c0000c203440c020804e00c004001002d00b0107106940f2440c040b03c0364260ba0341010300e58031176003001842240b19a40400c16101104018140064000b8001c118000500054201035054030030b074030000c00c0c2d0b00c2d04942d400c008041500f003140d0b001d003200d160a507612815502001005841c0341c2070804550710000c44181001d124100748238460761500c4890302119560030740000041d8480e500d005865030422a419000040603000e0301481140b8205039500507030324110b0030318040e40b5401000889103d0740c508002844880445030650a00011081c01d9230 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 614861951 1250 614860701 614860711
    0x60603050f01060c0c060f050c060a0e10150b09190b030f0a021c0b0109081605011e0206070c06060506270103090201140309150106050c01182a0f030803 67
    0x80500400419001d0090034142162036005d03605128003810548100e844c00701c0e0740340c0e000c00d00c1018040d4020740c1005100d8180b164450b10380000b400850086501e1410052005c4100c00500d070505815488a103140050255000942025662100c03000071030b00c0c0c1003d51a01c01250840c24402190b8818160b0055001c4c140a403040241b0b40c80b00381d00c41c01248601142d05161401008a900c1a459a500030240e01c0905040c29810709680740100c505221400d46100100c2544840074040381da00850243d0402400043c0c05040311308a20019682d060301500101c1032000b408103000c00c0120350f40147c805002c4c050070072074840000003041c1c030701c0900602c21031a100110034a0085194424805d121a143c4c050b501c1044c220120501c4003090341c80501503603014010780c4a50708900b00b06441c0c05008020961b642e680e038400008620b42100c4503010f0510040d28055010030100d0f80750000b0410340740c02c0800c68520012103c10000103075000e0b07446401500b0f07400c0c600100b1710140102940c0700c0c3d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 614863201 1250 614861951 614861971
    0x20606011404080d0315090207032d020604030c0819020606011101270204140c0c0610050a0312110601080706170709170102070501021306031802131e06060305 70
    0x5803540103901071a50041c0c1c05080a160311020401d140c05120f0780200031511001c03e1480c6509031100500e0050b80d219034000e8002c1034241411075040200c1d0f46290b9104402c0350340c04c2002aa07154002074551002420141c01c01151246013014010071604a80d841c40314046c2a420096007044003a40310f040458506020420704800041d0780c3c4018010030425604070203a22443d03082420343e42e00300542e031079004e83c0c0060340d42100b4511014055082030003881003052080d101c0c0c18181c68146002c1d8010041c540110b0810800c10454030750076039920076650b02141c0180303500760b01e120440d64842000344448461041c4000010010000301d104001d5889540d10801c640c0094ce825075004a4141c0d661000111000c0c4c0420641000103103c20b1900308a8001500d8180b194880c54203a0b000385075240200421940c041020680500c1040f8000c04180c1c804000300c00550006400010303107207140704c056500c1d01c02500a0014100006954020b9010204801c84d1101e600400401c1d081343e1305161 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 614864451 1250 614863201 614863217
    0x71a040c061e050313240902120309090a23070801081e0c040c0c240509010902181e040f0c050d081e0f031306110c03043302060601 58
    0x28080c65507400e05000d006680301c4034030315210340c3c40c03022456901e041705a4141a0500820002c81c0d48403140845c0e040700c07100b000c0b0354480340b4010440603224160450080e644104918600383e202c01c00000c0e403120081e0300c0041c9017007040b10305d02d203400c160390340306c08891070203208000b40c41d908020054185c1c0d1200044409004120102c91480381004080203910b920204c498000d03032a060304800e080d20424034040d4200c0701140d59110300307424490440d02182603100d045091242440c0300c0c00f83e00101290080c89600c080b074002c14401001300814401124010000510b02c080900c52119401c4000e00d07100194a02414040410068440120780303500d520700001038507140030341181403aa0340041f403103860b041001088c2c04e51020008800340c1c40e60424000d981308440e10030040c40c41401d000c0d5a0340c1d80844207141040880f42c00181c0110900010701120800100003c280c03006c0d0342154014400c0040850341d0b03002d071000186171a0401001c0705440c0d828035540811418000c40003a00c2d2001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 614865701 1250 614864451 614864477
    0x70c0209160e060703090302120f0f010506030d1434030201090b09010507050301060518061603020607140d0e010e060c13080a0201320417060a06050303040605071a040c06 75
    0x2820320504c0d03409800180d51034014000f5141c41e11303d030808041410300711003001c01c03400c50f65800c09400c0fa40b10012655904100300c1c0754102031011040150782442e107035a05a400e2100e500c0c8500a041c010115a00c8070a54202014140300c200302c1051000d80c0034051700d42c00c600d00203020b00074011046440b1070980001c19140607050141501407201038036554251ba080803c11201c0c1d4000d00d84210600c2803041002d130042d1680c4004042d040c0034650b03103041346c144c2401c0192501402404100400040c005124000c0c0041001e0303821490103080c01141d101035610100c0e0150280c6045d00c00d8038054201807001d007080c07600090a418a41ca60020140c4e951041180e40300c000020303002c3c0c081340980300702d9202204e41d0b1400f9001c5000c00d884c4c550461030303148400c4149402c02d401c510050310070b85600902c3c1d402c040210690040f80550248001414107001c2901c90090b44200028040081031400800c0340500503086182d0003500d05100700d00e46410322001400142c49000003280156a4540c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 614866951 1250 614865701 614865709
    0x60806040b1b04031b08010c021f02130810020702100809030f0c010e0618070b03040804030b060a03060915050105031b091503120904060b1908070c0209160e 69
    0x18455604021101007980e281d6030b200080040480100300e07001c2080001000182100c01c5038211351682c0032038003d40d9402c0001207421902003052420541d40604100c140388003818016145410725000b0150300c445001846000e0f1300d43c5500084854010030403040c1940c091030740a829058000c69144101c03a80705401554460010f031410111900200007820b000d40d91a0700800813a240c1c072000140c6140c10360321507400d00c00142e680c1c000581d007040c2e0741c5000010400420002d01048020586903040c0b07691921124803651000500b158081c0c0e00007000c0380d0760a900000203580202c41403082d20051302c0c15603500c1c080c21800104131071a010011525040014070f12510442003100c01002d1500d602c2044109603000f05803445482c003580c1d031105541ca0a06c01c00c1c0060700040d20880d02d0f00140c808003c00d9590341d400c90a55200140a25100220074001c82804a8403a003004065510f51540854a0b113039000000394000030781109200944111219107680e11406a072810000740c0040200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 614868201 1250 614866951 614866963
    0x30210170c03102102091e09011415180a06150e090708010302060d0504062009031212010b3a05010504020903100f090c0f150203042403060e010909060608 68
    0x100c00c1420301d0543e06001400c02c6ca510941080649070310841c01412000d9071195110215184c04859444051040c80049400400b039040901400340122544803000813401642e4088240da88a041502c0820310a04041c1e0110b00601120403e8450b18160f03910044d10190303800500a00841611000680c0c803845001c82c941625402021985002e031540741040203000060003d0701c00682e1140f50441545070002220070400c034103190180c44a440208040c101454128000a0007004025003070241070602074040c15160a014030980310710490145001c071108180381e9603180b00003030040306001c030747c400019002601540818041c07a0388500070300090380258901d00307802d43e04c1507203050030a078820341200940d603540f554001519401034a0340301da0303412075038042c0800c0d20400030f090003e075603581044030500700d2030b0000318900307481c040000e0101050a0603016031000c40480c0003201034843e0300100018546030201075031550b168001c00c8001c018043c02100d141d4500407000660000102d24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 614869451 1250 614868201 614868239
    0x70312050a120f0f181a01030218041407230d05030901210515011b0f021c0c081b010903020604050105160602161406040b01030210170c0310 62
    0x95100b00302e41d11268002030403202c24a41d511503121603940858200310f104507040c03120061001c0900c0044d03400e0035a50001140403509201d029a4014030250b240d003401c0c1c482084203100f0b107900c540e032542000030703d9803641d10768000140510040003694100340c0c05010f00722000c1000e140310b10005441040503601e190500180b0341d401c140801e80c1c0e10341c0a0b5001e0881007120000d40c803c00c450354a20038040703400445a5910303040c081e009408165900416200c2061102c0e440806160a81d0b2590007007481700b00002031141d1100c004803409095450001925140e200400b2603000340c6880340d407602ea50341803264034074035541d69800f540e2962049440c1012280c0180c441450141000700440f0b00b03600c08468589188403c0b030680300058038902c003e161703040c90080300107000c81c40e5162490309002014520340c0a41d000c2424480800e10f030700902c03030449504036864070b45400c900005482c01040c11400e00d404842c0c20040001c04000e01c0001e5215809082c00c40c0d1a29840306c054070844400c00e10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 614870701 1250 614869451 614869457
    0x120415180210020f0303131b0f14150a08040506070e0a03060c0302040b070606050103050f190e0c060409063b04150609091109070e010309060e07030302070312050a 72
    0x5032080250034120214001c5000780e2041c0c540d00040b10040341c2c5540e20680d010551008810f80f0b00013440b03024100c3c28810004100700c0b50b00149082980c901440180c000c11148054080c16400180d540702c3c5c050401007213003108151207400041015103a0391040b0b0b01541c040c0a50382c0003c1a045c418501c0c0000c0440081c0304881d0142540c41703140c0148429510801032650803c000705000c5800701c084c05280744180d0b40400d204d400d1500040aa0300040c1041085005450034048070103142c40807000c64503030b13800c000260640f01980302407408010502540c1c00c6040054007085664841d0000750a42e5440d54408450301d0445d107900205962515941c8650555030400c281e208800c200c070160050700991400312042c0311a583c020489000740e01c215016562044290208a100039002e0b5001d40200c80c4040c0616019102a0050040c00f8055040690312440e0170100010303030f480300c1c0d80d42c3c2c1600d02301c0310300b00d0b203034a0081c3d99039800d80010340b91298005081e00402c1d01c643c048034541c3d0881d41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 614871951 1250 614870701 614870741
    0x90e0f07050d08070c0b0c03180f0612040c2d0e100611070306050f0603010b0a03020619140309070302031501050f0d0305070b0702101401053102120415 67
    0x6150f08070700d41c105031001c82c1c11041c3c2d64400031710561410090010081c104d409141e4541840700c021841ca4031912040e806106001010b40c4595a1070050340c07000c030444403c400b5203580e6031420012040e42c1d604000884402540c1801c50907190786891000400d004240d1120f00d5203500901e002008100c03403140001c00c403204240300c1103101d00c18621142200c81e084070300d0107450fa910401034420803510146164100ca04100240c9024050707184070100580b40c05c000c050a6801040c02da20035110341f45569562804020176052095005a804104000740342d502d90601051003038450760315210a84c802d214020010112143d40320003036040350002810000c0b1054088103001801340b01c4030702a001d000061140c1c00c0841c241c100b610344244441c5d03001e8a0005041484001240e4224150310134420200c00184203540380c001640702000240c240c403040107511500c02010521800030104800382c00031070b00f40e40000841031441d000714810915443d03103290720b201c0341c8112603640c0c400700101241d075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 614873201 1250 614871951 614871953
    0x25140d05040f15091805060a1401080a021804110309121620130902010f020d0207171c020109020f0909101a1002060a061a07032601090e0f07050d 64
    0x308041e040003c500d4201440c140365100e80000d4075001c3d2144940300c203a1904100001c1c0e01d42401d01c0c8000c0c1c0030000d0002c100b10360b030710300082c035080e0000c194032000c503400540c05a4090b0000c52280c0002401002030041202140e9451107a8000f994480300398801d610b1180b030140f501e042690101203420b110001140030b42c2c0ca507005588211a200210030744e40c103034002546e807240c0c0d00b04d030520480180003040c2c0103604d1000403c2d80c025001d0710400c54001d1500d60b04a103602003201300490742ca804a0000704420040365905010308240515101203c0c01104101e03550107400806079140202c0b07000038800241e2040c4805d20504440740c00c2150081c0c90301d0680717001150f02c44d0511000a2412920400720300010400e190030303038207080001d680580100407102c0c80d40c0c0070b04000762100c00c0040050141c0048408240c3c014420000c06004c4103000104a4441903d5544041e02d01c261b0485a1965260f00742c1d0300a0000f03542d80a881d00940321012001e181c001040c6048840242501104000c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 614874451 1250 614873201 614873219
    0x60304170d020f03091b010219170904020a12050705090f1e03030d0e10140708181204081c0530010303030b0907080402090c25140d05040f 61
    0x5003000e8500c090b030911049034000c02c42c0000d144034141c8030004000030807508464240411284c40b1090441d440307481c0c541e6140f0b0406090500b41070780b002c0c0b4060044850309903085280603007040e5640003480440d5000342d80d5404054411444084481003059868900b0100d0749803181050045d0005000900424030303060603103011503c60b4240200002e20315205001a046a01c62081100010b4440901101e40d03035092122503194403e1420400c800d81c040501440c0c0740e28010500010700c81984005000100e40114842e06404100152140ca41281300e001d091070300240a40c000620030301c00c2c040e1034501d040c0c000c03070115001500c500e401c019400000d04180034080070a0582c014070004030607400840c0d40c5500c0d02a601c039480105000d02e040b0140040007000070301282c10130514109000260f200c141005400ca201d01100c203a84036505034905040403400110403110022850305038050200031204107e020351420151004042202c0707048035180650300408a1030000d2900400c06084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 614875701 1250 614874451 614874457
    0x80c03030307050a021e061906080a081c05010303170106051812070801050a051e0411012f0a0302060106090e01140d050304030308010306140915040c08191106030417 73
    0xda05c1220228154101c2c041d0718140941030701441c90344840184429400d00122036240f0681494040250500c1c1000b10b60f1b4881d1a490301510b00d4800081e1242c0142d04c9100c0304505043c108814005940c1d20700d001413110848030381039005050305500200b0042d1007501195140d8a01c0030400d8510b000f0070003004a80f030011589880380b807140120004120100380241d81c441c2d0703d44c0c00002060301c2d03d08410686440001d00a14414441c0810400052a101c0281c01442000e00c1d02c1c0042e45a1b0901c81000b10581c02a0840003144010140290038400038140091038402d600780c1d03a060741c0e85d070800c1d203103034451b401083c40c408003803c01803000c9103c01a161456640080c0342400c00d0200781c0310107040d680280c109400003106040188180701a500640607030000880031110f00d40741074061991550750710b080320b01100061101160a100440c0340c51800381c41d03404180d030f540603810880250221207004c01110b2034106036041e00d0a074601001540d02c119040102000d80030b203d0b0301d5a000c0340d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 614876951 1250 614875701 614875717
    0x5040515030627012405030109030c060902040b1e0f010503091203061513030302010614010503060f210c0f1e0d14120c0c0f1e062101050901080c0303030705 69
    0xd0100e1115200c0a00900a000002d002140b1366641790801442a02c20118540c018602a0381401c4041000940c0005000c00d001e4106a0000d5034080ba072000401810f13001280c6903106401c4011201c603401000040280e26900710b48134010750031540c00654517400120303101105c030340100003502c5194408200035a4402c40c000c1070514641d000d14810750035500704250b888100d892007131080c07081503024856180078000030b10151581071032042c0000e100f072100900e9240201c0d2000380f9030540b5220241c3e0fa950218100055001c01806881c0903035a0385091101e1600ca9940f00d009058207040c0800da11444c2007003404617160384244072060003103440d80043c044035941098204154011400d214920640643e1201a5a41c8860001607850544511429485031000341300b1031010f40c1d52410440c509155400e4070394181104880000d480e801649080c1c0f00000d1010a9652a1048100818182c40049980030f06698a07404031664a49200000a030154810004100124051005040d4071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 614878201 1250 614876951 614877001
    0x1050d080c0106030506061c05100b030c0d08030703060e0f16020a140706090b09010206011403030408060a0e0f03210a1b09030507090b1305090106050d0c050405150306 74
    0x1004450300803a085031110784c0140d806820010901c00350345005c1c490343c800401521801070f214403207511040d860302041180d80c401e00b0f42d2004218040e44081c0402100c0240c01840704041f400740e41441d00130f543c412502c02c2c001910b17054012511510481c3c1850160301c1c1604207888075920083d85510302d11910070101c095104d4100540000f03540fa41d643c00103039040c14040c00d1070a19191000e460104903030040181007d050240c4c0b4080d90340001c5a41c11641c1c0ca004502d03141043c80b01181c11032003150410007150080e503081200c1c80c0c030303550841003c801c0800d049603441c1004401031602e90140702e510103044810443c41e915984501410503030404628400024269034510303200b01c1154030b4070004004107422079000c00034840280010700007050800020301c102d2400400254003a00f442400d40c1c01c040e50746000c0b421008003580800b001c1c2030007402040010701141450080d0052034403495114605200026400d0301d440510b004c3c3d50b0300c0140c004d01c09521a07403409064408490301c44004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 614879451 1250 614878201 614878207
    0x40509060f0a0b180604080a020f041112041202060601050706091104140f010509090712050319050c010e01020405010e0603040201121803091a1c021e0a020c0103050103080301050d08 80
    0x2e5403405440b000401038180c4190f941c840e000c0f00000301c0e003c0c9030f80039403080300144401c002d0b180d004104421911307411202c14108100100025004001c9441c0f2050f00305030200303190b012072010a252070700490040e031203040c589e21340440c102c0e501c00d0202c0301103001400c28400f0b0340020381c00b07802420303415100356050148182032401280448804100f45080c11840c1c2081c00300c4032816000e041e014000540c0d0407511440e082c0171207aa80e0215200d0500c030080410f400c2d03001d01c081802500c01c49403031110340034003089001c0c0000701203402c0f0342d200502c0d9500c1e02c0c030ba0401c00c0205200305c0b000c858068640700b034000d40d14030401030590002030003a414051040301800040266103d00b20f0b54041091040c54442a00d05004040c440d6030381117090961161012074001a001c1c1055561035254060056002c210320041704000e805508041121443c0029004c074607040c20601502c644940c6500b10f403400c5200d00c0044054500a00c4003400b0000e04100501150134004040c00625000d040c07440c4ca = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 614880701 1250 614879451 614879479
    0x15050309030c1606080a0b10180306060b12010b03012103020114190605090f160212070614150d0305090d1e03200309040b1f030c020609010c0504050906 67
    0x305000028607040d490141c2c603e0248100c5800481e0039402c40344d0030f0760030410003200d06c01080300d0618620844051004143c500d15900d6400b41e4a80007441e8800428401c031f03030f6552001001508a5a0000164420f080001c40d1140340304050302c1c102d444040440c62000c034000e0707920b802c40002180660455494820460407804616501c601562003540a0489426900d20110441e41140c1006204900031014802052504450303103400c04880d00b1544a8800c85242c181d20385070407031014001d400c001040391300900a0551200b0b803408441c15541d00c00d0f82d6152440c0b03009111023014294084410044040401d1054010700380800703003d4200d00412039152103421140203502442108198108081401c06600c038548408410044061685048c00b1504607526030180125a6010355660b00d104400380d076883d006011b90f02c0c1c0b40040312075802002d0340001d01030b0451b400302d1005441604045117207410705114446d0074004c0745da00c1e0303414a8280810400300013405441580e004440b803080072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 614881951 1250 614880701 614880703
    0x60703050708031503010c09030503040e090c0d0b06010806150d1e06030c1703030421050f030f070f082e090e06010e010b0909010e0403030e06130203060a050115050309030c 76
    0x143c0602c0b40d400c444c0141e484081c04050030f4542404954041000d0010b04000044000061300c0c181c0b051410f603101c0721b80d40c416109240045018003950700421151050341403001d0801418090182070b84c4149980d5180d80038885903200c03814005006c00010000514440b0039039006c000e001c8a00c02c02d011081004942d10020758a5640094501c0c42d01107034100716007141d910b025000001410080c500f1450240c035080c0820400e0122810b01da212203000c1c000561042d000c0380c2c0c0250007400d07a1500c81c00c00000c10135181c070048608802207400e200020366494024440b00323104e1071074a0310386c079000725031004019000048203100d540039408010010500745900d005540114100310014102c940c5480b5016511080603408564010b40802248500392a0b100d203090565100308003080080d16145000c600900e040601d440d1580610020302c101c444064030841c410a000b182102d940381c8a009441c0d00321074081c07180a0780582c602842140e03083c024405141d209111074181c83c01e0015501c401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 614883201 1250 614881951 614881957
    0x9130b070e040c1710080d1d0d03080a05070e06030c16050d02010e0723010e0d02040f020c011a0603130f0c0605190e01020606061c1a040506120a02060703050708 71
    0xc44003040034071402c48400d040340d404c400c0d030201d03260ba0580c05032490700b0030a035124096032403044100041b0940c40d01b12911000241d46034440041d01e0000000810b08000302401001e4650711903107401c00c00400c4c946481400601c1d48a08028907061a40e00c1301c1d8079020165108081045d03c6900001507800418014000741600190710b8001161841d8000120781c1020000d400c507585000c0c0c80ca1034000384000d010702c52000c1440c01c1c00c1c1f4072001c2c045100060340703254030303018020f41c050305010100c9031100c0c00e50007134100701c00780704002c0c0310411b030049201e640d0003110303804180c004200740001880c0241a0310041038060040c0d00c00311f003c4401d921080d81d280d41d150480804260005040030f6954a4076088180e60406468500300050b07030b0300d0000352a940003501c0103110300c90102d000c3e003520505002c1903400011402040141048040211b0982080c4010503840b451404001803600d0800c840810720000106010305808099607017002540e810082c070640800c44144211000118144d0013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 614884451 1250 614883201 614883221
    0x1b030b0a0f0902220806070804110316030b0a140c0d06031505100b040b0a080c041503060f21120210020c0109050c10050f07060207060c0c0b0609130b070e04 69
    0x5a84c5003c08202203201038410022030702018601c910170844c0ca50b000c039545810200f01e141c0740340c550310b0714102070051900d040840ba0b03041c01584150f194191100284008803841151186c001da580c129082088840d0b420b04550203124940001d2244a0008000c000811681c6400205c07070b512170710f0314540640582c5c4020a1390383c0c1c2d6414001000c0610440b032005000742500c02d4036140c200038840c0d1250181501c40700a0107503c0e40404d021498601c166000b0b003108840c445000e199410740140584000c0c841d800000328400404111869071400d400700c0114441132482d0411565960342c1d01103400900d1150441c01a07410300496195140014850b01c200c2800100e86000d0b941842414000c607540324600c1354100203c1c1811a41d002000d035000b0425140b50903807180c0890034007101038454034400801c0c8626040140d1b45403500024580b044900a600c0d4000c00d030b80b00f4080c002c0685003138614921000c0442c0c1900c1c001501e280655074404198030300040e0003d0541d0214080d2a42100c8d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 614885701 1250 614884451 614884469
    0xb07081209060105011e030605130f0b04020903030f130f0e0601031406010813030e09091f0917070201050d0e0d030f0203040c0303080c1b030711041b030b0a0f 70
    0x44480d000c018a500c0160401105409040c1e00e51405001030f01300d5a401c804070400024040d021214940654041401040090007401c05400340c00c0001000380300c4898464034441c84e00601604600b802d1003500c4403008050003c601e0000050390203815504000417807040360000550101d42000d110301c80f00c009020741803502815040203000981640c5e107025619029503010010407007a680c0c030030900b40e00302441c4a000c0f200e102c0c080c14206c804001c0b003195190054494400c3c003074110400100d0001000927100c101403070446441e1900d0690341d0000300a81601c0a142c40748108072480b5000b4108144141044c81c03074840c01c0d0150b4400e036003480400c02d94542200030078542c0d19415009036244041400c4045113549403d81d0740d0107e01da490301020b410480300e00d000548140c592400c41d102e050030301c01042e90181110005940c5d03544580821140b000d513071030020b4140d0401d0300070b13500010380702c40c51440c0c0b1281c2070000310f00800c00045081d80c4440308090008ac07065400080300081d21000c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 614886951 1250 614885701 614885707
    0x15041e02070c15050a090302040c0207092c06010806042d0311160305060a0c031404050703030f031109040504080f0c0102130b040609090b0303040905180f21070c0b0708 74
    0xe0214028840c03e030300c0f0710701400010040f500040758456005005c0c2d0354111000241480c0820b4101d01c1d104543d04550152450040204000b07210400c4129240601c20030300c89038050410320fa40c1d00d43c80e080c42010007540c080c0307012a00040d9011180440004014490240c0f409010200c6070500340d090420f4000c1000d84610484000043c000e0307072045020340a80c160301030b1460b510301740e0b140740060948046c1d580c1c074003206060301d20940140740b140c4041400040300f82801d0034602c0d1280001d100c100c011600030087d4141d030502a004940d0485003a0030070509061100d020b20020b0240180202d6000c0c4d01003003541f010352043d4029204c81ea43d510001a2910003c541448012282d03400245040703900b8002006034550041c072600513a0030300c000c0402d01e0412100443d255000d02c4d0411000300c0e040a00700951074507554171818641142030b040f03440b214015131400d500c842042226049000380460210a5010500d00815819102c1d0003110384082d510703ca481600e4104c1f01040b9a5a9000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 614888201 1250 614886951 614886959
    0xd06020714010b060a050c03090a1728060b1203130501120e03031308070b0a020a0f09230102031b07081b0307090f09021002101415041e02070c 63
    0x501e000d00a4440d0040007000401e480c08001031640c000c906950040010015a11040c45024425502c000a024150040b11503c0d808641d803480c01050a01c0d0700b5108404d4060b00071b010035442506101034610784403481d41307000c0e16650050128100000d4001d1500d030b050940b80c18081000340312013084031803280c031031038100740004069598010f40c00700d413941085030360780c0018000b20460b0742101c000344143e810b2903168500584c41d8002d00e00051b102d9980c410400c2310001a6800a140803485540c2e0440341042c0f0110980e60b1480038081c0390384000b0305030080549070460b503420242ca50014011281054240032800c141c0031100b0380e26100d20b0700412002c02c18258108248242d0041072001200c2201c51000440c0c0d40341f500c2c0c40b5050110761540070400b4511850307404079004540140003001c2c0343c540740001955038500c6070541d02c000f91524181d01d400280409e03081d4000d60480b0003610707081d114074040002614a402e0030142520021041d01903046042c801005054400c100c2030b400d06240c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 614889451 1250 614888201 614888213
    0x71d280f060c05030a0503100f06080a0c2606040207140115120b0a05070e03010c0804020f0307140405060324040b1506030a09080f0f04140a050d03030b040b0d060207 73
    0xc035030300920030b00400c0c80381040029404020360f881c003810340c5000b81d245c0da51901100c03210002a84200292809210701041035540489090712914100e44140002101d0f4501162080114900c4503c041c00f0000194124141162004d0700008000c00250824007a034560f1200c110040c2d800c2d510307a82d550001c2e211021030356001280105400310206c000070b40c0507142c0e240c214500a0884040c696210b00040e081401845096010b86029008002d0300041005c0500440800d41d0164419521070185c0d030034500d4000342100940d0441d00c2003480d00b07250340d024407000d090041c00c2158036000e0480788103c80c0e0750140001311070000800c4900114149818800031101e00982407070030890300c00081c0303400c60315510100d071b41103240c440c000180c001d800c1c200058a0300503560f16500040000070702d03148425800c0044d100395190b64000c051048000c00801103040440e115081d0846018010f00e03000c28001e0f44164102e0001074004207140010000041e01e40202c03413811615560702003802418414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 614890701 1250 614889451 614889479
    0x41e0f0605180a0506030717100501170a0201030b130c090320010c08030402041514010e040b0f1201060b0706091208060102032703030a020c090f071d28 67
    0x100944450500c03500b085490315503418000c00c202003003a240d030003041c0140c80802000c00241000450b052580c014007110989440415004290b203a0408002054510382d04007100038405400c4006c0c0280b40c4940c1c010360280c00e40905090b44a100c0008824801d11203006080840305107680c1c1c400704504618203e851101c030007040846800d480504803c45036041010781d140c054021490607103d0f525440001c010b480e0f0300c0000310040004c1440020b03080d03103981d008080d50000b40c84000c0c00c103c00009000849000d2000305030b002c20070f00041d481c5414a03004544a541600c000418070940703901894036568000c02080b00c0082e501c000740d809001c41d800226180c00010302d0548050308185000035501c0c01610400d050148050300c1c50071403a20006141c20710282c020342500e4a8008240020f5100c1da051070106004164100004040340139807079800740b091070240c03214014012060240707095011071408039600503032034222030001100d00030410350240112100490800d030500c80c080719022 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 614891951 1250 614890701 614890709
    0x18070210050c090f060d0c0e011704050309060c10020a05040f08030307080114010c050601080c0901060f0c1209080a060e0c032107020f060c07080d05210402041e0f06 73
    0x60700d0300d03007804010000d180488201c20300c00c41d00032031100b8558000444a104210b6118695460855100e681d10740081030f09020101c240c950f03141207201c0d5514030345140c0c41141c0040139500100700c5503640749814030141030501d030b10504444014031000541402caa21005090f0003050340407504005503441d40b040400540095805141181000000609406810b004045180a050602154591146400d1102d4a800208607a95540c1d508103080c0c4640c40888264051005a400818a1400b0f210100c1114147c0d51b0780c00b40a030384075294629501d0090220200f000400307031001420340e0040295400203409a20f00003800c0320b20240e440d15110600c01194000d8000c180e1514a05964442c10b942c1c0b8a0300d03a031440c3d580c10300d80c40090224100840e810781d0009000ca140701c480c00c00090304005845038041164411500c003103080d11240a68080407000d903001540e1048103a01c400607040d04103201400200f2000c544080c500300542c0314400c00d50444e669500d49451b110350345c2c01404010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 614893201 1250 614891951 614891983
    0x806070509030c0906151803120703081302030a170c070819200a08031309051b071a130303050f040807020909120310031109010f060f0201060302180702 67
    0x410808008a5114440d80703505904c210032400c000350240d158404d1917041980316004a40e503c50f4461110650258400c103164040d114031008400000d2042c403c60310b000d074141d243e4400a96442084014009410078100d03094000c0b5460440000c80c58140c7c03c0c40700406036005500d40c003100c034100b468408103a01102040d844007032004190401d501807c0d140b20f420801c201400300894005462030840000d00c0740e0407003005800040d403000c2c0403024001e0500302050780300581e0fa40d600c00702c080c1d441c2542e040030b5103280c007145010107060400c000c0009612070f5449241c8016640c40e413011125044071017030384415403520341701c00b015031600c58076a04c020380000d612010b0900340c03682c81981c090020001d00440044000c40c000036000c01510506000c1d154005a8916000e0785551501c03202e4030044803d01007a441411052405c0c815207130607648030052244010745005021142c2c0e0540c40d02c210255541d038180403000d43c40e541010320b40e4941030200345006081c13040b4020714200346401e0102c44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 614894451 1250 614893201 614893207
    0xb030a0e102415050a030e030c0a1a06060d091103010c05030601032708070f0b0406061403010207031205060a0b1b0f0d090510050d05040b1501020d02030706180807050708060705 78
    0x2155501d803c15000b024010315000d80c442c2d042d004154000c0c441280041054030011481d5007650f04c0004e0f1900403079100f10301c501843d100e1004109101c80003070700c0f4183c2c0040c003404030b002a0000d60b0f00456156000c0e104070440c2c2030060001c24211054026104c0000d5400820050556010b0142419140703034101c56000d0407265207406814007048100007080035038001410760a01400b241b20368050f44d0081c10b5402d4900f0540341000003050b0174464458100321900c1a64141d01d41882074840643e0107890700d500d41120110518020013000303000952240142002080b1340800402920004201c0003280a400f400a24650700e03001415440301c940d6031009145141c002d0740500c004007128010303214044407080810b0b0a0351580601c1808800080c40c000400003800b001b030200b01d02402414104c6500007045600490316070038a00c3ea80c50250340200b00c8000010807940c0940380304000b070101e00d40a0003450b65071500541c004a070035645544103510a00215109002d4541c0140d03090400c00d107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 614895701 1250 614894451 614894459
    0x1505030606060a0201110a1e03050919060204182304050d1202040b0d0f0542030a030207060e0f211c030e071e0b030a0e1024 55
    0x1a984000414807800780c9004142c0f182064001d41108446d220808169a241d880a50000304059440c288003071080030443e01074482c50340a4880c1900409140c0043c203105070044042601324082c40302c044605070346c20030000071240072803803d4040c41840590042001c00302c1d103034440c1615464a4423100b001d002c0c0e20030302c4005000069442038680240c1440504100c1500d4688000d0103503600851121800040c20007100b1000e500c040c452001c41881080541c443d1aa008800741071001d00781214054100b89951000101c00410402d02000311491403810030340022a08011081d80d0031409680411002d110301a00300c030102080501c1562002c01d1070b1700c03040c0042c0285480c0303030510b41c805541c201d5007000e5440074021060300b106202220301000c42c071660000d0052101c60609000c82c0525580810802e8240f626105035221202090f400305003041003281190340060046e0070030952701c8000b0021520240034544084904080020b03036100030903030403101010305084180c04030654000c284 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 614896951 1250 614895701 614895703
    0x8060a0b040509090a1707021306060e010c050c180f01080309030c0d060b0d12030605040203040203150c120a050106110f0d140405120d0207051c1502071a0604150503 73
    0x10304558040360f402d100c680311461003e080000ca40e0025019200b00188100303034450380801021154070079503140b840307000c559a00500f00d51090203900c00040040001c0304d032a40c858203891090600690079506005221000140b1148a03d00001c0b205407a40042190703001525441600424040003d18542072201d00001e4441c2092241c051003181150440000e109a552010000b040003070321001c802d520b9801c26045e1401c4011f020b40004c2d08103c03003c25513044c0303402a28019a4082d0042440d1740d81030598490345040280300c0440c80b03a040c40440c0c105501041440d0050600c400700142c1c07941052001004603c484c0c0c2c1624990b8068800c0248070740000031001c0f00d081e041e103014803d680b04c0c100080d050340318a520965008030f00e810402c065900c0850034180d0340d9103580071160000e503550140b11241500c0c1c0d8001c02c410505c0c103201c1002c2080e40510494102104d4001494680c16585041c10700040050326074109080c1400c0001d03500b4103101d804640e404211210546a180400003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 614898201 1250 614896951 614896957
    0xd02030f120a020d33030201020a06020307020f0322090b2404051003060806010e01060f2109060c02011d120d0207020d210302040f0b1b010f0b0108060a0b 68
    0x30365441507000380000d246100a42c152031004e0411039082c84945000c5850071160390303503014050240d151081d0344c2450908804000c0013102d9060300602138420481c6c0b103002c001d40000f00356401b94000e4594140c03001005000400c2d840010b412090a40c0441d001012a102c500c0d8003d100960310306154440a40d40301011041e403094410075001c0e8194003d02c881c00d8034003d6501864201010171000b98100343c141d041903056a9401040720450fa0340ca6002e003c11004c20b12030321003c00c00ca040c4407038030544210113801c030724580c80000c0c045100645c0000310803201100426200680c0c0e400741c86507042d034203010728265843d903a8100c441c3c19000e4086c42c0d848070814581c05003103450004620ba03005000b03070195844150001c2141da0300c2c5c0c1e100d0a080b0442c0148510402e1001c3c415201d03011507502074401d450035901c03114440c440c640d0802850344550781c01031215280b000262003e04102c01000d0140d079040340c074603003000310351031b030030f990000d04944005000c42d44106011041070050b100300c0d4040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614899451 1250 614898201 614898217
    0x2030706060b031b22121401020a1e0215010e01061e020c010c0606031a0f010b03040f030f0e0a03150b1206160912120e0108070f080601050d180201020d02030f 70
    0x8502e030742d04d805401d20301d03504e1007170316a14800d41c200c2a00080c00825090120f00c0c2103008600300702c01ca000200480d0308071b120f43c403159408140091703a40040003840407019903c02072140115052207005024004c110304003640080402500d030401400596849985150107404a08a8101000351036401940301c1d64141039480c108410207048606000c281e42104000319040f01031001544002035515920060132104441600d103c1000084c0c607a20920880c1e20507900400c8014016a00e0b0f038003210200c602040b18820004031894211207546d4038280000114481c4810304808401c6051603003e940401d04100d11540480e502c003c0610300100e80254000380c42051082d44a807481c00540b24900c03150404c24aa481131107401042103284c80e010720b0014650703120000d25240b03140046903080c1d4126015030004150301c0044404c28065021036402040505100d400c003031040055000b1240991184000030080c90190000d65030180001c0450700303421320240d45030406040382d614641c030850340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614900701 1250 614899451 614899501
    0x109092f0d060803040f0501140f03060406050429011407062004060f03141302010c03020c03030c06060a09090507180b060f030601030b0a060f03150f0602030706060b03 74
    0x6022110281464101c8440e454400d0041200a80394024550b4a82090107400781481d15401c0100d030540c00b409030028a8800b1180e0303145040c2c80006421115007024000030f8002d921058013040541d0b69015580d98012070714180008000b0401e804055030802c80320150600c2040310228004d180180100c8000d80d4001c60089a1401c8002000c105900041c100d80b03005100480e01046003079120701c01480c031841c81c2c0c1c0c0038000450900c2c3e44e103810303403800d440b00402e01820318110b600650007007140c85216030083c010386940a42d1900407030300715400314070350002d141c100c030301005414540428004040d08028008220103881940c0c2c841c0d4a0030300740110040700c014507290307450ba4105074120314041500a00760036241d56100c580c1c40c060b41c00a850701d9011904040912040742448009241140e80503601c0d406909070b442400d4004040307111109030401840c40c8040340c03452803500311200900c41940196610240d9050600403500c0c5600076012005040081c008665581c24403401c001003001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614901951 1250 614900701 614900771
    0xc0f020a060b03151906060f0c030e210c150909012304060303090603051501051c180b06030609071d130b010924030803010605090a0f030f02010909 65
    0x1030000b40380941d60b4013069240114401008030103020802009072101950b1014810180c540c401520f940a2440c407000001c0c82403000d0740d02007485511405050000070b4440810090070032600c00601c041c08000d082c0726404002c3e06079182c10010030700e01a503c1c03100d038510b0406242000194401c1e0041c40380814840408a0340508007045540c1d10b5a2014002c2c01004059a80d18000e0f003c40e1840c4200404a842e010008085031311103c0d000c01c20600580d15180b4104004c0e048944100108808004645c1d48114111007040030b46108100c480c040c96003810701f440c00504152900a0090006e00c040d04883c000700400010640f540d03903481c1c100140b00013140d41d1070882c4048183c0da00809450000941e0000a6003081540700c0402c8501d0380246907042c000081c2030030020010780c800109110801c200401c0143d1054010b018140401030840c440396682c1c0c41811410b01c01900152006040d20801e00210740c0c00181140c001c01c088003062011200054841f440c0ba4450380300526002540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614903201 1250 614901951 614901971
    0x1d011d1f0e150708040b070e09042607150518030306060a05091008090f070b030105091e0a060501090e0c070b0402040e39031209040b220c0f020a06 65
    0x90002c091100706011842c03030503180c007100c001e20b602800d54003540e42c82c40e1100031035030081c030483da6800410300c0644191915151030350360010420700e01003264008400d0005480b00f0041c800300070510240505542182284d46088403001c0304c4029150706018400724824101c03650000c030030759601400440d085503c40b0b545007000d5a191140c2c1e4141ba80c080040d40e810307e5020340040c9850b004000e0602100c04545002190356503c010500402180c000240300411161038075421096000e00051808031040034a410020002c01c0c041c1c4409210795103e001c144801e585c03119401300180312400c044011030070580303241809442128806000b0101000000b400d546894019219007503124007283c4003c1c1607201440c3d040b500e02840c007400600341840c4514181c009000805008500034081d100e000b41c1141e0000e07a50380810303440d581054949141118942d10a480401850f00002c4400c9105070b9031048138084948843d4010300b401202c45c0c0014001382c0c00a140d15045500c1080007820f4016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614904451 1250 614903201 614903203
    0x2070e0c04050a080d1e09140613030506160903020d0204051806070507060b043b010617160b0306010c060b06040303030212090708120304061d011d1f0e 67
    0x3560000d58000842c0f007000140c0103000034030b01600304a10b0390340a900a450113681c20541024000a400050040f141800045042c0c0350300d440703024004124600e4074680b03141070900728911394400d0b00c10350040e0080045a000c0f000750705001c50600d01c0e0101d4020309681c0054501d0340550381c081d0003140d990307002074903140c1d001c148140d2070010101203415514111000811903070080a049802d1400c1040d0807905080c140114010410368021031904078ad83c218610103511300400794800a250140d49419181400703108100c09419122002580d00b4842c0310340301d00e000007000c000b00d20102c6c1c1090820000080701c099a401207400d20b4105e01d040040d04014025011417160340b80c0c1700400040010802d501580200000d40f580304400f01d0303582d100c0e1202500d0341030b107124a041640040314001c9244260100469100d840b23400005407101030880068a0410840f0320004260341da0b07554a4952600d890a0308942442c1000406031030580904042103210341c2d9103c0803001d0b496401006140e44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614905701 1250 614904451 614904457
    0x90e0a14011a0f0f0402090105220f06050705070509150a0e01050405010f080a0f03110a0f0611040b040902090a030512030a150605030631021b0102040602070e0c 71
    0x40c110244100034854446814001e10402e262001e0035000c04064108074100407405000526000306001e258414000034040030354060329085040100400070402002e00f140c02a02241170980d134004010f1341071000c0c414516006070860001e010717082c0f20081c00184000354545c160380307054625140d188c40303000039110700c40f0b40320f00690341c886501100407805203e000c6d0001e04803041241d0601c1582d80c0c503140e54103411064000e008150300040e8100010400100c100c848452080c98105a156504e01505003000400034003200e03600c2000c58144144126401840843c841000a075813419151010308d202c203125901c40c01070f07029000f02d001311319552148411002140c1100542c3e00510901da46c18603207500c00c50b001c2e2400c41c503108100741d0b40345032603482c41c00f81c50464607410300d11303191641080001441c4c46018040f03000c490009040039400d01c03c810f01940d040800c0076840c1c03c074106810110030b580200001c41e60b0704c144810002241c2c0050319408a507a440c4404910341c840001c1811988 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614906951 1250 614905701 614905703
    0xb090c0324060c01021b0106050d0b011203050d090308090c040501050f0d020d08120123210a05120c0c100512040c05060a200a0b01091a0d060207050f0706020601090e0a 74
    0xd480030506c030340042c41c90004c1c40c560348200b8001300221603c8070200880d0340381094014210400020051090005000d0701122950103810514100300b1441740c0714055403500d0404800180d400c0050021900003080309442c03a100440c0c041c40158100b00200e400c0900002440d03100380040b04401041d51180e2000c0d1441e036800a00660707807001c50070720500039281c081c4903903c000e05104040c1c4500040c480741c40c00c044480201100424440b034a6850240e08295108181901485d001000002c1040040452251081d107503c0e40f00c5400841342800c011181819500980d0313296410300c06154454116200ca400c00050420103884d10700703111504045d1a004541c0101c00020302410003900704a4040c0701c40306400501c0c1c1410b500c48495074a03501c084200038071003100350300140440310b281d802c480c2040810b1001d081c0b4003c040320000f000805e282030309a07250769000404c0810701c40e05104850032000550010300310355140c039600030341c2c41e00c2c144a440c2c0c0c11950703241e010b105040305020684040d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614908201 1250 614906951 614906953
    0x1b040c0903050d0f27051903052a19090f06031a0705070c0803074d0604030804050406120f0305031503030c01050a1b0203070219180b090c0324060c 65
    0x109060100c00e480d1a02d00c4c0a02c0b4890b4a090840c6c683d2031400802282c1900c0d40f10000c4d04d040700d80c40c039101030b9404000300b41d551040083c02c003440c01d41d258051252f4500d00ca207490a010b0510b00f00a00c011580402a44103e11303041c41024004640c680c410103401d0b001c01101c000f082d580301c0c1e00072a210300550000a00c00e062520b80040c00c24000009040100d0140d00142480090b070140000101f80007a80801019002d800541805440c18184692846100e0b01e00e0011855880020001c3d4016041110302600100b014006400e05100c1d0300b01a0517018050250711003d625070040200180b4401400c0110010000e05080c42a112b001e182c0c220240840e610b03181e101c07900d50301901d02203031920483e91a107005000d208116000003001c00e0455006540b83c500720303400307210380c3d040c920000401c60103125000203420715000d8006640340c0d00a510014850034200104100040c0c00b1340503868000c801d001b40011110901e841c503000d0100034000040446e61100131400c1c81c050001d00081d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614909451 1250 614908201 614908247
    0x7110f060705030711040522060e0d180b0a090b03130602030c18010f200f0607050a080609043201050a06030203190c170a051b040c0903050d0f 63
    0x2c006000010b4066144507440038042030801074248400c4034000c5610343c07054040c0d0900b5000700100407101141644c02040007250100085008500d8124005c2900c8001081981c85440d54280320114402038102408514500840990000c080807440d006551801c0f60001c080341141c404010510032140c0d00040641d03c9181150142969401c001c060002d2188411000c07102580300c4c0d80e440510031840e444000702490142c0304c1030f00a5010807084070180c0301d44210190190003c1254520030415551060380d200a0002c0007090681d024107030a0041541c402030000003001040c4800c1c1181040c030403540107038940c860708401020f5110304900d5030b5181030b0a000c000f51142e00a101502e000750111092030303003800d040d294105901348000c0d2492007200e82c2407052240c0c2128181100c580e1000b2103c503460240c5078141418241c001141d584a80c1c9070b1401d500d810710f4040d0900d15021810440308903032954880503140d02e503905004003000421a00001e200340112001c1440e21580b84407814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614910701 1250 614909451 614909453
    0x100515030601030b12060118200703120218040f091a090706090806040803043801080609070312090306020d140105030a0807030c03110a0c0e010f03050307110f0607 72
    0x5040d441501c0090019041c00b24038840e0b401d1403d184d0440400c0350004000326840e280500742c80d0b9540c448101455912176031101c2c04c1000074020203034003031440d801b09584e400891401400d4520328841d4804a1350040c06007030f0070103941020f03805003807000b0748010448441c510203540042000d04002800400503098080007002d1404050b44214508030071600d000b5100c0c0c1040d5071a0240d8823641c885944400d000400061004001c2c580180c4240c440030000c0620801140124522082c6155002110100743c0d4079079441d0564540140080302c00703001241843c214160700e5030ba1900000e45141010802c051090380705441403070086030407601c01c5455404100d801e0340648218012100c4c492a01c0001040503d00030070320182c400e90101c1624236100103941d0643d181200741400f94184040c0d1400031800032014841c89802521900403e10844c3c10301040c103440302c0381a00100c9180500420074030000c0d80010807100c116401841c81d2400c03505200001c0c180d240d80031186500600040761180c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614911951 1250 614910701 614910739
    0x50418170d02220f0b120112020d0506070c0b060108070507240e070329010326070f1a090d0518060c060a051e0703020307030b03240c07030f05031005 66
    0x751020400e00161143d5203802407180e6001c0e06d01c807000f240d011351004101500030a0210b0150038405401c0c0031190000c1d4580c94201401181e18002003082c00c0c06450810030074480090307000e2002d0a0030f41d0141440783c00240503001d0000f00a2a20310340c0d401c8040364200d145040e4124403490b01c01130100400a100140d20382a407840103d91148080c05043c07116601c040704003c00b80d20307204600302141e103142c690380b50030807040c2111001e4810305078158070040b00083c028009070340203d01040c0c0c009030602c0c00c8502d140e014000d0f55007074008003050200100300800c0d5200104480d2410a483d00d041d042007030b2001c0c641d14070700d607030168001039101c1210201043e00ca1203110031403000c000359500c10304030403c8241d03100388206078a054140081c4c07026000e540510342103142031600181401010b030100f442c0c02c0d100a6030f02c20107101501d5041014400e07120403540140c42d24411401c090032658040d0200540c071144c001030103004000a80c1d03200ca040080801454000c0c0130005954404080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614913201 1250 614911951 614912017
    0x80a090c09230a1109010f0512040c0e18190318080d120c14030406240503100e070303030506150307030209012607080c120a0501050418170d02 63
    0x95100e04510000100491004e21600b01c00c0384440764080c0ca4009500300441d040e0495818110511500744442402c072103181100d1031080348600c1d8004030303d81c104244a402a40002c00b42c100c4bd00642c284e0b03884160010904804284658104507050480d03464151202c1c4400c2c0156400001811030000c0c8140d0f00007600d054075003058440c0700752550380741d181030141e90128180714085080c0880345041c0c0d24024000b19800f0f4003d03a40001d1140b500070088060142001c3c0d11011000c5160007402036203400d1014821800c0d400e03004002c0d815a01c00c2c42c40d110340891201070301303165540d0006900d82d00c41c10424042811b0701282180d0b00e142200d406002904015110380c002140381a078039540ea04116807410a00201041040340703a50303500821284800010881744581109000e400041040c010603107014019041020031150b0402003800229080b034402107201501d074698586c04038003540d0041016810b00218a0790320000340180a000c0d10a010748981919119aa40c0e6003161034101c407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614914451 1250 614913201 614913251
    0x204090506060405160903030f110f1b0109030c030f0f0f030807021203040b390403120507020d140a020901090903080f070f030b03010b06030f04030801050d03080a090c09 75
    0x1c00c0296417110714000c04003038110f001304400308140160910102c0d00510880381c0700c0151b4904444090388001010342410420000384c00b05034409a02500c0c8942d03c0101031041c0f5400380703000d4040a10b10f0b1541c4103080818400134107a0200b0311b14150a001c007210404407485d4004501c1011064985001000110216501c4c00140900c0c4894000c210340030f82103e00458200c02c04546540714208401c100009844104030b0018480406c04618403a007029040c81542c010b11141d2100d1960030084100c0c3c0741d40c41a44c003040700420212006a46042d0146050303038020214032095000703910b20310f2034008914400b0b98041c6100c00001514001d540042032070512a03a40c56003561140d00200081c0314003511301c0d2005c01c005030300c6244c40c1ca00c65400003a0b100030040000c00c0441484e404101c2c2540183c1c0d03241100c540150411090540003000d9a00405007668030901c440c0721074400400c0d100010b40f0080700303d5210706481013488107003009031010700302c1c2c0d0004014034a001c041d800c1e0a420b60140d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614915701 1250 614914451 614914459
    0x30d050403050f12070b0a061509030c0504020c0a080a020703021503090c030109022b08030103050f061302060a05030624180f0a05012001110913020c07091503020409050606 76
    0x1500c11100301c0c089050010199814a0a420300d85c0701ea550348440302d00100618003860740c1c0c1c040081ca05480c00d03408079039070314540c942d035242a0860600c160309110540000340a0b83c010442d000c0c10f4000068201c0019821510b05038688401f0b41049040642940c4007942c08002ea0301300c0071000940c100114000c95121080300c0390b040d4180117150981e607507501e020758080511010040d2000d4040481138108a00c0700301d000d02101940d689000503002a0015207042e807107180f42c040c1d4081d0030003003160031010114401d03076202d2095000680c28802c64040e0810030502001090003070302c4070f104484803171800e524080340c581d4681c898106242c21204107115444030200c0f00c00660b0130501c428602403032000c3c00d011500c6050000640d40c0c01c130303d088200c0c0120410f140b152803591080c80359803c1d15900035541950382840d0010080c07035103005240c2e1281c80c1e00c1080b074001c0003030b00001d0303040071549032031804621070442201240089010f6030010b9005070409850b4000c111b400720307144c4d20a1a0440d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614916951 1250 614915701 614915713
    0xa120f0c0f0c020f3001020702010906140403061109060d0b090604021c0509030715140c0f0d0504140d0e04050c130b0708090d1514130609060b030d05040305 69
    0x8002c0302d03269007501000e5000354549011452034145039245109416188000b000c14004c0c0440c44013900c0c941100d81003030341c1d6001c100711341150b034003c58910040c07441c0e00e820300020011743d10700405803269210083c5410340d2100206d181081c5c420a48000d0000188099110081c0050b0f20380600003c50440c1d104140520004941389060b2007584e401240b0104503500c200c00e640d15180040c42c0c0039104c0c000a2005200d400000b981034400d0480f0082125400f0a103546404404440404050050600d140052004008402181d0241c90320f40160000102e802c4d100c41c10000c50400d0b1070781007a8003c1c082c00300c0119001d50800c0f50300c80064010740d4200400c1c5e441222442d0140640c0c5d82103030380200e002c8030800c16510200040c0a0301409000e10b2031603d4440000507803065514481180c142c0c4080301410782c1410907119003441c4000112070580c0c9840c007424a03401c002212100105180d545070742060074400c941e03020060004c0083c2c00c0700d12520014201801d01d070050300c801c43d00e5104032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614918201 1250 614916951 614916977
    0x30f03080a0b12031b19050708010f050402090609071e170603010c050403120e092404050103050607050f04080d0216090908030708060f0a180609050c07080a120f0c 72
    0x4080303092190000c401450401902030207140310302d1003801716800d003072181130030090714400f90a400b40082d510400051410919290b001030941c0c0c0307800301060320380d0b190004000150303c0340642158000004c881c9421140d85d20b007415103c030240581d1401311000000da5642c001c603005071180a0b41201007603000025541c0c40e080509840b42e842141001403070038801040082c15602d0781070020341c0769003040c0114081103000300301c5002c02103c2400c420700311030706030010042c94688550b940d110140e03014490f035819030701c0d444c0d80c0e500050714000030090006242c400e0101240b0981d4090084041581ca03c2800a0002984c132041c1540c02816640c0e00140040d42035110321079400340590011800741590303580b80e0142c6144500400864104682c4103026480d80d494109240140000b4001a442c3c1c00e06030542c0c1080b1503ca800a105291400c01031019048030308040d501600d5000e400c103603840d109840110746148046140f043c80d50f06240b8140800f94140d040300d02900c603e0b554040105140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614919451 1250 614918201 614918209
    0x52802010b0607172a060a0b0913140f1b0306090a050c10090806071d0f0319020303040e070203040812311206020c0d09051804020a030f03080a0b 64
    0x680d0300c004018040001c44a5042241c440140c05401d244003140c040f1002d202c00405d5201c0a030f04103101250300084100010010035200d00414048103445604052904c5240242c0b80307400800007820200d5403000c40b5100700420000a150100003005880084402c01403041101c543c5c1d0380950320a00540c0c00180381c182c0005520301c0d505030844000c004002a402c01c1c0441d40505140e60802c00116810124181504001c3d03940540380e2a80c40412014003036180340c400740b4900071101d1082c0c40c070b500b035041c0583c0c000403224110f03880000c1c8040300b0300e49480000e2551240b41d00c500e54045a4804100c1c090b81c010016104561100c1c080d20640781283ca4440100d04c00c14030f00c1c01d020034070405000b102000159100741800c6101e0701c1c0d003841c162103405081d800180c00030100c50403a00010044d540e401c00f401440c81c200c86c0c43c20301031900c1c1d003000001156514000109421007503080005002d5584d0702858034000c0d5045000c0003001d100905000304141e20031500050303070b44c2c140341c17002e982810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614920701 1250 614919451 614919457
    0x5010515060310060f0c06060605180102070b0d0b0f0306040f1401090c0e07021002160c14011b0503040f120302061e070f0527030f121603052802010b06 67
    0xf201c41c81d00403880341000c01c1600d040000811610070404c0d010058000100544140f81c0900b0594540b561100504400340700c141c4c090700c0c8140e045400c00784040040c001400d05550072481301d6000070500202d604041150907200f81e5003160300d0b1042400744010301c00c4196042e41c26900842494568010880691b400e031581c0c035000a00c0c206401c24204840c1d0312810300b85401543d01c2c8141c9004d1810304503420180c0e0400d544040c4815040200c00d400c004403034000600602e0110a460314400582001904504600e102810480c261001c02e00800070113004441c00b804244c5074008070b141d120b0820802d291845403049025104240100b90340804124500c0c5215240701c00410041d40d41c510b084a84483c034000c003800b4040c00780700b1040042c1910300e8080015100c0151000301d90010010146008603000740c452242e0000c84250200381d0804041740c030800700c06000441c40d50040d00d800c03185480b555a0300c03500341715031800d6282c2401032850885107011140d802031061712104020042644 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614921951 1250 614920701 614920711
    0xd1b08010302090c071b030309050330070311010c090f090509061602010e15070215090a0206091201090609020a0602031c0510030c030804150c050312190603050105150603 75
    0x490300c000520a405513802801c66521a06010020184c0b0303882d50f046d6524950001c80110340c240d041030000b41002c1051140a5034201e2800f0b003003c0e1114896041d400e000205000003480c001011401d150041151680d0203800741d008008040c60040010b141040a002c0c034000d404118500141ca10b44134080e1501170001d0202070482074a8111035403d11200c6d0301d21410541d501d424070504d81c07000c20711400350003404980c600d6042d13203004400203040002d02214860b9032048001845045800041e617003484542c16181c0c0d564030104038000410710002d41c002d00c0c200c1c2d0700344648001004595000750174094803d4950311000c58451400303036228040d030040d035120f05d03c52b45212015000503401442e00b016043c1692032406440e600e5040d40d10605410030b64042034001400c000740c036040344045241080d03910b003000f100d9050340ea40c2c588a100f0304501c1c01c06040b042003c1061a04030080c611410070405404010b81c2c3d41d203242c850301030401141d0b01c1c1c0752210000303142d00c043d0134110101ca1140e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614923201 1250 614921951 614921959
    0x7050324030d030f0f020406020705031c080c0a180b0a2a030c0f06062601050f0103120207180b13140c030a020409090803180d02121b01020d1b08010302 67
    0x40c07808440c00c80052180f600300301c400030b84079042c01e14042d17020320051014050b6a805040010b080106062070543c814005e402c18007125401e00544582c0105015080040003c404c5d542c0c0d4000b0b2411a0080442a54800240070114001402e410725800900902c61107864031102d4101d4580c14a2005d804008032001c5200c41907610700c0000c1c880c1a00c889400d107d60300c103840b4806a91254421a41d9542103518400c1000d0000b403080c5041d08140600d40f01024024005d503e402100e80342080c2040c40007c00d0386080340c64113552140240428000f030003070074581000021031842c04d40058200405514000c98002180d81c40350044d600541d4200d010924051702c86445000e0006400d61000304510525a82844045401e001ea4000c0c27410903400f9940180e2a801d242c041801183c6190545040640c403441c80c140d003140c1c000c13400401c002d85080309075848c0c4103684030140b111885aa2030b681d141d4030004403c050f84141c0d078030045203104142004091100c0b0035400355076120081c000039500c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614924451 1250 614923201 614923213
    0x80f07060e13140108010b1219020d14061f0807051f020a050a030305011404021606020a170a0615020f0a0f0305090d0b0a2016020303070b0705032403 66
    0x490a020420b01c0340404090350019459015014502d1085070a0304004030740d035121080f44d58070780b034801040f1120518403809071a00454160480a01080d8800024010007001c1d0950f001d00031049454261000701d00d09a030b03214075001c0c8403801d01c541c1e0925a9108058948d0340482c0030440050a001514009001040342c1108100c0c48000c060744415032401b1403055004c100009041881406110303031223510089225418040175407240d03c40d001c00140100d105214201180050150b003034000b83d00800c1c0144d881c0414030301120100740c2c1a020840304075006040c04105442a17000d0021556100040d5142c9a5425802c9813605170410740540d1a0b402818100003107101c3c03520042d0607030701c01e040c824506050180030640540c0795040590300c001d200070422a200c0094003501500100d100f11551100c4405800300c60a030044c5039032203801104203001c1104544040040f282099041203100c0c11601c1d0000d00200150320483d9029540b4103400655481e4002e4000341012804006000c4c100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614925701 1250 614924451 614924477
    0x4060903030f3e0406030507120c02190501060b0406020c09061203030c03280b01090603111602030a05030f0d061a03013807031b020604050d050313060801080f0706 72
    0xc3e00b1014103000b1406608549001c48084610401000245002d0300c004c1f03010b10b04414080c1c040c40c4100c0c0c10a601038144900d1600c590380c0499103002d5a2034101354043d840046007062070040100b600001c40d100c100003008910550006001d00c45490101e61041c800e94400090242001500f0340c00758007607100b4008100c00440d0f0b9000341d90b0000f020403682d9010f46040e107000c80c8245102d03c0300ba1100d9a24042151039503400042400504801d05040c0302440d0084041040e612400743c0780c5440b203c840003481c01b1990288207400002d500710048980f5540d0781d6901e0301a41d0f0007000c0c11500e031803078100300003225403e42c00102607a2245440303250547e860b292220b80480340181d078503164002c0d0b000080d200380c00ca00300c0300031888145000341500c0304610310f005024044803131103508000003e0090b00e80141d407050100c80c2a214255414408640c862074017501e94001d1a00d075070880400b5a01c04120581d0011403e4102d8442004075400070540700031581d15058140160301c0080c280f4500e0032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614926951 1250 614925701 614925761
    0x705120307120c0507230304091a0a030c0f060e0f040e150709140402160201030e030d0216031229012601080606030f0a020d0c0e04060903030f 63
    0x5611407450304141d205002c4003008601201d40041800c00490030209401d0144540c400001000d2030107044404480721070425000d0743c030f001e0f521440c0041620380241901d500300d03c640014030980058131a8200799201c1c5450403101d003050280c2c8e00c10307049040c0c0000d1014400c100307525003241c020b0060081d24a14034244030203041c180f030b501c034020304c19050b4524840070103410080c81140c6070303035842400505000c01c0300010f107207900380144200c1c014080310318003003002c0c10408131032582404c0015520941b03062030750450103243c120284141c4042120000e08152183c00030f5124880d58603910020000c0d00084100c69130034003a103602120010011a075503000826165280605050a00e40c445000209846c4040d100c00701c1700310001c0003001007040c0381040000c1c0b50000030131401b0300500307601c0800d501e68400f107000e0080e10506d6004400d00c248401c4195580107825406200c20a616080c1000e002030841c1c480218006490b1a01491440840d44180364120880c240c903103500400300007000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614928057 1106 614926951 614926957
    0x90109031718070801090201030c0801032303300106020a08180607021c02030705062505030f0a091409100923010f1a070512 55
    0x100003900110600d1040856005240040d5600266280303050800c119442c2180550640480e07441c0064110110b818001c2e04d09100765400071b00110748540091001616100340c0d504140c810200203815840032200302e50840b0b04005081d241c8100201ca0b18005640070030040c842c107110800300100a80c0100b10030700203081e24030610388900c43c241c403400e80305e0314a20400311440c10645c1e40d6039080d06d00d03c83e009481c4aa1b049842000080c44801500c0240e100c7c0c801c0c0c440c0040d091070858101c0d442450904641c03001d494010301450001c50546404032070601043c002c003024000b0141c06414000d0150382c400002c1c5180001e0040c43da107840e02c0310707402000410100003200d1005190b101c11101070304000a03100c0091410105141c10039a280340a800c101d4000060380402800f030b0b44107a6030380d0141c10200b15901d440e140040e101d0b0b00e07070050035a0070000034212000214809 = true := by decide +kernel

theorem cover : BRFrame.Cov 614748201 614928057 := by
  have h0 := BRFrame.cov_init 614748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614748201 ≤ n) (h2 : n < 614928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
